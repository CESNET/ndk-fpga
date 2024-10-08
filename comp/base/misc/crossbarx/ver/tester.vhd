-- tester.vhd: Verification unit for CrossbarX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.basics_test_pkg.all;
use work.test_pkg.all;
use STD.textio.all;
use std.env.stop;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_TESTER is
port(
    -- Clock and Reset
    CLK                : in  std_logic;
    RESET              : in  std_logic;

    -- Generated Transactions
    TX_TRANS_RECORD    : out trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    TX_TRANS_VLD       : out slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    TX_TRANS_SRC_RDY   : out std_logic_vector(TRANS_STREAMS-1 downto 0);
    TX_TRANS_DST_RDY   : in  std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Completed Transactions
    RX_TRANS_RECORD    : in  trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_SRC_RDY   : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_DST_RDY   : out slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)
);
end entity;

architecture FULL of CROSSBARX_TESTER is

    shared variable tx_trans_cnt : natural := 0;
    shared variable rx_trans_cnt : natural := 0;

    shared variable a_wr_ptr : n_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_SECTIONS-1 downto 0);
    shared variable b_wr_ptr : n_array_t(BUF_B_SECTIONS-1 downto 0);
    shared variable a_rd_ptr : n_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_SECTIONS-1 downto 0);
    shared variable b_rd_ptr : n_array_t(BUF_B_SECTIONS-1 downto 0);
    shared variable a_status : n_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_SECTIONS-1 downto 0);
    shared variable b_status : n_array_t(BUF_B_SECTIONS-1 downto 0);

    shared variable trans_fifo : slv_fifo_t(fifo(TRANS_FIFO_ITEMS*TRANS_STREAMS*4-1 downto 0)(TRANS_WIDTH-1 downto 0)) :=
                                                      (fifo  => (others => (others => 'U')),
                                                       fill  => 0,
                                                       full  => '0',
                                                       empty => '1',
                                                       fill_max => 0,
                                                       fill_sum => 0,
                                                       fill_num => 0);

    signal err_reg : natural := 0;
    signal err_t   : trans_t;
    signal ref_t   : trans_t;

    shared variable l : line;

    function get_throughput(sum : natural; ttime : natural) return real is
        variable max_thr : real := real(minimum(BUF_A_ROWS,BUF_B_ROWS)*ROW_ITEMS);
        variable thr     : real;
    begin
        thr := real(sum)/real(ttime)/max_thr;
        return thr*100.0;
    end function;

begin

    -------------------------------------------------------------
    -- Transaction generation
    -------------------------------------------------------------

    gen_pr : process (CLK)
        variable s1     : natural := SEED1;
        variable s2     : natural := SEED2;
        variable rand   : natural;
        variable t      : trans_t;
        variable start_a_section   : natural;
        variable start_a_col       : natural;
        variable start_vld         : boolean;
        variable force_align_ab    : boolean := true;
        variable force_align_start : boolean := true;
        variable a_align           : natural;
        variable b_align           : natural;
        variable misalign          : integer;
        variable thr_sum           : natural;
        variable thr_time          : natural;
        variable gen_time          : natural;
    begin
        if (rising_edge(CLK)) then

            for i in 0 to TRANS_STREAMS-1 loop

                start_vld := false;

                if (TX_TRANS_DST_RDY(i)='1') then
                    TX_TRANS_VLD    (i) <= (others => '0');
                    TX_TRANS_SRC_RDY(i) <= '0';
                end if;

                if (TX_TRANS_DST_RDY(i)='1' or TX_TRANS_SRC_RDY(i)='0') then

                    for e in 0 to TRANSS-1 loop

                        -- check end of verification
                        if (tx_trans_cnt>=TRANSACTIONS) then
                            exit;
                        end if;

                        -- generate randomly
                        randint(s1,s2,1,100,rand);
                        if (rand<=RX_TRANS_NOT_RDY_CH) then
                            next;
                        end if;

                        -- new Transation
                        gen_random(s1,s2,t);
                        t.a_stream := i;
                        -- only generate Transaction from one Section in one cycle
                        if (start_vld) then
                            t.a_section := start_a_section;
                        end if;
                        start_a_section := t.a_section;

                        -- Change A Gap to align Buffer A address
                        if (force_align_start) then
                            a_align  := (a_wr_ptr(i)(t.a_section)+t.a_gap_length) mod ROW_ITEMS;
                            misalign := ROW_ITEMS-a_align;
                            if (misalign=ROW_ITEMS) then
                                misalign := 0;
                            end if;
                            t.a_gap_length := t.a_gap_length+misalign;
                        end if;

                        -- Change A Gap to align both adresses
                        if (force_align_ab) then
                            a_align  := (a_wr_ptr(i)(t.a_section)+t.a_gap_length) mod ROW_ITEMS;
                            b_align  := (b_wr_ptr   (t.b_section)+t.b_gap_length) mod ROW_ITEMS;
                            misalign := a_align-b_align;
                            if (misalign<0) then
                                misalign := misalign+ROW_ITEMS;
                            end if;
                            t.b_gap_length := t.b_gap_length+misalign;
                        end if;

                        -- Force align length
                        randint(s1,s2,1,100,rand);
                        if (rand<=TRANS_LENGTH_ALIGNED_CH) then
                            t.length := natural(round_up(integer(t.length),log2(ROW_ITEMS)));
                        end if;

                        -- Check Buffer A space (leave at least 1 free Row for alignment)
                        if (a_status(t.a_stream)(t.a_section)<t.a_gap_length+t.length+ROW_ITEMS) then
                            next;
                        end if;

                        -- Check Buffer B space
                        if (b_status(t.b_section)<t.b_gap_length+t.length) then
                            next;
                        end if;

                        -- Check verification fifo
                        if (trans_fifo.full='1') then
                            report "Verification slowed due to full FIFO! Increase FIFO size!" severity error;
                            next;
                        end if;

                        -- Move Buffer pointers
                        a_wr_ptr(i)(t.a_section) := (a_wr_ptr(i)(t.a_section)+t.a_gap_length) mod (BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS);
                        b_wr_ptr   (t.b_section) := (b_wr_ptr   (t.b_section)+t.b_gap_length) mod (BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS);

                        t.a_ptr := a_wr_ptr(i)(t.a_section);
                        t.b_ptr := b_wr_ptr   (t.b_section);

                        -- only generate Transactions starting in one Word in one cycle
                        if (start_vld) then
                            if (t.a_ptr/(BUF_A_STREAM_ROWS*ROW_ITEMS)/=start_a_col) then
                                a_wr_ptr(i)(t.a_section) := (a_wr_ptr(i)(t.a_section)-t.a_gap_length) mod (BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS);
                                b_wr_ptr   (t.b_section) := (b_wr_ptr   (t.b_section)-t.b_gap_length) mod (BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS);
                                next;
                            end if;
                        end if;
                        start_a_col := t.a_ptr/(BUF_A_STREAM_ROWS*ROW_ITEMS);

                        a_wr_ptr(i)(t.a_section) := (a_wr_ptr(i)(t.a_section)+t.length) mod (BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS);
                        b_wr_ptr   (t.b_section) := (b_wr_ptr   (t.b_section)+t.length) mod (BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS);

                        -- Take space from Buffers
                        a_status(i)(t.a_section) :=  a_status(i)(t.a_section)-(t.a_gap_length+t.length);
                        b_status   (t.b_section) :=  b_status   (t.b_section)-(t.b_gap_length+t.length);

                        -- next Transaction must not start in the same Row
                        misalign := ROW_ITEMS-(a_wr_ptr(i)(t.a_section) mod ROW_ITEMS);
                        if (misalign=ROW_ITEMS) then
                            misalign := 0;
                        end if;
                        a_wr_ptr(i)(t.a_section) := (a_wr_ptr(i)(t.a_section)+misalign) mod (BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS);
                        -- Take space from Buffer A and add as Gap to be returned later
                        a_status(i)(t.a_section) := a_status(i)(t.a_section)-misalign;
                        t.a_gap_length := t.a_gap_length+misalign;

                        -- Force align next Transaction randomly
                        force_align_start := false;
                        randint(s1,s2,1,100,rand);
                        if (rand<=TRANS_START_ALIGNED_CH) then
                            force_align_start := true;
                        end if;

                        -- Force align next Transaction randomly
                        force_align_ab := false;
                        randint(s1,s2,1,100,rand);
                        if (rand<=TRANS_AB_ALIGNED_CH) then
                            force_align_ab := true;
                        end if;

                        -- save reference Transaction
                        slv_fifo_put(trans_fifo,trans_ser(t));

                        -- post Transaction
                        TX_TRANS_RECORD (i)(e) <= t;
                        TX_TRANS_VLD    (i)(e) <= '1';
                        TX_TRANS_SRC_RDY(i)    <= '1';

                        -- increment Transaction counter
                        tx_trans_cnt := tx_trans_cnt+1;

                        start_vld := true;

                        -- print
                        if (VERBOSITY_LEVEL>0 and RESET/='1') then
                            write(l,now);writeline(output,l);
                            write(l,string'(" ---- Generated new Transaction ---- "));writeline(output,l);
                            write(l,string'("Trans Stream: " & to_string(i) & ", Instr Index: " & to_string(e)));writeline(output,l);
                            trans_print(l,t);
                        end if;

                        -- accumulate throughput
                        thr_sum := thr_sum+TX_TRANS_RECORD(i)(e).length;
                    end loop;

                end if;

            end loop;

            -- Print generated Transactions
            gen_time := gen_time+1;
            if (gen_time=GENERATING_LOG_PERIOD) then
                write(l,now);write(l,string'(" : generated Transactions : " & to_string(tx_trans_cnt)) & "/" & to_string(TRANSACTIONS));writeline(output,l);
                gen_time := 0;
            end if;

            -- Measure throughput
            thr_time := thr_time+1;
            if (thr_time=THROUGHPUT_LOG_PERIOD) then
                write(l,now);write(l,string'("    : current RX throughput : " & to_string(get_throughput(thr_sum, thr_time),"%3.2f") & "%"));writeline(output,l);
                thr_sum  := 0;
                thr_time := 0;
            end if;

            if (RESET='1') then
                TX_TRANS_SRC_RDY <= (others => '0');
                slv_fifo_new(trans_fifo);
                a_status := (others => (others => BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS));
                b_status := (others => BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS);
                a_wr_ptr := (others => (others => 0));
                b_wr_ptr := (others => 0);
                a_rd_ptr := (others => (others => 0));
                b_rd_ptr := (others => 0);
                tx_trans_cnt := 0;
                thr_sum  := 0;
                thr_time := 0;
            end if;
        end if;
    end process;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction Checking
    -------------------------------------------------------------

    check_pr : process
        variable s1       : natural := SEED1;
        variable s2       : natural := SEED2;
        variable rand     : natural;
        variable t_vec    : std_logic_vector(TRANS_WIDTH-1 downto 0);
        variable t        : trans_t;
        variable thr_sum  : natural;
        variable thr_time : natural;
        variable i        : natural;
        variable ee       : n_array_t(TRANS_STREAMS-1 downto 0);
    begin
--        if (falling_edge(CLK)) then
            wait until (rising_edge(CLK));
            wait for C_CLK_PER / 4;

            if (err_reg=1) then
                write(l,now);writeline(output,l);
                write(l,string'("ERROR: Received a non-matching Transaction!"));writeline(output,l);
                write(l,string'(" ---- Referential ---- "));writeline(output,l);
                trans_print(l,ref_t);
                write(l,string'(" ---- Received ---- "));writeline(output,l);
                trans_print(l,err_t);
                report "" severity failure;
            end if;

            if (err_reg=2) then
                write(l,now);writeline(output,l);
                write(l,string'("ERROR: Received an unexpected Transaction!"));writeline(output,l);
                write(l,string'(" ---- Received ---- "));writeline(output,l);
                trans_print(l,err_t);
                report "" severity failure;
            end if;

            RX_TRANS_DST_RDY <= (others => (others => '0'));

            ee := (others => 0);

            for g in 0 to TRANSS-1 loop

                -- fall randomly
                randint(s1,s2,1,100,rand);
                if (rand<=TX_TRANS_NOT_RDY_CH) then
                    exit;
                end if;

                t := trans_deser(trans_fifo.fifo(0));
                i := t.a_stream;

                if (RX_TRANS_SRC_RDY(i)(ee(i))='1') then
                    if (trans_fifo.empty='1') then
                        err_t   <= RX_TRANS_RECORD(i)(ee(i));
                        err_reg <= 2;
                        exit;
                    end if;
                    slv_fifo_pop(trans_fifo,t_vec);
                    if (trans_deser(t_vec)/=RX_TRANS_RECORD(i)(ee(i))) then
                        err_t   <= RX_TRANS_RECORD(i)(ee(i));
                        ref_t   <= trans_deser(t_vec);
                        err_reg <= 1;
                    else
                        rx_trans_cnt := rx_trans_cnt+1;
                        -- Free space from Buffers
                        a_status(i)(RX_TRANS_RECORD(i)(ee(i)).a_section) := a_status(i)(RX_TRANS_RECORD(i)(ee(i)).a_section)+RX_TRANS_RECORD(i)(ee(i)).a_gap_length+RX_TRANS_RECORD(i)(ee(i)).length;
                        b_status   (RX_TRANS_RECORD(i)(ee(i)).b_section) := b_status   (RX_TRANS_RECORD(i)(ee(i)).b_section)+RX_TRANS_RECORD(i)(ee(i)).b_gap_length+RX_TRANS_RECORD(i)(ee(i)).length;
                        a_rd_ptr(i)(RX_TRANS_RECORD(i)(ee(i)).a_section) := (a_rd_ptr(i)(RX_TRANS_RECORD(i)(ee(i)).a_section)+RX_TRANS_RECORD(i)(ee(i)).a_gap_length+RX_TRANS_RECORD(i)(ee(i)).length) mod (BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS);
                        b_rd_ptr   (RX_TRANS_RECORD(i)(ee(i)).b_section) := (b_rd_ptr   (RX_TRANS_RECORD(i)(ee(i)).b_section)+RX_TRANS_RECORD(i)(ee(i)).b_gap_length+RX_TRANS_RECORD(i)(ee(i)).length) mod (BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS);

                        -- print
                        if (VERBOSITY_LEVEL>0) then
                            write(l,now);writeline(output,l);
                            write(l,string'(" ---- Received new Transaction ---- "));writeline(output,l);
                            write(l,string'("Trans Stream: " & to_string(i) & ", Instr Index: " & to_string(ee(i))));writeline(output,l);
                            trans_print(l,RX_TRANS_RECORD(i)(ee(i)));
                        end if;

                        RX_TRANS_DST_RDY(i)(ee(i)) <= '1';

                        -- accumulate throughput
                        thr_sum := thr_sum+RX_TRANS_RECORD(i)(ee(i)).length;

                        ee(i) := ee(i)+1;
                    end if;
                end if;
            end loop;

            -- Measure throughput
            thr_time := thr_time+1;
            if (thr_time=THROUGHPUT_LOG_PERIOD) then
                write(l,now);write(l,string'(" : current TX throughput : " & to_string(get_throughput(thr_sum, thr_time),"%3.2f") & "%"));writeline(output,l);
                thr_sum  := 0;
                thr_time := 0;
            end if;

            if (RESET='1') then
                RX_TRANS_DST_RDY <= (others => (others => '0'));
                thr_sum  := 0;
                thr_time := 0;
            end if;
--        end if;
    end process;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Check successful end
    -------------------------------------------------------------

    end_pr : process
    begin
        while (rx_trans_cnt<TRANSACTIONS) loop
            wait until (rising_edge(CLK));
        end loop;

        fifo_print_stats(trans_fifo,"Transaction FIFO:");
        if (trans_fifo.empty/='1') then
            write(l,string'("ERROR: Verification finished, but verification FIFO is not empty!"));
            report "" severity failure;
        end if;

        for i in 0 to 8-1 loop
            wait until (rising_edge(CLK));
        end loop;

        write(l,string'("VERIFICATION SUCCESS"));writeline(output,l);
        stop;
    end process;

    -------------------------------------------------------------

end architecture;
