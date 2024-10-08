-- delay_fifo.vhd: FIFO storage with configurable delay for verification purposes (NOT FOR SYNTH!!!)
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;

entity DELAY_FIFO is
    generic(
        -- Data word width in bits.
        DATA_WIDTH          : natural := 16;
        -- FIFO depth, i.e. number of data words
        ITEMS               : natural := 16;
        -- Disables the FIFO implementation and replaces it with straight wires.
        FAKE_FIFO           : boolean := false;
        -- Mean delay value from RX to TX in clock cycles
        DELAY               : integer := 10;
        -- Variance of the delay, actual delays for processed words are uniformly distributed inside <DELAY-JITTER,DELAY+JITTER>
        --    JITTER should be lower than delay
        JITTER              : integer := 5;
        -- Can transactions leave FIFO in different order as they arrived, i.e. can FIFO reorder transactions based on their delays?
        REORDER             : boolean := false;
        -- Seeds for random number generator
        SEED1               : integer := 16#C0FFEE#;
        SEED2               : integer := 16#DECADE#
    );
    port(
        CLK    : in  std_logic;
        RESET  : in  std_logic;
        DI     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WR     : in  std_logic;
        FULL   : out std_logic;
        DO     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RD     : in  std_logic;
        EMPTY  : out std_logic
    );
end entity;

architecture behavioral of DELAY_FIFO is

    constant TIME_WIDTH : integer := 64;

    type item_t is record
        d : std_logic_vector(DATA_WIDTH-1 downto 0);
        t : unsigned(TIME_WIDTH-1 downto 0);
    end record;
    type memory_t is array (ITEMS-1 downto 0) of item_t;

    signal fifo        : memory_t;
    signal delay_val   : integer := 0;
    signal rd_ptr      : natural := 0;
    signal wr_ptr      : natural := 0;
    signal rd_flag     : std_logic;
    signal wr_flag     : std_logic;
    signal ptr_cmp     : std_logic;
    signal flag_diff   : std_logic;
    signal item_ready  : std_logic;
    signal time_cnt    : unsigned(TIME_WIDTH-1 downto 0);
    signal item_time   : unsigned(TIME_WIDTH-1 downto 0);

begin

    assert JITTER <= DELAY report "DELAY FIFO: Jitter cannot be higher than delay!" severity failure;

    fake_fifo_g: if FAKE_FIFO generate
        DO     <= DI;
        FULL   <= not RD;
        EMPTY  <= not WR;
    end generate;

    full_fifo_g: if not FAKE_FIFO generate
        -- Read and write pointers used to determine FIFO fullness state
        control_regs_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if RESET='1' then
                     wr_ptr <= 0;
                     rd_ptr <= 0;
                     wr_flag <= '0';
                     rd_flag <= '0';
                else
                    if WR='1' and FULL='0' then
                        wr_ptr  <= tsel(wr_ptr = (ITEMS-1), 0,           wr_ptr+1);
                        wr_flag <= tsel(wr_ptr = (ITEMS-1), not wr_flag, wr_flag);
                    end if;
                    if RD='1' and EMPTY='0' then
                        rd_ptr  <= tsel(rd_ptr = (ITEMS-1), 0,           rd_ptr+1);
                        rd_flag <= tsel(rd_ptr = (ITEMS-1), not rd_flag, rd_flag);
                    end if;
                end if;
            end if;
        end process;
        ptr_cmp    <= '1' when rd_ptr = wr_ptr else '0';
        flag_diff  <= rd_flag xor wr_flag;
        item_ready <= '1' when fifo(rd_ptr).t <= time_cnt else '0';
        EMPTY      <= (ptr_cmp and not flag_diff) or not item_ready;
        DO         <= fifo(rd_ptr).d;
        FULL       <= ptr_cmp and flag_diff;

        -- Free running counter to determine timestamps in clock cycles
        time_keeper_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if RESET='1' then
                    time_cnt <= (others => '0');
                else
                    time_cnt <= time_cnt + 1;
                end if;
            end if;
        end process;
        item_time <= time_cnt + delay_val;

        -- Random delay generation for input item
        simple_delay_g: if JITTER = 0 generate
            delay_val <= DELAY;
        end generate;
        full_delay_g: if JITTER /= 0 generate
            delay_randomize_p: process(CLK)
                variable s1   : positive;
                variable s2   : positive;
                variable rand : real;
            begin
                if rising_edge(CLK) then
                    if RESET='1' then
                        s1 := SEED1;
                        s2 := SEED2;
                    else
                        uniform(s1, s2, rand);
                        delay_val <= DELAY - JITTER + integer(rand * real(2*JITTER));
                    end if;
                end if;
            end process;
        end generate;

        -- Ordered FIFO implementation
        simple_fifo_g: if not REORDER generate
            storage_p: process(CLK)
            begin
                if rising_edge(CLK) then
                    if WR='1' and FULL='0' then
                        fifo(wr_ptr).d <= DI;
                        fifo(wr_ptr).t <= item_time;
                    end if;
                end if;
            end process;
        end generate;

        -- Reordering FIFO implementation
        reorder_fifo_g: if REORDER generate
            storage_p: process(CLK)
                variable inserted : item_t;
            begin
                if rising_edge(CLK) then
                    if WR='1' and FULL='0' then -- perform one loop of insert sort on item write
                        inserted.d := DI;
                        inserted.t := item_time;
                        for i in rd_ptr+1 to ITEMS-1 loop -- insert loop from read pointer to write pointer or end of memory
                            if wr_ptr = i then
                                exit;
                            elsif inserted.t < fifo(i).t then
                                fifo(i) <= inserted;
                                inserted := fifo(i);
                            end if;
                        end loop;
                        if wr_flag /= rd_flag then -- continue the insert loop after memory end if needed
                            for i in 0 to wr_ptr-1 loop
                                if inserted.t < fifo(i).t then
                                    fifo(i) <= inserted;
                                    inserted := fifo(i);
                                end if;
                            end loop;
                        end if;
                        fifo(wr_ptr) <= inserted; -- do not forget to insert the last item
                    end if;
                end if;
            end process;
        end generate;

    end generate;

end architecture;
