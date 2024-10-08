-- crdt_down.vhd: Credit Flow Control logic - R-Tile downstream
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity CB_RTILE_CRDT_DOWN is
    generic(
        REGIONS          : natural := 2;
        CRDT_ENABLE      : boolean := True
    );
    port (
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        --  TLP METADATA INPUT (must be valid on end of TLP)
        -- =====================================================================
        TLP_FMT_TYPE   : in  slv_array_t(REGIONS-1 downto 0)(8-1 downto 0);
        TLP_LENGTH     : in  slv_array_t(REGIONS-1 downto 0)(10-1 downto 0);
        TLP_VALID      : in  std_logic_vector(REGIONS-1 downto 0);

        -- =====================================================================
        --  CREDIT FLOW CONTROL INTERFACE
        -- =====================================================================
        CRDT_INIT_DONE : in  std_logic;
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_UPDATE    : out std_logic_vector(6-1 downto 0);
        -- Update count of credits
        CRDT_CNT_PH    : out std_logic_vector(2-1 downto 0);
        CRDT_CNT_NPH   : out std_logic_vector(2-1 downto 0);
        CRDT_CNT_CPLH  : out std_logic_vector(2-1 downto 0);
        CRDT_CNT_PD    : out std_logic_vector(4-1 downto 0);
        CRDT_CNT_NPD   : out std_logic_vector(4-1 downto 0);
        CRDT_CNT_CPLD  : out std_logic_vector(4-1 downto 0)
    );
end entity;

architecture FULL of CB_RTILE_CRDT_DOWN is

    -- There should be no overflow!
    -- Counter decrement should be faster than increment.
    constant CRDT_PH_CNT_W : natural := 10;
    constant CRDT_PD_CNT_W : natural := 14;

    signal tlp_code         : slv_array_t(REGIONS-1 downto 0)(6-1 downto 0);
    signal crdt_pd_inc      : u_array_t(REGIONS-1 downto 0)(8-1 downto 0);
    signal crdt_status      : slv_array_t(REGIONS-1 downto 0)(6-1 downto 0);
    signal crdt_valid       : std_logic_vector(REGIONS-1 downto 0);

    signal crdt_ph_cnt_upda : std_logic_vector(3-1 downto 0);
    signal crdt_ph_cnt_last : std_logic_vector(3-1 downto 0);
    signal crdt_ph_cnt_inc  : u_array_t(3-1 downto 0)(log2(REGIONS+1)-1 downto 0);
    signal crdt_ph_cnt_dec  : u_array_t(3-1 downto 0)(2-1 downto 0);
    signal crdt_ph_cnt      : u_array_t(3-1 downto 0)(CRDT_PH_CNT_W-1 downto 0);

    signal crdt_pd_cnt_upda : std_logic_vector(3-1 downto 0);
    signal crdt_pd_cnt_last : std_logic_vector(3-1 downto 0);
    signal crdt_pd_cnt_inc  : u_array_t(3-1 downto 0)(log2(REGIONS+1)+8-1 downto 0);
    signal crdt_pd_cnt_dec  : u_array_t(3-1 downto 0)(4-1 downto 0);
    signal crdt_pd_cnt      : u_array_t(3-1 downto 0)(CRDT_PD_CNT_W-1 downto 0);

    signal cnt_last_bit             : std_logic_vector(6-1 downto 0);
    signal dbg_err_cnt_overflow     : std_logic;
    signal dbg_err_cnt_overflow_reg : std_logic;

    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of dbg_err_cnt_overflow_reg : signal is true;

begin

    crdt_on_g : if CRDT_ENABLE generate
        region_g: for i in 0 to REGIONS-1 generate
            tlp_code(i) <= TLP_FMT_TYPE(i)(6) & TLP_FMT_TYPE(i)(4 downto 0);

            process(CLK)
            begin
                if (rising_edge(CLK)) then
                    crdt_valid(i) <= TLP_VALID(i);
                    crdt_pd_inc(i) <= enlarge_right(round_up(unsigned(TLP_LENGTH(i)),2),-2);
                    -- crdt_status: CPLD,NPD,PD,CPLH,NPH,PH
                    if std_match(tlp_code(i),"010---") then
                        -- Message Request without Data
                        crdt_status(i) <= "000001"; -- PH
                    elsif std_match(tlp_code(i),"100000") or std_match(tlp_code(i),"110---") then
                        -- Memory Write Request, Message Request with Data
                        crdt_status(i) <= "001001"; -- PH + n*PD
                    elsif std_match(tlp_code(i),"00000-") or std_match(tlp_code(i),"00010-") or std_match(tlp_code(i),"000010") then
                        -- Memory Read Request, Configuration Read, I/O Read Request
                        crdt_status(i) <= "000010"; -- NPH
                    elsif std_match(tlp_code(i),"1011--") or std_match(tlp_code(i),"10010-") or std_match(tlp_code(i),"100010") then
                        -- AtomicOp Requests, Configuration Write, I/O Write Request
                        crdt_status(i) <= "010010"; -- NPH + n*NPD
                    elsif std_match(tlp_code(i),"00101-") then
                        -- Completion without Data
                        crdt_status(i) <= "000100"; -- CLPH
                    elsif std_match(tlp_code(i),"10101-") then
                        -- Completion with Data
                        crdt_status(i) <= "100100"; -- CLPH + n*CLPD
                    else
                        crdt_status(i) <= "000000"; -- none
                    end if;
                end if;
            end process;
        end generate;

        crdt_ph_g : for i in 0 to 3-1 generate
            process(CLK)
                variable crdt_cnt_v : unsigned(log2(REGIONS+1)-1 downto 0);
            begin
                if (rising_edge(CLK)) then
                    crdt_cnt_v := (others => '0');
                    for r in 0 to REGIONS-1 loop
                        if (crdt_valid(r) = '1' and crdt_status(r)(i) = '1') then
                            crdt_cnt_v := crdt_cnt_v + 1;
                        end if;
                    end loop;
                    crdt_ph_cnt_inc(i) <= crdt_cnt_v;
                end if;
            end process;

            crdt_ph_cnt_upda(i) <= (or crdt_ph_cnt(i)) and CRDT_INIT_DONE;
            crdt_ph_cnt_last(i) <= nor crdt_ph_cnt(i)(CRDT_PH_CNT_W-1 downto 2);
            crdt_ph_cnt_dec(i)  <= (others => '0')            when (crdt_ph_cnt_upda(i) = '0') else
                                   crdt_ph_cnt(i)(1 downto 0) when (crdt_ph_cnt_last(i) = '1') else
                                   (others => '1');

            process(CLK)
            begin
                if (rising_edge(CLK)) then
                    crdt_ph_cnt(i) <= crdt_ph_cnt(i) - crdt_ph_cnt_dec(i) + crdt_ph_cnt_inc(i);
                    if (RESET = '1') then
                        crdt_ph_cnt(i) <= (others => '0');
                    end if;
                end if;
            end process;
        end generate;

        crdt_pd_g : for i in 0 to 3-1 generate
            process(CLK)
                variable crdt_cnt_v : unsigned(log2(REGIONS+1)+8-1 downto 0);
            begin
                if (rising_edge(CLK)) then
                    crdt_cnt_v := (others => '0');
                    for r in 0 to REGIONS-1 loop
                        if (crdt_valid(r) = '1' and crdt_status(r)(i+3) = '1') then
                            crdt_cnt_v := crdt_cnt_v + crdt_pd_inc(r);
                        end if;
                    end loop;
                    crdt_pd_cnt_inc(i) <= crdt_cnt_v;
                end if;
            end process;

            crdt_pd_cnt_upda(i) <= (or crdt_pd_cnt(i)) and CRDT_INIT_DONE;
            crdt_pd_cnt_last(i) <= nor crdt_pd_cnt(i)(CRDT_PD_CNT_W-1 downto 4);
            crdt_pd_cnt_dec(i)  <= (others => '0')            when (crdt_pd_cnt_upda(i) = '0') else
                                   crdt_pd_cnt(i)(3 downto 0) when (crdt_pd_cnt_last(i) = '1') else
                                   (others => '1');

            process(CLK)
            begin
                if (rising_edge(CLK)) then
                    crdt_pd_cnt(i) <= crdt_pd_cnt(i) - crdt_pd_cnt_dec(i) + crdt_pd_cnt_inc(i);
                    if (RESET = '1') then
                        crdt_pd_cnt(i) <= (others => '0');
                    end if;
                end if;
            end process;
        end generate;

        process(CLK)
        begin
            if (rising_edge(CLK)) then
                CRDT_CNT_PH   <= std_logic_vector(crdt_ph_cnt_dec(0));
                CRDT_CNT_NPH  <= std_logic_vector(crdt_ph_cnt_dec(1));
                CRDT_CNT_CPLH <= std_logic_vector(crdt_ph_cnt_dec(2));
                CRDT_CNT_PD   <= std_logic_vector(crdt_pd_cnt_dec(0));
                CRDT_CNT_NPD  <= std_logic_vector(crdt_pd_cnt_dec(1));
                CRDT_CNT_CPLD <= std_logic_vector(crdt_pd_cnt_dec(2));
                CRDT_UPDATE   <= crdt_pd_cnt_upda & crdt_ph_cnt_upda;
                if (RESET = '1') then
                    CRDT_UPDATE <= (others => '0');
                end if;
            end if;
        end process;

        cnt_last_bit_g: for i in 0 to 3-1 generate
            cnt_last_bit(i)   <= crdt_ph_cnt(i)(CRDT_PH_CNT_W-1);
            cnt_last_bit(i+3) <= crdt_pd_cnt(i)(CRDT_PD_CNT_W-1);
        end generate;

        dbg_err_cnt_overflow <= or cnt_last_bit;

        process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (dbg_err_cnt_overflow = '1') then
                    dbg_err_cnt_overflow_reg <= '1';
                end if;
                if (RESET = '1') then
                    dbg_err_cnt_overflow_reg <= '0';
                end if;
            end if;
        end process;

        assert (dbg_err_cnt_overflow_reg /= '1')
            report "CB_RTILE_CRDT_DOWN: some credit counter overflow!"
            severity failure;
    end generate;

    crdt_off_g : if not CRDT_ENABLE generate
        CRDT_UPDATE   <= (others => '0');
        CRDT_CNT_PH   <= (others => '0');
        CRDT_CNT_NPH  <= (others => '0');
        CRDT_CNT_CPLH <= (others => '0');
        CRDT_CNT_PD   <= (others => '0');
        CRDT_CNT_NPD  <= (others => '0');
        CRDT_CNT_CPLD <= (others => '0');
    end generate;

end architecture;
