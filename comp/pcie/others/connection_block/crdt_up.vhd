-- crdt_up.vhd: Credit Flow Control logic - R-Tile upstream
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity CB_RTILE_CRDT_UP is
    generic(
        REGIONS        : natural := 2;
        -- Maximum write request (payload) size (in DWORDs)
        PCIE_MPS_DW    : natural := 512/4;
        -- Enable this module
        CRDT_ENABLE    : boolean := True;
        CRDT_MASK      : std_logic_vector(6-1 downto 0) := "111111";
        -- Maximum allowed count of PCIe credits
        CRDT_MAX_PH    : natural := 1024;
        CRDT_MAX_NPH   : natural := 1024;
        CRDT_MAX_CPLH  : natural := 1024;
        CRDT_MAX_PD    : natural := 4096;
        CRDT_MAX_NPD   : natural := 4096;
        CRDT_MAX_CPLD  : natural := 4096
    );
    port(
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        --  PCIe Flow Control Interface
        -- =====================================================================
        -- In init phase, the receiver must set the total number of credits
        -- using incremental credit updates. The user logic only receives the
        -- credit updates and waits for CRDT_INIT_DONE to be high.
        CRDT_INIT_DONE : in  std_logic;
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_UPDATE    : in  std_logic_vector(6-1 downto 0);
        -- Update count of credits
        CRDT_CNT_PH    : in  std_logic_vector(2-1 downto 0);
        CRDT_CNT_NPH   : in  std_logic_vector(2-1 downto 0);
        CRDT_CNT_CPLH  : in  std_logic_vector(2-1 downto 0);
        CRDT_CNT_PD    : in  std_logic_vector(4-1 downto 0);
        CRDT_CNT_NPD   : in  std_logic_vector(4-1 downto 0);
        CRDT_CNT_CPLD  : in  std_logic_vector(4-1 downto 0);

        -- =====================================================================
        --  TLP Check Interface
        -- =====================================================================
        TLP_FMT_TYPE   : in  slv_array_t(REGIONS-1 downto 0)(8-1 downto 0);
        TLP_LENGTH     : in  slv_array_t(REGIONS-1 downto 0)(10-1 downto 0);
        TLP_HDR_VLD    : in  std_logic_vector(REGIONS-1 downto 0);
        TLP_CRDT_OK    : out std_logic;
        READY          : in  std_logic
    );
end entity;

architecture FULL of CB_RTILE_CRDT_UP is

    constant CRDT_XPH_CNT_W  : natural := log2(maximum(CRDT_MAX_PH,CRDT_MAX_NPH)+1);
    constant CRDT_XPD_CNT_W  : natural := log2(maximum(CRDT_MAX_PD,CRDT_MAX_NPD)+1);
    constant CRDT_XPX_CNT_W  : natural := maximum(CRDT_XPH_CNT_W,CRDT_XPD_CNT_W);
    constant CRDT_CNT_DEC_W  : natural := log2((REGIONS*div_roundup(PCIE_MPS_DW,4))+1);

    signal crdt_upda_masked  : std_logic_vector(6-1 downto 0);

    signal crdt_cnt          : u_array_t(6-1 downto 0)(CRDT_XPX_CNT_W-1 downto 0);
    signal crdt_cnt_inc      : u_array_t(6-1 downto 0)(4-1 downto 0);
    signal crdt_cnt_dec      : u_array_t(6-1 downto 0)(CRDT_CNT_DEC_W-1 downto 0);
    signal crdt_infinite     : std_logic_vector(6-1 downto 0);

    signal tlp_read          : std_logic_vector(REGIONS-1 downto 0);
    signal tlp_write         : std_logic_vector(REGIONS-1 downto 0);
    signal tlp_compl         : std_logic_vector(REGIONS-1 downto 0);
    signal tlp_error         : std_logic_vector(REGIONS-1 downto 0);
    signal tlp_error_vld     : std_logic_vector(REGIONS-1 downto 0);
    signal tlp_error_vld_or  : std_logic;
    signal tlp_error_vld_reg : std_logic;

    signal some_tlp_hdr      : std_logic;
    signal crdt_tlp          : u_array_t(6-1 downto 0)(CRDT_CNT_DEC_W-1 downto 0);
    signal crdt_ok           : std_logic_vector(6-1 downto 0);
    signal crdt_word_ok      : std_logic;
    signal crdt_dec_en       : std_logic;

    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of tlp_error_vld_reg : signal is true;

begin

    en_g: if CRDT_ENABLE generate

        crdt_upda_masked <= CRDT_UPDATE and CRDT_MASK;

        -- =====================================================================
        --  CREDIT COUNTERS
        -- =====================================================================

        crdt_cnt_inc(0) <= resize(unsigned(CRDT_CNT_PH),4)   when (crdt_upda_masked(0) = '1') else (others => '0');
        crdt_cnt_inc(1) <= resize(unsigned(CRDT_CNT_NPH),4)  when (crdt_upda_masked(1) = '1') else (others => '0');
        crdt_cnt_inc(2) <= resize(unsigned(CRDT_CNT_CPLH),4) when (crdt_upda_masked(2) = '1') else (others => '0');
        crdt_cnt_inc(3) <= resize(unsigned(CRDT_CNT_PD),4)   when (crdt_upda_masked(3) = '1') else (others => '0');
        crdt_cnt_inc(4) <= resize(unsigned(CRDT_CNT_NPD),4)  when (crdt_upda_masked(4) = '1') else (others => '0');
        crdt_cnt_inc(5) <= resize(unsigned(CRDT_CNT_CPLD),4) when (crdt_upda_masked(5) = '1') else (others => '0');

        crdt_cnt_g : for i in 0 to 6-1 generate
            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    crdt_cnt(i) <= crdt_cnt(i) + crdt_cnt_inc(i) - crdt_cnt_dec(i);
                    if (RESET = '1') then
                        crdt_cnt(i) <= (others => '0');
                    end if;
                end if;
            end process;

            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (CRDT_INIT_DONE = '0' and crdt_upda_masked(i) = '1') then
                        if (crdt_cnt_inc(i) = 0) then
                            crdt_infinite(i) <= '1';
                        else
                            crdt_infinite(i) <= '0';
                        end if;
                    end if;
                    if (RESET = '1') then
                        crdt_infinite(i) <= '0';
                    end if;
                end if;
            end process;

            crdt_cnt_dec(i) <= crdt_tlp(i) when (crdt_dec_en = '1' and crdt_infinite(i) = '0') else (others => '0');
        end generate;

        -- =====================================================================
        --  CREDIT AVAILABILITY CHECK
        -- =====================================================================

        -- Possible upstream transactions in NDK:
        -- ======================================
        -- from MTC => Completion with Data     => fmt & type = "01001010"
        -- from PTC => 32b Memory Read Request  => fmt & type = "00000000"
        -- from PTC => 64b Memory Read Request  => fmt & type = "00100000"
        -- from PTC => 32b Memory Write Request => fmt & type = "01000000"
        -- from PTC => 64b Memory Write Request => fmt & type = "01100000"
        tlp_decode_g : for i in 0 to REGIONS-1 generate
            process (all)
            begin
                tlp_read(i)  <= '0';
                tlp_write(i) <= '0';
                tlp_compl(i) <= '0';
                tlp_error(i) <= '0';

                case TLP_FMT_TYPE(i) is
                    when "01001010" =>
                        tlp_compl(i) <= '1';
                    when "00000000" =>
                        tlp_read(i) <= '1';
                    when "00100000" =>
                        tlp_read(i) <= '1';
                    when "01000000" =>
                        tlp_write(i) <= '1';
                    when "01100000" =>
                        tlp_write(i) <= '1';
                    when others =>
                        tlp_error(i) <= '1';
                end case;
            end process;
        end generate;

        tlp_error_vld <= tlp_error and TLP_HDR_VLD;

        process (all)
            variable v_crdt_tlp : u_array_t(6-1 downto 0)(CRDT_CNT_DEC_W-1 downto 0);
        begin
            v_crdt_tlp := (others => (others => '0'));
            for i in 0 to REGIONS-1 loop
                if (TLP_HDR_VLD(i) = '1') then
                    if (tlp_write(i) = '1') then
                        v_crdt_tlp(0) := v_crdt_tlp(0) + 1;
                        -- convert transaction length to number of credits
                        v_crdt_tlp(3) := v_crdt_tlp(3) + resize(enlarge_right(round_up(unsigned(TLP_LENGTH(i)),2),-2),CRDT_CNT_DEC_W);
                    elsif (tlp_compl(i) = '1') then
                        v_crdt_tlp(2) := v_crdt_tlp(2) + 1;
                        -- convert transaction length to number of credits
                        v_crdt_tlp(5) := v_crdt_tlp(5) + resize(enlarge_right(round_up(unsigned(TLP_LENGTH(i)),2),-2),CRDT_CNT_DEC_W);
                    elsif (tlp_read(i) = '1') then
                        v_crdt_tlp(1) := v_crdt_tlp(1) + 1;
                    end if;
                end if;
            end loop;
            crdt_tlp <= v_crdt_tlp;
        end process;

        crdt_comp_g : for i in 0 to 6-1 generate
            crdt_ok(i) <= '1' when (crdt_cnt(i) >= crdt_tlp(i) or crdt_infinite(i) = '1') else '0';
        end generate;

        some_tlp_hdr <= or TLP_HDR_VLD;
        crdt_word_ok <= (and crdt_ok) and CRDT_INIT_DONE;
        crdt_dec_en  <= crdt_word_ok and some_tlp_hdr and READY;

        TLP_CRDT_OK <= (not some_tlp_hdr) or crdt_word_ok;

        tlp_error_vld_or <= or tlp_error_vld;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (tlp_error_vld_or = '1') then
                    tlp_error_vld_reg <= '1';
                end if;
                if (RESET = '1') then
                    tlp_error_vld_reg <= '0';
                end if;
            end if;
        end process;

        assert (tlp_error_vld_reg /= '1')
            report "CB_RTILE_CRDT_UP: Unsupported TLP type!"
            severity failure;

    end generate;

    off_g: if not CRDT_ENABLE generate
        TLP_CRDT_OK <= '1';
    end generate;

end architecture;
