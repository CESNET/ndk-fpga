-- pcie_crdt_logic.vhd: PCIe Credit Flow Control Logic
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PCIE_CRDT_LOGIC is
    generic(
        -- Total PCIe credits for down stream
        CRDT_TOTAL_PH   : natural := 128;
        CRDT_TOTAL_NPH  : natural := 128;
        CRDT_TOTAL_CPLH : natural := 128;
        CRDT_TOTAL_PD   : natural := 1024;
        CRDT_TOTAL_NPD  : natural := 32;
        CRDT_TOTAL_CPLD : natural := 32
    );
    port(
        CLK                      : in  std_logic;
        RESET                    : in  std_logic;

        -- =====================================================================
        --  PCIE HARD IP DOWN/UP Flow Control Interface - R-Tile
        -- =====================================================================
        PCIE_HCRDT_UP_INIT       : in  std_logic_vector(2 downto 0);
        PCIE_HCRDT_UP_INIT_ACK   : out std_logic_vector(2 downto 0);
        PCIE_HCRDT_UP_UPDATE     : in  std_logic_vector(2 downto 0);
        PCIE_HCRDT_UP_UPDATE_CNT : in  std_logic_vector(5 downto 0);
        PCIE_DCRDT_UP_INIT       : in  std_logic_vector(2 downto 0);
        PCIE_DCRDT_UP_INIT_ACK   : out std_logic_vector(2 downto 0);
        PCIE_DCRDT_UP_UPDATE     : in  std_logic_vector(2 downto 0);
        PCIE_DCRDT_UP_UPDATE_CNT : in  std_logic_vector(11 downto 0);
    
        PCIE_HCRDT_DW_INIT       : out std_logic_vector(2 downto 0);
        PCIE_HCRDT_DW_INIT_ACK   : in  std_logic_vector(2 downto 0);
        PCIE_HCRDT_DW_UPDATE     : out std_logic_vector(2 downto 0);
        PCIE_HCRDT_DW_UPDATE_CNT : out std_logic_vector(5 downto 0);
        PCIE_DCRDT_DW_INIT       : out std_logic_vector(2 downto 0);
        PCIE_DCRDT_DW_INIT_ACK   : in  std_logic_vector(2 downto 0);
        PCIE_DCRDT_DW_UPDATE     : out std_logic_vector(2 downto 0);
        PCIE_DCRDT_DW_UPDATE_CNT : out std_logic_vector(11 downto 0);

        -- =====================================================================
        --  User DOWN/UP Flow Control Interface
        -- =====================================================================
        -- In init phase the receiver must set the total number of credits using
        -- incremental credit updates. The user logic only receives the credit
        -- updates and waits for CRDT_UP_INIT_DONE to be high.
        CRDT_UP_INIT_DONE        : out std_logic;
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_UP_UPDATE           : out std_logic_vector(6-1 downto 0);
        -- Update count of credits
        CRDT_UP_CNT_PH           : out std_logic_vector(2-1 downto 0);
        CRDT_UP_CNT_NPH          : out std_logic_vector(2-1 downto 0);
        CRDT_UP_CNT_CPLH         : out std_logic_vector(2-1 downto 0);
        CRDT_UP_CNT_PD           : out std_logic_vector(4-1 downto 0);
        CRDT_UP_CNT_NPD          : out std_logic_vector(4-1 downto 0);
        CRDT_UP_CNT_CPLD         : out std_logic_vector(4-1 downto 0);
        
        -- In init phase the receiver must set the total number of credits using
        -- incremental credit updates. The user logic only waits for
        -- CRDT_DOWN_INIT_DONE to be high.
        CRDT_DOWN_INIT_DONE      : out std_logic;
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_DOWN_UPDATE         : in  std_logic_vector(6-1 downto 0) := (others => '0');
        -- Update count of credits
        CRDT_DOWN_CNT_PH         : in  std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_NPH        : in  std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_CPLH       : in  std_logic_vector(2-1 downto 0);
        CRDT_DOWN_CNT_PD         : in  std_logic_vector(4-1 downto 0);
        CRDT_DOWN_CNT_NPD        : in  std_logic_vector(4-1 downto 0);
        CRDT_DOWN_CNT_CPLD       : in  std_logic_vector(4-1 downto 0)
    );
end entity;

architecture FULL of PCIE_CRDT_LOGIC is

    constant CRDT_XPH_CNT_W : natural := log2(maximum(maximum(CRDT_TOTAL_PH,CRDT_TOTAL_NPH),CRDT_TOTAL_CPLH)+1);
    constant CRDT_XPD_CNT_W : natural := log2(maximum(maximum(CRDT_TOTAL_PD,CRDT_TOTAL_NPD),CRDT_TOTAL_CPLD)+1);

    signal hcrdt_up_init_done     : std_logic_vector(3-1 downto 0);
    signal dcrdt_up_init_done     : std_logic_vector(3-1 downto 0);

    signal hcrdt_dw_init_done     : std_logic_vector(3-1 downto 0);
    signal hcrdt_dw_init_cnt_en   : std_logic_vector(3-1 downto 0);
    signal hcrdt_dw_init_cnt_last : std_logic_vector(3-1 downto 0);
    signal hcrdt_dw_init_cnt_dec  : u_array_t(3-1 downto 0)(2-1 downto 0);
    signal hcrdt_dw_init_cnt      : u_array_t(3-1 downto 0)(CRDT_XPH_CNT_W-1 downto 0);

    signal dcrdt_dw_init_done     : std_logic_vector(3-1 downto 0);
    signal dcrdt_dw_init_cnt_en   : std_logic_vector(3-1 downto 0);
    signal dcrdt_dw_init_cnt_last : std_logic_vector(3-1 downto 0);
    signal dcrdt_dw_init_cnt_dec  : u_array_t(3-1 downto 0)(4-1 downto 0);
    signal dcrdt_dw_init_cnt      : u_array_t(3-1 downto 0)(CRDT_XPD_CNT_W-1 downto 0);

begin

    -- =========================================================================
    --  UP-STREAM LOGIC
    -- =========================================================================

    crdt_up_g : for j in 0 to 3-1 generate
        hcrdt_up_fsm_i: entity work.PCIE_CRDT_UP_FSM
        port map(
            CLK                => CLK,
            RESET              => RESET,
            CRDT_UP_INIT       => PCIE_HCRDT_UP_INIT(j),
            CRDT_UP_INIT_ACK   => PCIE_HCRDT_UP_INIT_ACK(j),
            CRDT_UP_INIT_DONE  => hcrdt_up_init_done(j)
        );

        dcrdt_up_fsm_i: entity work.PCIE_CRDT_UP_FSM
        port map(
            CLK                => CLK,
            RESET              => RESET,
            CRDT_UP_INIT       => PCIE_DCRDT_UP_INIT(j),
            CRDT_UP_INIT_ACK   => PCIE_DCRDT_UP_INIT_ACK(j),
            CRDT_UP_INIT_DONE  => dcrdt_up_init_done(j)
        );
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            CRDT_UP_INIT_DONE <= (and hcrdt_up_init_done) and (and dcrdt_up_init_done);
            CRDT_UP_UPDATE(2 downto 0) <= PCIE_HCRDT_UP_UPDATE;
            CRDT_UP_UPDATE(5 downto 3) <= PCIE_DCRDT_UP_UPDATE;
            CRDT_UP_CNT_PH   <= PCIE_HCRDT_UP_UPDATE_CNT(1 downto 0);
            CRDT_UP_CNT_NPH  <= PCIE_HCRDT_UP_UPDATE_CNT(3 downto 2);
            CRDT_UP_CNT_CPLH <= PCIE_HCRDT_UP_UPDATE_CNT(5 downto 4);
            CRDT_UP_CNT_PD   <= PCIE_DCRDT_UP_UPDATE_CNT(3 downto 0);
            CRDT_UP_CNT_NPD  <= PCIE_DCRDT_UP_UPDATE_CNT(7 downto 4);
            CRDT_UP_CNT_CPLD <= PCIE_DCRDT_UP_UPDATE_CNT(11 downto 8);
        end if;
    end process;

    -- =========================================================================
    --  DOWN-STREAM LOGIC
    -- =========================================================================

    crdt_dw_g : for i in 0 to 3-1 generate
        hcrdt_dw_fsm_i: entity work.PCIE_CRDT_DW_FSM
        port map(
            CLK               => CLK,
            RESET             => RESET,
            CRDT_DW_INIT      => PCIE_HCRDT_DW_INIT(i),
            CRDT_DW_INIT_ACK  => PCIE_HCRDT_DW_INIT_ACK(i),
            CRDT_DW_INIT_EN   => hcrdt_dw_init_cnt_en(i),
            CRDT_DW_INIT_LAST => hcrdt_dw_init_cnt_last(i),
            CRDT_DW_INIT_DONE => hcrdt_dw_init_done(i)
        );

        hcrdt_dw_init_cnt_last(i) <= nor hcrdt_dw_init_cnt(i)(CRDT_XPH_CNT_W-1 downto 2);
        hcrdt_dw_init_cnt_dec(i)  <= (others => '0') when (hcrdt_dw_init_cnt_en(i) = '0') else
            hcrdt_dw_init_cnt(i)(2-1 downto 0) when (hcrdt_dw_init_cnt_last(i) = '1') else (others => '1');

        dcrdt_dw_fsm_i: entity work.PCIE_CRDT_DW_FSM
        port map(
            CLK               => CLK,
            RESET             => RESET,
            CRDT_DW_INIT      => PCIE_DCRDT_DW_INIT(i),
            CRDT_DW_INIT_ACK  => PCIE_DCRDT_DW_INIT_ACK(i),
            CRDT_DW_INIT_EN   => dcrdt_dw_init_cnt_en(i),
            CRDT_DW_INIT_LAST => dcrdt_dw_init_cnt_last(i),
            CRDT_DW_INIT_DONE => dcrdt_dw_init_done(i)
        );

        dcrdt_dw_init_cnt_last(i) <= nor dcrdt_dw_init_cnt(i)(CRDT_XPD_CNT_W-1 downto 4);
        dcrdt_dw_init_cnt_dec(i)  <= (others => '0') when (dcrdt_dw_init_cnt_en(i) = '0') else
            dcrdt_dw_init_cnt(i)(4-1 downto 0) when (dcrdt_dw_init_cnt_last(i) = '1') else (others => '1');
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            for i in 0 to 3-1 loop
                hcrdt_dw_init_cnt(i) <= hcrdt_dw_init_cnt(i) - hcrdt_dw_init_cnt_dec(i);
                dcrdt_dw_init_cnt(i) <= dcrdt_dw_init_cnt(i) - dcrdt_dw_init_cnt_dec(i);
            end loop;
            if (RESET = '1') then
                hcrdt_dw_init_cnt(0) <= to_unsigned(CRDT_TOTAL_PH,CRDT_XPH_CNT_W);
                hcrdt_dw_init_cnt(1) <= to_unsigned(CRDT_TOTAL_NPH,CRDT_XPH_CNT_W);
                hcrdt_dw_init_cnt(2) <= to_unsigned(CRDT_TOTAL_CPLH,CRDT_XPH_CNT_W);
                dcrdt_dw_init_cnt(0) <= to_unsigned(CRDT_TOTAL_PD,CRDT_XPD_CNT_W);
                dcrdt_dw_init_cnt(1) <= to_unsigned(CRDT_TOTAL_NPD,CRDT_XPD_CNT_W);
                dcrdt_dw_init_cnt(2) <= to_unsigned(CRDT_TOTAL_CPLD,CRDT_XPD_CNT_W);
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            PCIE_HCRDT_DW_UPDATE <= CRDT_DOWN_UPDATE(2 downto 0);
            PCIE_DCRDT_DW_UPDATE <= CRDT_DOWN_UPDATE(5 downto 3);
            PCIE_HCRDT_DW_UPDATE_CNT(2-1 downto 0)  <= CRDT_DOWN_CNT_PH;
            PCIE_HCRDT_DW_UPDATE_CNT(4-1 downto 2)  <= CRDT_DOWN_CNT_NPH;
            PCIE_HCRDT_DW_UPDATE_CNT(6-1 downto 4)  <= CRDT_DOWN_CNT_CPLH;
            PCIE_DCRDT_DW_UPDATE_CNT(4-1 downto 0)  <= CRDT_DOWN_CNT_PD;
            PCIE_DCRDT_DW_UPDATE_CNT(8-1 downto 4)  <= CRDT_DOWN_CNT_NPD;
            PCIE_DCRDT_DW_UPDATE_CNT(12-1 downto 8) <= CRDT_DOWN_CNT_CPLD;
            for i in 0 to 3-1 loop
                if (hcrdt_dw_init_done(i) = '0') then
                    PCIE_HCRDT_DW_UPDATE(i) <= hcrdt_dw_init_cnt_en(i);
                    PCIE_HCRDT_DW_UPDATE_CNT((i+1)*2-1 downto i*2) <= std_logic_vector(hcrdt_dw_init_cnt_dec(i));
                end if;
                if (dcrdt_dw_init_done(i) = '0') then
                    PCIE_DCRDT_DW_UPDATE(i) <= dcrdt_dw_init_cnt_en(i);
                    PCIE_DCRDT_DW_UPDATE_CNT((i+1)*4-1 downto i*4) <= std_logic_vector(dcrdt_dw_init_cnt_dec(i));
                end if;
            end loop;
            if (RESET = '1') then
                PCIE_HCRDT_DW_UPDATE <= (others => '0');
                PCIE_DCRDT_DW_UPDATE <= (others => '0');
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            CRDT_DOWN_INIT_DONE <= (and hcrdt_dw_init_done) and (and dcrdt_dw_init_done);
        end if;
    end process;

end architecture;
