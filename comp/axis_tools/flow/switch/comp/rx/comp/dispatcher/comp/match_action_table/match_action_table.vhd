-- match_action_table.vhd: MATCH_ACTION_TABLE component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity MATCH_ACTION_TABLE is
    generic (
        -- Capacity in number of rules.
        ITEMS             : natural := 64;
        -- Address width in bits.
        ADDR_WIDTH        : natural := max(1,log2(ITEMS));
        -- Data vector width in bits.
        MATCH_DATA_WIDTH  : natural := 48;
        -- Action width in bits.
        ACTION_DATA_WIDTH : natural := 4;
        -- Enable reading rules.
        READ_ENABLE       : boolean := true;
        -- Target device.
        DEVICE            : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK          : in  std_logic;
        RESET        : in  std_logic;

        -- =========================================================================
        -- READ INTERFACE
        -- =========================================================================
        READ_ADDR    : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        READ_EN      : in  std_logic;
        READ_RDY     : out std_logic;
        READ_VLD     : out std_logic;
        READ_DATA    : out std_logic_vector(MATCH_DATA_WIDTH-1 downto 0);
        READ_MASK    : out std_logic_vector(MATCH_DATA_WIDTH-1 downto 0);
        READ_ACTION  : out std_logic_vector(ACTION_DATA_WIDTH-1 downto 0);

        -- =========================================================================
        -- WRITE INTERFACE
        -- =========================================================================
        WRITE_ADDR   : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        WRITE_EN     : in  std_logic;
        WRITE_RDY    : out std_logic;
        WRITE_DATA   : in  std_logic_vector(MATCH_DATA_WIDTH-1 downto 0);
        WRITE_MASK   : in  std_logic_vector(MATCH_DATA_WIDTH-1 downto 0);
        WRITE_ACTION : in  std_logic_vector(ACTION_DATA_WIDTH-1 downto 0);

        -- =========================================================================
        -- MATCH/ACTION INTERFACE
        -- =========================================================================
        MATCH_DATA   : in  std_logic_vector(MATCH_DATA_WIDTH-1 downto 0);
        MATCH_EN     : in  std_logic;
        MATCH_RDY    : out std_logic;
        ACTION_VLD   : out std_logic;
        ACTION       : out std_logic_vector(ACTION_DATA_WIDTH-1 downto 0)

    );
end entity;

architecture FULL of MATCH_ACTION_TABLE is

    constant LATENCY_MATCH_STORAGE  : natural := 3; -- TCAM2 MATCH_OUT ifc latency
    constant LATENCY_ACTION_STORAGE : natural := 1;
    constant LATENCY_TOTAL          : natural := LATENCY_MATCH_STORAGE + LATENCY_ACTION_STORAGE;

    signal s_match_out_hit      : std_logic;
    signal s_match_out_addr_vec : std_logic_vector(ITEMS-1 downto 0);
    signal s_match_out_addr     : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal s_match_out_vld      : std_logic;

    signal s_action_rd_addr     : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal s_action_rd_data     : std_logic_vector(ACTION_DATA_WIDTH-1 downto 0);

begin

    match_storage_i : entity work.TCAM2
    generic map (
        DATA_WIDTH         => MATCH_DATA_WIDTH,
        ITEMS              => ITEMS,
        RESOURCES_SAVING   => 0,
        WRITE_BEFORE_MATCH => true,
        READ_FROM_TCAM     => READ_ENABLE,
        OUTPUT_READ_REGS   => READ_ENABLE,
        USE_UNMATCHABLE    => true,
        USE_FRAGMENTED_MEM => false,
        DEVICE             => DEVICE
    )
    port map (
        CLK                => CLK,
        RST                => RESET,
        READ_ADDR          => READ_ADDR,
        READ_EN            => READ_EN,
        READ_RDY           => READ_RDY,
        READ_DATA          => READ_DATA,
        READ_MASK          => READ_MASK,
        READ_DATA_VLD      => READ_VLD,
        WRITE_DATA         => WRITE_DATA,
        WRITE_MASK         => WRITE_MASK,
        WRITE_ADDR         => WRITE_ADDR,
        WRITE_EN           => WRITE_EN,
        WRITE_RDY          => WRITE_RDY,
        MATCH_DATA         => MATCH_DATA,
        MATCH_EN           => MATCH_EN,
        MATCH_RDY          => MATCH_RDY,
        MATCH_OUT_HIT      => s_match_out_hit,
        MATCH_OUT_ADDR     => s_match_out_addr_vec,
        MATCH_OUT_VLD      => s_match_out_vld
    );

    action_rd_data_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            READ_ACTION <= s_action_rd_data;
        end if;
    end process;

    addr_encoder_i : entity work.GEN_ENC
    generic map (
        ITEMS  => ITEMS,
        DEVICE => DEVICE
    )
    port map (
        DI   => s_match_out_addr_vec,
        ADDR => s_match_out_addr
    );

    action_storage_i : entity work.GEN_LUTRAM
    generic map (
        DATA_WIDTH         => ACTION_DATA_WIDTH,
        ITEMS              => ITEMS,
        RD_PORTS           => 1,
        RD_LATENCY         => LATENCY_ACTION_STORAGE,
        WRITE_USE_RD_ADDR0 => false,
        MLAB_CONSTR_RDW_DC => false,
        DEVICE             => DEVICE
    )
    port map (
        CLK                => CLK,
        WR_EN              => WRITE_EN,
        WR_ADDR            => WRITE_ADDR,
        WR_DATA            => WRITE_ACTION,
        RD_ADDR            => s_action_rd_addr,
        RD_DATA            => s_action_rd_data
    );

    s_action_rd_addr <= READ_ADDR when READ_EN = '1' else s_match_out_addr;
    ACTION           <= s_action_rd_data;

    action_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                ACTION_VLD <= '0';
            else
                ACTION_VLD <= s_match_out_hit and s_match_out_vld;
            end if;
        end if;
    end process;

end architecture;
