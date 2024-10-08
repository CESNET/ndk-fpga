-- offset_processor.vhd: This component processes the received offset based on the received SOF signals.
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- The Offset Processor (OP) receives the offset from the OP in the previous stage along with its SOF (the Old SOF).
-- From the SOF Creator (also in the previous stage), it receives the extracted Length and its own SOF (the New SOF).
-- Based on the Old SOF, it propagates either the received offset (when Old SOF = 1) or "creates" a new offset by rounding up the received offset to the next Block and adding the received length to it.
-- The updated offset is propagated by the ``MVB_AGGREGATE_LAST_VLD`` component to the following Regions and Words until another SOF (Old or New) overwrites the current one.
entity OFFSET_PROCESSOR is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS           : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items), must be 8.
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;
    -- Metadata width (in bits).
    MFB_META_WIDTH        : natural := 0;

    -- Maximum size of a packet (in Items).
    PKT_MTU               : natural := 2**12;
    -- Maximum amount of words one (individual) packet can strech over.
    MAX_WORDS             : natural := PKT_MTU/(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE);
    -- Offset size (in Blocks).
    OFFSET_WIDTH          : natural := log2(MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE);
    -- Width of the Length field.
    LENGTH_WIDTH          : natural := 16;

    -- Last Valid implementation.
    -- Options: "serial", "parallel", "prefixsum"
    LAST_VLD_IMPL         : string := "serial";
    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- =====================================================================
    --  RX inf
    -- =====================================================================

    RX_DATA     : in  slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_META     : in  slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    RX_OFFSET   : in  u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    RX_LENGTH   : in  u_array_t       (MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    RX_WORD     : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    RX_OLD_SOF  : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_NEW_SOF  : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_SOF_MASK : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_SRC_RDY  : in  std_logic;
    RX_DST_RDY  : out std_logic;

    -- =====================================================================
    --  TX inf
    -- =====================================================================

    TX_DATA     : out slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_META     : out slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    TX_OFFSET   : out u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    TX_WORD     : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    TX_OLD_SOF  : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_SOF_MASK : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_SRC_RDY  : out std_logic;
    TX_DST_RDY  : in  std_logic
);
end entity;

architecture FULL of OFFSET_PROCESSOR is

    signal roundup_offset   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rounded_offset   : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal updated_offset   : slv_array_t     (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal updated_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal offset_propg     : std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);

begin

    roundup_offset_g : for r in 0 to MFB_REGIONS-1 generate
        roundup_offset(r) <= or (RX_OFFSET(r)(log2(MFB_BLOCK_SIZE)-1 downto 0));
        rounded_offset(r) <= resize_right(RX_OFFSET(r)(OFFSET_WIDTH-1 downto log2(MFB_BLOCK_SIZE)) + roundup_offset(r), OFFSET_WIDTH);
    end generate;

    updated_offset_g : for r in 0 to MFB_REGIONS-1 generate
        updated_offset(r) <= std_logic_vector(RX_OFFSET(r)) when (RX_OLD_SOF(r) = '1') else std_logic_vector(rounded_offset(r) + resize(RX_LENGTH(r), OFFSET_WIDTH));
    end generate;

    updated_sof <= RX_OLD_SOF or RX_NEW_SOF;

    last_vld_i : entity work.MVB_AGGREGATE_LAST_VLD
    generic map(
        ITEMS          => MFB_REGIONS  ,
        ITEM_WIDTH     => OFFSET_WIDTH ,
        IMPLEMENTATION => LAST_VLD_IMPL,
        INTERNAL_REG   => true
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA         => slv_array_ser(updated_offset),
        RX_VLD          => updated_sof,
        RX_SRC_RDY      => RX_SRC_RDY,
        RX_DST_RDY      => RX_DST_RDY,

        REG_IN_DATA     => (others => '0'),
        REG_IN_VLD      => '0',
        REG_OUT_DATA    => open,
        REG_OUT_VLD     => open,
        REG_OUT_WR      => open,

        TX_DATA         => offset_propg,
        TX_VLD          => open,
        TX_PRESCAN_DATA => open,
        TX_PRESCAN_VLD  => open,
        TX_SRC_RDY      => open,
        TX_DST_RDY      => TX_DST_RDY
    );

    TX_DATA     <= RX_DATA;
    TX_META     <= RX_META;
    TX_OFFSET   <= slv_arr_to_u_arr(slv_array_deser(offset_propg, MFB_REGIONS));
    TX_WORD     <= RX_WORD;
    TX_OLD_SOF  <= updated_sof;
    TX_SOF_MASK <= RX_SOF_MASK;
    TX_SRC_RDY  <= RX_SRC_RDY;

end architecture;
