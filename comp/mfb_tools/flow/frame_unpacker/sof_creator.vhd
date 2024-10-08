-- sof_creator.vhd: This component searches for SOF and extracts the length from the following individual packet.
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

-- The SOF Creator accepts the "new" offset from the Offset Processor and rounds it up to the nearest Block.
-- Then it evaluates it to determine whether it points to this Word and this Region, and if it does, it asserts (creates) SOF.
-- Lastly, with the help of the rounded offset, it extracts the Length field of the header of the following individual frame in the SuperPacket.
entity SOF_CREATOR is
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
    -- Header length (in Items).
    HDR_LENGTH            : natural := 16;

    -- The ID of the analyzer withing this stage.
    REGION_NUMBER         : natural := 0;
    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK         : in  std_logic;
    RESET       : in  std_logic;

    -- =====================================================================
    --  RX inf
    -- =====================================================================

    RX_DATA     : in  std_logic_vector(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_META     : in  std_logic_vector(MFB_META_WIDTH-1 downto 0);
    RX_OFFSET   : in  unsigned        (OFFSET_WIDTH-1 downto 0);
    RX_WORD     : in  unsigned        (log2(MAX_WORDS)-1 downto 0);
    RX_SOF_MASK : in  std_logic;

    -- =====================================================================
    --  TX inf
    -- =====================================================================

    TX_DATA     : out std_logic_vector(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_META     : out std_logic_vector(MFB_META_WIDTH-1 downto 0);
    TX_OFFSET   : out unsigned        (OFFSET_WIDTH-1 downto 0);
    TX_LENGTH   : out unsigned        (LENGTH_WIDTH-1 downto 0);
    TX_WORD     : out unsigned        (log2(MAX_WORDS)-1 downto 0);
    TX_NEW_SOF  : out std_logic;
    TX_SOF_MASK : out std_logic
);
end entity;

architecture FULL of SOF_CREATOR is

    constant OFFSET_WIDTH_BLOCKS : natural := OFFSET_WIDTH - log2(MFB_BLOCK_SIZE);

    signal multiple_items        : std_logic;
    signal rx_offset_round_block : unsigned(OFFSET_WIDTH_BLOCKS-1 downto 0);

    signal target_word   : unsigned(log2(MAX_WORDS)-1 downto 0);
    signal target_region : unsigned(max(1,log2(MFB_REGIONS))-1 downto 0);
    signal target_block  : unsigned(log2(MFB_REGION_SIZE)-1 downto 0);

    signal sof           : std_logic;
    signal sof_masked    : std_logic;

    signal rx_data_arr   : slv_array_t     (MFB_REGION_SIZE-1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ext_block     : std_logic_vector                            (MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ext_length    : std_logic_vector(LENGTH_WIDTH-1 downto 0);

begin

    -- ========================================================================
    -- Offset roundup to Blocks
    -- ========================================================================

    multiple_items <= or (RX_OFFSET(log2(MFB_BLOCK_SIZE)-1 downto 0));
    -- Round RX offset to Blocks (increment the number of Blocks if the SOF offest is not aligned to a Block).
    rx_offset_round_block <= (unsigned(RX_OFFSET(OFFSET_WIDTH-1 downto log2(MFB_BLOCK_SIZE))) + multiple_items);

    -- ========================================================================
    -- Offset parsing
    -- ========================================================================

    single_region_g : if MFB_REGIONS > 1 generate

        target_word   <= rx_offset_round_block(OFFSET_WIDTH_BLOCKS                            -1 downto OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS            ));
        target_region <= rx_offset_round_block(OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS            )-1 downto OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS*MFB_REGIONS));
        target_block  <= rx_offset_round_block(OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS*MFB_REGIONS)-1 downto 0                                              );

    else generate

        target_region(0) <= '0';

        target_word  <= rx_offset_round_block(OFFSET_WIDTH_BLOCKS                -1 downto OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS));
        target_block <= rx_offset_round_block(OFFSET_WIDTH_BLOCKS-log2(MAX_WORDS)-1 downto 0                                  );

    end generate;

    -- ========================================================================
    -- SOF evaluation and validation
    -- ========================================================================

    sof <= '1' when (RX_WORD = target_word) and (REGION_NUMBER = target_region) else '0';
    sof_masked <= sof and RX_SOF_MASK;

    -- ========================================================================
    -- Length extraction
    -- ========================================================================

    rx_data_arr <= slv_array_deser(RX_DATA, MFB_REGION_SIZE);
    ext_block   <= rx_data_arr(to_integer(target_block));
    ext_length  <= ext_block(LENGTH_WIDTH-1 downto 0);

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    TX_DATA     <= RX_DATA;
    TX_META     <= RX_META;
    TX_OFFSET   <= RX_OFFSET;
    TX_LENGTH   <= unsigned(ext_length) + HDR_LENGTH;
    TX_WORD     <= RX_WORD;
    TX_NEW_SOF  <= sof_masked;
    TX_SOF_MASK <= RX_SOF_MASK;

end architecture;
