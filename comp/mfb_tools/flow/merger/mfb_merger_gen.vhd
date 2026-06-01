-- mfb_merger_gen.vhd: MFB+MVB bus merger with generic number of inputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- MFB+MVB bus merger with generic number of inputs.
--
-- This module merges multiple input MVB+MFB streams into a single output stream
-- using a binary tree of 2:1 MFB_MERGER units. The number of inputs can be any
-- positive integer (non-power-of-2 inputs are padded internally).
--
-- MVB and MFB Interface Usage
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- The MVB interface carries header information (e.g., DMA descriptors) while
-- the MFB interface carries the associated data payload. Each MVB header can
-- be marked as having an associated payload frame using the ``RX_MVB_PAYLOAD``
-- signal. When ``RX_MVB_PAYLOAD(i)(j) = '1'``, the j-th header on input i is
-- associated with data on the MFB interface. The merger maintains this
-- association throughout the merging process.
--
-- .. warning::
--   Related MVB headers and their corresponding MFB data frames must arrive at
--   each input in the same order they are expected to appear on the output. The
--   merger pairs headers with payloads based on arrival order, not by content
--   matching. Out-of-order arrival will result in incorrect header-payload pairing.
--
-- RX_MVB_PAYLOAD Signal Usage
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- This signal indicates which MVB headers have associated data payload on MFB.
--
-- * When ``'1'``: The corresponding header has an associated data frame on MFB
-- * When ``'0'``: The header is standalone (control-only, no data payload)
--
-- Each bit in ``RX_MVB_PAYLOAD(i)`` corresponds to one MVB header item on input i.
--
-- RX_PAYLOAD_EN Generic
-- ^^^^^^^^^^^^^^^^^^^^^
-- Controls whether the MFB data path is implemented for each input port.
--
-- * When ``true``: Full MVB+MFB merging with header-payload association
-- * When ``false``: Only MVB headers are processed; MFB path is bypassed
--
-- Use ``false`` for inputs that only send control headers without data payload,
-- reducing resource consumption by eliminating unnecessary MFB pipeline stages.
--
-- Features
-- ^^^^^^^^
-- * Configurable number of input streams (any positive integer)
-- * Configurable MVB item count and MFB geometry
-- * Optional mid-stage MFB FIFOs for buffering
-- * Configurable input/output pipelining
-- * Timeout-based stream switching
-- * Metadata support on MFB interface
--
entity MFB_MERGER_GEN is
    generic (
        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- Number of merger input streams
        -- Can be any positive integer (non-power-of-2 values are padded internally)
        MERGER_INPUTS   : integer := 2;

        -- =====================================================================
        -- MVB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MVB header items (parallel headers per cycle)
        MVB_ITEMS       : integer := 2;
        -- Width of each MVB header item in bits
        MVB_ITEM_WIDTH  : integer := 32;

        -- =====================================================================
        -- MFB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MFB regions per word
        MFB_REGIONS     : integer := 2;
        -- Number of blocks per region
        MFB_REG_SIZE    : integer := 1;
        -- Number of items per block
        MFB_BLOCK_SIZE  : integer := 8;
        -- Width of one MFB item in bits
        MFB_ITEM_WIDTH  : integer := 32;
        -- Width of MFB metadata bus in bits
        MFB_META_WIDTH  : integer := 1;

        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- Depth of input MVB and MFB FIFOs in words
        -- Minimum value is 2
        INPUT_FIFO_SIZE : integer := 8;

        -- MFB data payload enable for each input port
        -- RX_PAYLOAD_EN(i) = true: Full MVB+MFB operation on input i
        -- RX_PAYLOAD_EN(i) = false: MVB headers only on input i (MFB path optimized away)
        -- Use false for inputs that only carry control headers without data
        RX_PAYLOAD_EN   : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);

        -- Width of stream switch timeout counter
        -- Timeout = 2^SW_TIMEOUT_WIDTH cycles of inactivity before switching
        -- Higher values reduce switching frequency but increase latency for
        -- the non-active stream. Lower values may create gaps between MFB
        -- packets during switching, reducing throughput (only one input port
        -- is read per cycle per merger stage)
        SW_TIMEOUT_WIDTH : natural := 4;

        -- Enable optional MFB FIFOs at intermediate merger stages
        -- false: No FIFOs between merger stages (input FIFOs only)
        -- true: Adds MFB_FIFOX buffers at each internal tree stage
        MID_MFB_FIFOS_EN : boolean := False;

        -- Enable input PIPE stages for all internal 2:1 merger units
        -- true: Uses MVB_PIPE and MFB_PIPE components for registered inputs
        -- false: Uses simple registers (combinatorial input path)
        IN_PIPE_EN      : boolean := false;

        -- Enable output PIPE stage for all internal 2:1 merger units
        -- true: Uses MVB_PIPE and MFB_PIPE components for registered outputs
        -- false: Uses simple output registers
        OUT_PIPE_EN     : boolean := true;

        -- Architecture selection for internal FIFOX_MULTI component
        -- Supported values:
        -- * "SHAKEDOWN": Handshake-based FIFO with better buffering and throughput
        -- * "FULL": Standard implementation with wide MUXes
        FIFOX_MULTI_ARCH : string := "SHAKEDOWN";

        -- Target device family for FIFO/PIPE implementation
        -- Specifies the FPGA device family for optimal resource inference
        DEVICE          : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        -- System clock
        CLK            : in  std_logic;
        -- Synchronous reset (active high)
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX INTERFACES (per input port)
        -- =====================================================================

        -- MVB header bus array (one per input port)
        -- RX_MVB_DATA(i) contains MVB_ITEMS headers, each MVB_ITEM_WIDTH bits
        RX_MVB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- Payload association flags array (one per input port)
        -- RX_MVB_PAYLOAD(i)(j) = '1': Header j on input i has associated MFB data
        RX_MVB_PAYLOAD : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        -- Header valid flags array (one per input port)
        RX_MVB_VLD     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        -- Source ready array (one per input port)
        -- Backpressure from merger to upstream sender
        RX_MVB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        -- Destination ready array (one per input port)
        -- Flow control from merger to upstream sender
        RX_MVB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        -- MFB data bus array (one per input port)
        -- Organized as: MFB_REGIONS x MFB_REG_SIZE x MFB_BLOCK_SIZE x MFB_ITEM_WIDTH bits
        RX_MFB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- MFB metadata bus array (one per input port)
        -- Always valid when MFB data is valid; passed through unchanged
        RX_MFB_META    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
        -- Start of Frame flags array (one per input port)
        -- RX_MFB_SOF(i)(r) = '1': Region r on input i contains SOF
        RX_MFB_SOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        -- End of Frame flags array (one per input port)
        -- RX_MFB_EOF(i)(r) = '1': Region r on input i contains EOF
        RX_MFB_EOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        -- SOF position array (one per input port)
        -- Indicates which block within the region contains the SOF
        RX_MFB_SOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        -- EOF position array (one per input port)
        -- Indicates which item within the block contains the EOF
        RX_MFB_EOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- Source ready array (one per input port)
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        -- Destination ready array (one per input port)
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        -- =====================================================================
        -- TX INTERFACE (merged output)
        -- =====================================================================

        -- Merged MVB header bus
        -- Contains headers from all inputs, merged based on activity
        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- Payload association flags for merged output
        -- Maintains the header-to-payload relationship from input streams
        TX_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- Header valid flags for merged output
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- Source ready - backpressure from downstream receiver
        -- Asserted when the merger has valid data to send
        TX_MVB_SRC_RDY : out std_logic;
        -- Destination ready - flow control from downstream consumer
        -- When '1', the consumer can accept new data
        TX_MVB_DST_RDY : in  std_logic;

        -- Merged MFB data bus
        -- Contains payload data from all inputs, synchronized with TX_MVB_DATA
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Merged MFB metadata bus
        -- Metadata from active input stream passed through unchanged
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        -- Start of Frame flags for merged output
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- End of Frame flags for merged output
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- SOF position for merged output
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        -- EOF position for merged output
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- Source ready - backpressure from downstream receiver
        -- Asserted when the merger has valid MFB data to send
        TX_MFB_SRC_RDY : out std_logic;
        -- Destination ready - flow control from downstream consumer
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER_GEN is

    constant TREE_STAGES         : natural := log2(MERGER_INPUTS);
    constant MERGER_INPUTS_2_POW : natural := 2**TREE_STAGES;

    function rx_payload_en_2_pow_init return b_array_t is
        variable tmp : b_array_t(MERGER_INPUTS_2_POW-1 downto 0) := (others => false);
    begin
        tmp(MERGER_INPUTS-1 downto 0) := RX_PAYLOAD_EN;
        return tmp;
    end function;

    constant RX_PAYLOAD_EN_2_POW : b_array_t(MERGER_INPUTS_2_POW-1 downto 0) := rx_payload_en_2_pow_init;

    function get_payload_en (stage, index : integer) return boolean;

    function get_payload_en (stage, index : integer) return boolean is
    begin
        -- JC: Reports do not work in Vivado!
        -- report "inputs " & to_string(MERGER_INPUTS) & "; inputs 2 pow " & to_string(MERGER_INPUTS_2_POW) & "; stages " & to_string(TREE_STAGES);
        -- report "gen_payload_en ( " & to_string(stage) & " , " & to_string(index) & " )";
        if (stage /= 0) then
            -- Recursive call to previous stage
            return get_payload_en(stage-1,2*index) or get_payload_en(stage-1,2*index+1);
        else
            -- End of recursion -> user input
            return RX_PAYLOAD_EN_2_POW(index);
        end if;
    end function;

    signal s_rx_mvb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mvb_payload : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_vld     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0) := (others => (others => '0'));
    signal s_rx_mvb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);
    signal s_rx_mfb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mfb_meta    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal s_rx_mfb_sof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_eof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_sof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal s_rx_mfb_eof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal s_rx_mfb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);
    signal s_rx_mfb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);

begin

    inputs_g : for i in 0 to MERGER_INPUTS-1 generate

        s_rx_mvb_data   (0)(i) <= RX_MVB_DATA   (i);
        s_rx_mvb_payload(0)(i) <= RX_MVB_PAYLOAD(i);
        s_rx_mvb_vld    (0)(i) <= RX_MVB_VLD    (i);
        s_rx_mvb_src_rdy(0)(i) <= RX_MVB_SRC_RDY(i);

        RX_MVB_DST_RDY(i)      <= s_rx_mvb_dst_rdy(0)(i);

        s_rx_mfb_data   (0)(i) <= RX_MFB_DATA   (i);
        s_rx_mfb_meta   (0)(i) <= RX_MFB_META   (i);
        s_rx_mfb_sof    (0)(i) <= RX_MFB_SOF    (i);
        s_rx_mfb_eof    (0)(i) <= RX_MFB_EOF    (i);
        s_rx_mfb_sof_pos(0)(i) <= RX_MFB_SOF_POS(i);
        s_rx_mfb_eof_pos(0)(i) <= RX_MFB_EOF_POS(i);
        s_rx_mfb_src_rdy(0)(i) <= RX_MFB_SRC_RDY(i);

        RX_MFB_DST_RDY(i)      <= s_rx_mfb_dst_rdy(0)(i);

    end generate;

    stage_g : for s in 0 to TREE_STAGES-1 generate
        merger_g : for i in 0 to (2**(TREE_STAGES-s-1))-1 generate
            merger_i: entity work.MFB_MERGER(FULL)
            generic map (
                MVB_ITEMS           => MVB_ITEMS,
                MFB_REGIONS         => MFB_REGIONS,
                MFB_REG_SIZE        => MFB_REG_SIZE,
                MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
                MFB_META_WIDTH      => MFB_META_WIDTH,
                HDR_WIDTH           => MVB_ITEM_WIDTH,
                RX0_PAYLOAD_ENABLED => get_payload_en(s,2*i  ),
                RX1_PAYLOAD_ENABLED => get_payload_en(s,2*i+1),
                IN_MFB_FIFO_EN      => (s /= 0 and MID_MFB_FIFOS_EN),
                INPUT_FIFO_SIZE     => INPUT_FIFO_SIZE,
                SW_TIMEOUT_WIDTH    => SW_TIMEOUT_WIDTH,
                IN_PIPE_EN          => IN_PIPE_EN,
                OUT_PIPE_EN         => OUT_PIPE_EN,
                FIFOX_MULTI_ARCH    => FIFOX_MULTI_ARCH,
                DEVICE              => DEVICE
            )
            port map (
                CLK             => CLK,
                RESET           => RESET,

                RX0_MVB_HDR     => s_rx_mvb_data   (s)(2*i),
                RX0_MVB_PAYLOAD => s_rx_mvb_payload(s)(2*i),
                RX0_MVB_VLD     => s_rx_mvb_vld    (s)(2*i),
                RX0_MVB_SRC_RDY => s_rx_mvb_src_rdy(s)(2*i),
                RX0_MVB_DST_RDY => s_rx_mvb_dst_rdy(s)(2*i),
                RX0_MFB_DATA    => s_rx_mfb_data   (s)(2*i),
                RX0_MFB_META    => s_rx_mfb_meta   (s)(2*i),
                RX0_MFB_SOF     => s_rx_mfb_sof    (s)(2*i),
                RX0_MFB_EOF     => s_rx_mfb_eof    (s)(2*i),
                RX0_MFB_SOF_POS => s_rx_mfb_sof_pos(s)(2*i),
                RX0_MFB_EOF_POS => s_rx_mfb_eof_pos(s)(2*i),
                RX0_MFB_SRC_RDY => s_rx_mfb_src_rdy(s)(2*i),
                RX0_MFB_DST_RDY => s_rx_mfb_dst_rdy(s)(2*i),

                RX1_MVB_HDR     => s_rx_mvb_data   (s)(2*i+1),
                RX1_MVB_PAYLOAD => s_rx_mvb_payload(s)(2*i+1),
                RX1_MVB_VLD     => s_rx_mvb_vld    (s)(2*i+1),
                RX1_MVB_SRC_RDY => s_rx_mvb_src_rdy(s)(2*i+1),
                RX1_MVB_DST_RDY => s_rx_mvb_dst_rdy(s)(2*i+1),
                RX1_MFB_DATA    => s_rx_mfb_data   (s)(2*i+1),
                RX1_MFB_META    => s_rx_mfb_meta   (s)(2*i+1),
                RX1_MFB_SOF     => s_rx_mfb_sof    (s)(2*i+1),
                RX1_MFB_EOF     => s_rx_mfb_eof    (s)(2*i+1),
                RX1_MFB_SOF_POS => s_rx_mfb_sof_pos(s)(2*i+1),
                RX1_MFB_EOF_POS => s_rx_mfb_eof_pos(s)(2*i+1),
                RX1_MFB_SRC_RDY => s_rx_mfb_src_rdy(s)(2*i+1),
                RX1_MFB_DST_RDY => s_rx_mfb_dst_rdy(s)(2*i+1),

                TX_MVB_HDR      => s_rx_mvb_data   (s+1)(i),
                TX_MVB_PAYLOAD  => s_rx_mvb_payload(s+1)(i),
                TX_MVB_VLD      => s_rx_mvb_vld    (s+1)(i),
                TX_MVB_SRC_RDY  => s_rx_mvb_src_rdy(s+1)(i),
                TX_MVB_DST_RDY  => s_rx_mvb_dst_rdy(s+1)(i),
                TX_MFB_DATA     => s_rx_mfb_data   (s+1)(i),
                TX_MFB_META     => s_rx_mfb_meta   (s+1)(i),
                TX_MFB_SOF      => s_rx_mfb_sof    (s+1)(i),
                TX_MFB_EOF      => s_rx_mfb_eof    (s+1)(i),
                TX_MFB_SOF_POS  => s_rx_mfb_sof_pos(s+1)(i),
                TX_MFB_EOF_POS  => s_rx_mfb_eof_pos(s+1)(i),
                TX_MFB_SRC_RDY  => s_rx_mfb_src_rdy(s+1)(i),
                TX_MFB_DST_RDY  => s_rx_mfb_dst_rdy(s+1)(i)
            );

        end generate;
    end generate;

    TX_MVB_DATA    <= s_rx_mvb_data   (TREE_STAGES)(0);
    TX_MVB_PAYLOAD <= s_rx_mvb_payload(TREE_STAGES)(0);
    TX_MVB_VLD     <= s_rx_mvb_vld    (TREE_STAGES)(0);
    TX_MVB_SRC_RDY <= s_rx_mvb_src_rdy(TREE_STAGES)(0);

    s_rx_mvb_dst_rdy(TREE_STAGES)(0) <= TX_MVB_DST_RDY;

    TX_MFB_DATA    <= s_rx_mfb_data   (TREE_STAGES)(0);
    TX_MFB_META    <= s_rx_mfb_meta   (TREE_STAGES)(0);
    TX_MFB_SOF     <= s_rx_mfb_sof    (TREE_STAGES)(0);
    TX_MFB_EOF     <= s_rx_mfb_eof    (TREE_STAGES)(0);
    TX_MFB_SOF_POS <= s_rx_mfb_sof_pos(TREE_STAGES)(0);
    TX_MFB_EOF_POS <= s_rx_mfb_eof_pos(TREE_STAGES)(0);
    TX_MFB_SRC_RDY <= s_rx_mfb_src_rdy(TREE_STAGES)(0);

    s_rx_mfb_dst_rdy(TREE_STAGES)(0) <= TX_MFB_DST_RDY;

end architecture;
