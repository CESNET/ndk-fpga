-- mfb_merger_ent.vhd: MFB+MVB bus merger
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- Merges two input MVB+MFB interfaces into a single output interface.
--
-- The module alternates between two input streams (RX0 and RX1) and merges
-- them into one output stream (TX). It handles both MVB (control headers)
-- and MFB (data payload) interfaces simultaneously, maintaining association
-- between headers and their corresponding data frames.
--
-- MVB and MFB Interface Usage
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- The MVB interface carries header information (e.g., DMA descriptors) while
-- the MFB interface carries the associated data payload. Each MVB header can
-- be marked as having an associated payload frame using the ``RXx_MVB_PAYLOAD``
-- signal. When ``RXx_MVB_PAYLOAD(i) = '1'``, the i-th header is associated with
-- data on the MFB interface. The merger maintains this association throughout
-- the merging process, ensuring headers and their payloads emerge together on
-- the TX interface.
--
-- .. warning::
--   Related MVB headers and their corresponding MFB data frames must arrive at
--   the input in the same order they are expected to appear on the output. The
--   merger pairs headers with payloads based on arrival order, not by content
--   matching. If a header with ``RXx_MVB_PAYLOAD(i)='1'`` arrives, the next MFB
--   frame on that input port will be associated with that header. Out-of-order
--   arrival will result in incorrect header-payload pairing.
--
-- RXx_MVB_PAYLOAD Signal Usage
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- This signal indicates which MVB headers have associated data payload on MFB.
--
-- * When ``'1'``: The corresponding header has an associated data frame on MFB
-- * When ``'0'``: The header is standalone (control-only, no data payload)
--
-- Each bit in ``RXx_MVB_PAYLOAD`` corresponds to one MVB header item.
--
-- RXx_PAYLOAD_ENABLED Generic
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- Controls whether the MFB data path is implemented for each input port.
--
-- * When ``true``: Full MVB+MFB merging with header-payload association
-- * When ``false``: Only MVB headers are processed; MFB path is bypassed
--
-- Use ``false`` when an input port only sends control headers without data
-- payload, reducing resource consumption by eliminating unnecessary MFB
-- pipeline stages.
--
-- Features
-- ^^^^^^^^
-- * Configurable MVB item count and MFB geometry
-- * Optional input FIFOs for MFB interface
-- * Configurable input/output pipelining
-- * Timeout-based stream switching
-- * Metadata support on MFB interface
--
entity MFB_MERGER is
    generic (
        -- =====================================================================
        -- MVB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MVB header items (parallel headers per cycle)
        -- Determines the width of MVB-related signals: MVB_ITEMS * HDR_WIDTH
        MVB_ITEMS           : integer := 2;

        -- =====================================================================
        -- MFB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MFB regions per word
        -- Each region can independently carry SOF/EOF markers
        MFB_REGIONS         : integer := 2;
        -- Number of blocks per region
        -- Affects EOF position width: log2(MFB_REG_SIZE * MFB_BLOCK_SIZE)
        MFB_REG_SIZE        : integer := 1;
        -- Number of items per block
        -- Combined with ITEM_WIDTH determines total MFB data width
        MFB_BLOCK_SIZE      : integer := 8;
        -- Width of one MFB item in bits
        -- Typical values: 32, 64, 128, 256
        MFB_ITEM_WIDTH      : integer := 32;

        -- Width of MFB metadata bus in bits
        -- Set to 0 to disable metadata support
        -- Metadata is passed through unchanged for each region
        MFB_META_WIDTH      : integer := 0;

        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- Width of each MVB header item in bits
        -- Common values: DMA_DOWNHDR_WIDTH (downstream) or DMA_UPHDR_WIDTH (upstream)
        -- from dma_bus_pack package
        HDR_WIDTH           : integer := DMA_DOWNHDR_WIDTH;

        -- Enable MFB data payload processing on RX0 input port
        -- true: Full MVB+MFB operation with header-payload association
        -- false: MVB headers processed; MFB path optimized away (FAKE_PIPE)
        -- Use false when RX0 only carries standalone headers without data
        RX0_PAYLOAD_ENABLED : boolean := true;

        -- Enable MFB data payload processing on RX1 input port
        -- Same behavior as RX0_PAYLOAD_ENABLED but for the second input
        RX1_PAYLOAD_ENABLED : boolean := true;

        -- Enable optional MFB FIFOs at input ports for additional buffering
        -- true: Instantiates MFB_FIFOX buffers of INPUT_FIFO_SIZE depth
        -- false: Direct connection without input buffering
        IN_MFB_FIFO_EN      : boolean := false;

        -- Depth of input MVB and MFB FIFOs in words
        -- Minimum value is 2
        -- Only used when IN_MFB_FIFO_EN = true
        INPUT_FIFO_SIZE     : integer := 8;

        -- Width of stream switch timeout counter
        -- Timeout = 2^SW_TIMEOUT_WIDTH cycles of inactivity before switching
        -- Higher values reduce switching frequency but increase latency for
        -- the non-active stream. Lower values may create bigger gaps between MFB
        -- packets during switching, reducing throughput (only one input port
        -- is read per cycle)
        SW_TIMEOUT_WIDTH    : natural := 4;

        -- Enable input PIPE stages for registered inputs
        -- true: Uses MVB_PIPE and MFB_PIPE components for registered inputs
        -- false: Uses simple registers (combinatorial input path)
        IN_PIPE_EN          : boolean := false;

        -- Enable output PIPE stage for registered outputs
        -- true: Uses MVB_PIPE and MFB_PIPE components for registered outputs
        -- false: Uses simple output registers
        OUT_PIPE_EN         : boolean := true;

        -- Architecture selection for internal FIFOX_MULTI component
        -- Supported values:
        -- * "SHAKEDOWN": Handshake-based FIFO with better buffering and throughput
        -- * "FULL": Standard implementation with wide MUXes
        FIFOX_MULTI_ARCH    : string := "SHAKEDOWN";

        -- Target device family for FIFO/PIPE implementation
        -- Specifies the FPGA device family for optimal resource inference
        DEVICE              : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        -- System clock
        CLK                 : in  std_logic;
        -- Synchronous reset (active high)
        RESET               : in  std_logic;

        -- =====================================================================
        -- RX INTERFACE 0 (MVB)
        -- =====================================================================

        -- MVB header bus containing up to MVB_ITEMS headers in parallel
        -- Each header is HDR_WIDTH bits wide
        -- Format: {header[MVB_ITEMS-1], ..., header[0]}
        RX0_MVB_HDR         : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        -- Payload association flags for each MVB header item
        -- Bit i = '1': Header i has associated data payload on MFB interface
        -- Bit i = '0': Header i is standalone (control-only, no MFB data)
        -- This signal establishes the header-to-payload relationship that the
        -- merger maintains throughout the merging process
        RX0_MVB_PAYLOAD     : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Header valid flags
        -- Bit i = '1': Header i (and payload if RX0_MVB_PAYLOAD(i)='1') is valid
        RX0_MVB_VLD         : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Source ready - backpressure signal from downstream receiver
        -- When '0', the receiver cannot accept data; hold all signals stable
        RX0_MVB_SRC_RDY     : in  std_logic;
        -- Destination ready - flow control to upstream sender
        -- When '1', the merger can accept a new header/payload combination
        RX0_MVB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- RX INTERFACE 0 (MFB)
        -- =====================================================================

        -- MFB data bus carrying payload data
        -- Organized as: MFB_REGIONS regions x MFB_REG_SIZE blocks x MFB_BLOCK_SIZE items x MFB_ITEM_WIDTH bits
        -- Total width: MFB_REGIONS * MFB_REG_SIZE * MFB_BLOCK_SIZE * MFB_ITEM_WIDTH bits
        RX0_MFB_DATA        : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- MFB metadata bus (optional)
        -- One metadata word per region, each MFB_META_WIDTH bits wide
        -- Always valid when MFB data is valid; passed through unchanged
        -- Tied to '0' by default when MFB_META_WIDTH = 0
        RX0_MFB_META        : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
        -- Start of Frame flags - one per region
        -- RX0_MFB_SOF(i) = '1': Region i contains the start of a new packet
        RX0_MFB_SOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- End of Frame flags - one per region
        -- RX0_MFB_EOF(i) = '1': Region i contains the end of a packet
        RX0_MFB_EOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- SOF position within each region
        -- Indicates which block within the region contains the SOF
        -- Width: MFB_REGIONS * log2(MFB_REG_SIZE) bits
        RX0_MFB_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        -- EOF position within each block
        -- Indicates which item within the block contains the EOF
        -- Width: MFB_REGIONS * log2(MFB_REG_SIZE * MFB_BLOCK_SIZE) bits
        RX0_MFB_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- Source ready - backpressure signal from downstream receiver
        RX0_MFB_SRC_RDY     : in  std_logic;
        -- Destination ready - flow control to upstream sender
        RX0_MFB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- RX INTERFACE 1 (MVB)
        -- =====================================================================

        -- MVB header bus (same format as RX0_MVB_HDR)
        RX1_MVB_HDR         : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        -- Payload association flags (same format as RX0_MVB_PAYLOAD)
        RX1_MVB_PAYLOAD     : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Header valid flags (same format as RX0_MVB_VLD)
        RX1_MVB_VLD         : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Source ready (same format as RX0_MVB_SRC_RDY)
        RX1_MVB_SRC_RDY     : in  std_logic;
        -- Destination ready (same format as RX0_MVB_DST_RDY)
        RX1_MVB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- RX INTERFACE 1 (MFB)
        -- =====================================================================

        -- MFB data bus (same format as RX0_MFB_DATA)
        RX1_MFB_DATA        : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- MFB metadata bus (same format as RX0_MFB_META)
        RX1_MFB_META        : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
        -- Start of Frame flags (same format as RX0_MFB_SOF)
        RX1_MFB_SOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- End of Frame flags (same format as RX0_MFB_EOF)
        RX1_MFB_EOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- SOF position (same format as RX0_MFB_SOF_POS)
        RX1_MFB_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        -- EOF position (same format as RX0_MFB_EOF_POS)
        RX1_MFB_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- Source ready (same format as RX0_MFB_SRC_RDY)
        RX1_MFB_SRC_RDY     : in  std_logic;
        -- Destination ready (same format as RX0_MFB_DST_RDY)
        RX1_MFB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- TX INTERFACE (MVB)
        -- =====================================================================

        -- Merged MVB header bus
        -- Contains headers from both RX0 and RX1, merged based on activity
        TX_MVB_HDR          : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        -- Payload association flags for merged output
        -- Maintains the header-to-payload relationship from the input streams
        TX_MVB_PAYLOAD      : out std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Header valid flags for merged output
        TX_MVB_VLD          : out std_logic_vector(MVB_ITEMS          -1 downto 0);
        -- Source ready - backpressure from downstream receiver
        -- Asserted when the merger has valid data to send
        TX_MVB_SRC_RDY      : out std_logic;
        -- Destination ready - flow control from downstream consumer
        -- When '1', the consumer can accept new data
        TX_MVB_DST_RDY      : in  std_logic;

        -- =====================================================================
        -- TX INTERFACE (MFB)
        -- =====================================================================

        -- Merged MFB data bus
        -- Contains payload data from both RX0 and RX1, synchronized with TX_MVB_HDR
        TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Merged MFB metadata bus
        -- Metadata from active input stream passed through unchanged
        TX_MFB_META         : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        -- Start of Frame flags for merged output
        TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- End of Frame flags for merged output
        TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- SOF position for merged output
        TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        -- EOF position for merged output
        TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- Source ready - backpressure from downstream receiver
        -- Asserted when the merger has valid MFB data to send
        TX_MFB_SRC_RDY      : out std_logic;
        -- Destination ready - flow control from downstream consumer
        TX_MFB_DST_RDY      : in  std_logic
    );
end entity;
