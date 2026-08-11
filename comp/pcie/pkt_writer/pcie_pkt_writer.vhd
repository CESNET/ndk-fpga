-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;


-- =========================================================================
--  Basic description (more information in README)
-- =========================================================================
--
-- This module accepts packets and the address to which it shall be written into memory.
-- It splits packets according to the PCIe MTU and memory page boundaries.
-- Then it generates an Upstream DMA header for each of these packet parts.
-- Its output interface is compatible with the PTC module.
--
-- Input packets are expected to start at the beginning of the word (Item 0).
--
-- Check out this :ref:`diagram <ppw_toplevel_diagram>` for a top-level view of the PCIe Packet Writer's architecture.
--
entity PCIE_PKT_WRITER is
    generic (
        -- ========================================================
        -- MFB parameters
        -- ========================================================

        -- For RX (user) interface.
        -- Number of MFB Regions in a word, cannot handle more than 1.
        MFB_REGIONS          : natural := 1;
        MFB_REGION_SIZE      : natural := 8;
        MFB_BLOCK_SIZE       : natural := 8;
        MFB_ITEM_WIDTH       : natural := 8;

        -- For TX (PCIe) interface.
        PCIE_MFB_REGIONS     : natural := 2;
        PCIE_MFB_REGION_SIZE : natural := 1;
        PCIE_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_MFB_ITEM_WIDTH  : natural := 32;

        -- ========================================================
        -- AXI-Stream parameters
        -- ========================================================

        -- Uses the RX_AXI input interface when true, RX_MFB when false.
        AXI_RX_DIRECT        : boolean := true;
        AXI_TDATA_WIDTH      : natural := 512;
        AXI_TUSER_WIDTH      : natural := 0; -- not supported

        -- ========================================================
        -- Other parameters
        -- ========================================================

        -- Maximum packet size (in bytes).
        PKT_MTU              : integer := 2**12;
        PCIE_MPS_WIDTH       : integer := 15;
        ADDRESS_WIDTH        : natural := 64;
        -- Size of a RAM page (in bytes).
        -- Must be a power of two.
        PAGE_SIZE            : natural := 4096;
        INSTR_FIFO_SIZE      : natural := 512;
        DEVICE               : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- Specifies the currently configured max PCIe write request (in bytes).
        -- PCIe specification allows at least 128.
        PCIE_MPS       : in  std_logic_vector(PCIE_MPS_WIDTH-1 downto 0);

        -- ========================================================
        -- RX Interface
        --   - select between MFB and AXI RX interface using AXI_RX_DIRECT
        -- ========================================================

        RX_MVB_ADDRESS : in  std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic := '0';
        RX_MFB_DST_RDY : out std_logic;

        RX_AXI_TDATA   : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP   : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER   : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0'); -- not supported
        RX_AXI_TLAST   : in  std_logic;
        RX_AXI_TVALID  : in  std_logic := '0';
        RX_AXI_TREADY  : out std_logic;

        -- ========================================================
        -- TX Interface
        -- ========================================================

        -- Contains DMA Upstream header
        TX_MVB_DATA    : out std_logic_vector(PCIE_MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(PCIE_MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(PCIE_MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(PCIE_MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1,log2(PCIE_MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1,log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PCIE_PKT_WRITER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    -- MFB constants
    constant REGION_WIDTH    : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant SOF_POS_WIDTH   : natural := max(1, log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH   : natural := max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    constant MFB_WORD_WIDTH  : natural := MFB_REGIONS*REGION_WIDTH;
    constant MFB_WORD_ITEMS  : natural := MFB_WORD_WIDTH/MFB_ITEM_WIDTH;

    -- AXI constants
    constant AXI_WORD_WIDTH  : natural := AXI_TDATA_WIDTH;
    constant AXI_WORD_ITEMS  : natural := AXI_TDATA_WIDTH/8;

    -- Number of Regions on output MFB bus.
    -- Equal to PCIE_MFB_REGIONS when input and output MFB buses have the same width.
    -- When they are not, the value contains the amount of Regions that will make the word widths equal.
    constant PCIE_REGIONS_UNRESIZED : natural := AXI_WORD_WIDTH/(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH);

    -- DMA_REQUEST_LENGTH_W extended by 2 bits (conversion from Dwords to Bytes).
    constant DMA_REQUEST_LENGTH_W_EXT : natural := DMA_REQUEST_LENGTH_W + 2;
    -- Width of instructions destined for Packet Breaker: Last flag + transaction length.
    constant PBR_INSTR_WIDTH          : natural := 1 + DMA_REQUEST_LENGTH_W_EXT;
    -- Width of instructions destined for Packet Extender: First and Last Invalid Bytes.
    constant EXT_INSTR_WIDTH          : natural := DMA_REQUEST_FIRSTIB_W + DMA_REQUEST_LASTIB_W;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal hdrgen_rx_mvb_address        : std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
    signal hdrgen_rx_mvb_length         : std_logic_vector(MFB_REGIONS*PCIE_MPS_WIDTH-1 downto 0);
    signal hdrgen_rx_mvb_meta           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrgen_rx_mvb_valid          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrgen_rx_mvb_src_rdy        : std_logic;
    signal hdrgen_rx_mvb_dst_rdy        : std_logic;

    signal hdrgen_tx_mvb_data           : std_logic_vector(MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
    signal hdrgen_tx_mvb_meta           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrgen_tx_mvb_valid          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrgen_tx_mvb_src_rdy        : std_logic;
    signal hdrgen_tx_mvb_dst_rdy        : std_logic;

    signal hdrgen_tx_mvb_data_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);
    signal hdrgen_tx_mvb_len_fixed      : u_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_LENGTH_W_EXT-1 downto 0);
    signal pbr_instr_fifo_rx_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(PBR_INSTR_WIDTH-1 downto 0);
    signal pbr_instr_fifo_rx_data       : std_logic_vector(MFB_REGIONS*PBR_INSTR_WIDTH-1 downto 0);
    signal pbr_instr_fifo_rx_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pbr_instr_fifo_rx_src_rdy    : std_logic;
    signal pbr_instr_fifo_rx_dst_rdy    : std_logic;

    signal pbr_instr_fifo_tx_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(PBR_INSTR_WIDTH-1 downto 0);
    signal pbr_instr_fifo_tx_data       : std_logic_vector(MFB_REGIONS*PBR_INSTR_WIDTH-1 downto 0);
    signal pbr_instr_fifo_tx_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pbr_instr_fifo_tx_src_rdy    : std_logic;
    signal pbr_instr_fifo_tx_dst_rdy    : std_logic;

    signal ext_instr_fifo_rx_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(EXT_INSTR_WIDTH-1 downto 0);
    signal ext_instr_fifo_rx_data       : std_logic_vector(MFB_REGIONS*EXT_INSTR_WIDTH-1 downto 0);
    signal ext_instr_fifo_rx_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ext_instr_fifo_rx_src_rdy    : std_logic;
    signal ext_instr_fifo_rx_dst_rdy    : std_logic;

    signal ext_instr_fifo_tx_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(EXT_INSTR_WIDTH-1 downto 0);
    signal ext_instr_fifo_tx_data       : std_logic_vector(MFB_REGIONS*EXT_INSTR_WIDTH-1 downto 0);
    signal ext_instr_fifo_tx_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ext_instr_fifo_tx_src_rdy    : std_logic;
    signal ext_instr_fifo_tx_dst_rdy    : std_logic;

    signal fifo_tx_mfb_data             : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal fifo_tx_mfb_sof_pos          : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal fifo_tx_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal fifo_tx_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_tx_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_tx_mfb_src_rdy          : std_logic;
    signal fifo_tx_mfb_dst_rdy          : std_logic;

    signal fifo_tx_axis_tdata           : std_logic_vector(AXI_WORD_WIDTH-1 downto 0);
    signal fifo_tx_axis_tkeep           : std_logic_vector(AXI_WORD_ITEMS-1 downto 0);
    signal fifo_tx_axis_tlast           : std_logic;
    signal fifo_tx_axis_tvalid          : std_logic;
    signal fifo_tx_axis_tready          : std_logic;

    signal pbr_rx_mvb_length_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_LENGTH_W_EXT-1 downto 0);
    signal pbr_rx_mvb_length            : std_logic_vector(MFB_REGIONS*DMA_REQUEST_LENGTH_W_EXT-1 downto 0);
    signal pbr_rx_mvb_last              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pbr_rx_mvb_valid             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pbr_rx_mvb_src_rdy           : std_logic;
    signal pbr_rx_mvb_dst_rdy           : std_logic;

    signal pbr_tx_axi_tdata             : std_logic_vector(AXI_WORD_WIDTH-1 downto 0);
    signal pbr_tx_axi_tkeep             : std_logic_vector(AXI_WORD_ITEMS-1 downto 0);
    signal pbr_tx_axi_tlast             : std_logic;
    signal pbr_tx_axi_tvalid            : std_logic;
    signal pbr_tx_axi_tready            : std_logic;

    signal ext_rx_axi_tdata             : std_logic_vector(AXI_WORD_WIDTH-1 downto 0);
    signal ext_rx_axi_tkeep             : std_logic_vector(AXI_WORD_ITEMS-1 downto 0);
    signal ext_rx_axi_tlast             : std_logic;
    signal ext_rx_axi_tvalid            : std_logic;
    signal ext_rx_axi_tready            : std_logic;
    signal ext_rx_axi_ext_len_start     : std_logic_vector(MFB_REGIONS*DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal ext_rx_axi_ext_len_end       : std_logic_vector(MFB_REGIONS*DMA_REQUEST_LASTIB_W-1 downto 0);
    signal ext_rx_axi_ext_len_start_arr : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_FIRSTIB_W-1 downto 0);
    signal ext_rx_axi_ext_len_end_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(DMA_REQUEST_LASTIB_W-1 downto 0);

    signal ext_tx_axi_tdata             : std_logic_vector(AXI_WORD_WIDTH-1 downto 0);
    signal ext_tx_axi_tkeep             : std_logic_vector(AXI_WORD_ITEMS-1 downto 0);
    signal ext_tx_axi_tlast             : std_logic;
    signal ext_tx_axi_tvalid            : std_logic;
    signal ext_tx_axi_tready            : std_logic;

    signal pcie_mfb_data                : std_logic_vector(PCIE_REGIONS_UNRESIZED*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_mfb_sof                 : std_logic_vector(PCIE_REGIONS_UNRESIZED-1 downto 0);
    signal pcie_mfb_eof                 : std_logic_vector(PCIE_REGIONS_UNRESIZED-1 downto 0);
    signal pcie_mfb_sof_pos             : std_logic_vector(PCIE_REGIONS_UNRESIZED*max(1,log2(PCIE_MFB_REGION_SIZE))-1 downto 0);
    signal pcie_mfb_eof_pos             : std_logic_vector(PCIE_REGIONS_UNRESIZED*max(1,log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE))-1 downto 0);
    signal pcie_mfb_src_rdy             : std_logic;
    signal pcie_mfb_dst_rdy             : std_logic;

begin

    assert MFB_REGIONS = 1
        report "PCIE_PKT_WRITER: unable to handle more than 1 MFB Region!"
        severity Failure;

    -- ========================================================
    --  Generate break instructions
    -- ========================================================

    instr_gen_i : entity work.PPW_INSTR_GEN
    generic map (
        MVB_ITEMS      => MFB_REGIONS,
        PKT_MTU        => PKT_MTU,
        PCIE_MPS_WIDTH => PCIE_MPS_WIDTH,
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        PAGE_SIZE      => PAGE_SIZE,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        PCIE_MPS       => PCIE_MPS,

        RX_MVB_ADDRESS => RX_MVB_ADDRESS,
        RX_MVB_LENGTH  => RX_MVB_LENGTH,
        RX_MVB_VALID   => RX_MVB_VLD,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY,

        TX_MVB_ADDRESS => hdrgen_rx_mvb_address,
        TX_MVB_LENGTH  => hdrgen_rx_mvb_length,
        TX_MVB_LAST    => hdrgen_rx_mvb_meta, -- propagate Last Instr flag through PPW_DMA_UPHDR_GEN
        TX_MVB_VALID   => hdrgen_rx_mvb_valid,
        TX_MVB_SRC_RDY => hdrgen_rx_mvb_src_rdy,
        TX_MVB_DST_RDY => hdrgen_rx_mvb_dst_rdy
    );

    -- ========================================================
    --  DMA header generator
    -- ========================================================

    dma_uphdr_gen_i : entity work.PPW_DMA_UPHDR_GEN
    generic map (
        MVB_ITEMS     => MFB_REGIONS,
        PKT_MTU       => 2**DMA_REQUEST_LENGTH_W_EXT-1,
        ADDRESS_WIDTH => ADDRESS_WIDTH,
        META_WIDTH    => 1
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MVB_ADDRESS => hdrgen_rx_mvb_address,
        RX_MVB_LENGTH  => std_logic_vector(resize(unsigned(hdrgen_rx_mvb_length),DMA_REQUEST_LENGTH_W_EXT)),
        RX_MVB_META    => hdrgen_rx_mvb_meta,
        RX_MVB_VALID   => hdrgen_rx_mvb_valid,
        RX_MVB_SRC_RDY => hdrgen_rx_mvb_src_rdy,
        RX_MVB_DST_RDY => hdrgen_rx_mvb_dst_rdy,

        TX_MVB_DATA    => hdrgen_tx_mvb_data,
        TX_MVB_META    => hdrgen_tx_mvb_meta,
        TX_MVB_VLD     => hdrgen_tx_mvb_valid,
        TX_MVB_SRC_RDY => hdrgen_tx_mvb_src_rdy,
        TX_MVB_DST_RDY => hdrgen_tx_mvb_dst_rdy
    );

    -- NOTE: hdrgen_tx_mvb_data and hdrgen_tx_mvb_meta are also used for instructions for Packet Breaker
    -- and Packet Extender. They are first stored in respecive FIFOs. The control logic only takes
    -- into account the Full signal (ext_instr_fifo_rx_dst_rdy) of the FIFO with instructions for
    -- the Packet Extender, as it is located after the Packet Breaker in the pipeline and will fill
    -- up at the same time or sooner than FIFO with instructions for Packet Breaker.

    -- NOTE2: DMA headers are assigned only to Region 0, even in the case of multiple PCIE_MFB_REGIONS.

    TX_MVB_DATA(DMA_UPHDR_WIDTH-1 downto 0) <= hdrgen_tx_mvb_data(DMA_UPHDR_WIDTH-1 downto 0);
    TX_MVB_VLD(0)                           <= hdrgen_tx_mvb_valid(0);
    TX_MVB_SRC_RDY                          <= hdrgen_tx_mvb_src_rdy and ext_instr_fifo_rx_dst_rdy;
    hdrgen_tx_mvb_dst_rdy                   <= TX_MVB_DST_RDY and ext_instr_fifo_rx_dst_rdy;

    -- ========================================================
    --  Clone DMA header data
    -- ========================================================

    -- ----------------------------------------------------
    --  DMA header data -> instructions for Packet breaker
    -- ----------------------------------------------------
    hdrgen_tx_mvb_data_arr <= slv_array_deser(hdrgen_tx_mvb_data, MFB_REGIONS);
    pbr_instr_fifo_din_g : for r in 0 to MFB_REGIONS-1 generate
        -- Fix transaction's length: convert DWORDs to bytes and subtract First Inv Bytes to
        -- accomodate for extension that happens after packet breaking.
        hdrgen_tx_mvb_len_fixed   (r) <= unsigned(hdrgen_tx_mvb_data_arr(r)(DMA_REQUEST_LENGTH)) & "00" -
                                         unsigned(hdrgen_tx_mvb_data_arr(r)(DMA_REQUEST_FIRSTIB));
        -- Last flag & transaction length in Dwords.
        pbr_instr_fifo_rx_data_arr(r) <= hdrgen_tx_mvb_meta(r) & std_logic_vector(hdrgen_tx_mvb_len_fixed(r));
    end generate;
    pbr_instr_fifo_rx_data    <= slv_array_ser(pbr_instr_fifo_rx_data_arr);
    pbr_instr_fifo_rx_vld     <= hdrgen_tx_mvb_valid;
    -- Write to pbr_instr_fifo_i at the same time as we write to ext_instr_fifo_i.
    pbr_instr_fifo_rx_src_rdy <= ext_instr_fifo_rx_src_rdy and ext_instr_fifo_rx_dst_rdy;

    pbr_instr_fifo_i : entity work.MVB_FIFOX
    generic map (
        ITEMS               => MFB_REGIONS,
        ITEM_WIDTH          => PBR_INSTR_WIDTH,
        FIFO_DEPTH          => INSTR_FIFO_SIZE,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        FAKE_FIFO           => False
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => pbr_instr_fifo_rx_data,
        RX_VLD     => pbr_instr_fifo_rx_vld,
        RX_SRC_RDY => pbr_instr_fifo_rx_src_rdy,
        RX_DST_RDY => pbr_instr_fifo_rx_dst_rdy,

        TX_DATA    => pbr_instr_fifo_tx_data,
        TX_VLD     => pbr_instr_fifo_tx_vld,
        TX_SRC_RDY => pbr_instr_fifo_tx_src_rdy,
        TX_DST_RDY => pbr_instr_fifo_tx_dst_rdy,

        STATUS     => open,
        AFULL      => open,
        AEMPTY     => open
    );

    -- NOTE: pbr_instr_fifo_i overflow should be covered by ext_instr_fifo_rx_dst_rdy of ext_instr_fifo_i
    -- as it accepts data from the same source of data (and at the same time), has the same capacity,
    -- and is located where it will fill up at the same time or sooner than pbr_instr_fifo_i. Hence
    -- pbr_instr_fifo_rx_dst_rdy is used only in the assert below.

    -- psl assert_fifo_overflow :
    --      assert never ((pbr_instr_fifo_rx_src_rdy = '1') and (pbr_instr_fifo_rx_dst_rdy = '0')) @rising_edge(CLK)
    --      report "PCIE_PKT_WRITER: pbr_instr_fifo_i overflow!";

    pbr_instr_fifo_tx_data_arr <= slv_array_deser(pbr_instr_fifo_tx_data, MFB_REGIONS);
    pbr_instr_fifo_dout_g : for r in 0 to MFB_REGIONS-1 generate
        pbr_rx_mvb_last      (r) <= pbr_instr_fifo_tx_data_arr(r)(PBR_INSTR_WIDTH-1);
        pbr_rx_mvb_length_arr(r) <= pbr_instr_fifo_tx_data_arr(r)(PBR_INSTR_WIDTH-2 downto 0);
    end generate;
    pbr_rx_mvb_length         <= slv_array_ser(pbr_rx_mvb_length_arr);
    pbr_rx_mvb_valid          <= pbr_instr_fifo_tx_vld;
    pbr_rx_mvb_src_rdy        <= pbr_instr_fifo_tx_src_rdy;
    pbr_instr_fifo_tx_dst_rdy <= pbr_rx_mvb_dst_rdy;

    -- -----------------------------------------------------
    --  DMA header data -> instructions for Packet extender
    -- -----------------------------------------------------
    ext_instr_fifo_din_g : for r in 0 to MFB_REGIONS-1 generate
        -- Last flag & transaction length in Dwords.
        ext_instr_fifo_rx_data_arr(r) <= hdrgen_tx_mvb_data_arr(r)(DMA_REQUEST_FIRSTIB) & hdrgen_tx_mvb_data_arr(r)(DMA_REQUEST_LASTIB);
    end generate;
    ext_instr_fifo_rx_data    <= slv_array_ser(ext_instr_fifo_rx_data_arr);
    ext_instr_fifo_rx_vld     <= hdrgen_tx_mvb_valid;
    ext_instr_fifo_rx_src_rdy <= hdrgen_tx_mvb_src_rdy and TX_MVB_DST_RDY;

    ext_instr_fifo_i : entity work.MVB_FIFOX
    generic map (
        ITEMS               => MFB_REGIONS,
        ITEM_WIDTH          => EXT_INSTR_WIDTH,
        FIFO_DEPTH          => INSTR_FIFO_SIZE,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        FAKE_FIFO           => False
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => ext_instr_fifo_rx_data,
        RX_VLD     => ext_instr_fifo_rx_vld,
        RX_SRC_RDY => ext_instr_fifo_rx_src_rdy,
        RX_DST_RDY => ext_instr_fifo_rx_dst_rdy,

        TX_DATA    => ext_instr_fifo_tx_data,
        TX_VLD     => ext_instr_fifo_tx_vld,
        TX_SRC_RDY => ext_instr_fifo_tx_src_rdy,
        TX_DST_RDY => ext_instr_fifo_tx_dst_rdy,

        STATUS     => open,
        AFULL      => open,
        AEMPTY     => open
    );

    ext_instr_fifo_tx_data_arr <= slv_array_deser(ext_instr_fifo_tx_data, MFB_REGIONS);
    ext_instr_fifo_dout_g : for r in 0 to MFB_REGIONS-1 generate
        ext_rx_axi_ext_len_start_arr(r) <= ext_instr_fifo_tx_data_arr(r)(EXT_INSTR_WIDTH-1 downto DMA_REQUEST_LASTIB_W);
        ext_rx_axi_ext_len_end_arr  (r) <= ext_instr_fifo_tx_data_arr(r)(DMA_REQUEST_LASTIB_W-1 downto 0);
    end generate;
    ext_rx_axi_ext_len_start <= slv_array_ser(ext_rx_axi_ext_len_start_arr);
    ext_rx_axi_ext_len_end   <= slv_array_ser(ext_rx_axi_ext_len_end_arr);

    ext_instr_fifo_tx_dst_rdy <= pbr_tx_axi_tlast and pbr_tx_axi_tvalid and ext_rx_axi_tready;

    -- ========================================================
    --  Optional MFB to AXI4Stream converter
    -- ========================================================

    mfb_fifox_g : if not AXI_RX_DIRECT generate
        mfb_fifox_i : entity work.MFB_FIFOX
        generic map (
            REGIONS             => MFB_REGIONS,
            REGION_SIZE         => MFB_REGION_SIZE,
            BLOCK_SIZE          => MFB_BLOCK_SIZE,
            ITEM_WIDTH          => MFB_ITEM_WIDTH,
            META_WIDTH          => 0,
            FIFO_DEPTH          => 512,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map (
            CLK         => CLK,
            RST         => RESET,

            RX_DATA     => RX_MFB_DATA,
            RX_META     => (others => '0'),
            RX_SOF_POS  => RX_MFB_SOF_POS,
            RX_EOF_POS  => RX_MFB_EOF_POS,
            RX_SOF      => RX_MFB_SOF,
            RX_EOF      => RX_MFB_EOF,
            RX_SRC_RDY  => RX_MFB_SRC_RDY,
            RX_DST_RDY  => RX_MFB_DST_RDY,

            TX_DATA     => fifo_tx_mfb_data,
            TX_META     => open,
            TX_SOF_POS  => fifo_tx_mfb_sof_pos,
            TX_EOF_POS  => fifo_tx_mfb_eof_pos,
            TX_SOF      => fifo_tx_mfb_sof,
            TX_EOF      => fifo_tx_mfb_eof,
            TX_SRC_RDY  => fifo_tx_mfb_src_rdy,
            TX_DST_RDY  => fifo_tx_mfb_dst_rdy,

            FIFO_STATUS => open,
            FIFO_AFULL  => open,
            FIFO_AEMPTY => open
        );

        RX_AXI_TREADY <= '0';
    else generate
        axis_fifox_i : entity work.AXIS_FIFO
        generic map (
            AXI_TDATA_WIDTH     => AXI_TDATA_WIDTH,
            AXI_TUSER_WIDTH     => AXI_TUSER_WIDTH,
            ITEMS               => 512,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FIFO_TYPE           => 1 -- FIFOX
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,

            RX_AXI_TDATA  => RX_AXI_TDATA,
            RX_AXI_TKEEP  => RX_AXI_TKEEP,
            RX_AXI_TUSER  => RX_AXI_TUSER,
            RX_AXI_TLAST  => RX_AXI_TLAST,
            RX_AXI_TVALID => RX_AXI_TVALID,
            RX_AXI_TREADY => RX_AXI_TREADY,

            TX_AXI_TDATA  => fifo_tx_axis_tdata,
            TX_AXI_TKEEP  => fifo_tx_axis_tkeep,
            TX_AXI_TUSER  => open,
            TX_AXI_TLAST  => fifo_tx_axis_tlast,
            TX_AXI_TVALID => fifo_tx_axis_tvalid,
            TX_AXI_TREADY => fifo_tx_axis_tready,

            FULL          => open,
            AFULL         => open,
            STATUS        => open,
            EMPTY         => open,
            AEMPTY        => open
        );

        RX_MFB_DST_RDY <= '0';
    end generate;

    -- ========================================================
    --  Packet breaker
    -- ========================================================

    packet_breaker_i : entity work.PPW_PKT_BREAKER
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        AXI_RX_DIRECT   => AXI_RX_DIRECT,
        AXI_TX_DIRECT   => True,
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        PKT_MTU         => 2**DMA_REQUEST_LENGTH_W_EXT-1,
        DEVICE          => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MFB_DATA    => fifo_tx_mfb_data,
        RX_MFB_SOF_POS => fifo_tx_mfb_sof_pos,
        RX_MFB_EOF_POS => fifo_tx_mfb_eof_pos,
        RX_MFB_SOF     => fifo_tx_mfb_sof,
        RX_MFB_EOF     => fifo_tx_mfb_eof,
        RX_MFB_SRC_RDY => fifo_tx_mfb_src_rdy,
        RX_MFB_DST_RDY => fifo_tx_mfb_dst_rdy,

        RX_AXI_TDATA   => fifo_tx_axis_tdata,
        RX_AXI_TKEEP   => fifo_tx_axis_tkeep,
        RX_AXI_TLAST   => fifo_tx_axis_tlast,
        RX_AXI_TVALID  => fifo_tx_axis_tvalid,
        RX_AXI_TREADY  => fifo_tx_axis_tready,

        RX_MVB_LENGTH  => pbr_rx_mvb_length,
        RX_MVB_LAST    => pbr_rx_mvb_last,
        RX_MVB_VALID   => pbr_rx_mvb_valid,
        RX_MVB_SRC_RDY => pbr_rx_mvb_src_rdy,
        RX_MVB_DST_RDY => pbr_rx_mvb_dst_rdy,

        TX_MFB_DATA    => open,
        TX_MFB_SOF_POS => open,
        TX_MFB_EOF_POS => open,
        TX_MFB_SOF     => open,
        TX_MFB_EOF     => open,
        TX_MFB_SRC_RDY => open,
        TX_MFB_DST_RDY => '1',

        TX_AXI_TDATA   => pbr_tx_axi_tdata,
        TX_AXI_TKEEP   => pbr_tx_axi_tkeep,
        TX_AXI_TLAST   => pbr_tx_axi_tlast,
        TX_AXI_TVALID  => pbr_tx_axi_tvalid,
        TX_AXI_TREADY  => pbr_tx_axi_tready
    );

    pbr_tx_axi_tready <= ext_rx_axi_tready and ext_instr_fifo_tx_src_rdy;

    -- ========================================================
    --  Packet extender
    -- ========================================================

    ext_rx_axi_tdata  <= pbr_tx_axi_tdata;
    ext_rx_axi_tkeep  <= pbr_tx_axi_tkeep;
    ext_rx_axi_tlast  <= pbr_tx_axi_tlast;
    ext_rx_axi_tvalid <= pbr_tx_axi_tvalid and ext_instr_fifo_tx_src_rdy;

    pkt_extender_i : entity work.AXIS_PACKET_EXTENDER
    generic map (
        AXI_TDATA_WIDTH => AXI_WORD_WIDTH,
        AXI_TUSER_WIDTH => 0,
        EXT_LEN_S_WIDTH => DMA_REQUEST_FIRSTIB_W,
        EXT_LEN_E_WIDTH => DMA_REQUEST_LASTIB_W
    )
    port map (
        CLK                => CLK,
        RESET              => RESET,

        RX_AXI_TDATA       => ext_rx_axi_tdata,
        RX_AXI_TUSER       => (others => '0'),
        RX_AXI_TKEEP       => ext_rx_axi_tkeep,
        RX_AXI_TLAST       => ext_rx_axi_tlast,
        RX_AXI_TVALID      => ext_rx_axi_tvalid,
        RX_AXI_TREADY      => ext_rx_axi_tready,

        RX_AXI_EXT_LEN_S   => ext_rx_axi_ext_len_start,
        RX_AXI_EXT_LEN_E   => ext_rx_axi_ext_len_end,

        TX_AXI_TDATA       => ext_tx_axi_tdata,
        TX_AXI_TUSER       => open,
        TX_AXI_TKEEP       => ext_tx_axi_tkeep,
        TX_AXI_TLAST       => ext_tx_axi_tlast,
        TX_AXI_TVALID      => ext_tx_axi_tvalid,
        TX_AXI_TREADY      => ext_tx_axi_tready
    );

    -- ========================================================
    --  AXI4Stream to MFB converter
    -- ========================================================

    -- Also does bus conversion to PCIe MFB parameters.
    -- Cannot handle different bus widths.
    axis2mfb_i : entity work.AXI2MFB
    generic map (
        USE_IN_PIPE       => False,
        USE_OUT_PIPE      => True,
        REGIONS           => PCIE_REGIONS_UNRESIZED,
        REGION_SIZE       => PCIE_MFB_REGION_SIZE,
        BLOCK_SIZE        => PCIE_MFB_BLOCK_SIZE,
        ITEM_WIDTH        => PCIE_MFB_ITEM_WIDTH,
        AXI_DATA_WIDTH    => AXI_WORD_WIDTH,
        AXI_USER_WIDTH    => 0,
        META_WIDTH        => 0,
        MFB_META_WITH_SOF => True,
        PIPE_TYPE         => "SHREG",
        DEVICE            => DEVICE
    )
    port map (
        CLK            => CLK,
        RST            => RESET,

        RX_AXI_TDATA   => ext_tx_axi_tdata,
        RX_AXI_TUSER   => (others => '0'),
        RX_AXI_TKEEP   => ext_tx_axi_tkeep,
        RX_AXI_TLAST   => ext_tx_axi_tlast,
        RX_AXI_TVALID  => ext_tx_axi_tvalid,
        RX_AXI_TREADY  => ext_tx_axi_tready,

        TX_MFB_DATA    => pcie_mfb_data,
        TX_MFB_META    => open,
        TX_MFB_SOF_POS => pcie_mfb_sof_pos,
        TX_MFB_EOF_POS => pcie_mfb_eof_pos,
        TX_MFB_SOF     => pcie_mfb_sof,
        TX_MFB_EOF     => pcie_mfb_eof,
        TX_MFB_SRC_RDY => pcie_mfb_src_rdy,
        TX_MFB_DST_RDY => pcie_mfb_dst_rdy
    );

    -- ========================================================
    --  Final bus resizing
    -- ========================================================

    -- Handles bus resizing when input and output bus widths differ.
    pcie_mfb_reconfigurator_i : entity work.MFB_RECONFIGURATOR
    generic map (
        RX_REGIONS            => PCIE_REGIONS_UNRESIZED,
        RX_REGION_SIZE        => PCIE_MFB_REGION_SIZE,
        RX_BLOCK_SIZE         => PCIE_MFB_BLOCK_SIZE,
        RX_ITEM_WIDTH         => PCIE_MFB_ITEM_WIDTH,
        TX_REGIONS            => PCIE_MFB_REGIONS,
        TX_REGION_SIZE        => PCIE_MFB_REGION_SIZE,
        TX_BLOCK_SIZE         => PCIE_MFB_BLOCK_SIZE,
        TX_ITEM_WIDTH         => PCIE_MFB_ITEM_WIDTH,
        META_WIDTH            => 0,
        META_MODE             => 0,
        FIFO_SIZE             => 32,
        FRAMES_OVER_TX_BLOCK  => 0,
        FRAMES_OVER_TX_REGION => 0,
        DEVICE                => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => pcie_mfb_data,
        RX_META    => (others => '0'),
        RX_SOF     => pcie_mfb_sof,
        RX_EOF     => pcie_mfb_eof,
        RX_SOF_POS => pcie_mfb_sof_pos,
        RX_EOF_POS => pcie_mfb_eof_pos,
        RX_SRC_RDY => pcie_mfb_src_rdy,
        RX_DST_RDY => pcie_mfb_dst_rdy,

        TX_DATA    => TX_MFB_DATA,
        TX_META    => open,
        TX_SOF     => TX_MFB_SOF,
        TX_EOF     => TX_MFB_EOF,
        TX_SOF_POS => TX_MFB_SOF_POS,
        TX_EOF_POS => TX_MFB_EOF_POS,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
