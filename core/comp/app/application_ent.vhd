-- application_ent.vhd: Entity of user application core
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;

entity APPLICATION_CORE is
generic (
    -- ETH: number of Ethernet streams from network module
    ETH_STREAMS        : natural := 1;
    -- ETH: number of possible logical Ethernet links per Ethernet stream
    ETH_CHANNELS       : natural := 1;
    -- ETH MFB: number of regions in word
    ETH_MFB_REGIONS       : natural := 1;
    -- ETH MFB: number of blocks in region
    ETH_MFB_REGION_SIZE   : natural := 8;
    -- Number of instantiated PCIe endpoints
    PCIE_ENDPOINTS     : natural := 1;
    -- DMA: number of DMA streams
    DMA_STREAMS        : natural := 1;
    -- DMA: number of RX channel per DMA stream
    DMA_RX_CHANNELS    : natural := 16;
    -- DMA: number of TX channel per DMA stream
    DMA_TX_CHANNELS    : natural := 16;
    -- DMA: size of User Header Metadata in bits
    DMA_HDR_META_WIDTH : natural := 12;
    -- DMA: Maximum size of a frame on RX DMA interfaces (in bytes)
    DMA_RX_FRAME_SIZE_MAX : natural := 2**12;
    -- DMA: Maximum size of a frame on TX DMA interfaces (in bytes)
    DMA_TX_FRAME_SIZE_MAX : natural := 2**12;
    -- DMA MFB: number of regions in word
    DMA_MFB_REGIONS       : natural := 1;
    -- DMA MFB: number of blocks in region
    DMA_MFB_REGION_SIZE   : natural := 8;
    -- MFB parameters: number of regions in word, DEPRECATED!
    MFB_REGIONS        : natural := ETH_MFB_REGIONS;
    -- MFB parameters: number of blocks in region, DEPRECATED!
    MFB_REG_SIZE       : natural := ETH_MFB_REGION_SIZE;
    -- MFB parameters: number of items in block
    MFB_BLOCK_SIZE     : natural := 8;
    -- MFB parameters: width of one item in bits
    MFB_ITEM_WIDTH     : natural := 8;
    -- HBM parameters: number of HBM ports
    HBM_PORTS          : natural := 1;
    -- HBM parameters: width of AXI address signal
    HBM_ADDR_WIDTH     : natural := 32;
    -- HBM parameters: width of AXI data signal
    HBM_DATA_WIDTH     : natural := 256;
    -- HBM parameters: width of AXI burst signal
    HBM_BURST_WIDTH    : natural := 2;
    -- HBM parameters: width of AXI ID signal
    HBM_ID_WIDTH       : natural := 6;
    -- HBM parameters: width of AXI LEN signal
    HBM_LEN_WIDTH      : natural := 4;
    -- HBM parameters: width of AXI size signal
    HBM_SIZE_WIDTH     : natural := 3;
    -- HBM parameters: width of AXI resp signal
    HBM_RESP_WIDTH     : natural := 2;
     -- HBM parameters: width of AXI prot signal
    HBM_PROT_WIDTH     : natural := 3;
     -- HBM parameters: width of AXI qos signal
    HBM_QOS_WIDTH      : natural := 4;
     -- HBM parameters: width of AXI user signal
    HBM_USER_WIDTH     : natural := 1;
    -- MEM parameters: number of external memory ports (EMIFs)
    MEM_PORTS          : natural := 1;
    -- MEM parameters: width of AVMM address signal
    MEM_ADDR_WIDTH     : natural := 27;
    -- MEM parameters: width of AVMM burst count signal
    MEM_BURST_WIDTH    : natural := 7;
    -- MEM parameters: width of AVMM data signals
    MEM_DATA_WIDTH     : natural := 512;
    -- MEM parameters: width of user refresh period
    MEM_REFR_PERIOD_WIDTH: natural := 32;
    -- MEM parameters: default refresh periods for each interface
    MEM_DEF_REFR_PERIOD: integer := 0;
    -- Freq of the AMM bus with EMIF
    AMM_FREQ_KHZ       : integer := 266660;
    -- MI parameters: width of data signals
    MI_DATA_WIDTH      : integer := 32;
    -- MI parameters: width of address signal
    MI_ADDR_WIDTH      : integer := 32;
    -- Width of FPGA ID
    FPGA_ID_WIDTH      : natural := 64;
    -- Width of reset signals
    RESET_WIDTH        : integer := 2;
    -- Name of FPGA board
    BOARD              : string;
    -- Name of FPGA device
    DEVICE             : string
);
port (
    -- =========================================================================
    -- USER CLOCK AND RESET INPUTS
    -- =========================================================================

    -- user clock input
    CLK_USER      : in  std_logic;
    -- user clock input with double frequency
    CLK_USER_X2   : in  std_logic;
    -- user clock input with triple frequency
    CLK_USER_X3   : in  std_logic;
    -- user clock input with quadruple frequency
    CLK_USER_X4   : in  std_logic;

    -- reset input synchronized with CLK_USER
    RESET_USER    : in  std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset input synchronized with CLK_USER_X2
    RESET_USER_X2 : in  std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset input synchronized with CLK_USER_X3
    RESET_USER_X3 : in  std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset input synchronized with CLK_USER_X4
    RESET_USER_X4 : in  std_logic_vector(RESET_WIDTH-1 downto 0);

    -- clock input with ethernet core frequency for each ETH stream
    CLK_ETH       : in  std_logic_vector(ETH_STREAMS-1 downto 0);
    -- reset input synchronized with CLK_ETH for each ETH stream
    RESET_ETH     : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    -- =========================================================================
    -- CLOCK AND RESET OUTPUTS (DEFINED BY APPLICATION)
    -- =========================================================================

    -- clock output for MI interconnect
    MI_CLK        : out std_logic;
    -- clock output for DMA Module
    DMA_CLK       : out std_logic;
    -- clock output for DMA Module with double frequency
    DMA_CLK_X2    : out std_logic;
    -- clock output for Application logic
    APP_CLK       : out std_logic;

    -- reset output synchronized with MI_CLK
    MI_RESET      : out std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset output synchronized with DMA_CLK
    DMA_RESET     : out std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset output synchronized with DMA_CLK_X2
    DMA_RESET_X2  : out std_logic_vector(RESET_WIDTH-1 downto 0);
    -- reset output synchronized with APP_CLK
    APP_RESET     : out std_logic_vector(RESET_WIDTH-1 downto 0);

    -- =========================================================================
    -- TIMESTAPS
    -- =========================================================================

    -- TSU clock input
    TSU_CLK    : in std_logic;
    -- reset input synchronized with TSU_CLK
    TSU_RESET  : in std_logic;
    -- Timestamp from TSU in nanoseconds format
    TSU_TS_NS  : in std_logic_vector(64-1 downto 0);
    -- Timestamp valid flag
    TSU_TS_VLD : in std_logic;

    -- =========================================================================
    -- STATUS INPUTS
    -- =========================================================================

    -- Link Up flags of each PCIe endpoints, active when PCIe EP is ready for data transfers.
    -- DMA channels are statically and evenly mapped to all PCIe EPs (clocked at APP_CLK)
    PCIE_LINK_UP            : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    -- RX Link Up flags of each Ethernet channel
    ETH_RX_LINK_UP          : in  std_logic_vector(ETH_STREAMS*ETH_CHANNELS-1 downto 0);
    -- TX PHY Ready flags of each Ethernet channel
    ETH_TX_PHY_RDY          : in  std_logic_vector(ETH_STREAMS*ETH_CHANNELS-1 downto 0);
    -- Unique identification number of the FPGA chip (clocked at MI_CLK)
    FPGA_ID                 : in  std_logic_vector(FPGA_ID_WIDTH-1 downto 0);
    FPGA_ID_VLD             : in  std_logic;
 
    -- =========================================================================
    -- RX ETHERNET STREAMS (clocked at APP_CLK)
    --
    -- MFB+MVB interface with incoming network packets
    -- Each data packet (MFB) must have an appropriate header (MVB)!
    -- =========================================================================

    -- ETH RX MVB streams: data word with MVB items (ETH RX headers see eth_hdr_pack)
    ETH_RX_MVB_DATA         : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    -- ETH RX MVB streams: valid of each MVB item
    ETH_RX_MVB_VLD          : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS-1 downto 0);
    -- ETH RX MVB streams: source ready of each MVB bus
    ETH_RX_MVB_SRC_RDY      : in  std_logic_vector(ETH_STREAMS-1 downto 0);
    -- ETH RX MVB streams: destination ready of each MVB bus
    ETH_RX_MVB_DST_RDY      : out std_logic_vector(ETH_STREAMS-1 downto 0);
    
    -- ETH RX MFB streams: data word with frames (packets)
    ETH_RX_MFB_DATA         : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- ETH RX MFB streams: Start Of Frame (SOF) flag for each MFB region
    ETH_RX_MFB_SOF          : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS-1 downto 0);
    -- ETH RX MFB streams: End Of Frame (EOF) flag for each MFB region
    ETH_RX_MFB_EOF          : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS-1 downto 0);
    -- ETH RX MFB streams: SOF position for each MFB region in MFB blocks
    ETH_RX_MFB_SOF_POS      : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE))-1 downto 0);
    -- ETH RX MFB streams: EOF position for each MFB region in MFB items
    ETH_RX_MFB_EOF_POS      : in  std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    -- ETH RX MFB streams: source ready of each MFB bus
    ETH_RX_MFB_SRC_RDY      : in  std_logic_vector(ETH_STREAMS-1 downto 0);
    -- ETH RX MFB streams: destination ready of each MFB bus
    ETH_RX_MFB_DST_RDY      : out std_logic_vector(ETH_STREAMS-1 downto 0);

    -- =========================================================================
    -- TX ETHERNET STREAMS (clocked at APP_CLK)
    --
    -- MFB interface with outgoing network packets
    -- There is packet header the meta signal in MFB bus.
    -- =========================================================================

    -- ETH TX MFB streams: data word with frames (packets)
    ETH_TX_MFB_DATA         : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- ETH TX MFB streams: header (see eth_hdr_pack) for each frame, is valid for each SOF
    ETH_TX_MFB_HDR          : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0) := (others => '0');
    -- ETH TX MFB streams: Start Of Frame (SOF) flag for each MFB region
    ETH_TX_MFB_SOF          : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS-1 downto 0);
    -- ETH TX MFB streams: End Of Frame (EOF) flag for each MFB region
    ETH_TX_MFB_EOF          : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS-1 downto 0);
    -- ETH TX MFB streams: SOF position for each MFB region in MFB blocks
    ETH_TX_MFB_SOF_POS      : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE))-1 downto 0);
    -- ETH TX MFB streams: EOF position for each MFB region in MFB items
    ETH_TX_MFB_EOF_POS      : out std_logic_vector(ETH_STREAMS* ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    -- ETH TX MFB streams: source ready of each MFB bus
    ETH_TX_MFB_SRC_RDY      : out std_logic_vector(ETH_STREAMS-1 downto 0);
    -- ETH TX MFB streams: destination ready of each MFB bus
    ETH_TX_MFB_DST_RDY      : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    -- This interface is to transmit Channel IDs and Timestamps of packets
    -- from the APP Core to the demo/testing logic in the Network Mod Core (E-Tile).
    ETH_TX_MVB_CHANNEL      : out std_logic_vector(ETH_STREAMS* MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    ETH_TX_MVB_TIMESTAMP    : out std_logic_vector(ETH_STREAMS* MFB_REGIONS*48-1 downto 0);
    ETH_TX_MVB_VLD          : out std_logic_vector(ETH_STREAMS* MFB_REGIONS-1 downto 0) := (others => '0');

    -- =========================================================================
    -- RX DMA STREAMS (clocked at APP_CLK)
    --
    -- MFB+MVB interfaces to DMA module (to software)
    -- Each data packet (MFB) must have an appropriate header (MVB)!
    -- =========================================================================

    -- DMA RX MVB streams: length of data packet in bytes
    DMA_RX_MVB_LEN           : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    -- DMA RX MVB streams: user metadata for DMA header
    DMA_RX_MVB_HDR_META      : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    -- DMA RX MVB streams: number of DMA channel
    DMA_RX_MVB_CHANNEL       : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    -- DMA RX MVB streams: discard flag (when is set, packet is discarded in DMA module)
    DMA_RX_MVB_DISCARD       : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA RX MVB streams: valid of each MVB item
    DMA_RX_MVB_VLD           : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA RX MVB streams: source ready of each MVB bus
    DMA_RX_MVB_SRC_RDY       : out std_logic_vector(DMA_STREAMS-1 downto 0);
    -- DMA RX MVB streams: destination ready of each MVB bus
    DMA_RX_MVB_DST_RDY       : in  std_logic_vector(DMA_STREAMS-1 downto 0);

    -- DMA RX MFB streams: data word with frames (packets)
    DMA_RX_MFB_DATA          : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- DMA RX MFB streams: Start Of Frame (SOF) flag for each MFB region
    DMA_RX_MFB_SOF           : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA RX MFB streams: End Of Frame (EOF) flag for each MFB region
    DMA_RX_MFB_EOF           : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA RX MFB streams: SOF position for each MFB region in MFB blocks
    DMA_RX_MFB_SOF_POS       : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    -- DMA RX MFB streams: EOF position for each MFB region in MFB items
    DMA_RX_MFB_EOF_POS       : out std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    -- DMA RX MFB streams: source ready of each MFB bus
    DMA_RX_MFB_SRC_RDY       : out std_logic_vector(DMA_STREAMS-1 downto 0);
    -- DMA RX MFB streams: destination ready of each MFB bus
    DMA_RX_MFB_DST_RDY       : in  std_logic_vector(DMA_STREAMS-1 downto 0);
 
    -- =========================================================================
    -- TX DMA STREAMS (clocked at APP_CLK)
    --
    -- MFB+MVB interface from DMA module (from software)
    -- Each data packet (MFB) must have an appropriate header (MVB)!
    -- =========================================================================

    -- DMA TX MVB streams: length of data packet in bytes
    DMA_TX_MVB_LEN          : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    -- DMA TX MVB streams: user metadata for DMA header
    DMA_TX_MVB_HDR_META     : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    -- DMA TX MVB streams: number of DMA channel
    DMA_TX_MVB_CHANNEL      : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    -- DMA TX MVB streams: valid of each MVB item
    DMA_TX_MVB_VLD          : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA TX MVB streams: source ready of each MVB bus
    DMA_TX_MVB_SRC_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);
    -- DMA TX MVB streams: destination ready of each MVB bus
    DMA_TX_MVB_DST_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);

    -- DMA TX MFB streams: data word with frames (packets)
    DMA_TX_MFB_DATA         : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- DMA TX MFB streams: Start Of Frame (SOF) flag for each MFB region
    DMA_TX_MFB_SOF          : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA TX MFB streams: End Of Frame (EOF) flag for each MFB region
    DMA_TX_MFB_EOF          : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS-1 downto 0);
    -- DMA TX MFB streams: SOF position for each MFB region in MFB blocks
    DMA_TX_MFB_SOF_POS      : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    -- DMA TX MFB streams: EOF position for each MFB region in MFB items
    DMA_TX_MFB_EOF_POS      : in  std_logic_vector(DMA_STREAMS* DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    -- DMA TX MFB streams: source ready of each MFB bus
    DMA_TX_MFB_SRC_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);
    -- DMA TX MFB streams: destination ready of each MFB bus
    DMA_TX_MFB_DST_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);
 
    -- =====================================================================
    --  Application specific signals
    -- =====================================================================

    -- Selectively pause (choke) a DMA channel(s) from Application.
    -- Can be used to avoid stopping the whole DMA Module when just a single channel is slacking behind.
    DMA_TX_USR_CHOKE_CHANS  : out std_logic_vector(DMA_STREAMS* DMA_TX_CHANNELS-1 downto 0) := (others => '0');

    -- =========================================================================
    -- HBM AXI INTERFACES (clocked at HBM_CLK)
    -- =========================================================================
    HBM_CLK                 : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_RESET               : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_INIT_DONE           : in  std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_ARADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARVALID         : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_ARREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_ARPROT          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARQOS           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_ARUSER          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0) := (others => (others => '0'));

    HBM_AXI_RDATA           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    HBM_AXI_RDATA_PARITY    : in  slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    HBM_AXI_RID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    HBM_AXI_RLAST           : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_RRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    HBM_AXI_RVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_RREADY          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

    HBM_AXI_AWADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWVALID         : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_AWREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_AWPROT          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWQOS           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_AWUSER          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0) := (others => (others => '0'));

    HBM_AXI_WDATA           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_WDATA_PARITY    : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => '0'));
    HBM_AXI_WLAST           : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_WSTRB           : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => '0'));
    HBM_AXI_WVALID          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_WREADY          : in  std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_BID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    HBM_AXI_BRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    HBM_AXI_BVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_BREADY          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

    -- =========================================================================
    -- EXTERNAL MEMORY INTERFACES (clocked at MEM_CLK)
    -- =========================================================================

    -- Clock for each memory port
    MEM_CLK                : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- Reset synchronized with MEM_CLK for each memory port
    MEM_RST                : in  std_logic_vector(MEM_PORTS-1 downto 0);

    -- MEM Avalon-MM: ready for request
    MEM_AVMM_READY         : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- MEM Avalon-MM: read request
    MEM_AVMM_READ          : out std_logic_vector(MEM_PORTS-1 downto 0);
    -- MEM Avalon-MM: write request
    MEM_AVMM_WRITE         : out std_logic_vector(MEM_PORTS-1 downto 0);
    -- MEM Avalon-MM: address of r/w request
    MEM_AVMM_ADDRESS       : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    -- MEM Avalon-MM: burst count of read/write request
    MEM_AVMM_BURSTCOUNT    : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    -- MEM Avalon-MM: write data, valid only with write request
    MEM_AVMM_WRITEDATA     : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    -- MEM Avalon-MM: read data
    MEM_AVMM_READDATA      : in  slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    -- MEM Avalon-MM: read data valid flag
    MEM_AVMM_READDATAVALID : in  std_logic_vector(MEM_PORTS-1 downto 0);

    -- MEM parameter: user refresh period
    MEM_REFR_PERIOD         : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_REFR_PERIOD_WIDTH - 1 downto 0) := (others => std_logic_vector(to_unsigned(MEM_DEF_REFR_PERIOD, MEM_REFR_PERIOD_WIDTH)));
    -- MEM parameter: user refresh request
    MEM_REFR_REQ            : out std_logic_vector(MEM_PORTS - 1 downto 0);
    -- MEM parameter: user refresh ack
    MEM_REFR_ACK            : in std_logic_vector(MEM_PORTS - 1 downto 0);

    -- EMIF local reset request
    EMIF_RST_REQ           : out std_logic_vector(MEM_PORTS-1 downto 0);
    -- EMIF local reset done flag
    EMIF_RST_DONE          : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- EMIF ECC user interupt flag
    EMIF_ECC_USR_INT       : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- EMIF calibration success flag
    EMIF_CAL_SUCCESS       : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- EMIF calibration fail flag
    EMIF_CAL_FAIL          : in  std_logic_vector(MEM_PORTS-1 downto 0);
    -- EMIF auto precharge request
    EMIF_AUTO_PRECHARGE    : out std_logic_vector(MEM_PORTS-1 downto 0);

    -- =========================================================================
    -- MI INTERFACE (clocked at MI_CLK)
    -- =========================================================================

    -- MI bus: data from master to slave (write data)
    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    -- MI bus: slave address
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    -- MI bus: byte enable
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    -- MI bus: read request
    MI_RD                   : in  std_logic;
    -- MI bus: write request
    MI_WR                   : in  std_logic;
    -- MI bus: ready of slave module
    MI_ARDY                 : out std_logic;
    -- MI bus: data from slave to master (read data)
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    -- MI bus: valid of MI_DRD data signal
    MI_DRDY                 : out std_logic
);
end entity;
