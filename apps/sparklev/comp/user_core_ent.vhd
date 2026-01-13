-- user_core_ent.vhd: Entity declaration of the user core to ensure consistent port names
-- Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-P-2.0

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.combo_user_const.all;

entity USER_CORE is
    generic (
        -- MI parameters: width of data signals
        MI_DATA_WIDTH : integer := 32;
        -- MI parameters: width of address signal
        MI_ADDR_WIDTH : integer := 32;

        -- DMA: number of DMA streams
        DMA_STREAMS : natural := 1;

        -- DMA: number of RX channel per DMA stream
        C2H_DMA_CHANNELS     : natural := 16;
        -- DMA: number of TX channel per DMA stream
        H2C_DMA_CHANNELS     : natural := 16;

        -- DMA: size of User Header Metadata in bits
        DMA_HDR_META_WIDTH  : natural := 12;
        -- DMA: Maximum size of a packet in bytes
        DMA_PKT_SIZE_MAX    : natural := 2**12;

        -- DMA MFB: number of regions in word
        DMA_MFB_REGIONS     : natural := 1;
        -- DMA MFB: number of blocks in region
        DMA_MFB_REGION_SIZE : natural := 8;
        -- MFB parameters: number of items in block
        DMA_MFB_BLOCK_SIZE  : natural := 8;
        -- MFB parameters: width of one item in bits
        DMA_MFB_ITEM_WIDTH  : natural := 8;

        HBM_PORTS       : natural := 32;
        HBM_DATA_WIDTH  : natural := 256;
        HBM_ADDR_WIDTH  : natural := 34;
        HBM_BURST_WIDTH : natural := 2;
        HBM_ID_WIDTH    : natural := 6;
        HBM_LEN_WIDTH   : natural := 4;
        HBM_SIZE_WIDTH  : natural := 3;
        HBM_RESP_WIDTH  : natural := 2;

        FPGA_ID_WIDTH : integer := 16;
        DEVICE        : string  := "ULTRASCALE"
    );
    port (
        -- Custom user clock and reset
        USR_CLK : in std_logic;
        -- Driven from a clock tree and deasserted when the PLL in the MMCM locks
        USR_RST : in std_logic;

        DMA_CLK : in std_logic_vector(DMA_STREAMS -1 downto 0);
        -- Driven from the PCIe IP and deasserted when initialization of the link is done 
        DMA_RST : in std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =========================================================================================
        -- Memory Interface (MI) bus
        -- =========================================================================================
        MI_CLK : in std_logic;
        -- Driven from a clock tree and deasserted when the PLL in the MMCM locks
        MI_RST : in std_logic;

        -- data from master to slave (write data)
        MI_DWR  : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- slave address
        MI_ADDR : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        -- byte enable for write data
        MI_BE   : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        -- read request
        MI_RD   : in  std_logic;
        -- write request
        MI_WR   : in  std_logic;
        -- ready of slave module
        MI_ARDY : out std_logic;
        -- data from slave to master (read data)
        MI_DRD  : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- valid of MI_DRD data signal
        MI_DRDY : out std_logic;

        -- =========================================================================================
        -- DMA Host-to-Card MFB streams (driven by DMA_CLK)
        -- =========================================================================================
        -- size of current packet in bytes 
        H2C_DMA_MFB_META_PKT_SIZE : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(DMA_PKT_SIZE_MAX+1)-1 downto 0);
        -- user metadata for DMA header
        H2C_DMA_MFB_META_HDR_META : in slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
        -- index of the DMA channel
        H2C_DMA_MFB_META_CHAN     : in slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*log2(H2C_DMA_CHANNELS)-1 downto 0);

        -- bus word with packet data 
        H2C_DMA_MFB_DATA    : in  slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
        -- Start Of Frame (SOF) flag for each MFB region
        H2C_DMA_MFB_SOF     : in  slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
        -- End Of Frame (EOF) flag for each MFB region
        H2C_DMA_MFB_EOF     : in  slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
        -- SOF position for each MFB region in MFB blocks
        H2C_DMA_MFB_SOF_POS : in  slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE))-1 downto 0);
        -- EOF position for each MFB region in MFB items
        H2C_DMA_MFB_EOF_POS : in  slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE))-1 downto 0);
        -- source ready of each MFB bus
        H2C_DMA_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS-1 downto 0);
        -- destination ready of each MFB bus
        H2C_DMA_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS-1 downto 0);

        -- =========================================================================================
        -- DMA Card-to-Host MFB streams (driven by DMA_CLK)
        -- =========================================================================================
        -- user metadata for DMA header
        C2H_DMA_MFB_META_HDR_META : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
        -- number of DMA channel
        C2H_DMA_MFB_META_CHAN     : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*log2(C2H_DMA_CHANNELS)-1 downto 0);

        -- bus word with packet data 
        C2H_DMA_MFB_DATA    : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
        -- Start Of Frame (SOF) flag for each MFB region
        C2H_DMA_MFB_SOF     : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
        -- End Of Frame (EOF) flag for each MFB region
        C2H_DMA_MFB_EOF     : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
        -- SOF position for each MFB region in MFB blocks
        C2H_DMA_MFB_SOF_POS : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE))-1 downto 0);
        -- EOF position for each MFB region in MFB items
        C2H_DMA_MFB_EOF_POS : out slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE))-1 downto 0);
        -- source ready of each MFB bus
        C2H_DMA_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS-1 downto 0);
        -- destination ready of each MFB bus
        C2H_DMA_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS-1 downto 0);

        -- =========================================================================================
        -- HBM ports (each driven by its corresponding HBM_AXI_CLK(x))
        -- =========================================================================================
        -- for customization, HBM clock and reset can be driven from user core either by DMA_CLK or
        -- USR_CLK. Be sure that some of these clocks is always connected to HBM_AXI_CLK port 
        HBM_AXI_CLK   : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_RESET : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_INIT_DONE : in std_logic;

        HBM_AXI_AWID    : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_AWADDR  : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
        HBM_AXI_AWLEN   : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
        HBM_AXI_AWSIZE  : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
        HBM_AXI_AWBURST : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
        HBM_AXI_AWVALID : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_AWREADY : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_WDATA        : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
        HBM_AXI_WSTRB        : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
        HBM_AXI_WDATA_PARITY : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
        HBM_AXI_WLAST        : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_WVALID       : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_WREADY       : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_BID    : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_BRESP  : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
        HBM_AXI_BVALID : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_BREADY : out std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_ARID    : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_ARADDR  : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
        HBM_AXI_ARLEN   : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
        HBM_AXI_ARSIZE  : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
        HBM_AXI_ARBURST : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
        HBM_AXI_ARVALID : out std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_ARREADY : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_RID          : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_RDATA        : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
        HBM_AXI_RDATA_PARITY : in  slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
        HBM_AXI_RRESP        : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
        HBM_AXI_RLAST        : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_RVALID       : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_RREADY       : out std_logic_vector(HBM_PORTS-1 downto 0);

        -- =========================================================================================
        -- Status signals
        -- =========================================================================================
        -- driven by USR_CLK
        PCIE_LINK_UP : in std_logic_vector(DMA_STREAMS -1 downto 0);
        -- driven by MI_CLK
        FPGA_ID      : in std_logic_vector(FPGA_ID_WIDTH -1 downto 0);
        -- driven by MI_CLK
        FPGA_ID_VLD  : in std_logic
    );
end entity;
