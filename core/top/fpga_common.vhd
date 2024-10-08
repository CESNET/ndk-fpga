-- fpga_common.vhd: Common top level architecture
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
use ieee.fixed_pkg.all;

use work.combo_const.all;
use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;
use work.pcie_meta_pack.all;
use work.eth_hdr_pack.all;
use work.mi_addr_space_pack.all;

entity FPGA_COMMON is
generic (
    -- System clock period in ns
    -- PCIE clock period in ns if USE_PCIE_CLK is used
    SYSCLK_PERIOD   : real    := 10.0;
    -- Settings of the MMCM
    -- Multiply factor of main clock (Xilinx: 2-64)
    PLL_MULT_F      : real    := 12.0;
    -- Division factor of main clock (Xilinx: 1-106)
    PLL_MASTER_DIV  : natural := 3;
    -- Output clock dividers (Xilinx: 1-128)
    PLL_OUT0_DIV_F  : real    := 3.0;
    PLL_OUT1_DIV    : natural := 4;
    PLL_OUT2_DIV    : natural := 6;
    PLL_OUT3_DIV    : natural := 12;

    -- Switch CLK_GEN ref clock to clk_pci, default SYSCLK
    USE_PCIE_CLK            : boolean := false; 

    -- Number of PCIe connectors present on board
    PCIE_CONS               : natural := 1;
    -- Number of PCIe lanes per connector
    PCIE_LANES              : natural := 16;
    -- Number of PCIe clocks per connector (useful for bifurcation)
    PCIE_CLKS               : natural := 1;
    -- PCI device identification (not applicable when using XCI PCIe cores)
    PCI_VENDOR_ID           : std_logic_vector(15 downto 0) := X"18EC";
    PCI_DEVICE_ID           : std_logic_vector(15 downto 0) := X"C400";
    PCI_SUBVENDOR_ID        : std_logic_vector(15 downto 0) := X"0000";
    PCI_SUBDEVICE_ID        : std_logic_vector(15 downto 0) := X"0000";
    -- Number of instantiated PCIe endpoints
    PCIE_ENDPOINTS          : natural := 1;
    -- Connected PCIe endpoint type: P_TILE, R_TILE, USP
    PCIE_ENDPOINT_TYPE      : string  := "R_TILE";
    -- Connected PCIe endpoint mode: 0 = 1x16 lanes, 1 = 2x8 lanes
    PCIE_ENDPOINT_MODE      : natural := 0;

    -- Number of instantiated DMA modules
    DMA_MODULES             : natural := 1;
    -- Total number of DMA endpoints (one or two DMA endpoints per PCIe endpoint)
    DMA_ENDPOINTS           : natural := 1;
    -- Number of DMA channels per DMA module
    DMA_RX_CHANNELS         : natural := 4;
    DMA_TX_CHANNELS         : natural := 4;
    -- DMA debug parameters
    DMA_400G_DEMO           : boolean := false;

    -- Ethernet core architecture: E_TILE, F_TILE, CMAC
    ETH_CORE_ARCH           : string := "F_TILE";
    -- Number of Ethernet ports present on board
    ETH_PORTS               : natural := 1;
    -- Speed for all Ethernet ports
    ETH_PORT_SPEED          : integer_vector(ETH_PORTS-1 downto 0) := (others => 0);
    -- Number of channels for all Ethernet ports
    ETH_PORT_CHAN           : integer_vector(ETH_PORTS-1 downto 0) := (others => 0);
    -- Number of lanes per Ethernet port
    ETH_LANES               : natural := 8;
    -- Logical indexes and polarities of Ethernet lanes
    ETH_LANE_MAP            : integer_vector(ETH_PORTS*ETH_LANES-1 downto 0) := (others => 0);
    ETH_LANE_RXPOLARITY     : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0) := (others => '0');
    ETH_LANE_TXPOLARITY     : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0) := (others => '0');
    ETH_PORT_LEDS           : natural := 2;
    QSFP_PORTS              : natural := 2;
    QSFP_I2C_PORTS          : natural := 1;
    QSFP_I2C_TRISTATE       : boolean := true;

    HBM_PORTS               : natural := 1;
    HBM_ADDR_WIDTH          : natural := 32;
    HBM_DATA_WIDTH          : natural := 256;
    HBM_BURST_WIDTH         : natural := 2;
    HBM_ID_WIDTH            : natural := 6;
    HBM_LEN_WIDTH           : natural := 4;
    HBM_SIZE_WIDTH          : natural := 3;
    HBM_RESP_WIDTH          : natural := 2;
    HBM_PROT_WIDTH          : natural := 3;
    HBM_QOS_WIDTH           : natural := 4;
    HBM_USER_WIDTH          : natural := 1;

    MEM_PORTS               : natural := 2;
    MEM_ADDR_WIDTH          : natural := 27;
    MEM_DATA_WIDTH          : natural := 512;
    MEM_BURST_WIDTH         : natural := 7;
    MEM_REFR_PERIOD_WIDTH   : natural := 32;
    MEM_DEF_REFR_PERIOD     : integer := 0;
    AMM_FREQ_KHZ            : natural := 0;
    
    STATUS_LEDS             : natural := 2;
    MISC_IN_WIDTH           : natural := 0;
    MISC_OUT_WIDTH          : natural := 0;

    DEVICE                  : string := "AGILEX";
    BOARD                   : string := "400G1"
);
port (
    SYSCLK                  : in    std_logic;
    SYSRST                  : in    std_logic;

    -- PCIe interface
    PCIE_SYSCLK_P           : in    std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
    PCIE_SYSCLK_N           : in    std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
    PCIE_SYSRST_N           : in    std_logic_vector(PCIE_CONS-1 downto 0);
    PCIE_RX_P               : in    std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
    PCIE_RX_N               : in    std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
    PCIE_TX_P               : out   std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
    PCIE_TX_N               : out   std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);

    -- ETH port interface
    ETH_REFCLK_P            : in    std_logic_vector(ETH_PORTS-1 downto 0);
    ETH_REFCLK_N            : in    std_logic_vector(ETH_PORTS-1 downto 0);
    ETH_RX_P                : in    std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    ETH_RX_N                : in    std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    ETH_TX_P                : out   std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    ETH_TX_N                : out   std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    ETH_LED_G               : out   std_logic_vector(ETH_PORTS*ETH_PORT_LEDS-1 downto 0);
    ETH_LED_R               : out   std_logic_vector(ETH_PORTS*ETH_PORT_LEDS-1 downto 0);

    -- QSFP management interface
    QSFP_I2C_SCL            : inout std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => 'Z');
    QSFP_I2C_SDA            : inout std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => 'Z');
    QSFP_I2C_SDA_I          : in    std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => '1');
    QSFP_I2C_SCL_I          : in    std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => '1');
    QSFP_I2C_SCL_O          : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SCL_OE         : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SDA_O          : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SDA_OE         : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_DIR            : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_MODSEL_N           : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_LPMODE             : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_RESET_N            : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_MODPRS_N           : in    std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_INT_N              : in    std_logic_vector(QSFP_PORTS-1 downto 0);

    -- =========================================================================
    -- HBM AXI interfaces (clocked at HBM_CLK)
    -- =========================================================================
    HBM_CLK                 : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_RESET               : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_INIT_DONE           : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

    HBM_AXI_ARADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    HBM_AXI_ARBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    HBM_AXI_ARID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    HBM_AXI_ARLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    HBM_AXI_ARSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    HBM_AXI_ARVALID         : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_ARREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_ARPROT          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0);
    HBM_AXI_ARQOS           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0);
    HBM_AXI_ARUSER          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0);

    HBM_AXI_RDATA           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_RDATA_PARITY    : in  slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => '0'));
    HBM_AXI_RID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_RLAST           : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_RRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_RVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_RREADY          : out std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_AWADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    HBM_AXI_AWBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    HBM_AXI_AWID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    HBM_AXI_AWLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    HBM_AXI_AWSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    HBM_AXI_AWVALID         : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_AWREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_AWPROT          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0);
    HBM_AXI_AWQOS           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0);
    HBM_AXI_AWUSER          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0);

    HBM_AXI_WDATA           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    HBM_AXI_WDATA_PARITY    : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    HBM_AXI_WLAST           : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_WSTRB           : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    HBM_AXI_WVALID          : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_WREADY          : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

    HBM_AXI_BID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_BRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0) := (others => (others => '0'));
    HBM_AXI_BVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
    HBM_AXI_BREADY          : out std_logic_vector(HBM_PORTS-1 downto 0);

    -- External memory interfaces (clocked at MEM_CLK)
    MEM_CLK                 : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    MEM_RST                 : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');

    MEM_AVMM_READY          : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    MEM_AVMM_READ           : out std_logic_vector(MEM_PORTS-1 downto 0);
    MEM_AVMM_WRITE          : out std_logic_vector(MEM_PORTS-1 downto 0);
    MEM_AVMM_ADDRESS        : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    MEM_AVMM_BURSTCOUNT     : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    MEM_AVMM_WRITEDATA      : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    MEM_AVMM_READDATA       : in  slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    MEM_AVMM_READDATAVALID  : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');

    MEM_REFR_PERIOD         : out slv_array_t(MEM_PORTS-1 downto 0)(MEM_REFR_PERIOD_WIDTH - 1 downto 0) := (others => std_logic_vector(to_unsigned(MEM_DEF_REFR_PERIOD, MEM_REFR_PERIOD_WIDTH)));
    MEM_REFR_REQ            : out std_logic_vector(MEM_PORTS - 1 downto 0);
    MEM_REFR_ACK            : in std_logic_vector(MEM_PORTS - 1 downto 0) := (others => '0');

    EMIF_RST_REQ            : out std_logic_vector(MEM_PORTS-1 downto 0);
    EMIF_RST_DONE           : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    EMIF_ECC_USR_INT        : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    EMIF_CAL_SUCCESS        : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    EMIF_CAL_FAIL           : in  std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    EMIF_AUTO_PRECHARGE     : out std_logic_vector(MEM_PORTS-1 downto 0);

    STATUS_LED_G            : out   std_logic_vector(STATUS_LEDS-1 downto 0);
    STATUS_LED_R            : out   std_logic_vector(STATUS_LEDS-1 downto 0);

    PCIE_CLK                : out std_logic;
    PCIE_RESET              : out std_logic;

    BOOT_MI_CLK             : out std_logic;
    BOOT_MI_RESET           : out std_logic;
    BOOT_MI_DWR             : out std_logic_vector(31 downto 0);
    BOOT_MI_ADDR            : out std_logic_vector(31 downto 0);
    BOOT_MI_RD              : out std_logic;
    BOOT_MI_WR              : out std_logic;
    BOOT_MI_BE              : out std_logic_vector(3 downto 0);
    BOOT_MI_DRD             : in  std_logic_vector(31 downto 0) := (others => '0');
    BOOT_MI_ARDY            : in  std_logic := '0';
    BOOT_MI_DRDY            : in  std_logic := '0';

    -- Misc interface, board specific
    MISC_IN                 : in    std_logic_vector(MISC_IN_WIDTH-1 downto 0) := (others => '0');
    MISC_OUT                : out   std_logic_vector(MISC_OUT_WIDTH-1 downto 0)
);
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture Declaration
-- ----------------------------------------------------------------------------

architecture FULL of FPGA_COMMON is

    constant HEARTBEAT_CNT_W     : natural := 27;
    constant CLK_COUNT           : natural := 4+ETH_PORTS;

    -- Number of ETH channels per each ETH port (QSFP)
    constant ETH_PORT_CHANNELS   : natural := ETH_PORT_CHAN(0);
    -- Number of ETH channels per each ETH stream (MFB+MVB bus)
    constant ETH_STREAM_CHANNELS : natural := tsel((ETH_STREAMS_MODE = 1), 1, ETH_PORT_CHANNELS);
    -- Number of ETH streams
    constant ETH_STREAMS         : natural := tsel((ETH_STREAMS_MODE = 1), (ETH_PORTS*ETH_PORT_CHANNELS), ETH_PORTS);
    -- Number of DMA streams
    constant DMA_STREAMS         : natural := DMA_MODULES;

    function f_get_eth_mfb_regions(P_ETH_STREAMS_MODE : natural) return natural is
    begin
        if (P_ETH_STREAMS_MODE = 1) then
            -- ETH stream = ETH channel
            if (ETH_PORT_SPEED(0) = 400) then
                return 4;
            elsif (ETH_PORT_SPEED(0) = 200) then
                return 2;
            else
                return 1;
            end if;
        elsif (ETH_CORE_ARCH = "F_TILE") then
            -- 400G cards...
            return 4;
        else
            return 1;
        end if;
    end function;

    function f_get_eth_mfb_region_size(P_ETH_STREAMS_MODE : natural) return natural is
    begin
        if (P_ETH_STREAMS_MODE = 1) then
            -- ETH stream = ETH channel
            if (ETH_PORT_SPEED(0) = 10) then
                return 1;
            elsif (ETH_PORT_SPEED(0) = 25) then
                return 2;
            elsif (ETH_PORT_SPEED(0) = 40 or ETH_PORT_SPEED(0) = 50) then
                return 4;
            else
                return 8;
            end if;
        else
            -- ETH stream = all ETH channels in ETH port
            return 8;
        end if;
    end function;

    constant ETH_MFB_REGIONS     : natural := f_get_eth_mfb_regions(ETH_STREAMS_MODE);
    constant ETH_MFB_REGION_SIZE : natural := f_get_eth_mfb_region_size(ETH_STREAMS_MODE);
    constant DMA_MFB_REGIONS     : natural := f_get_eth_mfb_regions(0);
    constant DMA_MFB_REGION_SIZE : natural := f_get_eth_mfb_region_size(0);

    constant PCIE_MPS     : natural := 256;
    constant PCIE_MRRS    : natural := 512;

    constant IS_USP_PCIE_EP : boolean := (PCIE_ENDPOINT_TYPE="USP" or PCIE_ENDPOINT_TYPE="USP_PCIE4" or PCIE_ENDPOINT_TYPE="USP_PCIE4C");

    constant RESET_WIDTH  : natural := 10;
    constant TS_MULT_SMART_DSP : boolean := (DEVICE="ULTRASCALE");
    constant TS_MULT_USE_DSP   : boolean := (DEVICE="AGILEX" or DEVICE="STRATIX10");

    constant FPGA_ID_WIDTH : natural := tsel(DEVICE="ULTRASCALE", 96, 64);

    constant MI_DATA_WIDTH      : integer := 32;
    constant MI_ADDR_WIDTH      : integer := 32;

    constant PTC_ENABLE : boolean := (DMA_TYPE = 3);

    constant DMA_DBG_CNTR_EN : boolean := DMA_DEBUG_ENABLE;

    constant HDR_META_WIDTH     : integer := 12;

    -- This function returns appropriate REGION_SIZE parameter value according to set DMA type, and
    -- PCIe configuration
    function mfb_reg_size_calc_f
        return natural is
    begin
        if (DEVICE = "ULTRASCALE" and DMA_TYPE = 4 and PCIE_ENDPOINTS = 1 and PCIE_ENDPOINT_MODE = 2) then
            return 4;
        end if;

        return 8;
    end function;

    function pcie_mfb_regions_calc_f(PCIE_DIR : string) return natural is
        variable pcie_mfb_regions : natural;
    begin
        pcie_mfb_regions := 0;

        if (PCIE_ENDPOINT_TYPE="P_TILE") then -- Gen4 mode only
            if (PCIE_ENDPOINT_MODE = 0) then -- x16
                pcie_mfb_regions := 2; --2x256b AVST
            elsif (PCIE_ENDPOINT_MODE = 1) then --x8x8
                pcie_mfb_regions := 1; --1x256b AVST
            end if;
        end if;

        if (PCIE_ENDPOINT_TYPE="R_TILE") then -- Gen5 mode only
            if (PCIE_ENDPOINT_MODE = 0) then -- x16
                pcie_mfb_regions := 4; --4x256b AVST
            elsif (PCIE_ENDPOINT_MODE = 1) then --x8x8
                pcie_mfb_regions := 2; --2x256b AVST
            end if;
        end if;

        if (PCIE_ENDPOINT_TYPE="H_TILE") then -- Gen3 mode only
            if (PCIE_ENDPOINT_MODE = 0) then -- x16
                pcie_mfb_regions := 2; --2x256b AVST
            end if;
        end if;

        if (IS_USP_PCIE_EP = True) then -- Gen3/4 mode only
            if (PCIE_ENDPOINT_MODE = 0) then -- x16
                pcie_mfb_regions := 2; --2x256b AXI
            elsif (PCIE_ENDPOINT_MODE = 1) then -- x8x8
                pcie_mfb_regions := 2; --2x256b AXI
            elsif (PCIE_ENDPOINT_MODE = 2) then --x8
                pcie_mfb_regions := 1; --1x256b AXI
            end if;
            if (PCIE_DIR="RC") then -- USP RC support up to 4 TLP in word
                pcie_mfb_regions := pcie_mfb_regions*2;
            end if;
        end if;

        -- PTC conversion to DMA streams for DMA_TYPE=3
        if ((PCIE_DIR="RQ" or PCIE_DIR="RC") and PTC_ENABLE) then
            if (PCIE_ENDPOINT_TYPE="P_TILE" and PCIE_ENDPOINT_MODE = 1) then
                -- 256b@~500MHz PCIe stream to 512b@200MHz PTC-DMA stream
                pcie_mfb_regions := pcie_mfb_regions*2;
            end if;
            if (PCIE_ENDPOINT_TYPE="R_TILE" and PCIE_ENDPOINT_MODE = 0) then --TODO
                -- 1024b@~250MHz PCIe stream to 512b@200MHz PTC-DMA stream
                pcie_mfb_regions := pcie_mfb_regions/2;
            end if;
        end if;

        return pcie_mfb_regions;
    end function;

    -- ETH/DMA MFB parameters
    constant MFB_BLOCK_SIZE   : natural := 8;  -- Number of items in block
    constant MFB_ITEM_WIDTH   : natural := 8;  -- Width of one item in bits

    -- DMA MVB RQ parameters
    constant DMA_RQ_MVB_ITEMS         : natural := pcie_mfb_regions_calc_f("RQ");
    constant DMA_RQ_MVB_ITEM_WIDTH    : natural := DMA_UPHDR_WIDTH;
    -- DMA MFB RQ parameters
    constant DMA_RQ_MFB_REGIONS       : natural := pcie_mfb_regions_calc_f("RQ");
    constant DMA_RQ_MFB_REGION_SIZE   : natural := 1;
    constant DMA_RQ_MFB_BLOCK_SIZE    : natural := 8;
    constant DMA_RQ_MFB_ITEM_WIDTH    : natural := 32;

    -- DMA MVB RC parameters
    constant DMA_RC_MVB_ITEMS       : natural := pcie_mfb_regions_calc_f("RC");
    constant DMA_RC_MVB_ITEM_WIDTH  : natural := DMA_DOWNHDR_WIDTH;
    -- DMA MFB RC parameters
    constant DMA_RC_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("RC");
    constant DMA_RC_MFB_REGION_SIZE : natural := 1;
    constant DMA_RC_MFB_BLOCK_SIZE  : natural := tsel(IS_USP_PCIE_EP,4,8);
    constant DMA_RC_MFB_ITEM_WIDTH  : natural := 32;

    constant DMA_CQ_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("CQ");
    constant DMA_CQ_MFB_REGION_SIZE : natural := DMA_RQ_MFB_REGION_SIZE;
    constant DMA_CQ_MFB_BLOCK_SIZE  : natural := DMA_RQ_MFB_BLOCK_SIZE;
    constant DMA_CQ_MFB_ITEM_WIDTH  : natural := DMA_RQ_MFB_ITEM_WIDTH;

    constant DMA_CC_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("CC");
    constant DMA_CC_MFB_REGION_SIZE : natural := DMA_RC_MFB_REGION_SIZE;
    -- this remains the same as RQ interface beacuse on straddling option enabled, the core supports
    -- only two TLPs on CC interface
    constant DMA_CC_MFB_BLOCK_SIZE  : natural := DMA_RQ_MFB_BLOCK_SIZE;
    constant DMA_CC_MFB_ITEM_WIDTH  : natural := DMA_RC_MFB_ITEM_WIDTH;

    -- DMA CrossbarX clock selection
    constant DMA_CROX_CLK_SEL    : integer := 0;
    constant DMA_USR_EQ_DMA      : boolean := false;
    constant DMA_CROX_EQ_DMA     : boolean := (DMA_CROX_CLK_SEL=1);
    constant DMA_CROX_DOUBLE_DMA : boolean := (DMA_CROX_CLK_SEL=0);

    signal heartbeat_cnt                 : unsigned(HEARTBEAT_CNT_W-1 downto 0);
    signal init_done_n                   : std_logic;
    signal pll_locked                    : std_logic;
    signal global_reset                  : std_logic;
    signal clk_vector                    : std_logic_vector(CLK_COUNT-1 downto 0);
    signal rst_vector                    : std_logic_vector(CLK_COUNT*RESET_WIDTH-1 downto 0);

    signal clk_usr_x1                    : std_logic;
    signal clk_usr_x2                    : std_logic;
    signal clk_usr_x3                    : std_logic;
    signal clk_usr_x4                    : std_logic;

    signal rst_usr_x1                    : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_usr_x2                    : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_usr_x3                    : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_usr_x4                    : std_logic_vector(RESET_WIDTH-1 downto 0);

    signal clk_pci                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal clk_eth_phy                   : std_logic_vector(ETH_PORTS-1 downto 0);
    signal clk_eth_streams               : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal clk_mi                        : std_logic;
    signal clk_dma                       : std_logic;
    signal clk_dma_x2                    : std_logic;
    signal clk_app                       : std_logic;
    
    signal rst_pci                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal rst_eth_phy                   : std_logic_vector(ETH_PORTS-1 downto 0);
    signal rst_eth_streams               : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal rst_mi                        : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_dma                       : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_dma_x2                    : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_app                       : std_logic_vector(RESET_WIDTH-1 downto 0);

    signal pcie_link_up                  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_pcie_link_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal app_pcie_link_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');

    signal xilinx_dna                    : std_logic_vector(95 downto 0);
    signal xilinx_dna_vld                : std_logic;
    signal intel_chip_id                 : std_logic_vector(63 downto 0);
    signal intel_chip_id_vld             : std_logic;
    signal fpga_id                       : std_logic_vector(FPGA_ID_WIDTH-1 downto 0);
    signal fpga_id_vld                   : std_logic := '0';
    signal pcie_fpga_id                  : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(FPGA_ID_WIDTH-1 downto 0);

    -- MI32 interface signals
    signal mi_dwr                        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_addr                       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_be                         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal mi_rd                         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_wr                         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_drd                        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_ardy                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_drdy                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    -- MI interfaces for individual components (clocked at clk_mi)
    signal mi_adc_dwr                    : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_addr                   : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_be                     : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32/8-1 downto 0);
    signal mi_adc_rd                     : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_wr                     : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_drd                    : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_ardy                   : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_drdy                   : std_logic_vector(MI_ADC_PORTS-1 downto 0);

    signal dma_mi_dwr                    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_addr                   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_be                     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal dma_mi_rd                     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_wr                     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_drd                    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_ardy                   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_drdy                   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal dma_rq_mvb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MVB_ITEMS*DMA_RQ_MVB_ITEM_WIDTH-1 downto 0);
    signal dma_rq_mvb_vld                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MVB_ITEMS-1 downto 0);
    signal dma_rq_mvb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_rq_mvb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal dma_rq_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS*DMA_RQ_MFB_REGION_SIZE*DMA_RQ_MFB_BLOCK_SIZE*DMA_RQ_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rq_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
    signal dma_rq_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS-1 downto 0);
    signal dma_rq_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS-1 downto 0);
    signal dma_rq_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS*max(1,log2(DMA_RQ_MFB_REGION_SIZE))-1 downto 0);
    signal dma_rq_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RQ_MFB_REGIONS*max(1,log2(DMA_RQ_MFB_REGION_SIZE*DMA_RQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_rq_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_rq_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal dma_rc_mvb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MVB_ITEMS*DMA_RC_MVB_ITEM_WIDTH-1 downto 0);
    signal dma_rc_mvb_vld                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MVB_ITEMS-1 downto 0);
    signal dma_rc_mvb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_rc_mvb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal dma_rc_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MFB_REGIONS*DMA_RC_MFB_REGION_SIZE*DMA_RC_MFB_BLOCK_SIZE*DMA_RC_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rc_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MFB_REGIONS-1 downto 0);
    signal dma_rc_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MFB_REGIONS-1 downto 0);
    signal dma_rc_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MFB_REGIONS*max(1,log2(DMA_RC_MFB_REGION_SIZE))-1 downto 0);
    signal dma_rc_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_RC_MFB_REGIONS*max(1,log2(DMA_RC_MFB_REGION_SIZE*DMA_RC_MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_rc_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_rc_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal dma_cq_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS*DMA_CQ_MFB_REGION_SIZE*DMA_CQ_MFB_BLOCK_SIZE*DMA_CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_cq_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
    signal dma_cq_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS-1 downto 0);
    signal dma_cq_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS-1 downto 0);
    signal dma_cq_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS*max(1,log2(DMA_CQ_MFB_REGION_SIZE))-1 downto 0);
    signal dma_cq_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CQ_MFB_REGIONS*max(1,log2(DMA_CQ_MFB_REGION_SIZE*DMA_CQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_cq_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_cq_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal dma_cc_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS*DMA_CC_MFB_REGION_SIZE*DMA_CC_MFB_BLOCK_SIZE*DMA_CC_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_cc_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS*PCIE_CC_META_WIDTH -1 downto 0);
    signal dma_cc_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS-1 downto 0);
    signal dma_cc_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS-1 downto 0);
    signal dma_cc_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS*max(1,log2(DMA_CC_MFB_REGION_SIZE))-1 downto 0);
    signal dma_cc_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(DMA_CC_MFB_REGIONS*max(1,log2(DMA_CC_MFB_REGION_SIZE*DMA_CC_MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_cc_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal dma_cc_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal app_dma_rx_mvb_len            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal app_dma_rx_mvb_hdr_meta       : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*HDR_META_WIDTH-1 downto 0);
    signal app_dma_rx_mvb_channel        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal app_dma_rx_mvb_discard        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_vld            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal app_dma_rx_mvb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal app_dma_rx_mfb_data           : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal app_dma_rx_mfb_sof            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mfb_eof            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mfb_sof_pos        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    signal app_dma_rx_mfb_eof_pos        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal app_dma_rx_mfb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal app_dma_rx_mfb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal app_dma_tx_mvb_len            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal app_dma_tx_mvb_hdr_meta       : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH-1 downto 0);
    signal app_dma_tx_mvb_channel        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    signal app_dma_tx_mvb_vld            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mvb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal app_dma_tx_mvb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal app_dma_tx_mfb_data           : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal app_dma_tx_mfb_sof            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mfb_eof            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mfb_sof_pos        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    signal app_dma_tx_mfb_eof_pos        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal app_dma_tx_mfb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal app_dma_tx_mfb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal app_dma_tx_usr_choke          : std_logic_vector(DMA_STREAMS*DMA_TX_CHANNELS-1 downto 0);

    signal eth_rx_mvb_data               : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal eth_rx_mvb_vld                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);
    signal eth_rx_mvb_src_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0) := (others => '0');
    signal eth_rx_mvb_dst_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal eth_rx_mfb_data               : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal eth_rx_mfb_sof                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);
    signal eth_rx_mfb_eof                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);
    signal eth_rx_mfb_sof_pos            : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE))-1 downto 0);
    signal eth_rx_mfb_eof_pos            : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal eth_rx_mfb_src_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0) := (others => '0');
    signal eth_rx_mfb_dst_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal eth_tx_mfb_data               : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal eth_tx_mfb_hdr                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0); --valid with sof
    signal eth_tx_mfb_sof                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);
    signal eth_tx_mfb_eof                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);
    signal eth_tx_mfb_sof_pos            : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE))-1 downto 0);
    signal eth_tx_mfb_eof_pos            : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*max(1,log2(ETH_MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal eth_tx_mfb_src_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal eth_tx_mfb_dst_rdy            : std_logic_vector(ETH_STREAMS-1 downto 0) := (others => '1');

    signal eth_tx_mvb_channel            : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    signal eth_tx_mvb_timestamp_vld      : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS*48-1 downto 0);
    signal eth_tx_mvb_vld                : std_logic_vector(ETH_STREAMS*ETH_MFB_REGIONS-1 downto 0);

    signal tsu_clk                       : std_logic;
    signal tsu_rst                       : std_logic;
    signal tsu_freq                      : std_logic_vector(31 downto 0);
    signal tsu_ns                        : std_logic_vector(63 downto 0);
    signal tsu_dv                        : std_logic;

    signal eth_rx_link_up_ser            : std_logic_vector(ETH_PORTS*ETH_PORT_CHANNELS-1 downto 0);
    signal eth_tx_phy_rdy_ser            : std_logic_vector(ETH_PORTS*ETH_PORT_CHANNELS-1 downto 0);
    signal eth_rx_link_up                : slv_array_t(ETH_PORTS-1 downto 0)(ETH_PORT_CHANNELS-1 downto 0);
    signal eth_tx_phy_rdy                : slv_array_t(ETH_PORTS-1 downto 0)(ETH_PORT_CHANNELS-1 downto 0);
    signal eth_rx_activity_ser           : std_logic_vector(ETH_PORTS*ETH_PORT_CHANNELS-1 downto 0);
    signal eth_tx_activity_ser           : std_logic_vector(ETH_PORTS*ETH_PORT_CHANNELS-1 downto 0);
    signal eth_rx_activity               : slv_array_t(ETH_PORTS-1 downto 0)(ETH_PORT_CHANNELS-1 downto 0);
    signal eth_tx_activity               : slv_array_t(ETH_PORTS-1 downto 0)(ETH_PORT_CHANNELS-1 downto 0);
    signal eth_modprs_n                  : std_logic_vector(ETH_PORTS-1 downto 0);

    signal flash_wr_data                 : std_logic_vector(64-1 downto 0);
    signal flash_wr_en                   : std_logic;
    signal flash_rd_data                 : std_logic_vector(64-1 downto 0);
    signal boot_request                  : std_logic;
    signal boot_image                    : std_logic;

    signal axi_mi_addr_s                 : std_logic_vector(8 - 1 downto 0);           
    signal axi_mi_dwr_s                  : std_logic_vector(32 - 1 downto 0);         
    signal axi_mi_wr_s                   : std_logic;        
    signal axi_mi_rd_s                   : std_logic;        
    signal axi_mi_be_s                   : std_logic_vector((32/8)-1 downto 0) := (others => '0');
    signal axi_mi_ardy_s                 : std_logic;          
    signal axi_mi_drd_s                  : std_logic_vector(32 - 1 downto 0);         
    signal axi_mi_drdy_s                 : std_logic;

    signal bmc_mi_addr_s                 : std_logic_vector(8 - 1 downto 0);           
    signal bmc_mi_dwr_s                  : std_logic_vector(32 - 1 downto 0);         
    signal bmc_mi_wr_s                   : std_logic;        
    signal bmc_mi_rd_s                   : std_logic;        
    signal bmc_mi_be_s                   : std_logic_vector((32/8)-1 downto 0) := (others => '0');
    signal bmc_mi_ardy_s                 : std_logic;          
    signal bmc_mi_drd_s                  : std_logic_vector(32 - 1 downto 0);         
    signal bmc_mi_drdy_s                 : std_logic;

    -- clk_gen reference clock
    signal ref_clk_in                    : std_logic;
    signal ref_rst_in                    : std_logic;

begin

    -- =========================================================================
    --  CLOCK AND RESET GENERATOR
    -- =========================================================================

    clk_gen_g: if USE_PCIE_CLK = true generate
        ref_clk_in <= clk_pci(0);
        ref_rst_in <= rst_pci(0);
    else generate
        ref_clk_in <= SYSCLK;
        ref_rst_in <= SYSRST;
    end generate;

    clk_gen_i : entity work.COMMON_CLK_GEN
    generic map(
        REFCLK_PERIOD   => SYSCLK_PERIOD,
        PLL_MULT_F      => PLL_MULT_F,
        PLL_MASTER_DIV  => PLL_MASTER_DIV,
        PLL_OUT0_DIV_F  => PLL_OUT0_DIV_F,
        PLL_OUT1_DIV    => PLL_OUT1_DIV,
        PLL_OUT2_DIV    => PLL_OUT2_DIV,
        PLL_OUT3_DIV    => PLL_OUT3_DIV,

        INIT_DONE_AS_RESET => TRUE,
        DEVICE             => DEVICE
    )
    port map (
        REFCLK      => ref_clk_in,
        ASYNC_RESET => ref_rst_in,
        LOCKED      => pll_locked,
        INIT_DONE_N => init_done_n,
        OUTCLK_0    => clk_usr_x4, -- 400 MHz
        OUTCLK_1    => clk_usr_x3, -- 300 MHz
        OUTCLK_2    => clk_usr_x2, -- 200 MHz
        OUTCLK_3    => clk_usr_x1  -- 100 MHz
    );

    clk_vector <= clk_eth_phy & clk_usr_x4 & clk_usr_x3 & clk_usr_x2 & clk_usr_x1;

    global_reset_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => ref_clk_in,
        ASYNC_RST  => not pll_locked,
        OUT_RST(0) => global_reset
    );

    reset_tree_gen_i : entity work.RESET_TREE_GEN
    generic map(
        CLK_COUNT    => CLK_COUNT,
        RST_REPLICAS => RESET_WIDTH
    )
    port map (
        STABLE_CLK   => ref_clk_in,
        GLOBAL_RESET => global_reset,
        CLK_VECTOR   => clk_vector,
        RST_VECTOR   => rst_vector
    );

    rst_usr_x1 <= rst_vector((0+1)*RESET_WIDTH-1 downto 0*RESET_WIDTH);
    rst_usr_x2 <= rst_vector((1+1)*RESET_WIDTH-1 downto 1*RESET_WIDTH);
    rst_usr_x3 <= rst_vector((2+1)*RESET_WIDTH-1 downto 2*RESET_WIDTH);
    rst_usr_x4 <= rst_vector((3+1)*RESET_WIDTH-1 downto 3*RESET_WIDTH);

    rst_eth_phy_g: for i in 0 to ETH_PORTS-1 generate
        rst_eth_phy(i) <= rst_vector((4+i)*RESET_WIDTH);
    end generate;

    -- usefull clocks for boot control in top-level
    PCIE_CLK    <= clk_pci(0);
    PCIE_RESET  <= rst_pci(0);
    MISC_OUT(0) <= clk_usr_x1;  -- 100 MHz
    MISC_OUT(1) <= rst_usr_x1(0);
    MISC_OUT(2) <= clk_usr_x2;  -- 200 MHz
    MISC_OUT(3) <= rst_usr_x2(0);

    eth_streams_g: for i in 0 to ETH_PORTS-1 generate
        constant ETH_PPS : natural := ETH_STREAMS/ETH_PORTS;
    begin
        eth_streams_g2: for j in 0 to ETH_PPS-1 generate
            clk_eth_streams(i*ETH_PPS+j) <= clk_eth_phy(i);
            rst_eth_streams(i*ETH_PPS+j) <= rst_vector((4+i)*RESET_WIDTH+1);
        end generate;
    end generate;

    -- =========================================================================
    --                      PCIe module instance and connections
    -- =========================================================================

    pcie_i : entity work.PCIE
    generic map (
        BAR0_BASE_ADDR      => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR      => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR      => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR      => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR      => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR      => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR   => EXP_ROM_BASE_ADDR,

        CQ_MFB_REGIONS      => DMA_CQ_MFB_REGIONS,
        CQ_MFB_REGION_SIZE  => DMA_CQ_MFB_REGION_SIZE,
        CQ_MFB_BLOCK_SIZE   => DMA_CQ_MFB_BLOCK_SIZE,
        CQ_MFB_ITEM_WIDTH   => DMA_CQ_MFB_ITEM_WIDTH,

        RC_MFB_REGIONS      => DMA_RC_MFB_REGIONS,
        RC_MFB_REGION_SIZE  => DMA_RC_MFB_REGION_SIZE,
        RC_MFB_BLOCK_SIZE   => DMA_RC_MFB_BLOCK_SIZE,
        RC_MFB_ITEM_WIDTH   => DMA_RC_MFB_ITEM_WIDTH,

        CC_MFB_REGIONS      => DMA_CC_MFB_REGIONS,
        CC_MFB_REGION_SIZE  => DMA_CC_MFB_REGION_SIZE,
        CC_MFB_BLOCK_SIZE   => DMA_CC_MFB_BLOCK_SIZE,
        CC_MFB_ITEM_WIDTH   => DMA_CC_MFB_ITEM_WIDTH,

        RQ_MFB_REGIONS      => DMA_RQ_MFB_REGIONS,
        RQ_MFB_REGION_SIZE  => DMA_RQ_MFB_REGION_SIZE,
        RQ_MFB_BLOCK_SIZE   => DMA_RQ_MFB_BLOCK_SIZE,
        RQ_MFB_ITEM_WIDTH   => DMA_RQ_MFB_ITEM_WIDTH,

        DMA_PORTS           => DMA_ENDPOINTS,
        PCIE_ENDPOINT_TYPE  => PCIE_ENDPOINT_TYPE,
        PCIE_ENDPOINT_MODE  => PCIE_ENDPOINT_MODE,
        PCIE_ENDPOINTS      => PCIE_ENDPOINTS,
        PCIE_CLKS           => PCIE_CLKS,
        PCIE_CONS           => PCIE_CONS,
        PCIE_LANES          => PCIE_LANES,

        PTC_DISABLE         => not PTC_ENABLE,
        DMA_BAR_ENABLE      => (DMA_TYPE = 4),
        XVC_ENABLE          => VIRTUAL_DEBUG_ENABLE,
        CARD_ID_WIDTH       => FPGA_ID_WIDTH,
        DEVICE              => DEVICE
    )
    port map (
        PCIE_SYSCLK_P      => PCIE_SYSCLK_P,
        PCIE_SYSCLK_N      => PCIE_SYSCLK_N,
        PCIE_SYSRST_N      => PCIE_SYSRST_N,
        INIT_DONE_N        => init_done_n,
        PCIE_RX_P          => PCIE_RX_P,
        PCIE_RX_N          => PCIE_RX_N,
        PCIE_TX_P          => PCIE_TX_P,
        PCIE_TX_N          => PCIE_TX_N,
        PCIE_USER_CLK      => clk_pci,
        PCIE_USER_RESET    => rst_pci,
        PCIE_LINK_UP       => pcie_link_up,

        CARD_ID            => pcie_fpga_id,

        DMA_CLK            => clk_dma,
        DMA_RESET          => rst_dma(0),
        
        DMA_RQ_MFB_DATA    => dma_rq_mfb_data,
        DMA_RQ_MFB_META    => dma_rq_mfb_meta,
        DMA_RQ_MFB_SOF     => dma_rq_mfb_sof,
        DMA_RQ_MFB_EOF     => dma_rq_mfb_eof,
        DMA_RQ_MFB_SOF_POS => dma_rq_mfb_sof_pos,
        DMA_RQ_MFB_EOF_POS => dma_rq_mfb_eof_pos,
        DMA_RQ_MFB_SRC_RDY => dma_rq_mfb_src_rdy,
        DMA_RQ_MFB_DST_RDY => dma_rq_mfb_dst_rdy,

        DMA_RQ_MVB_DATA    => dma_rq_mvb_data,
        DMA_RQ_MVB_VLD     => dma_rq_mvb_vld,
        DMA_RQ_MVB_SRC_RDY => dma_rq_mvb_src_rdy,
        DMA_RQ_MVB_DST_RDY => dma_rq_mvb_dst_rdy,

        DMA_RC_MFB_DATA    => dma_rc_mfb_data,
        DMA_RC_MFB_META    => open,
        DMA_RC_MFB_SOF     => dma_rc_mfb_sof,
        DMA_RC_MFB_EOF     => dma_rc_mfb_eof,
        DMA_RC_MFB_SOF_POS => dma_rc_mfb_sof_pos,
        DMA_RC_MFB_EOF_POS => dma_rc_mfb_eof_pos,
        DMA_RC_MFB_SRC_RDY => dma_rc_mfb_src_rdy,
        DMA_RC_MFB_DST_RDY => dma_rc_mfb_dst_rdy,

        DMA_RC_MVB_DATA    => dma_rc_mvb_data,
        DMA_RC_MVB_VLD     => dma_rc_mvb_vld,
        DMA_RC_MVB_SRC_RDY => dma_rc_mvb_src_rdy,
        DMA_RC_MVB_DST_RDY => dma_rc_mvb_dst_rdy,

        DMA_CQ_MFB_DATA    => dma_cq_mfb_data,
        DMA_CQ_MFB_META    => dma_cq_mfb_meta,
        DMA_CQ_MFB_SOF     => dma_cq_mfb_sof,
        DMA_CQ_MFB_EOF     => dma_cq_mfb_eof,
        DMA_CQ_MFB_SOF_POS => dma_cq_mfb_sof_pos,
        DMA_CQ_MFB_EOF_POS => dma_cq_mfb_eof_pos,
        DMA_CQ_MFB_SRC_RDY => dma_cq_mfb_src_rdy,
        DMA_CQ_MFB_DST_RDY => dma_cq_mfb_dst_rdy,

        DMA_CC_MFB_DATA    => dma_cc_mfb_data,
        DMA_CC_MFB_META    => dma_cc_mfb_meta,
        DMA_CC_MFB_SOF     => dma_cc_mfb_sof,
        DMA_CC_MFB_EOF     => dma_cc_mfb_eof,
        DMA_CC_MFB_SOF_POS => dma_cc_mfb_sof_pos,
        DMA_CC_MFB_EOF_POS => dma_cc_mfb_eof_pos,
        DMA_CC_MFB_SRC_RDY => dma_cc_mfb_src_rdy,
        DMA_CC_MFB_DST_RDY => dma_cc_mfb_dst_rdy,

        MI_CLK             => clk_mi,
        MI_RESET           => rst_mi(0),

        MI_DWR             => mi_dwr,
        MI_ADDR            => mi_addr,
        MI_BE              => mi_be,
        MI_RD              => mi_rd,
        MI_WR              => mi_wr,
        MI_DRD             => mi_drd,
        MI_ARDY            => mi_ardy,
        MI_DRDY            => mi_drdy,

        MI_DBG_DWR         => mi_adc_dwr (MI_ADC_PORT_PCI_DBG),
        MI_DBG_ADDR        => mi_adc_addr(MI_ADC_PORT_PCI_DBG),
        MI_DBG_BE          => mi_adc_be  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_RD          => mi_adc_rd  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_WR          => mi_adc_wr  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_DRD         => mi_adc_drd (MI_ADC_PORT_PCI_DBG),
        MI_DBG_ARDY        => mi_adc_ardy(MI_ADC_PORT_PCI_DBG),
        MI_DBG_DRDY        => mi_adc_drdy(MI_ADC_PORT_PCI_DBG)
    );

    cdc_pcie_up_g: for i in 0 to PCIE_ENDPOINTS-1 generate
        cdc_pcie_up_dma_i: entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG  => true,
            TWO_REG => false     
        )  
        port map(
            ACLK     => clk_pci(i),
            BCLK     => clk_dma,
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => pcie_link_up(i),                
            BDATAOUT => dma_pcie_link_up(i) 
        );

        cdc_pcie_up_app_i: entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG  => true,
            TWO_REG => false     
        )  
        port map(
            ACLK     => clk_pci(i),
            BCLK     => clk_app,
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => pcie_link_up(i),                
            BDATAOUT => app_pcie_link_up(i) 
        );

        cdc_pcie_fpga_id_i: entity work.ASYNC_OPEN_LOOP_SMD
        generic map(
            DATA_WIDTH => FPGA_ID_WIDTH
        )
        port map(
            ACLK     => clk_mi,
            BCLK     => clk_pci(i),
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => fpga_id,
            BDATAOUT => pcie_fpga_id(i)
        );
    end generate;

    -- =========================================================================
    --  MI ADDRESS DECODER
    -- =========================================================================

    mi_adc_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH    => 32,
        DATA_WIDTH    => 32,
        -- defined in mi_addr_space_pack
        PORTS         => MI_ADC_PORTS,
        --PIPE_OUT      => MI_ADC_PIPE_EN,
        --ADDR_BASES    => MI_ADC_ADDR_BASES,
        ADDR_BASE     => MI_ADC_ADDR_BASE,
        --ADDR_MASK     => get_addr_mask(MI_ADC_ADDR_BASE),
        --PORT_MAPPING  => MI_ADC_PORT_MAPPING(0),
        DEVICE        => DEVICE
    )
    port map(
        CLK        => clk_mi,
        RESET      => rst_mi(1),

        RX_DWR     => mi_dwr (0),
        RX_ADDR    => mi_addr(0),
        RX_BE      => mi_be  (0),
        RX_RD      => mi_rd  (0),
        RX_WR      => mi_wr  (0),
        RX_ARDY    => mi_ardy(0),
        RX_DRD     => mi_drd (0),
        RX_DRDY    => mi_drdy(0),

        TX_DWR     => mi_adc_dwr ,
        TX_ADDR    => mi_adc_addr,
        TX_BE      => mi_adc_be  ,
        TX_RD      => mi_adc_rd  ,
        TX_WR      => mi_adc_wr  ,
        TX_ARDY    => mi_adc_ardy,
        TX_DRD     => mi_adc_drd ,
        TX_DRDY    => mi_adc_drdy
    );

    -- boot control module is in top-level
    BOOT_MI_CLK   <= clk_mi;
    BOOT_MI_RESET <= rst_mi(1);
    BOOT_MI_DWR   <= mi_adc_dwr (MI_ADC_PORT_BOOT);
    BOOT_MI_ADDR  <= mi_adc_addr(MI_ADC_PORT_BOOT);
    BOOT_MI_BE    <= mi_adc_be  (MI_ADC_PORT_BOOT);
    BOOT_MI_RD    <= mi_adc_rd  (MI_ADC_PORT_BOOT);
    BOOT_MI_WR    <= mi_adc_wr  (MI_ADC_PORT_BOOT);
    mi_adc_ardy(MI_ADC_PORT_BOOT) <= BOOT_MI_ARDY;
    mi_adc_drd (MI_ADC_PORT_BOOT) <= BOOT_MI_DRD;
    mi_adc_drdy(MI_ADC_PORT_BOOT) <= BOOT_MI_DRDY;

    -- =========================================================================
    --  MI TEST SPACE AND SDM/SYSMON INTERFACE
    -- =========================================================================

    mi_test_space_i : entity work.MI_TEST_SPACE
    generic map (
        DEVICE  => DEVICE
    )
    port map (
        CLK     => clk_mi,
        RESET   => rst_mi(3),
        MI_DWR  => mi_adc_dwr(MI_ADC_PORT_TEST),
        MI_ADDR => mi_adc_addr(MI_ADC_PORT_TEST),
        MI_BE   => mi_adc_be(MI_ADC_PORT_TEST),
        MI_RD   => mi_adc_rd(MI_ADC_PORT_TEST),
        MI_WR   => mi_adc_wr(MI_ADC_PORT_TEST),
        MI_DRD  => mi_adc_drd(MI_ADC_PORT_TEST),
        MI_ARDY => mi_adc_ardy(MI_ADC_PORT_TEST),
        MI_DRDY => mi_adc_drdy(MI_ADC_PORT_TEST)
    );

    sdm_ctrl_i: entity work.SDM_CTRL
    Generic map (
        DATA_WIDTH => 32,
        ADDR_WIDTH => 32,
        DEVICE     => DEVICE
    )
    Port map (
        CLK     => clk_mi,
        RESET   => rst_mi(2),
        MI_DWR  => mi_adc_dwr(MI_ADC_PORT_SENSOR),
        MI_ADDR => mi_adc_addr(MI_ADC_PORT_SENSOR),
        MI_RD   => mi_adc_rd(MI_ADC_PORT_SENSOR),
        MI_WR   => mi_adc_wr(MI_ADC_PORT_SENSOR),
        MI_BE   => mi_adc_be(MI_ADC_PORT_SENSOR),
        MI_DRD  => mi_adc_drd(MI_ADC_PORT_SENSOR),
        MI_ARDY => mi_adc_ardy(MI_ADC_PORT_SENSOR),
        MI_DRDY => mi_adc_drdy(MI_ADC_PORT_SENSOR),

        CHIP_ID     => intel_chip_id,
        CHIP_ID_VLD => intel_chip_id_vld
    );

    -- =========================================================================
    -- FPGA ID LOGIC
    -- =========================================================================

    hwid_i : entity work.hwid
    generic map (
        DEVICE          => DEVICE
    )
    port map (
        CLK             => clk_mi,
        XILINX_DNA      => xilinx_dna,
        XILINX_DNA_VLD  => xilinx_dna_vld
    );

    fpga_id_usp_g: if (DEVICE = "ULTRASCALE") generate
        fpga_id     <= xilinx_dna;
        fpga_id_vld <= xilinx_dna_vld;
    end generate;

    fpga_id_intel_g: if (DEVICE = "STRATIX10" or DEVICE = "AGILEX") generate
        fpga_id     <= intel_chip_id;
        fpga_id_vld <= intel_chip_id_vld;
    end generate;

    -- =========================================================================
    --  DMA MODULE
    -- =========================================================================

    dma_i : entity work.DMA
    generic map (
        DEVICE               => DEVICE                    ,
        DMA_STREAMS          => DMA_MODULES               ,

        USR_MVB_ITEMS        => DMA_MFB_REGIONS           ,
        USR_MFB_REGIONS      => DMA_MFB_REGIONS           ,
        USR_MFB_REGION_SIZE  => DMA_MFB_REGION_SIZE       ,
        USR_MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE            ,
        USR_MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH            ,

        USR_RX_PKT_SIZE_MAX  => DMA_RX_FRAME_SIZE_MAX     ,
        USR_TX_PKT_SIZE_MAX  => DMA_TX_FRAME_SIZE_MAX     ,

        DMA_ENDPOINTS        => DMA_ENDPOINTS             ,
        PCIE_MPS             => PCIE_MPS                  ,
        PCIE_MRRS            => PCIE_MRRS                 ,
        DMA_TAG_WIDTH        => 8                         ,

        PCIE_RQ_MFB_REGIONS     => DMA_RQ_MFB_REGIONS     ,
        PCIE_RQ_MFB_REGION_SIZE => DMA_RQ_MFB_REGION_SIZE ,
        PCIE_RQ_MFB_BLOCK_SIZE  => DMA_RQ_MFB_BLOCK_SIZE  ,
        PCIE_RQ_MFB_ITEM_WIDTH  => DMA_RQ_MFB_ITEM_WIDTH  ,

        PCIE_RC_MFB_REGIONS     => DMA_RC_MFB_REGIONS     ,
        PCIE_RC_MFB_REGION_SIZE => DMA_RC_MFB_REGION_SIZE ,
        PCIE_RC_MFB_BLOCK_SIZE  => DMA_RC_MFB_BLOCK_SIZE  ,
        PCIE_RC_MFB_ITEM_WIDTH  => DMA_RC_MFB_ITEM_WIDTH  ,

        PCIE_CQ_MFB_REGIONS     => DMA_CQ_MFB_REGIONS     ,
        PCIE_CQ_MFB_REGION_SIZE => DMA_CQ_MFB_REGION_SIZE ,
        PCIE_CQ_MFB_BLOCK_SIZE  => DMA_CQ_MFB_BLOCK_SIZE  ,
        PCIE_CQ_MFB_ITEM_WIDTH  => DMA_CQ_MFB_ITEM_WIDTH  ,

        PCIE_CC_MFB_REGIONS     => DMA_CC_MFB_REGIONS     ,
        PCIE_CC_MFB_REGION_SIZE => DMA_CC_MFB_REGION_SIZE ,
        PCIE_CC_MFB_BLOCK_SIZE  => DMA_CC_MFB_BLOCK_SIZE  ,
        PCIE_CC_MFB_ITEM_WIDTH  => DMA_CC_MFB_ITEM_WIDTH  ,

        HDR_META_WIDTH       => HDR_META_WIDTH            ,

        RX_CHANNELS          => DMA_RX_CHANNELS           ,
        RX_DP_WIDTH          => DMA_RX_DATA_PTR_W         ,
        RX_HP_WIDTH          => DMA_RX_HDR_PTR_W          ,
        RX_BLOCKING_MODE     => DMA_RX_BLOCKING_MODE      ,

        TX_CHANNELS          => DMA_TX_CHANNELS           ,
        TX_SEL_CHANNELS      => minimum(8,DMA_TX_CHANNELS),
        TX_DP_WIDTH          => DMA_TX_DATA_PTR_W         ,

        RX_GEN_EN            => RX_GEN_EN                 ,
        TX_GEN_EN            => TX_GEN_EN                 ,

        DBG_CNTR_EN          => DMA_DBG_CNTR_EN           ,
        USR_EQ_DMA           => DMA_USR_EQ_DMA            ,
        CROX_EQ_DMA          => DMA_CROX_EQ_DMA           ,
        CROX_DOUBLE_DMA      => DMA_CROX_DOUBLE_DMA       ,

        GEN_LOOP_EN          => DMA_GEN_LOOP_EN           ,
        DMA_400G_DEMO        => DMA_400G_DEMO             ,

        PCIE_ENDPOINTS       => PCIE_ENDPOINTS
    )
    port map (
        DMA_CLK             => clk_dma   ,
        DMA_RESET           => rst_dma(1),

        CROX_CLK            => clk_dma_x2   ,
        CROX_RESET          => rst_dma_x2(1),

        USR_CLK             => clk_app   ,
        USR_RESET           => rst_app(1),

        MI_CLK              => clk_mi    ,
        MI_RESET            => rst_mi(4) ,

        PCIE_USR_CLK        => clk_pci,
        PCIE_USR_RESET      => rst_pci,

        RX_USR_MVB_LEN      => slv_array_downto_deser(app_dma_rx_mvb_len, DMA_STREAMS),
        RX_USR_MVB_HDR_META => slv_array_downto_deser(app_dma_rx_mvb_hdr_meta, DMA_STREAMS),
        RX_USR_MVB_CHANNEL  => slv_array_downto_deser(app_dma_rx_mvb_channel, DMA_STREAMS),
        RX_USR_MVB_DISCARD  => slv_array_downto_deser(app_dma_rx_mvb_discard, DMA_STREAMS),
        RX_USR_MVB_VLD      => slv_array_downto_deser(app_dma_rx_mvb_vld, DMA_STREAMS),
        RX_USR_MVB_SRC_RDY  => app_dma_rx_mvb_src_rdy,
        RX_USR_MVB_DST_RDY  => app_dma_rx_mvb_dst_rdy,

        RX_USR_MFB_DATA     => slv_array_downto_deser(app_dma_rx_mfb_data, DMA_STREAMS),
        RX_USR_MFB_SOF      => slv_array_downto_deser(app_dma_rx_mfb_sof, DMA_STREAMS),
        RX_USR_MFB_EOF      => slv_array_downto_deser(app_dma_rx_mfb_eof, DMA_STREAMS),
        RX_USR_MFB_SOF_POS  => slv_array_downto_deser(app_dma_rx_mfb_sof_pos, DMA_STREAMS),
        RX_USR_MFB_EOF_POS  => slv_array_downto_deser(app_dma_rx_mfb_eof_pos, DMA_STREAMS),
        RX_USR_MFB_SRC_RDY  => app_dma_rx_mfb_src_rdy,
        RX_USR_MFB_DST_RDY  => app_dma_rx_mfb_dst_rdy,

        TX_USR_MVB_LEN      => app_dma_tx_mvb_len,
        TX_USR_MVB_HDR_META => app_dma_tx_mvb_hdr_meta,
        TX_USR_MVB_CHANNEL  => app_dma_tx_mvb_channel,
        TX_USR_MVB_VLD      => app_dma_tx_mvb_vld,
        TX_USR_MVB_SRC_RDY  => app_dma_tx_mvb_src_rdy,
        TX_USR_MVB_DST_RDY  => app_dma_tx_mvb_dst_rdy,

        TX_USR_MFB_DATA     => app_dma_tx_mfb_data,
        TX_USR_MFB_SOF      => app_dma_tx_mfb_sof,
        TX_USR_MFB_EOF      => app_dma_tx_mfb_eof,
        TX_USR_MFB_SOF_POS  => app_dma_tx_mfb_sof_pos,
        TX_USR_MFB_EOF_POS  => app_dma_tx_mfb_eof_pos,
        TX_USR_MFB_SRC_RDY  => app_dma_tx_mfb_src_rdy,
        TX_USR_MFB_DST_RDY  => app_dma_tx_mfb_dst_rdy,

        TX_USR_CHOKE_CHANS  => slv_array_downto_deser(app_dma_tx_usr_choke, DMA_STREAMS),

        PCIE_RQ_MVB_DATA    => dma_rq_mvb_data,
        PCIE_RQ_MVB_VLD     => dma_rq_mvb_vld,
        PCIE_RQ_MVB_SRC_RDY => dma_rq_mvb_src_rdy,
        PCIE_RQ_MVB_DST_RDY => dma_rq_mvb_dst_rdy,

        PCIE_RQ_MFB_DATA    => dma_rq_mfb_data,
        PCIE_RQ_MFB_META    => dma_rq_mfb_meta,
        PCIE_RQ_MFB_SOF     => dma_rq_mfb_sof,
        PCIE_RQ_MFB_EOF     => dma_rq_mfb_eof,
        PCIE_RQ_MFB_SOF_POS => dma_rq_mfb_sof_pos,
        PCIE_RQ_MFB_EOF_POS => dma_rq_mfb_eof_pos,
        PCIE_RQ_MFB_SRC_RDY => dma_rq_mfb_src_rdy,
        PCIE_RQ_MFB_DST_RDY => dma_rq_mfb_dst_rdy,

        PCIE_RC_MVB_DATA    => dma_rc_mvb_data,
        PCIE_RC_MVB_VLD     => dma_rc_mvb_vld,
        PCIE_RC_MVB_SRC_RDY => dma_rc_mvb_src_rdy,
        PCIE_RC_MVB_DST_RDY => dma_rc_mvb_dst_rdy,

        PCIE_RC_MFB_DATA    => dma_rc_mfb_data,
        PCIE_RC_MFB_SOF     => dma_rc_mfb_sof,
        PCIE_RC_MFB_EOF     => dma_rc_mfb_eof,
        PCIE_RC_MFB_SOF_POS => dma_rc_mfb_sof_pos,
        PCIE_RC_MFB_EOF_POS => dma_rc_mfb_eof_pos,
        PCIE_RC_MFB_SRC_RDY => dma_rc_mfb_src_rdy,
        PCIE_RC_MFB_DST_RDY => dma_rc_mfb_dst_rdy,

        PCIE_CQ_MFB_DATA    => dma_cq_mfb_data,
        PCIE_CQ_MFB_META    => dma_cq_mfb_meta,
        PCIE_CQ_MFB_SOF     => dma_cq_mfb_sof,
        PCIE_CQ_MFB_EOF     => dma_cq_mfb_eof,
        PCIE_CQ_MFB_SOF_POS => dma_cq_mfb_sof_pos,
        PCIE_CQ_MFB_EOF_POS => dma_cq_mfb_eof_pos,
        PCIE_CQ_MFB_SRC_RDY => dma_cq_mfb_src_rdy,
        PCIE_CQ_MFB_DST_RDY => dma_cq_mfb_dst_rdy,

        PCIE_CC_MFB_DATA    => dma_cc_mfb_data,
        PCIE_CC_MFB_META    => dma_cc_mfb_meta,
        PCIE_CC_MFB_SOF     => dma_cc_mfb_sof,
        PCIE_CC_MFB_EOF     => dma_cc_mfb_eof,
        PCIE_CC_MFB_SOF_POS => dma_cc_mfb_sof_pos,
        PCIE_CC_MFB_EOF_POS => dma_cc_mfb_eof_pos,
        PCIE_CC_MFB_SRC_RDY => dma_cc_mfb_src_rdy,
        PCIE_CC_MFB_DST_RDY => dma_cc_mfb_dst_rdy,

        MI_ADDR             => dma_mi_addr,
        MI_DWR              => dma_mi_dwr,
        MI_BE               => dma_mi_be,
        MI_RD               => dma_mi_rd,
        MI_WR               => dma_mi_wr,
        MI_DRD              => dma_mi_drd,
        MI_ARDY             => dma_mi_ardy,
        MI_DRDY             => dma_mi_drdy,

        GEN_LOOP_MI_ADDR    => mi_adc_addr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DWR     => mi_adc_dwr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_BE      => mi_adc_be(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_RD      => mi_adc_rd(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_WR      => mi_adc_wr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DRD     => mi_adc_drd(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_ARDY    => mi_adc_ardy(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DRDY    => mi_adc_drdy(MI_ADC_PORT_GENLOOP)
    );

    -- MI interface connection
    dma_mi_pr : process (all)
    begin
        -- Connect directly to MTC by default
        dma_mi_dwr  <= mi_dwr;
        dma_mi_addr <= mi_addr;
        dma_mi_rd   <= mi_rd;
        dma_mi_wr   <= mi_wr;
        dma_mi_be   <= mi_be;
        mi_drd (PCIE_ENDPOINTS-1 downto 1) <= dma_mi_drd (PCIE_ENDPOINTS-1 downto 1);
        mi_ardy(PCIE_ENDPOINTS-1 downto 1) <= dma_mi_ardy(PCIE_ENDPOINTS-1 downto 1);
        mi_drdy(PCIE_ENDPOINTS-1 downto 1) <= dma_mi_drdy(PCIE_ENDPOINTS-1 downto 1);

        -- Connect to MI ADC for PCIe Endpoint 0
        dma_mi_dwr (0) <= mi_adc_dwr(MI_ADC_PORT_DMA);
        dma_mi_addr(0) <= mi_adc_addr(MI_ADC_PORT_DMA);
        dma_mi_rd  (0) <= mi_adc_rd(MI_ADC_PORT_DMA);
        dma_mi_wr  (0) <= mi_adc_wr(MI_ADC_PORT_DMA);
        dma_mi_be  (0) <= mi_adc_be(MI_ADC_PORT_DMA);
        mi_adc_drd(MI_ADC_PORT_DMA)  <= dma_mi_drd (0);
        mi_adc_ardy(MI_ADC_PORT_DMA) <= dma_mi_ardy(0);
        mi_adc_drdy(MI_ADC_PORT_DMA) <= dma_mi_drdy(0);
    end process;

    -- =========================================================================
    --  THE APPLICATION
    -- =========================================================================

    app_i : entity work.APPLICATION_CORE
    generic map (
        ETH_STREAMS           => ETH_STREAMS,
        ETH_CHANNELS          => ETH_STREAM_CHANNELS,
        ETH_MFB_REGIONS       => ETH_MFB_REGIONS,
        ETH_MFB_REGION_SIZE   => ETH_MFB_REGION_SIZE,
        PCIE_ENDPOINTS        => PCIE_ENDPOINTS,
        DMA_STREAMS           => DMA_STREAMS,
        DMA_RX_CHANNELS       => DMA_RX_CHANNELS,
        DMA_TX_CHANNELS       => DMA_TX_CHANNELS,
        DMA_HDR_META_WIDTH    => HDR_META_WIDTH,
        DMA_RX_FRAME_SIZE_MAX => DMA_RX_FRAME_SIZE_MAX,
        DMA_TX_FRAME_SIZE_MAX => DMA_TX_FRAME_SIZE_MAX,
        DMA_MFB_REGIONS       => DMA_MFB_REGIONS,
        DMA_MFB_REGION_SIZE   => DMA_MFB_REGION_SIZE,
        MFB_BLOCK_SIZE        => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH        => MFB_ITEM_WIDTH,
        HBM_PORTS             => HBM_PORTS,
        HBM_DATA_WIDTH        => HBM_DATA_WIDTH,
        HBM_ADDR_WIDTH        => HBM_ADDR_WIDTH,
        HBM_BURST_WIDTH       => HBM_BURST_WIDTH,
        HBM_ID_WIDTH          => HBM_ID_WIDTH,
        HBM_LEN_WIDTH         => HBM_LEN_WIDTH,
        HBM_SIZE_WIDTH        => HBM_SIZE_WIDTH,
        HBM_RESP_WIDTH        => HBM_RESP_WIDTH,
        HBM_PROT_WIDTH        => HBM_PROT_WIDTH,
        HBM_QOS_WIDTH         => HBM_QOS_WIDTH,
        HBM_USER_WIDTH        => HBM_USER_WIDTH,
        MEM_PORTS             => MEM_PORTS,
        MEM_ADDR_WIDTH        => MEM_ADDR_WIDTH,
        MEM_BURST_WIDTH       => MEM_BURST_WIDTH,
        MEM_DATA_WIDTH        => MEM_DATA_WIDTH,
        MEM_REFR_PERIOD_WIDTH => MEM_REFR_PERIOD_WIDTH,
        MEM_DEF_REFR_PERIOD   => MEM_DEF_REFR_PERIOD,
        AMM_FREQ_KHZ          => AMM_FREQ_KHZ,
        MI_DATA_WIDTH         => MI_DATA_WIDTH,
        MI_ADDR_WIDTH         => MI_ADDR_WIDTH,
        FPGA_ID_WIDTH         => FPGA_ID_WIDTH,
        RESET_WIDTH           => RESET_WIDTH,
        BOARD                 => BOARD,
        DEVICE                => DEVICE
    )
    port map (
        CLK_USER           => clk_usr_x1,
        CLK_USER_X2        => clk_usr_x2,
        CLK_USER_X3        => clk_usr_x3,
        CLK_USER_X4        => clk_usr_x4,
    
        RESET_USER         => rst_usr_x1,
        RESET_USER_X2      => rst_usr_x2,
        RESET_USER_X3      => rst_usr_x3,
        RESET_USER_X4      => rst_usr_x4,

        CLK_ETH            => clk_eth_streams,
        RESET_ETH          => rst_eth_streams,

        MI_CLK             => clk_mi,
        DMA_CLK            => clk_dma,
        DMA_CLK_X2         => clk_dma_x2,
        APP_CLK            => clk_app,

        MI_RESET           => rst_mi,
        DMA_RESET          => rst_dma,
        DMA_RESET_X2       => rst_dma_x2,
        APP_RESET          => rst_app,

        TSU_CLK            => tsu_clk,
        TSU_RESET          => tsu_rst,
        TSU_TS_NS          => tsu_ns,
        TSU_TS_VLD         => tsu_dv,

        PCIE_LINK_UP       => app_pcie_link_up,
        ETH_RX_LINK_UP     => eth_rx_link_up_ser,
        ETH_TX_PHY_RDY     => eth_tx_phy_rdy_ser,
        FPGA_ID            => fpga_id,
        FPGA_ID_VLD        => fpga_id_vld,

        ETH_RX_MVB_DATA    => eth_rx_mvb_data,
        ETH_RX_MVB_VLD     => eth_rx_mvb_vld,
        ETH_RX_MVB_SRC_RDY => eth_rx_mvb_src_rdy,
        ETH_RX_MVB_DST_RDY => eth_rx_mvb_dst_rdy,

        ETH_RX_MFB_DATA    => eth_rx_mfb_data,
        ETH_RX_MFB_SOF     => eth_rx_mfb_sof,
        ETH_RX_MFB_EOF     => eth_rx_mfb_eof,
        ETH_RX_MFB_SOF_POS => eth_rx_mfb_sof_pos,
        ETH_RX_MFB_EOF_POS => eth_rx_mfb_eof_pos,
        ETH_RX_MFB_SRC_RDY => eth_rx_mfb_src_rdy,
        ETH_RX_MFB_DST_RDY => eth_rx_mfb_dst_rdy,

        ETH_TX_MFB_DATA    => eth_tx_mfb_data,
        ETH_TX_MFB_HDR     => eth_tx_mfb_hdr,
        ETH_TX_MFB_SOF     => eth_tx_mfb_sof,
        ETH_TX_MFB_EOF     => eth_tx_mfb_eof,
        ETH_TX_MFB_SOF_POS => eth_tx_mfb_sof_pos,
        ETH_TX_MFB_EOF_POS => eth_tx_mfb_eof_pos,
        ETH_TX_MFB_SRC_RDY => eth_tx_mfb_src_rdy,
        ETH_TX_MFB_DST_RDY => eth_tx_mfb_dst_rdy,

        ETH_TX_MVB_CHANNEL   => eth_tx_mvb_channel,
        ETH_TX_MVB_TIMESTAMP => eth_tx_mvb_timestamp_vld,
        ETH_TX_MVB_VLD       => eth_tx_mvb_vld,

        DMA_RX_MVB_LEN      => app_dma_rx_mvb_len,
        DMA_RX_MVB_HDR_META => app_dma_rx_mvb_hdr_meta,
        DMA_RX_MVB_CHANNEL  => app_dma_rx_mvb_channel,
        DMA_RX_MVB_DISCARD  => app_dma_rx_mvb_discard,
        DMA_RX_MVB_VLD      => app_dma_rx_mvb_vld,
        DMA_RX_MVB_SRC_RDY  => app_dma_rx_mvb_src_rdy,
        DMA_RX_MVB_DST_RDY  => app_dma_rx_mvb_dst_rdy,

        DMA_RX_MFB_DATA     => app_dma_rx_mfb_data,
        DMA_RX_MFB_SOF      => app_dma_rx_mfb_sof,
        DMA_RX_MFB_EOF      => app_dma_rx_mfb_eof,
        DMA_RX_MFB_SOF_POS  => app_dma_rx_mfb_sof_pos,
        DMA_RX_MFB_EOF_POS  => app_dma_rx_mfb_eof_pos,
        DMA_RX_MFB_SRC_RDY  => app_dma_rx_mfb_src_rdy,
        DMA_RX_MFB_DST_RDY  => app_dma_rx_mfb_dst_rdy,

        DMA_TX_MVB_LEN      => slv_array_ser(app_dma_tx_mvb_len),
        DMA_TX_MVB_HDR_META => slv_array_ser(app_dma_tx_mvb_hdr_meta),
        DMA_TX_MVB_CHANNEL  => slv_array_ser(app_dma_tx_mvb_channel),
        DMA_TX_MVB_VLD      => slv_array_ser(app_dma_tx_mvb_vld),
        DMA_TX_MVB_SRC_RDY  => app_dma_tx_mvb_src_rdy,
        DMA_TX_MVB_DST_RDY  => app_dma_tx_mvb_dst_rdy,

        DMA_TX_MFB_DATA     => slv_array_ser(app_dma_tx_mfb_data),
        DMA_TX_MFB_SOF      => slv_array_ser(app_dma_tx_mfb_sof),
        DMA_TX_MFB_EOF      => slv_array_ser(app_dma_tx_mfb_eof),
        DMA_TX_MFB_SOF_POS  => slv_array_ser(app_dma_tx_mfb_sof_pos),
        DMA_TX_MFB_EOF_POS  => slv_array_ser(app_dma_tx_mfb_eof_pos),
        DMA_TX_MFB_SRC_RDY  => app_dma_tx_mfb_src_rdy,
        DMA_TX_MFB_DST_RDY  => app_dma_tx_mfb_dst_rdy,

        DMA_TX_USR_CHOKE_CHANS => app_dma_tx_usr_choke,

        HBM_CLK              => HBM_CLK,
        HBM_RESET            => HBM_RESET,
        HBM_INIT_DONE        => HBM_INIT_DONE,

        HBM_AXI_ARADDR       => HBM_AXI_ARADDR,
        HBM_AXI_ARBURST      => HBM_AXI_ARBURST,
        HBM_AXI_ARID         => HBM_AXI_ARID,
        HBM_AXI_ARLEN        => HBM_AXI_ARLEN,
        HBM_AXI_ARSIZE       => HBM_AXI_ARSIZE,
        HBM_AXI_ARVALID      => HBM_AXI_ARVALID,
        HBM_AXI_ARREADY      => HBM_AXI_ARREADY,
        HBM_AXI_ARPROT       => HBM_AXI_ARPROT,
        HBM_AXI_ARQOS        => HBM_AXI_ARQOS,
        HBM_AXI_ARUSER       => HBM_AXI_ARUSER,

        HBM_AXI_RDATA        => HBM_AXI_RDATA,
        HBM_AXI_RDATA_PARITY => HBM_AXI_RDATA_PARITY,
        HBM_AXI_RID          => HBM_AXI_RID,
        HBM_AXI_RLAST        => HBM_AXI_RLAST,
        HBM_AXI_RRESP        => HBM_AXI_RRESP,
        HBM_AXI_RVALID       => HBM_AXI_RVALID,
        HBM_AXI_RREADY       => HBM_AXI_RREADY,

        HBM_AXI_AWADDR       => HBM_AXI_AWADDR,
        HBM_AXI_AWBURST      => HBM_AXI_AWBURST,
        HBM_AXI_AWID         => HBM_AXI_AWID,
        HBM_AXI_AWLEN        => HBM_AXI_AWLEN,
        HBM_AXI_AWSIZE       => HBM_AXI_AWSIZE,
        HBM_AXI_AWVALID      => HBM_AXI_AWVALID,
        HBM_AXI_AWREADY      => HBM_AXI_AWREADY,
        HBM_AXI_AWPROT       => HBM_AXI_AWPROT,
        HBM_AXI_AWQOS        => HBM_AXI_AWQOS,
        HBM_AXI_AWUSER       => HBM_AXI_AWUSER,
        
        HBM_AXI_WDATA        => HBM_AXI_WDATA,
        HBM_AXI_WDATA_PARITY => HBM_AXI_WDATA_PARITY,
        HBM_AXI_WLAST        => HBM_AXI_WLAST,
        HBM_AXI_WSTRB        => HBM_AXI_WSTRB,
        HBM_AXI_WVALID       => HBM_AXI_WVALID,
        HBM_AXI_WREADY       => HBM_AXI_WREADY,

        HBM_AXI_BID          => HBM_AXI_BID,
        HBM_AXI_BRESP        => HBM_AXI_BRESP,
        HBM_AXI_BVALID       => HBM_AXI_BVALID,
        HBM_AXI_BREADY       => HBM_AXI_BREADY,

        MEM_CLK                => MEM_CLK,
        MEM_RST                => MEM_RST,
                               
        MEM_AVMM_READY         => MEM_AVMM_READY,
        MEM_AVMM_READ          => MEM_AVMM_READ,
        MEM_AVMM_WRITE         => MEM_AVMM_WRITE,
        MEM_AVMM_ADDRESS       => MEM_AVMM_ADDRESS,
        MEM_AVMM_BURSTCOUNT    => MEM_AVMM_BURSTCOUNT,
        MEM_AVMM_WRITEDATA     => MEM_AVMM_WRITEDATA,
        MEM_AVMM_READDATA      => MEM_AVMM_READDATA,
        MEM_AVMM_READDATAVALID => MEM_AVMM_READDATAVALID,

        MEM_REFR_PERIOD        => MEM_REFR_PERIOD,
        MEM_REFR_REQ           => MEM_REFR_REQ,
        MEM_REFR_ACK           => MEM_REFR_ACK,
    
        EMIF_RST_REQ           => EMIF_RST_REQ,
        EMIF_RST_DONE          => EMIF_RST_DONE,
        EMIF_ECC_USR_INT       => EMIF_ECC_USR_INT,
        EMIF_CAL_SUCCESS       => EMIF_CAL_SUCCESS,
        EMIF_CAL_FAIL          => EMIF_CAL_FAIL,
        EMIF_AUTO_PRECHARGE    => EMIF_AUTO_PRECHARGE,

        MI_DWR             => mi_adc_dwr(MI_ADC_PORT_USERAPP),
        MI_ADDR            => mi_adc_addr(MI_ADC_PORT_USERAPP),
        MI_BE              => mi_adc_be(MI_ADC_PORT_USERAPP),
        MI_RD              => mi_adc_rd(MI_ADC_PORT_USERAPP),
        MI_WR              => mi_adc_wr(MI_ADC_PORT_USERAPP),
        MI_DRD             => mi_adc_drd(MI_ADC_PORT_USERAPP),
        MI_ARDY            => mi_adc_ardy(MI_ADC_PORT_USERAPP),
        MI_DRDY            => mi_adc_drdy(MI_ADC_PORT_USERAPP)
    );

    -- =========================================================================
    --  NETWORK MODULE
    -- =========================================================================

    network_mod_i : entity work.NETWORK_MOD
    generic map (
        ETH_CORE_ARCH     => ETH_CORE_ARCH  ,
        ETH_PORTS         => ETH_PORTS      ,
        ETH_STREAMS       => ETH_STREAMS    ,
        ETH_PORT_SPEED    => ETH_PORT_SPEED ,
        ETH_PORT_CHAN     => ETH_PORT_CHAN  ,
        ETH_PORT_RX_MTU   => ETH_PORT_RX_MTU,
        ETH_PORT_TX_MTU   => ETH_PORT_TX_MTU,
        ETH_MAC_BYPASS    => ETH_MAC_BYPASS ,
        LANES             => ETH_LANES      ,
        QSFP_PORTS        => QSFP_PORTS     ,
        QSFP_I2C_PORTS    => QSFP_I2C_PORTS ,
        QSFP_I2C_TRISTATE => QSFP_I2C_TRISTATE,

        REGIONS           => ETH_MFB_REGIONS,
        REGION_SIZE       => ETH_MFB_REGION_SIZE,
        BLOCK_SIZE        => MFB_BLOCK_SIZE ,
        ITEM_WIDTH        => MFB_ITEM_WIDTH ,

        MI_DATA_WIDTH     => 32             ,
        MI_ADDR_WIDTH     => 32             ,

        MI_DATA_WIDTH_PHY => 32             ,
        MI_ADDR_WIDTH_PHY => 32             ,

        TS_DEMO_EN        => TS_DEMO_EN     ,
        TX_DMA_CHANNELS   => DMA_TX_CHANNELS,

        LANE_RX_POLARITY  => ETH_LANE_RXPOLARITY,
        LANE_TX_POLARITY  => ETH_LANE_TXPOLARITY,
        RESET_WIDTH       => 1              ,
        DEVICE            => DEVICE         ,
        BOARD             => BOARD          ,

        EHIP_PORT_TYPE    => EHIP_PORT_TYPE
    )
    port map (
        CLK_USER        => clk_app,
        CLK_ETH         => clk_eth_phy,
        RESET_USER(0)   => rst_app(2),
        RESET_ETH       => rst_eth_phy,

        ETH_REFCLK_P    => ETH_REFCLK_P,
        ETH_REFCLK_N    => ETH_REFCLK_N,
        ETH_RX_P        => ETH_RX_P,
        ETH_RX_N        => ETH_RX_N,
        ETH_TX_P        => ETH_TX_P,
        ETH_TX_N        => ETH_TX_N,

        QSFP_I2C_SCL    => QSFP_I2C_SCL,
        QSFP_I2C_SDA    => QSFP_I2C_SDA,
        QSFP_I2C_SCL_I  => QSFP_I2C_SCL_I,
        QSFP_I2C_SDA_I  => QSFP_I2C_SDA_I,
        QSFP_I2C_SCL_O  => QSFP_I2C_SCL_O,
        QSFP_I2C_SCL_OE => QSFP_I2C_SCL_OE,
        QSFP_I2C_SDA_O  => QSFP_I2C_SDA_O,
        QSFP_I2C_SDA_OE => QSFP_I2C_SDA_OE,
        QSFP_I2C_DIR    => QSFP_I2C_DIR,
        QSFP_MODSEL_N   => QSFP_MODSEL_N,
        QSFP_LPMODE     => QSFP_LPMODE,
        QSFP_RESET_N    => QSFP_RESET_N,
        QSFP_MODPRS_N   => QSFP_MODPRS_N,
        QSFP_INT_N      => QSFP_INT_N,

        --REPEATER_CTRL   => (others => '0'), --TBD
        --PORT_ENABLED    => open, --TBD
        ACTIVITY_RX     => eth_rx_activity_ser,
        ACTIVITY_TX     => eth_tx_activity_ser,
        RX_LINK_UP      => eth_rx_link_up_ser,
        TX_LINK_UP      => eth_tx_phy_rdy_ser,

        RX_MFB_DATA     => eth_tx_mfb_data,
        RX_MFB_HDR      => eth_tx_mfb_hdr,
        RX_MFB_SOF_POS  => eth_tx_mfb_sof_pos,
        RX_MFB_EOF_POS  => eth_tx_mfb_eof_pos,
        RX_MFB_SOF      => eth_tx_mfb_sof,
        RX_MFB_EOF      => eth_tx_mfb_eof,
        RX_MFB_SRC_RDY  => eth_tx_mfb_src_rdy,
        RX_MFB_DST_RDY  => eth_tx_mfb_dst_rdy,

        ETH_TX_MVB_CHANNEL   => eth_tx_mvb_channel,
        ETH_TX_MVB_TIMESTAMP => eth_tx_mvb_timestamp_vld,
        ETH_TX_MVB_VLD       => eth_tx_mvb_vld,

        TX_MFB_DATA     => eth_rx_mfb_data,
        TX_MFB_SOF_POS  => eth_rx_mfb_sof_pos,
        TX_MFB_EOF_POS  => eth_rx_mfb_eof_pos,
        TX_MFB_SOF      => eth_rx_mfb_sof,
        TX_MFB_EOF      => eth_rx_mfb_eof,
        TX_MFB_SRC_RDY  => eth_rx_mfb_src_rdy,
        TX_MFB_DST_RDY  => eth_rx_mfb_dst_rdy,
        TX_MVB_DATA     => eth_rx_mvb_data,
        TX_MVB_VLD      => eth_rx_mvb_vld,
        TX_MVB_SRC_RDY  => eth_rx_mvb_src_rdy,
        TX_MVB_DST_RDY  => eth_rx_mvb_dst_rdy,

        MI_CLK          => clk_mi,
        MI_RESET        => rst_mi(5),
        MI_DWR          => mi_adc_dwr(MI_ADC_PORT_NETMOD),
        MI_ADDR         => mi_adc_addr(MI_ADC_PORT_NETMOD),
        MI_RD           => mi_adc_rd(MI_ADC_PORT_NETMOD),
        MI_WR           => mi_adc_wr(MI_ADC_PORT_NETMOD),
        MI_BE           => mi_adc_be(MI_ADC_PORT_NETMOD),
        MI_DRD          => mi_adc_drd(MI_ADC_PORT_NETMOD),
        MI_ARDY         => mi_adc_ardy(MI_ADC_PORT_NETMOD),
        MI_DRDY         => mi_adc_drdy(MI_ADC_PORT_NETMOD),

        MI_CLK_PHY      => clk_mi,
        MI_RESET_PHY    => rst_mi(6),
        MI_DWR_PHY      => mi_adc_dwr(MI_ADC_PORT_ETHMOD),
        MI_ADDR_PHY     => mi_adc_addr(MI_ADC_PORT_ETHMOD),
        MI_RD_PHY       => mi_adc_rd(MI_ADC_PORT_ETHMOD),
        MI_WR_PHY       => mi_adc_wr(MI_ADC_PORT_ETHMOD),
        MI_BE_PHY       => mi_adc_be(MI_ADC_PORT_ETHMOD),
        MI_DRD_PHY      => mi_adc_drd(MI_ADC_PORT_ETHMOD),
        MI_ARDY_PHY     => mi_adc_ardy(MI_ADC_PORT_ETHMOD),
        MI_DRDY_PHY     => mi_adc_drdy(MI_ADC_PORT_ETHMOD),

        MI_CLK_PMD      => clk_mi,
        MI_RESET_PMD    => rst_mi(6),
        MI_DWR_PMD      => mi_adc_dwr(MI_ADC_PORT_ETHPMD),
        MI_ADDR_PMD     => mi_adc_addr(MI_ADC_PORT_ETHPMD),
        MI_RD_PMD       => mi_adc_rd(MI_ADC_PORT_ETHPMD),
        MI_WR_PMD       => mi_adc_wr(MI_ADC_PORT_ETHPMD),
        MI_BE_PMD       => mi_adc_be(MI_ADC_PORT_ETHPMD),
        MI_DRD_PMD      => mi_adc_drd(MI_ADC_PORT_ETHPMD),
        MI_ARDY_PMD     => mi_adc_ardy(MI_ADC_PORT_ETHPMD),
        MI_DRDY_PMD     => mi_adc_drdy(MI_ADC_PORT_ETHPMD),

        TSU_CLK         => tsu_clk,
        TSU_RST         => tsu_rst,
        TSU_TS_NS       => tsu_ns,
        TSU_TS_DV       => tsu_dv
    );

    eth_led_ctrl_i: entity work.ETH_LED_CTRL_TOP
    generic map (
        ETH_PORTS      => ETH_PORTS,
        ETH_CHANNELS   => ETH_PORT_CHANNELS,
        LEDS_PER_PORT  => ETH_PORT_LEDS,
        SYS_CLK_PERIOD => 5, -- 200 MHz
        LED_ON_VAL     => '1'
    )
    port map(
        ETH_CLK          => clk_eth_phy,
        SYS_CLK          => clk_usr_x2,
        SYS_RESET        => rst_usr_x2(0),
    
        ETH_RX_LINK_UP   => eth_rx_link_up_ser,
        ETH_RX_ACTIVITY  => eth_rx_activity_ser,
        ETH_TX_ACTIVITY  => eth_tx_activity_ser,
        ETH_PORT_ENABLED => (others => '1'),
        ETH_MODPRS_N     => eth_modprs_n,
    
        ETH_LED_G        => ETH_LED_G,
        ETH_LED_R        => ETH_LED_R
    );

    eth_modprs_n_g: if QSFP_PORTS = ETH_PORTS generate
        eth_modprs_n <= QSFP_MODPRS_N;
    else generate -- fix for 2x100GE in QSFP-DD
        eth_modprs_n <= (others => QSFP_MODPRS_N(0));
    end generate;

    -- =========================================================================
    --  TimeStamp Unit
    -- =========================================================================
    tsu_gen_g: if (TSU_ENABLE) generate
        tsu_freq <= std_logic_vector(to_unsigned(TSU_FREQUENCY-1, 32)); -- input frequency is from only a single source

        tsu_gen_i: entity work.tsu_gen
        generic map (
            TS_MULT_SMART_DSP => TS_MULT_SMART_DSP,
            TS_MULT_USE_DSP   => TS_MULT_USE_DSP,
            PPS_SEL_WIDTH     => 0,
            CLK_SEL_WIDTH     => 0
        )
        port map (
            MI_CLK            => clk_mi   ,
            MI_RESET          => rst_mi(7),
            MI_DWR            => mi_adc_dwr(MI_ADC_PORT_TSU) ,
            MI_ADDR           => mi_adc_addr(MI_ADC_PORT_TSU),
            MI_RD             => mi_adc_rd(MI_ADC_PORT_TSU)  ,
            MI_WR             => mi_adc_wr(MI_ADC_PORT_TSU)  ,
            MI_BE             => mi_adc_be(MI_ADC_PORT_TSU)  ,
            MI_DRD            => mi_adc_drd(MI_ADC_PORT_TSU) ,
            MI_ARDY           => mi_adc_ardy(MI_ADC_PORT_TSU),
            MI_DRDY           => mi_adc_drdy(MI_ADC_PORT_TSU),
            PPS_N             => '0',
            PPS_SRC           => (others => '0'),
            PPS_SEL           => open,
            CLK               => tsu_clk,
            RESET             => tsu_rst,
            CLK_FREQ          => tsu_freq,
            CLK_SRC           => X"0001",
            CLK_SEL           => open,
            TS                => open,
            TS_NS             => tsu_ns,
            TS_DV             => tsu_dv
        );
    else generate
        mi_adc_ardy(MI_ADC_PORT_TSU) <= mi_adc_rd(MI_ADC_PORT_TSU) or mi_adc_wr(MI_ADC_PORT_TSU);
        mi_adc_drd(MI_ADC_PORT_TSU) <= (others => '0');
        mi_adc_drdy(MI_ADC_PORT_TSU) <= mi_adc_rd(MI_ADC_PORT_TSU);

        tsu_ns <= (others => '0');
        tsu_dv <= '0';
    end generate;
    -- =========================================================================
    --  JTAG-OVER-PROTOCOL CONTROLLER
    -- =========================================================================
    jtag_op_ctrl_i: entity work.JTAG_OP_CTRL
    generic map (
        MI_ADDR_WIDTH => 32,
        MI_DATA_WIDTH => 32,
        JOP_ENABLE    => VIRTUAL_DEBUG_ENABLE,
        DEVICE        => DEVICE
    )
    port map (
        USER_CLK      => clk_mi,
        USER_RESET    => rst_mi(7),
        JOP_CLK       => clk_usr_x1,
        JOP_RESET     => rst_usr_x1(0),
        MI_DWR        => mi_adc_dwr(MI_ADC_PORT_JTAG_IP),
        MI_ADDR       => mi_adc_addr(MI_ADC_PORT_JTAG_IP),
        MI_RD         => mi_adc_rd(MI_ADC_PORT_JTAG_IP),
        MI_WR         => mi_adc_wr(MI_ADC_PORT_JTAG_IP),
        MI_BE         => mi_adc_be(MI_ADC_PORT_JTAG_IP),
        MI_DRD        => mi_adc_drd(MI_ADC_PORT_JTAG_IP),
        MI_ARDY       => mi_adc_ardy(MI_ADC_PORT_JTAG_IP),
        MI_DRDY       => mi_adc_drdy(MI_ADC_PORT_JTAG_IP)
    );

    -- =========================================================================
    --  STATUS LEDs
    -- =========================================================================

    process (clk_usr_x1)
    begin
        if rising_edge(clk_usr_x1) then
            if (rst_usr_x1(0) = '1') then
                heartbeat_cnt <= (others => '0');
            else
                heartbeat_cnt <= heartbeat_cnt + 1;
            end if;
            STATUS_LED_R(0) <= heartbeat_cnt(HEARTBEAT_CNT_W-1);
        end if;
    end process;

    STATUS_LED_G(0) <= (and app_pcie_link_up);

    STATUS_LED_R(1) <= (or EMIF_CAL_FAIL);
    STATUS_LED_G(1) <= (and EMIF_CAL_SUCCESS);

end architecture;
