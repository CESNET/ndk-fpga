-- network_mod_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;


entity NETWORK_MOD is
generic(
    -- Ethernet core architecture: E_TILE, F_TILE, CMAC
    ETH_CORE_ARCH     : string := "E_TILE";
    -- =====================================================================
    -- Network ports configuration:
    -- =====================================================================    
    ETH_PORTS         : natural := 2; -- max 2 (MI address space limit)
    -- Number ETH streams, must be equal to ETH_PORTS or ETH_PORTS*ETH_PORT_CHAN!
    ETH_STREAMS       : natural := ETH_PORTS;
    -- Speed per Ethernet port.
    -- Options: F_TILE core: 400, 200, 100, 50, 40, 25, 10;
    --          E_TILE core: 100, 25, 10;
    --          CMAC   core: 100.
    ETH_PORT_SPEED    : integer_vector(ETH_PORTS-1 downto 0) := (others => 25);
    -- Number of channels per Ethernet port.
    -- Options: F_TILE core: 1, 2, 4, 8;
    --          E_TILE core: 1, 4;
    --          CMAC   core: 1.

    ETH_PORT_CHAN     : integer_vector(ETH_PORTS-1 downto 0) := (others => 4);
    -- Type of used IP core default is F_Tile.
    EHIP_PORT_TYPE    : integer_vector(ETH_PORTS-1 downto 0) := (others => 0);
    -- Maximum allowed size of RX frame in bytes per Ethernet port.
    ETH_PORT_RX_MTU   : integer_vector(ETH_PORTS-1 downto 0) := (others => 16383);
    -- Maximum allowed size of TX frame in bytes per Ethernet port.
    ETH_PORT_TX_MTU   : integer_vector(ETH_PORTS-1 downto 0) := (others => 16383);
    -- Optional option to disable MAC Lite modules. Dangerously!
    ETH_MAC_BYPASS    : boolean := False;
    -- Number of serial lanes.
    -- Options: F_TILE      core: 8;
    --          E_TILE/CMAC core: 4.
    LANES             : natural := 4;
    QSFP_PORTS        : natural := 2;
    QSFP_I2C_PORTS    : natural := 1; -- max 2
    QSFP_I2C_TRISTATE : boolean := true;

    -- =====================================================================
    -- MFB configuration:
    -- =====================================================================
    -- Recommended MFB parameters:
    --     F_TILE core: 4,8,8,8.
    --     E_TILE core: 1,8,8,8.
    REGIONS           : natural := 1;
    REGION_SIZE       : natural := 8;
    BLOCK_SIZE        : natural := 8;
    ITEM_WIDTH        : natural := 8;

    -- =====================================================================
    -- MI configuration:
    -- =====================================================================
    MI_DATA_WIDTH     : natural := 32;
    MI_ADDR_WIDTH     : natural := 32;
    
    MI_DATA_WIDTH_PHY : natural := 32;
    MI_ADDR_WIDTH_PHY : natural := 32;

    -- =====================================================================
    -- Other configuration:
    -- =====================================================================
    -- Enable timestamp-limiting demo/testing.
    -- Timestamps and channel IDs are sent from the APP Core to the Network module
    -- via a special MVB-like interface. There, before entering the IP core,
    -- time between packets from the same DMA channel is measured.
    -- The measured data is presented to the user via a couple of dedicated registers.
    -- WARNING: works only for a single-channel (and single-Region) designs with E-Tile (Intel)!
    TS_DEMO_EN        : boolean := false;
    TX_DMA_CHANNELS   : natural := 16;
    -- Ethernet lanes polarity
    LANE_RX_POLARITY  : std_logic_vector(ETH_PORTS*LANES-1 downto 0) := (others => '0');
    LANE_TX_POLARITY  : std_logic_vector(ETH_PORTS*LANES-1 downto 0) := (others => '0');
    -- Number of user resets.
    RESET_WIDTH       : natural := 8;
    -- Select correct FPGA device.
    DEVICE            : string := "STRATIX10"; -- AGILEX, STRATIX10, ULTRASCALE
    BOARD             : string := "DK-DEV-1SDX-P" -- 400G1, DK-DEV-AGI027RES, DK-DEV-1SDX-P
);
port(
    -- =====================================================================
    -- CLOCK AND RESET
    -- =====================================================================
    CLK_USER        : in  std_logic;
    CLK_ETH         : out std_logic_vector(ETH_PORTS-1 downto 0);

    RESET_USER      : in  std_logic_vector(RESET_WIDTH-1 downto 0);
    RESET_ETH       : in  std_logic_vector(ETH_PORTS-1 downto 0);

    -- =====================================================================
    -- ETH SERIAL INTERFACES
    -- =====================================================================
    ETH_REFCLK_P    : in  std_logic_vector(ETH_PORTS-1 downto 0);
    ETH_REFCLK_N    : in  std_logic_vector(ETH_PORTS-1 downto 0);
    ETH_RX_P        : in  std_logic_vector(ETH_PORTS*LANES-1 downto 0);
    ETH_RX_N        : in  std_logic_vector(ETH_PORTS*LANES-1 downto 0);
    ETH_TX_P        : out std_logic_vector(ETH_PORTS*LANES-1 downto 0);
    ETH_TX_N        : out std_logic_vector(ETH_PORTS*LANES-1 downto 0);
    -- =====================================================================
    -- QSFP Control
    -- =====================================================================        
    QSFP_I2C_SCL    : inout std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => 'Z');
    QSFP_I2C_SDA    : inout std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => 'Z');
    QSFP_I2C_SDA_I  : in    std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => '1');
    QSFP_I2C_SCL_I  : in    std_logic_vector(QSFP_I2C_PORTS-1 downto 0) := (others => '1');
    QSFP_I2C_SCL_O  : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SCL_OE : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SDA_O  : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_SDA_OE : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_I2C_DIR    : out   std_logic_vector(QSFP_I2C_PORTS-1 downto 0);
    QSFP_MODSEL_N   : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_LPMODE     : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_RESET_N    : out   std_logic_vector(QSFP_PORTS-1 downto 0);
    QSFP_MODPRS_N   : in    std_logic_vector(QSFP_PORTS-1 downto 0) := (others => '0');
    QSFP_INT_N      : in    std_logic_vector(QSFP_PORTS-1 downto 0) := (others => '1');


    -- =====================================================================
    -- Link control/status - runs on CLK_ETH
    -- =====================================================================        
    -- REPEATER_CTRL   : in  std_logic_vector(ETH_PORTS*2-1 downto 0);
    -- PORT_ENABLED    : out std_logic_vector(ETH_PORTS-1 downto 0);
    ACTIVITY_RX     : out std_logic_vector(ETH_PORTS*ETH_PORT_CHAN(0)-1 downto 0);
    ACTIVITY_TX     : out std_logic_vector(ETH_PORTS*ETH_PORT_CHAN(0)-1 downto 0);
    RX_LINK_UP      : out std_logic_vector(ETH_PORTS*ETH_PORT_CHAN(0)-1 downto 0);
    TX_LINK_UP      : out std_logic_vector(ETH_PORTS*ETH_PORT_CHAN(0)-1 downto 0);

    -- =====================================================================
    -- RX interface (Packets for transmit to Ethernet)
    -- =====================================================================
    RX_MFB_DATA     : in  std_logic_vector(ETH_STREAMS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_MFB_HDR      : in  std_logic_vector(ETH_STREAMS*REGIONS*ETH_TX_HDR_WIDTH-1 downto 0); -- valid with SOF
    RX_MFB_SOF      : in  std_logic_vector(ETH_STREAMS*REGIONS-1 downto 0);
    RX_MFB_EOF      : in  std_logic_vector(ETH_STREAMS*REGIONS-1 downto 0);
    RX_MFB_SOF_POS  : in  std_logic_vector(ETH_STREAMS*REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS  : in  std_logic_vector(ETH_STREAMS*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);
    RX_MFB_DST_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);

    -- This interface is to transmit Channel IDs and Timestamps of packets
    -- from the APP Core to the demo/testing logic in the Network Mod Core (E-Tile).
    ETH_TX_MVB_CHANNEL   : in std_logic_vector(ETH_PORTS*REGIONS*max(1,log2(TX_DMA_CHANNELS))-1 downto 0);
    ETH_TX_MVB_TIMESTAMP : in std_logic_vector(ETH_PORTS*REGIONS*48-1 downto 0);
    ETH_TX_MVB_VLD       : in std_logic_vector(ETH_PORTS*REGIONS-1 downto 0);

    -- =====================================================================
    -- TX interface (Packets received from Ethernet)
    -- =====================================================================
    TX_MFB_DATA     : out std_logic_vector(ETH_STREAMS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_MFB_SOF      : out std_logic_vector(ETH_STREAMS*REGIONS-1 downto 0);
    TX_MFB_EOF      : out std_logic_vector(ETH_STREAMS*REGIONS-1 downto 0);
    TX_MFB_SOF_POS  : out std_logic_vector(ETH_STREAMS*REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS  : out std_logic_vector(ETH_STREAMS*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);
    TX_MFB_DST_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    TX_MVB_DATA     : out std_logic_vector(ETH_STREAMS*REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    TX_MVB_VLD      : out std_logic_vector(ETH_STREAMS*REGIONS-1 downto 0);
    TX_MVB_SRC_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);
    TX_MVB_DST_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    -- =====================================================================
    -- MI interface - ETH MAC
    -- =====================================================================
    MI_CLK          : in  std_logic;
    MI_RESET        : in  std_logic;
    MI_DWR          : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR         : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_RD           : in  std_logic;
    MI_WR           : in  std_logic;
    MI_BE           : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_DRD          : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY         : out std_logic;
    MI_DRDY         : out std_logic;

    -- =====================================================================
    -- MI interface - ETH PCS/PMA
    -- =====================================================================
    MI_CLK_PHY      : in  std_logic;
    MI_RESET_PHY    : in  std_logic;
    MI_DWR_PHY      : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR_PHY     : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_RD_PHY       : in  std_logic;
    MI_WR_PHY       : in  std_logic;
    MI_BE_PHY       : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_DRD_PHY      : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY_PHY     : out std_logic;
    MI_DRDY_PHY     : out std_logic;

    -- =====================================================================
    -- MI interface - ETH PMD (QSFP)
    -- =====================================================================
    MI_CLK_PMD      : in  std_logic;
    MI_RESET_PMD    : in  std_logic;
    MI_DWR_PMD      : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR_PMD     : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_RD_PMD       : in  std_logic;
    MI_WR_PMD       : in  std_logic;
    MI_BE_PMD       : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_DRD_PMD      : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY_PMD     : out std_logic;
    MI_DRDY_PMD     : out std_logic;

    -- =====================================================================
    -- TSU interface
    -- =====================================================================
    TSU_CLK         : out std_logic;
    TSU_RST         : out std_logic;
    TSU_TS_NS       : in  std_logic_vector(64-1 downto 0);
    TSU_TS_DV       : in  std_logic
);
end entity;
