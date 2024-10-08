-- network_mod_ent.vhd: Entity declaration for the core of the Nework module
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

entity NETWORK_MOD_CORE is
generic(
    -- =====================================================================
    -- Network configuration:
    -- =====================================================================
    -- Select Ethernet port speed.
    -- Options: 400G1            card: 400, 200, 100, 50, 40, 25, 10;
    --          DK-DEV-AGI027RES card: 400, 200, 100, 50, 40, 25, 10;
    --          DK-DEV-1SDX-P    card: 100, 25, 10.
    ETH_PORT_SPEED  : natural := 25;
    -- Select number of channels per Ethernet port.
    -- Options: 400G1            card: 1, 2, 4, 8;
    --          DK-DEV-AGI027RES card: 1, 2, 4, 8;
    --          DK-DEV-1SDX-P    card: 1, 4.
    ETH_PORT_CHAN   : natural := 8;
    -- Number of serial lanes.
    -- Options: 400G1            card: 8;
    --          DK-DEV-AGI027RES card: 8;
    --          DK-DEV-1SDX-P    card: 4.
    LANES           : natural := 8;
    -- Type of used IP core
    -- Options: "EHIP=0" , "F-Tile"          ;
    --          "EHIP>=1", "F-Tile_Multirate";  
    EHIP_TYPE       : natural := 0;
    -- =====================================================================
    -- MFB configuration:
    -- =====================================================================
    -- Set according to eth port mode:
    --     400G1            card:     "400g1", "200g2", "100g4",  "100g2", "50g8" | "40g2", "25g8" | "10g8".
    --     DK-DEV-AGI027RES card:     "400g1", "200g2", "100g4",  "100g2", "50g8" | "40g2", "25g8" | "10g8".
    --     DK-DEV-1SDX-P    card:            , "100g1",        ,                          , "25g4" | "10g4".
    REGIONS           : natural := 1; -- 2   ,    1   ,    1   ,     1   ,        1       ,        1       .
    REGION_SIZE       : natural := 1; -- 8   ,    8   ,    4   ,     2   ,        2       ,        1       .
    BLOCK_SIZE        : natural := 8; -- 8   ,    8   ,    8   ,     8   ,        8       ,        8       .
    ITEM_WIDTH        : natural := 8; -- 8   ,    8   ,    8   ,     8   ,        8       ,        8       .

    -- =====================================================================
    -- MI configuration:
    -- =====================================================================
    MI_DATA_WIDTH_PHY : natural := 32;
    MI_ADDR_WIDTH_PHY : natural := 32;

    -- =====================================================================
    -- Other configuration:
    -- =====================================================================
    TS_DEMO_EN        : boolean := false;
    TX_DMA_CHANNELS   : natural := 8;
    -- GTY TX equalization bits: 59:40 - precursor,
    --                           39:20 - postcursor,
    --                           19:0  - drive (swing)
    GTY_TX_EQ         : std_logic_vector(3*20-1 downto 0) := X"0000000000C6318";
    -- Ethernet lanes polarity
    LANE_RX_POLARITY  : std_logic_vector(LANES-1 downto 0) := (others => '0');
    LANE_TX_POLARITY  : std_logic_vector(LANES-1 downto 0) := (others => '0');
    -- Select correct FPGA device.
    -- "AGILEX", "STRATIX10", "ULTRASCALE", ...
    DEVICE            : string  := "STRATIX10"
);
port(
    -- =====================================================================
    -- CLOCK AND RESET
    -- =====================================================================
    CLK_ETH         : out std_logic;
    RESET_ETH       : in  std_logic;

    -- =====================================================================
    -- QSFP interface
    -- =====================================================================
    QSFP_REFCLK_P   : in  std_logic;
    QSFP_REFCLK_N   : in  std_logic;
    QSFP_RX_P       : in  std_logic_vector(LANES-1 downto 0); -- QSFP XCVR RX Data
    QSFP_RX_N       : in  std_logic_vector(LANES-1 downto 0); -- QSFP XCVR RX Data
    QSFP_TX_P       : out std_logic_vector(LANES-1 downto 0); -- QSFP XCVR TX Data
    QSFP_TX_N       : out std_logic_vector(LANES-1 downto 0); -- QSFP XCVR TX Data

    -- =====================================================================
    -- Link control/status 
    -- =====================================================================        
    -- REPEATER_CTRL   : in  std_logic_vector(1 downto 0);
    -- PORT_ENABLED    : out std_logic;
    RX_LINK_UP      : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    TX_LINK_UP      : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- =====================================================================
    -- RX interface (Packets for transmit to Ethernet, recieved from MFB)
    -- =====================================================================
    RX_MFB_DATA     : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_MFB_SOF_POS  : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS  : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF      : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    RX_MFB_EOF      : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    RX_MFB_SRC_RDY  : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    RX_MFB_DST_RDY  : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- This interface is to transmit Channel IDs and Timestamps of packets
    -- from the APP Core to the demo/testing logic in the Network Mod Core (E-Tile).
    RX_MVB_CHANNEL   : in  std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    RX_MVB_TIMESTAMP : in  std_logic_vector(REGIONS*48-1 downto 0);
    RX_MVB_VLD       : in  std_logic_vector(REGIONS-1 downto 0);

    TSU_TS_NS        : in  std_logic_vector(64-1 downto 0);
    TSU_TS_DV        : in  std_logic;
    
    -- =====================================================================
    -- TX interface (Packets received from Ethernet, for transmit to MFB)
    -- =====================================================================
    TX_MFB_DATA     : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_MFB_ERROR    : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    TX_MFB_SOF_POS  : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS  : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF      : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    TX_MFB_EOF      : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    TX_MFB_SRC_RDY  : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- =====================================================================
    -- MI interface - ETH PCS/PMA/QSFP
    -- =====================================================================
    MI_CLK_PHY      : in  std_logic;
    MI_RESET_PHY    : in  std_logic;
    MI_DWR_PHY      : in  std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    MI_ADDR_PHY     : in  std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0);
    MI_RD_PHY       : in  std_logic;
    MI_WR_PHY       : in  std_logic;
    MI_BE_PHY       : in  std_logic_vector(MI_DATA_WIDTH_PHY/8-1 downto 0);
    MI_DRD_PHY      : out std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    MI_ARDY_PHY     : out std_logic;
    MI_DRDY_PHY     : out std_logic
);
end entity;
