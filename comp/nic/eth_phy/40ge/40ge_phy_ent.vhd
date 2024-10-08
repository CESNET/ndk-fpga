-- 40ge_phy_ent.vhd : The complete 40GBASE-R (PCS+PMA) PHY for Xilinx Ultrascale+ FPGAs
--                   (entity declaration)
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity phy_40ge is
   generic (
      CLK_SLAVE  : boolean := false; -- true = MASTER mode
      DEVICE     : string  := "ULTRASCALE"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
      SIMULATION : integer := 0      -- 1 speeds up simulation
   );
   port (
      RESET      : in std_logic; -- Global Async reset
      CLK_STABLE : out std_logic := '1'; -- XLGMII clock stable and running
      -- =====================================================================
      -- XLGMII interface
      -- =====================================================================
      XLGMII_CLK : out std_logic; -- XLGMII clock, 156.25MHz, common for both TX and RX
      XLGMII_TXD : in std_logic_vector(255 downto 0);  -- TX data
      XLGMII_TXC : in std_logic_vector(31 downto 0);   -- TX command
      XLGMII_RXD : out std_logic_vector(255 downto 0); -- RX data
      XLGMII_RXC : out std_logic_vector(31 downto 0);  -- RX command
      -- =====================================================================
      -- Transceiver clocking
      -- =====================================================================
      REFCLK_IN  : in std_logic := '0'; -- 322.2 MHz clock - SLAVE mode only
      REFCLK_P   : in std_logic := '1'; -- External GTY reference clock positive, 322.265625 MHz. MASTER mode only
      REFCLK_N   : in std_logic := '0'; -- External GTY reference clock negative, 322.265625 MHz. MASTER mode only
      REFCLK_OUT : out std_logic; -- Reference clock output for clocking a slave
      DRPCLK     : in std_logic;  -- Stable free running clock, up to 125 MHz
      -- =====================================================================
      -- Serial transceiver ports
      -- =====================================================================
      RXN        : in std_logic_vector(3 downto 0);
      RXP        : in std_logic_vector(3 downto 0);
      TXN        : out std_logic_vector(3 downto 0);
      TXP        : out std_logic_vector(3 downto 0);
      RXPOLARITY : in  std_logic_vector(3 downto 0) := (others => '0'); -- Optional polarity invert ('1' = inverts polarity on corresponding RXP/N pins)
      TXPOLARITY : in  std_logic_vector(3 downto 0) := (others => '0'); -- Optional polarity invert ('1' = inverts polarity on corresponding TXP/N pins)
      SIGNAL_DET : in std_logic_vector(3 downto 0) := "1111"; -- Optional signal detect from the external transceiver/PMD
      -- =====================================================================
      -- Management (MI32) - optional
      -- =====================================================================
      MI_RESET   : in std_logic;
      MI_CLK     : in std_logic;
      MI_DWR     : in std_logic_vector(31 downto 0) := X"00000000";
      MI_ADDR    : in std_logic_vector(31 downto 0) := X"00000000";
      MI_RD      : in std_logic := '0';
      MI_WR      : in std_logic := '0';
      MI_BE      : in std_logic_vector( 3 downto 0) := "0000";
      MI_DRD     : out  std_logic_vector(31 downto 0);
      MI_ARDY    : out  std_logic;
      MI_DRDY    : out  std_logic
   );
end phy_40ge;
