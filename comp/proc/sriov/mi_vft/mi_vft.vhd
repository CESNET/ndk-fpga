-- mi_vft_translator.vhd: Virtual Function Translator
-- Copyright (C) 2017 CESNET
-- Author(s): Jan Remes
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

entity MI_VFT is
    generic(
        DMA_TYPE            : integer := 0;
        DMA_RX_CHANNELS     : integer := 0;
        DMA_TX_CHANNELS     : integer := 0;

        PF0_VFS             : integer := 0;
        VF0_DMA_RX_CHANNELS : integer := 0;
        VF0_DMA_TX_CHANNELS : integer := 0;

        ADDR_WIDTH  : integer := 32;
        META_WIDTH  : integer := 8;
        DATA_WIDTH  : integer := 32
    );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Input MI interface ---------------------------------------------------
      IN_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0);
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;

      -- Output MI interface --------------------------------------------------
      OUT_DWR     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_MWR     : out std_logic_vector(META_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      OUT_BE      : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic;
      OUT_WR      : out std_logic;
      OUT_ARDY    : in  std_logic;
      OUT_DRD     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic
   );
end entity MI_VFT;
