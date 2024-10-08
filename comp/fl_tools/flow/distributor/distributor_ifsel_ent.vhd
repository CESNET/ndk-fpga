-- distributor_ifsel_ent.vhd: FrameLink distributor full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------
entity fl_distributor_ifsel is
   generic (
      DATA_WIDTH : integer := 32;
      INTERFACES_COUNT : integer := 2;
      DEFAULT_INTERFACE : integer := 0;
      INUM_OFFSET : integer := 0;
      PARTS : integer := 2;
      MASK : boolean := false
   );
   port (
      CLK          : in std_logic;
      RESET        : in std_logic;

      -- Write interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;

      -- Read interfaces
      TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM      : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic;
      TX_DST_RDY_N: in  std_logic;
      TX_SOP_N    : out std_logic;
      TX_EOP_N    : out std_logic;
      TX_SOF_N    : out std_logic;
      TX_EOF_N    : out std_logic;

      TX_INTERFACE : out std_logic_vector(log2(INTERFACES_COUNT)-1 downto 0)
   );
end entity;

