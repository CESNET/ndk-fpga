-- fl_distributor_ent.vhd: FrameLink 1-4 switch entity.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_distributor is
   generic (
      -- FrameLink data width
      DATA_WIDTH : integer := 64;

      -- count of output interfaces, MUST be 2^n and greater than one
      INTERFACES_COUNT : integer := 8;

      -- default interface that is used when the interface
      -- number doesn't come in the frame
      DEFAULT_INTERFACE : integer := 0;

      -- offset from the start of the part (in bits)
      -- where the interface number (INUM) is placed
      INUM_OFFSET : integer := 113;

      -- number of parts in every frame
      PARTS : integer := 2;

      -- False: Interpret inum as interface number
      -- True: Interpret inum as interface mask, select LSB
      --       In case of empty mask, ifc 0 is selected (not DEFAULT_INTERFACE)
      MASK  : boolean := false
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
      TX_DATA     : out std_logic_vector(INTERFACES_COUNT*DATA_WIDTH-1 downto 0);
      TX_REM      : out std_logic_vector(INTERFACES_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_DST_RDY_N: in  std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0)
   );
end entity fl_distributor;

