-- switch_ent.vhd: FrameLink 1-N switch entity.
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
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

--* The component is intended for sending FrameLink data from one RX interface
--* to many TX interfaces. Destination TX interfaces are chosen using data (IFNUM)
--* somewhere in the frame. The IFNUM is a bit mask. Ones means send to that interface.
--* It is possible to send to no interface.
--*
--* @author Jan Viktorin
entity fl_switch_1toN is
   generic (
      --* FrameLink data width
      DATA_WIDTH     : integer := 32;

      --* Count of output interfaces. It <b>must</b> fit into one
      --* word of FrameLink (it is the size of the searched bit mask).
      IF_COUNT       : integer := 4;

      --* Offset of IFNUM in bits, whole IFNUM <b>must</b> fit into one RX_DATA.
      IFNUM_OFFSET   : integer := 0;

      --* Number of FrameLink Parts in the frame
      PARTS          : integer := 1
   );
   port (
      -- Common signal
      CLK          : in std_logic;
      RESET        : in std_logic;

      -- Write interface signals
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;

      -- Read interfaces signals
      TX_DATA     : out std_logic_vector(IF_COUNT * DATA_WIDTH - 1 downto 0);
      TX_REM      : out std_logic_vector(IF_COUNT * log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SRC_RDY_N: out std_logic_vector(IF_COUNT - 1 downto 0);
      TX_DST_RDY_N: in  std_logic_vector(IF_COUNT - 1 downto 0);
      TX_SOP_N    : out std_logic_vector(IF_COUNT - 1 downto 0);
      TX_EOP_N    : out std_logic_vector(IF_COUNT - 1 downto 0);
      TX_SOF_N    : out std_logic_vector(IF_COUNT - 1 downto 0);
      TX_EOF_N    : out std_logic_vector(IF_COUNT - 1 downto 0)
   );
end entity;

