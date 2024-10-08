-- fl_dfifo_ent.vhd: FIFO with discard capability on input
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
--
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_dfifo is
   generic(
      -- Data width
      DATA_WIDTH     : integer := 128;
      -- number of items in the FIFO
      ITEMS          : integer := 64;
      -- Number of parts in each frame
      PARTS          : integer := 1
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      DISCARD        : in  std_logic;

      -- read interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic
   );
end entity fl_dfifo;

