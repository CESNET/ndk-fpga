--
-- packet_linker_ent.vhd: Packet linker component for Frame link
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
--use work.fl_pkg.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity PACKET_LINKER is
   generic(
       --DATA_WIDTH:   integer:=32;
       PACKET_ID: integer:=1
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame link input interface
      RX_DATA        : in std_logic_vector(31 downto 0);
      RX_REM         : in std_logic_vector(log2(32/8)-1 downto 0);
      RX_SOF_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;

      -- Frame link output interface
      TX_DATA        : out std_logic_vector(31 downto 0);
      TX_REM         : out std_logic_vector(log2(32/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
     );
end entity PACKET_LINKER;
