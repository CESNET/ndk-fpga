-- fl_watch_ent.vhd: Frame Link watch comp to gather statistics about trafic
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- Library with MI32 interface definition
use work.mi32_pkg.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_WATCH_EXTENDED is
   generic(
      INTERFACES     : integer := 1;  -- At least 1
      CNTR_WIDTH     : integer := 32;
      PIPELINE_LEN   : integer := 1;   -- At least 1
      GUARD          : boolean := true;
      PARTS          : integer := 1
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      SOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      DST_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);
      SRC_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);

      MI             : inout t_mi32
   );
end entity FL_WATCH_EXTENDED;
