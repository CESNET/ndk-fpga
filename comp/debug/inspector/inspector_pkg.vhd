-- inspector_pkg.vhd: package for debugger and analyser
-- Copyright (C) 2016 CESNET
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

package inspector_pkg is

   -- Specify total number of inspected values.
   constant IOBJ_COUNT_MAX       : integer := 128;

   -- Enum of inspector value types.
   constant IOBJ_NONE            : integer := 0;
   constant IOBJ_RESET           : integer := 1;
   constant IOBJ_STROBE          : integer := 2;
   constant IOBJ_OUTPUTREG       : integer := 3;
   constant IOBJ_INPUTREG        : integer := 4;
   constant IOBJ_COUNTER         : integer := 5;
   constant IOBJ_HISTOGRAM       : integer := 6;

   type t_inspector_objects_int  is array(IOBJ_COUNT_MAX-1 downto 0) of integer;

   type t_inspector_input is record
      inputreg                 : std_logic_vector(63 downto 0);
      inputreg_we              : std_logic;
      counter_inc              : integer;
      counter_ce               : std_logic;
      histogram_bucket         : integer;
      histogram_ce             : std_logic;
   end record;

   type t_inspector_output is record
      outputreg                : std_logic_vector(63 downto 0);
      outputreg_we             : std_logic;
   end record;

   type t_inspector_inputs  is array (natural range <>) of t_inspector_input;
   type t_inspector_outputs is array (natural range <>) of t_inspector_output;

end inspector_pkg;

package body inspector_pkg is

end inspector_pkg;
