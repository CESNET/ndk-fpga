-- lb_pkg.vhd: Local Bus Package
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Internal Bus Package
-- ----------------------------------------------------------------------------
package lb_pkg is

   -- Local 16 bit Bus
   type t_local_bus16 is record
      DWR        : std_logic_vector(15 downto 0);
      BE         : std_logic_vector(1 downto 0);
      ADS_N      : std_logic;
      RD_N       : std_logic;
      WR_N       : std_logic;
      DRD        : std_logic_vector(15 downto 0);
      RDY_N      : std_logic;
      ERR_N      : std_logic;
      ABORT_N    : std_logic;
   end record;

   -- Local 8 bit Bus
   type t_local_bus8 is record
      DWR        : std_logic_vector(7 downto 0);
      BE         : std_logic;
      ADS_N      : std_logic;
      RD_N       : std_logic;
      WR_N       : std_logic;
      DRD        : std_logic_vector(7 downto 0);
      RDY_N      : std_logic;
      ERR_N      : std_logic;
      ABORT_N    : std_logic;
   end record;

   -- Local Bus Frequency
   constant LOCAL_BUS_FREQUENCY : integer := 100;

end lb_pkg;


-- ----------------------------------------------------------------------------
--                        Internal Bus Package
-- ----------------------------------------------------------------------------
package body lb_pkg is

end lb_pkg;

