--
-- lb_root.vhd: Local Bus Root Component
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus package
use work.lb_pkg.all; -- Local Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ROOT is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0):=X"00000000";
      LIMIT            : std_logic_vector(31 downto 0):=X"00000100";

      -- Abort timeout counter width
      -- TIMEOUT and TIME will be 2**WIDTH cycles
      ABORT_CNT_WIDTH  : integer := 6
   );
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      RESET         : in std_logic;

      -- Local Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;

      -- Local Bus Interface
      LOCAL_BUS     : inout t_local_bus16
  );
end entity LB_ROOT;
