--
-- lb_endpoint_ent.vhd: Local Bus End Point Component
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
use work.mi32_pkg.all;
use work.lb_pkg.all;
use work.math_pack.all; -- Math Pack

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ENDPOINT is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0):= X"00000000";
      LIMIT            : std_logic_vector(31 downto 0):= X"00000800";
      FREQUENCY        : integer:= 100;
      BUFFER_EN        : boolean:= false
   );
   port(
      -- Common Interface
      RESET         : in std_logic;

      -- Local Bus Interface
      LB_CLK        : in std_logic;
      LOCALBUS      : inout t_local_bus16;

      -- User Component Interface
      CLK           : in  std_logic;
      MI32          : inout t_mi32
  );
end entity LB_ENDPOINT;
