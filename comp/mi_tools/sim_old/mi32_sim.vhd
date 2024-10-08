--
-- mi32_sim.vhd: Simulation component for mi32 interface
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
use work.ib_pkg.all;      -- Internal Bus Package
use work.lb_pkg.all;      -- Local Bus Package
use work.ib_sim_oper.all; -- in_sim Package
use work.mi32_pkg.all;
use work.math_pack.all; -- Math Pack

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MI32_SIM is
   generic(
      UPSTREAM_LOG_FILE   : string := "";
      DOWNSTREAM_LOG_FILE : string := "";
      BASE_ADDR           : std_logic_vector(31 downto 0):= X"00000000";
      LIMIT               : std_logic_vector(31 downto 0):= X"01048576";
      FREQUENCY           : integer:= LOCAL_BUS_FREQUENCY;
      BUFFER_EN           : boolean:= false
   );
   port(
      -- Common interface
      IB_RESET          : in  std_logic;
      IB_CLK            : in  std_logic;

      -- User Component Interface
      CLK           : in  std_logic;
      MI32          : inout t_mi32;

      -- IB SIM interface
      STATUS            : out t_ib_status;
      CTRL              : in  t_ib_ctrl;
      STROBE            : in  std_logic;
      BUSY              : out std_logic
  );
end entity MI32_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture MI32_SIM_ARCH of MI32_SIM is

     -- Internal Bus 64 (IB_SIM)
     signal internal_bus64      : t_internal_bus64;

     -- Local Bus 16 (LB_ROOT)
     signal local_bus16         : t_local_bus16;

begin

-- Internal Bus simulation component -----------------------------------------
IB_SIM_U : entity work.IB_SIM
   generic map (
      UPSTREAM_LOG_FILE   => UPSTREAM_LOG_FILE,
      DOWNSTREAM_LOG_FILE => DOWNSTREAM_LOG_FILE
   )
   port map (
      -- Common interface
      IB_RESET           => IB_RESET,
      IB_CLK             => IB_CLK,

      -- Internal Bus Interface
      INTERNAL_BUS       => internal_bus64,

      -- IB SIM interface
      STATUS             => STATUS,
      CTRL               => CTRL,
      STROBE             => STROBE,
      BUSY               => BUSY
      );

-- -----------------------Portmaping of LB root -------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => BASE_ADDR,
      LIMIT          => LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => IB_CLK,
      RESET          => IB_RESET,

      -- Local Bus Interface
      INTERNAL_BUS   => internal_bus64,

      -- Local Bus Interface
      LOCAL_BUS      => local_bus16
  );

-- -----------------------Portmaping of LB_Endpoint ---------------------------
LB_ENDPOINT_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => BASE_ADDR,
      LIMIT          => LIMIT,
      FREQUENCY      => FREQUENCY,
      BUFFER_EN      => BUFFER_EN
   )
   port map (
      -- Common Interface
      RESET          => IB_RESET,

      -- Local Bus Interface
      LB_CLK         => IB_CLK,
      LOCALBUS       => local_bus16,

      -- User Component Interface
      CLK            => CLK,
      MI32           => MI32
  );

end architecture  MI32_SIM_ARCH;
