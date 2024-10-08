-- watchdog_ent.vhd: watchdog entity
-- Copyright (C) 2015 CESNET
-- Author(s): Adam Piecek <xpiece00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use WORK.math_pack.all;

entity WATCHDOG is
   generic(
      --!   width of the the data flow
      DATA_WIDTH        : positive  := 10;
      --!   enable edge detection on signal KEEP_ALIVE
      EDGE_DETECT       : boolean   := false;
      --!   maximum value of steps to the counter
      COUNT             : positive  := 8;
      --!   width of the counter
      COUNTER_WIDTH     : positive  := 32;
      --! if TIMING is true, counter counts clock's periods, not data flowing
      TIMING            : boolean   := false
   );

   port(
      --! Common interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      --!   data flow
      DATA_IN           : in std_logic_vector(DATA_WIDTH-1 downto 0);
      --!   source is ready to send data
      SRC_RDY_IN        : in std_logic;
      --!   watchdog is ready to receive data
      DST_RDY_IN        : out std_logic;

      --!   data flow
      DATA_OUT          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --!   watchdog is ready to send data
      SRC_RDY_OUT       : out std_logic;
      --!   destination is ready to receive data
      DST_RDY_OUT       : in std_logic;

      --!   counter keep counting
      KEEP_ALIVE        : in std_logic;
      --!   contains exact status of internal counter
      COUNTER           : out std_logic_vector(COUNTER_WIDTH-1 downto 0);
      --!   if watchdog releases data or if it is locked
      LOCKED            : out std_logic
   );
end;
