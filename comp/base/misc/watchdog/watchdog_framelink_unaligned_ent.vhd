-- watchdog_framelink_unaligned_ent.vhd: watchdog FrameLinkUnaligned entity
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

entity WATCHDOG_FRAMELINK_UNALIGNED is
   generic(
      --!   width of the the data flow
      DATA_WIDTH        : positive  := 32;
      --!   enable edge detection on signal KEEP_ALIVE
      EDGE_DETECT       : boolean   := false;
      --!   maximum value of steps to the counter
      COUNT             : positive  := 8;
      --!   width of the counter
      COUNTER_WIDTH     : positive  := 32;
      --!   if TIMING is true, counter counts clock's periods, not data flowing
      TIMING            : boolean   := false
   );
   port(
   -----------------------------------------
   ---        watchdog signals           ---
   -----------------------------------------
      CLK               : in std_logic;
      RESET             : in std_logic;

      --!   counter keep counting
      KEEP_ALIVE        : in std_logic;
      --!   contains exact status of internal counter
      COUNTER           : out std_logic_vector(COUNTER_WIDTH-1 downto 0);
      --!   if watchdog releases data or if it is locked
      LOCKED            : out std_logic;

      -----------------------------------------
      ---     FrameLinkUnaligned signals    ---
      -----------------------------------------

      --! input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(LOG2(DATA_WIDTH/8)-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      --! output interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(LOG2(DATA_WIDTH/8)-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end;
