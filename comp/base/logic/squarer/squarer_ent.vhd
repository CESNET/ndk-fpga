-- squarer_ent.vhd: Squarer entity declaration
-- Copyright (C) 2009 CESNET
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity SQUARER is
   generic
   (
      -- widths of operand
      OPERAND_WIDTH         : integer := 20;
      -- width of result
      RESULT_WIDTH          : integer := 40;
      -- degree of parallelism, i.e. into how many parts will the input be split
      DEGREE_OF_PARALLELISM : integer := 2;
      -- latency in clock cycles
      LATENCY               : integer := 1
   );
   port
   (
      -- common interface
      CLK      :  in std_logic;

      -- the operand
      DATA     :  in std_logic_vector(OPERAND_WIDTH-1 downto 0);

      -- result (is valid LATENCY clock cycles after operands are set)
      RESULT   : out std_logic_vector(RESULT_WIDTH-1 downto 0)
   );
end entity;
