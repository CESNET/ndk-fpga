-- squarer.vhd: Squarer wrapper
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
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SQUARER is
begin

   -- when you add a new setting, add it at the end of OR in this assert
   assert (((DEGREE_OF_PARALLELISM = 2) AND (LATENCY = 1)) OR false)
      report "Unsupported settings of DEGREE_OF_PARALLELISM and LATENCY!"
      severity failure;

   gen_sqr_dop2_lat1: if ((DEGREE_OF_PARALLELISM = 2) AND (LATENCY = 1)) generate

      sqr: entity work.SQR_DOP2_LAT1
      generic map
      (
         -- widths of operands
         OPERAND_WIDTH         => OPERAND_WIDTH,
         -- width of result
         RESULT_WIDTH          => RESULT_WIDTH
      )
      port map
      (
         -- common interface
         CLK       => CLK,

         -- operand
         DATA      => DATA,

         -- result (is valid 2 clock cycles after operands are set)
         RESULT    => RESULT
      );
   end generate;

end architecture;
