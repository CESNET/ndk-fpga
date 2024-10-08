-- clk_gen_pkg.vhd: Package for CLK_GEN module
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;

package clk_gen_pkg is

   function cv2_clkper (is_125 : boolean) return real;
   function cv2_mult (is_125 : boolean) return integer;

end clk_gen_pkg;

package body clk_gen_pkg is

   function cv2_clkper (is_125 : boolean) return real is
   begin
      if is_125 then
         return 8.0;
      else
         return 4.0;
      end if;
   end cv2_clkper;

   function cv2_mult (is_125 : boolean) return integer is
   begin
      if is_125 then
         return 8;
      else
         return 4;
      end if;
   end cv2_mult;

end clk_gen_pkg;

