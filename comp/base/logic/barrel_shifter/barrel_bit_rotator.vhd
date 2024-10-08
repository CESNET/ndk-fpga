-- barrel_bit_shifter.vhd: Barrel shifter with generic data width
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture barrel_bit_shifter_arch of BARREL_BIT_SHIFTER is

begin

   multiplexors: for i in 0 to DATA_WIDTH-1 generate
      process (DATA_IN, SEL)
         variable sel_aux: integer;
      begin
         if (SHIFT_LEFT) then
            sel_aux := conv_integer('0'&SEL);
         else
            sel_aux := conv_integer('0'&(0-SEL));
         end if;

         DATA_OUT(i) <= DATA_IN((DATA_WIDTH-sel_aux+i) mod (DATA_WIDTH));
      end process;
   end generate;

end barrel_bit_shifter_arch;
