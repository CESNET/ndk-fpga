-- barrel_bit_shifter.vhd: Barrel shifter with generic data width
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

--
-- Shifts (NOT rotates!) the DATA_IN by SEL bits to LEFT/RIGHT.
-- The rest bits are filled with '0'.
-- Doesn't provide the last combination (shift by DATA_WIDTH, that
--  leads to zeros) becouse of entity (backward compatibility) - it
--  provides only log2(DATA_WIDTH) combinations.
-- Shifting is possible by value in range: 0 to DATA_WIDTH-1
--
architecture shifter_behav of BARREL_BIT_SHIFTER is

   --+ input to 'shifting' MUX
   signal mux_in : std_logic_vector(DATA_WIDTH * DATA_WIDTH - 1 downto 0);

begin

-- ----------------------------------------------------------------------------
--                 Generation of all possible combinations                   --
-- ----------------------------------------------------------------------------

-- generate n combinations (n = DATA_WIDTH)
gen_all_combinations:
for i in 0 to DATA_WIDTH - 1 generate

  shifterp : process(DATA_IN)
     variable result : std_logic_vector(DATA_WIDTH - 1 downto 0);
  begin
      -- identity
      if i = 0 then
         result := DATA_IN;

      -- shift by i bits to LEFT
      elsif SHIFT_LEFT = true then

         for j in 0 to DATA_WIDTH - 1 loop
            if j < i then
               result(j)   := '0';

            else
               result(j)   := DATA_IN(j - i);

            end if;
         end loop;

      -- shfit by i bits to RIGHT
      elsif SHIFT_LEFT = false then

         for j in DATA_WIDTH - 1 downto 0 loop
            if j >= (DATA_WIDTH - i) then
               result(j)   := '0';

            else
               result(j)   := DATA_IN(j + i);

            end if;
         end loop;

      end if;

      -- set the current combination
      mux_in((i + 1) * DATA_WIDTH - 1 downto i * DATA_WIDTH) <= result;
  end process;

end generate;


-- ----------------------------------------------------------------------------
--                 Output MUX to select the right combination                --
-- ----------------------------------------------------------------------------

shifting_mux : entity work.GEN_MUX
generic map (
   DATA_WIDTH  => DATA_WIDTH,
   MUX_WIDTH   => DATA_WIDTH
)
port map (
   DATA_IN     => mux_in,
   SEL         => SEL,
   DATA_OUT    => DATA_OUT
);

end architecture;

