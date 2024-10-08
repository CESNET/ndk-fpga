-- pipe_tree_adder.vhd: Component for generic adding of multiple values in piped tree structure
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                             Description
-- ----------------------------------------------------------------------------
-- Creates a tree of adders with registers in between to add multiple values together.
-- Tries to use as simple adders as the set latency allows.
-- Has a valid bit for each input.
-- ----------------------------------------------------------------------------
--                          Entity declaration
-- ----------------------------------------------------------------------------

entity PIPE_TREE_ADDER is
   generic(
      -- Number of input values
      ITEMS      : integer := 8;

      -- Width of each input and output value
      -- Warning:
      -- -- Output is the same width as input.
      -- -- Make sure its wide enough for the sum of all values.
      DATA_WIDTH : integer := 16;

      -- Desired latency
      -- Ideal value is log2(ITEMS).
      -- LATENCY==0 -> asynchronous adder
      -- LATENCY>log2(ITEMS) -> adds output registers
      -- Warning:
      -- -- For LATENCY<log2(ITEMS), register on output is not guaraneed.
      -- -- (For 4 ITEMS and 1 LATENCY, the register is in the middle of the tree.)
      LATENCY    : integer := 3
   );
   port(
      CLK          : in  std_logic;
      RESET        : in  std_logic;
      -- Input ports
      IN_DATA      : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      IN_VLD       : in  std_logic_vector(ITEMS-1 downto 0);
      -- Output ports
      OUT_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end PIPE_TREE_ADDER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of PIPE_TREE_ADDER is

   -- Function for 2**N ceiling
   function ceil2N(x : integer) return integer is
      variable v : integer := 1;
   begin
      while (v<x) loop
         v := v*2;
      end loop;

      return v;
   end function;

   -- Constants

   constant LEVELS_IDEAL : integer := log2(ITEMS);
   constant NONZERO_LAT  : integer := max(1,LATENCY);
   constant LEVELS_REAL  : integer := minimum(LEVELS_IDEAL,NONZERO_LAT);
   constant OUT_REGS     : integer := NONZERO_LAT-LEVELS_REAL;

   constant CEIL_ITEMS   : integer := ceil2N(ITEMS);

   -- Function for deciding positions of registers
   function isRegGen return b_array_t is
      variable y : real;
      variable z : real;
      variable result : b_array_t(LEVELS_IDEAL+1-1 downto 1);
   begin

      for x in 1 to LEVELS_IDEAL+1-1 loop
         y := real(x  )*real(LEVELS_REAL)/real(LEVELS_IDEAL);
         z := real(x-1)*real(LEVELS_REAL)/real(LEVELS_IDEAL);
         result(x) := (integer(z)/=integer(y));
      end loop;
      return result;
   end function;

   constant IS_REG_VEC : b_array_t(LEVELS_IDEAL+1-1 downto 1) := isRegGen;

   -- Signals

   signal add_input : u_array_2d_t(LEVELS_IDEAL+1-1 downto 0)(CEIL_ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0);
   signal out_reg   : u_array_t(OUT_REGS-1 downto 0)(DATA_WIDTH-1 downto 0);

begin

   -- input setup
   input_setup0_gen : for i in 0 to ITEMS-1 generate
      add_input(0)(i) <= unsigned(IN_DATA(DATA_WIDTH*(i+1)-1 downto DATA_WIDTH*i) and IN_VLD(i));
   end generate;

   input_setup1_gen : for i in ITEMS to CEIL_ITEMS-1 generate
      add_input(0)(i) <= (others => '0');
   end generate;

   -- LATENCY==0 special case

   l0_gen : if LATENCY=0 generate
      whole_adder_pr : process (add_input)
         variable sum : unsigned(DATA_WIDTH-1 downto 0);
      begin
         sum := (others => '0');
         for i in 0 to CEIL_ITEMS-1 loop
            sum := sum + add_input(0)(i);
         end loop;
         OUT_DATA <= std_logic_vector(sum);
      end process;
   end generate;

   -- LATENCY!=0

   l1_gen : if LATENCY/=0 generate
      -- adder tree
      adder_tree_gen : for i in 1 to LEVELS_IDEAL+1-1 generate

         -- asynch adder
         asynch_adder_gen : if IS_REG_VEC(i)=false generate
            asynch_adder_pr  : process (add_input)
            begin
               for e in 0 to CEIL_ITEMS/2-1 loop
                  add_input(i)(e) <= add_input(i-1)(e*2) + add_input(i-1)(e*2+1);
               end loop;
            end process;
         end generate;

         -- synch adder
         synch_adder_gen : if IS_REG_VEC(i)=true generate
            synch_adder_pr  : process (CLK)
            begin
               if (CLK'event and CLK='1') then
                  for e in 0 to CEIL_ITEMS/2-1 loop
                     add_input(i)(e) <= add_input(i-1)(e*2) + add_input(i-1)(e*2+1);
                  end loop;

                  if (RESET='1') then
                     add_input(i) <= (others => (others => '0'));
                  end if;
               end if;
            end process;
         end generate;

      end generate;

      -- output registers
      output_reg_gen  : if OUT_REGS/=0 generate
         output_reg_pr : process (CLK)
         begin
            if (CLK'event and CLK='1') then
               for i in 0 to OUT_REGS-1 loop
                  if (i=0) then
                     out_reg(0) <= add_input(LEVELS_IDEAL+1-1)(0);
                  else
                     out_reg(i) <= out_reg(i-1);
                  end if;
               end loop;

               if (RESET='1') then
                  out_reg <= (others => (others => '0'));
               end if;
            end if;
         end process;
      end generate;

      -- output
      output_r_gen  : if OUT_REGS/=0 generate
         OUT_DATA <= std_logic_vector(out_reg(OUT_REGS-1));
      end generate;
      output_nr_gen : if OUT_REGS=0 generate
         OUT_DATA <= std_logic_vector(add_input(LEVELS_IDEAL+1-1)(0));
      end generate;
   end generate;

end architecture;
