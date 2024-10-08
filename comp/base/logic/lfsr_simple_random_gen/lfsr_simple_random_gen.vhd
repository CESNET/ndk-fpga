-- lfsr_simple_random_gen.vhd: Simple LSFR pseudo-random generator
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- SIMPLE LFSR PSEUDO-RANDOM GENERATOR
-- ===================================
-- The generator uses Fibonacci implementation of LFSR with XNOR gate.
-- Only selected data widths are supported, but others can be added.
-- The diagram below shows connections for a 4-bit data width:
--
-- +--------------------------------------------------------------------+
-- |  +----------------------------------------------------+            |
-- |  |                                                    |            |
-- |  |   +------+                                         |            |
-- |  +-->|      |      +-----+      +-----+      +-----+  |   +-----+  |
-- |      | XNOR |----->|D   Q|----->|D   Q|----->|D   Q|--+-->|D   Q|--+
-- +----->|      |      |     |      |     |      |     |      |     |
--        +------+      |>    |      |>    |      |>    |      |>    |
--                      +-----+      +-----+      +-----+      +-----+
--
-- ENABLE is connected to enable of Flip-Flops.
-- DATA is output of all Flip-Flops.

entity LFSR_SIMPLE_RANDOM_GEN is
   generic(
      -- Data width in bits, alowed values: 4, 8, 16, 20, 24, 32, 64
      DATA_WIDTH : natural := 8;
      -- Reset seed value, all bits must NOT be set high!!!
      RESET_SEED : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0')
   );
   port(
      -- Clock
      CLK    : in  std_logic;
      -- Synchronous reset, active in high
      RESET  : in  std_logic;
      -- Enable of generation pseudo-random values
      ENABLE : in  std_logic;
      -- Output data with pseudo-random value
      DATA   : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end LFSR_SIMPLE_RANDOM_GEN;

architecture FULL of LFSR_SIMPLE_RANDOM_GEN is

   type taps_array_t is array (natural range 0 to 3) of natural;

   -- This function returns correct XNOR taps for suported data widts.
   -- If necessary, you can add support for the next data width. But do not
   -- forget to edit the comment in the entity! For a table of XNOR taps for
   -- Fibonacci implementation of the LFSR, see the following link:
   -- https://www.xilinx.com/support/documentation/application_notes/xapp052.pdf
   function fce_get_taps return taps_array_t is
      variable v_xnor_taps : taps_array_t;
   begin
      case DATA_WIDTH is
         when 3  => v_xnor_taps := ( 0, 0, 3, 2);
         when 4  => v_xnor_taps := ( 0, 0, 4, 3);
         when 5  => v_xnor_taps := ( 0, 0, 5, 3);
         when 6  => v_xnor_taps := ( 0, 0, 6, 5);
         when 7  => v_xnor_taps := ( 0, 0, 7, 6);
         when 8  => v_xnor_taps := ( 8, 6, 5, 4);
         when 9  => v_xnor_taps := ( 0, 0, 9, 5);
         when 10 => v_xnor_taps := ( 0, 0,10, 7);
         when 11 => v_xnor_taps := ( 0, 0,11, 9);
         when 12 => v_xnor_taps := (12, 6, 4, 1);
         when 13 => v_xnor_taps := (13, 4, 3, 1);
         when 14 => v_xnor_taps := (14, 5, 3, 1);
         when 15 => v_xnor_taps := ( 0, 0,15,14);
         when 16 => v_xnor_taps := (16,15,13, 4);
         when 17 => v_xnor_taps := ( 0, 0,17,14);
         when 18 => v_xnor_taps := ( 0, 0,18,11);
         when 19 => v_xnor_taps := (19, 6, 2, 1);
         when 20 => v_xnor_taps := ( 0, 0,20,17);
         when 21 => v_xnor_taps := ( 0, 0,21,19);
         when 22 => v_xnor_taps := ( 0, 0,22,21);
         when 23 => v_xnor_taps := ( 0, 0,23,18);
         when 24 => v_xnor_taps := (24,23,22,17);
         when 25 => v_xnor_taps := ( 0, 0,25,22);
         when 26 => v_xnor_taps := (26, 6, 2, 1);
         when 27 => v_xnor_taps := (27, 5, 2, 1);
         when 28 => v_xnor_taps := ( 0, 0,28,25);
         when 29 => v_xnor_taps := ( 0, 0,29,27);
         when 30 => v_xnor_taps := (30, 6, 4, 1);
         when 31 => v_xnor_taps := ( 0, 0,31,28);
         when 32 => v_xnor_taps := (32,22, 2, 1);
         -- TODO
         when 64 => v_xnor_taps := (64,63,61,60);
         -- Other data widths are currently not supported!
         when others => v_xnor_taps := ( 0, 0, 0, 0);
      end case;
      return v_xnor_taps;
   end function;

   constant XNOR_TAPS : taps_array_t := fce_get_taps;

   signal s_lfsr_xnor : std_logic;
   signal s_lfsr_reg  : std_logic_vector(DATA_WIDTH-1 downto 0) := RESET_SEED;

begin

   -- Will be ignered during synthesis!!
   assert XNOR_TAPS /= (0,0,0,0) report "LFSR random gen data width of " & natural'image(DATA_WIDTH) & " is not implemented!" severity error;

   lfsr_xnor_p : process (s_lfsr_reg)
      variable v_xnor : std_logic;
   begin
      v_xnor := '1';
      for i in 3 downto 0 loop
         if (XNOR_TAPS(i) /= 0) then
            v_xnor := v_xnor xnor s_lfsr_reg(XNOR_TAPS(i)-1);
         end if;
      end loop;
      s_lfsr_xnor <= v_xnor;
   end process;

   lfsr_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_lfsr_reg <= RESET_SEED;
         elsif (ENABLE = '1') then
            s_lfsr_reg <= s_lfsr_reg(DATA_WIDTH-2 downto 0) & s_lfsr_xnor;
         end if;
      end if;
   end process;

   DATA <= s_lfsr_reg;

end architecture;
