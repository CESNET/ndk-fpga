--!
--! testbench.vhd: Testbench of ASYNC_RESET
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <jakubcabal@gmail.com>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------

architecture behavioral of testbench is

   signal clk         : std_logic;
   signal async_rst   : std_logic;
   signal sync_rst    : std_logic;

   begin

   uut : entity work.ASYNC_RESET
   generic map(
      TWO_REG => false  --! For two reg = true, for three reg = false
   )
   port map(
      CLK        => clk,
      ASYNC_RST  => async_rst,
      OUT_RST(0) => sync_rst
   );

   clk_p : process
   begin
      clk <= '1';
      wait for 2 ns;
      clk <= '0';
      wait for 2 ns;
   end process;

   --! main testbench process
   sim : process
   begin

      async_rst <= '0';
      wait for 1 ns;

      async_rst <= '1';
      wait for 10 ns;

      async_rst <= '0';
      wait for 77 ns;

      async_rst <= '1';
      wait for 12 ns;

      async_rst <= '0';

      wait for 44 ns;

      async_rst <= '1';
      wait for 5 ns;

      async_rst <= '0';

      wait for 4 ns;

      async_rst <= '1';
      wait for 15 ns;

      async_rst <= '0';

      wait;

   end process;

end architecture behavioral;
