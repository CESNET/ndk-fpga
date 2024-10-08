--!
--! testbench.vhd: Testbench of ASYNC_OPEN_LOOP_SMD
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

   signal aclk        : std_logic;
   signal bclk        : std_logic;
   signal arst        : std_logic;
   signal brst        : std_logic;
   signal data_in     : std_logic;
   signal data_out    : std_logic;

   begin

   uut : entity work.ASYNC_OPEN_LOOP_SMD
   generic map(
      DATA_WIDTH => 1
   )
   port map(
      --! A clock domain
      ACLK       => aclk,         --! Source clock
      ARST       => arst,         --! Source reset
      ADATAIN(0) => data_in,      --! Data input

      --! B clock domain
      BCLK        => bclk,         --! Target clock
      BRST        => brst,         --! Target reset
      BDATAOUT(0) => data_out      --! Data output
   );

   clk_A : process
   begin
      aclk <= '1';
      wait for 6.3 ns;
      aclk <= '0';
      wait for 6.3 ns;
   end process;

   clk_B : process
   begin
      bclk <= '1';
      wait for 3 ns;
      bclk <= '0';
      wait for 3 ns;
   end process;

   --! main testbench process
   sim : process
   begin

      data_in <= '0';

      arst <= '1';
      brst <= '1';
      wait for 20 ns;
      arst <= '0';
      brst <= '0';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk);
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait;

   end process;

end architecture behavioral;
