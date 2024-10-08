--!
--! testbench.vhd: Testbench of GENERAL
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
   signal aready      : std_logic;

   begin

   uut : entity work.ASYNC_GENERAL
   generic map(
      TWO_REG            => false, --! For two reg = true
                                   --! for three reg = false

      --! When DETECT_RISING_EDGE=true  and DETECT_FALLING_EDGE=true
      --! are detected rising edges and falling edges.
      --! When DETECT_RISING_EDGE=true  and DETECT_FALLING_EDGE=false
      --! are detected rising edges.
      --! When DETECT_RISING_EDGE=false and DETECT_FALLING_EDGE=true
      --! are detected falling edges.
      --! When DETECT_RISING_EDGE=false and DETECT_FALLING_EDGE=false
      --! are detected log.1.
      DETECT_RISING_EDGE  => false,
      DETECT_FALLING_EDGE => false
   )
   port map(
      --! A clock domain
      ACLK     => aclk,         --! Source clock
      ARST     => arst,         --! Source reset
      ADATAIN  => data_in,      --! Data input
      AREADY   => aready,       --! Ready signal

      --! B clock domain
      BCLK     => bclk,         --! Target clock
      BRST     => brst,         --! Target reset
      BDATAOUT => data_out      --! Data output
   );

   clk_A : process
   begin
      aclk <= '1';
      wait for 3 ns;
      aclk <= '0';
      wait for 3 ns;
   end process;

   clk_B : process
   begin
      bclk <= '1';
      wait for 7.7 ns;
      bclk <= '0';
      wait for 7.7 ns;
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

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '1';

      wait until rising_edge(aclk);
      data_in <= '0';

      --! arst <= '1';
      --! brst <= '1';
      --! wait for 20 ns;
      --! arst <= '0';
      --! brst <= '0';

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '1';

      wait for 10 ns;

      wait until rising_edge(aclk);
      data_in <= '0';

      wait for 10 ns;

      wait until rising_edge(aclk);
      data_in <= '1';

      wait for 33 ns;

      wait until rising_edge(aclk);
      data_in <= '0';

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '1';

      wait for 99 ns;

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '0';

      wait for 19 ns;

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '1';

      wait for 99 ns;

      wait until rising_edge(aclk) and aready = '1';
      data_in <= '0';

      wait;

   end process;

end architecture behavioral;
