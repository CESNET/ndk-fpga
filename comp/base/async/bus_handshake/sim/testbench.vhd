--!
--! testbench.vhd: Testbench of ASYNC_BUS_HANDSHAKE
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

   signal aclk       : std_logic;
   signal bclk       : std_logic;
   signal arst       : std_logic;
   signal brst       : std_logic;
   signal adatain    : std_logic_vector(31 downto 0);
   signal aready     : std_logic;
   signal asend      : std_logic;
   signal bdataout   : std_logic_vector(31 downto 0);
   signal bload      : std_logic;
   signal bvalid     : std_logic;

   begin

   uut : entity work.ASYNC_BUS_HANDSHAKE
   port map(
      ADATAIN  => adatain,
      ASEND    => asend,
      AREADY   => aready,
      BDATAOUT => bdataout,
      BLOAD    => bload,
      BVALID   => bvalid,
      ARST     => arst,
      BRST     => brst,
      BCLK     => bclk,
      ACLK     => aclk
   );

   --! generate bclk
   clk_p : process
   begin
      bclk <= '1';
      wait for 7.7 ns;
      bclk <= '0';
      wait for 7.7 ns;
   end process;

   --! generate aclk
   clk_q : process
   begin
      aclk <= '1';
      wait for 3 ns;
      aclk <= '0';
      wait for 3 ns;
   end process;

   --! main testbench process
   sim : process
   begin

      adatain <= (others => '0');
      asend   <= '0';
      bload   <= '0';

      --! RESET FOR 10ns -------------------------------------------------------
      arst <= '1';
      brst <= '1';
      wait for 30 ns;
      arst <= '0';
      brst <= '0';
      --! ----------------------------------------------------------------------

      wait until rising_edge(aclk) and aready='1';
      adatain <= "10101010101010101010101010101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "00000010101010101010111111101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "10101111101010101010111110101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "10101010101010101010100000000111";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "10101011111000010101010000101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "00000000001110101010101010101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "00000010111100010101000100111010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= "00011011000110001111101011101010";
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= (others => '1');
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait until rising_edge(aclk) and aready='1';
      adatain <= (others => '0');
      asend <= '1';
      wait until rising_edge(aclk);
      asend <= '0';
      wait until rising_edge(bclk) and bvalid='1';
      bload <= '1';
      wait until rising_edge(bclk);
      bload <= '0';

      wait;
   end process;

end architecture behavioral;
