--!
--! testbench.vhd: Testbench of top level entity
--! Copyright (C) 2003 CESNET
--! Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--!            Jakub Cabal <jakubcabal@gmail.com>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:
--!
--!
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------

architecture behavioral of testbench is

   constant TEST_WIDTH   : integer := 16;
   constant STATUS_WIDTH : integer := 4;
   constant clkper_rd    : time    := 3 ns;
   constant clkper_wr    : time    := 8 ns;

   signal clk_rd   : std_logic;
   signal clk_wr   : std_logic;
   signal rst_rd   : std_logic;
   signal rst_wr   : std_logic;
   signal wr       : std_logic;
   signal di       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal full     : std_logic;
   signal empty    : std_logic;
   signal lstblk   : std_logic;
   signal rd       : std_logic;
   signal do       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal status   : std_logic_vector(STATUS_WIDTH - 1 downto 0);

--! ----------------------------------------------------------------------------
--!                     Architecture body
--! ----------------------------------------------------------------------------

begin

   uut : entity work.asfifo
   generic map(
      ITEMS        => 16,
      DATA_WIDTH   => TEST_WIDTH,
      STATUS_WIDTH => STATUS_WIDTH
   )
   port map(

      --! Write interface
      CLK_WR   => clk_wr,
      RST_WR   => rst_wr,
      WR       => wr,
      DI       => di,
      FULL     => full,
      STATUS   => status,

      --! Read interface
      CLK_RD   => clk_rd,
      RST_RD   => rst_rd,
      RD       => rd,
      DO       => do,
      EMPTY    => empty
   );

   --! ----------------------------------------------------
   --! CLK clock generator

   clk_wr_p: process
      begin
      clk_wr <= '1';
      wait for clkper_wr/2;
      clk_wr <= '0';
      wait for clkper_wr/2;
   end process;

   clk_rd_p: process
   begin
      clk_rd <= '1';
      wait for clkper_rd/2;
      clk_rd <= '0';
      wait for clkper_rd/2;
   end process;

   reset_p: process
   begin
      rst_wr <= '1';
      rst_rd <= '1';
      wait for 100 ns;
      rst_wr <= '0';
      rst_rd <= '0';
      wait;
   end process;

   --! ----------------------------------------------------------------------------
   --!                         Main testbench process
   --! ----------------------------------------------------------------------------

   tb_rd : process
   begin
      rd <= '0';
      wait for 37 ns;
      wait until (clk_rd'event and clk_rd='1' and rst_rd='0' and empty='0');
      for i in 1 to 40 loop
         wait for clkper_rd/4;
         rd    <= '1';
         wait until (clk_rd'event and clk_rd='1' and rst_rd='0' and empty='0');
         rd    <= '0';
      end loop;
      wait for 300 ns;
   end process;

   tb_wr : process
   begin
      di <= (others => '0');
      wr <= '0';

      wait until (clk_wr'event and clk_wr='1' and full='0');
      wr <= '1';
      for i in 1 to 20 loop
         di <= conv_std_logic_vector(i, di'length);
         wait until (clk_wr'event and clk_wr='1' and full='0');
      end loop;
      wr <= '0';

      wait for 400 ns;
      wait until (clk_wr'event and clk_wr='1' and full='0');
      wr <= '1';
      for i in 21 to 60 loop
         di <= conv_std_logic_vector(i, di'length);
         wait until (clk_wr'event and clk_wr='1' and full='0');
      end loop;
      wr <= '0';

      wait;
   end process;

   --! ----------------------------------------------------------------------------

end architecture behavioral;
