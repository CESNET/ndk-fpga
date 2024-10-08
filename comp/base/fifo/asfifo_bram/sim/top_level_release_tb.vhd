--!
--! testbench.vhd: Testbench of top level entity
--! Copyright (C) 2003 CESNET
--! Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--!            Jakub Cabal    <jakubcabal@gmail.com>
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
   signal reset    : std_logic;
   signal wr       : std_logic;
   signal di       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal full     : std_logic;
   signal empty    : std_logic;
   signal mark     : std_logic;
   signal release  : std_logic;
   signal lstblk   : std_logic;
   signal rd       : std_logic;
   signal do       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal dv       : std_logic;
   signal status   : std_logic_vector(STATUS_WIDTH - 1 downto 0);

--! ----------------------------------------------------------------------------
--!                      Architecture body
--! ----------------------------------------------------------------------------

begin

   uut : entity work.asfifo_bram_release
   generic map(
      ITEMS       => 16,
      DATA_WIDTH  => TEST_WIDTH,
      STATUS_WIDTH => STATUS_WIDTH,
      AUTO_PIPELINE => true
   )
   port map(
      --! Write interface
      CLK_WR   => clk_wr,
      RST_WR   => reset,
      WR       => wr,
      DI       => di,
      FULL     => full,
      STATUS   => status,
      MARK     => mark,
      RELEASE  => release,

      --! Read interface
      CLK_RD   => clk_rd,
      RST_RD   => reset,
      RD       => rd,
      DO       => do,
      DO_DV    => dv,
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
      reset <= '1';
      wait for 100 ns;
      reset <= '0';
      wait;
   end process;

   --! ----------------------------------------------------------------------------
   --!                         Main testbench process
   --! ----------------------------------------------------------------------------

   tb : process

      procedure read_n(n  : in integer) is
      begin
         wait until (clk_rd'event and clk_rd='1');
         rd <= '1';
         wait until (clk_rd'event and clk_rd='1');
         wait for (n-1)*clkper_rd;
         rd <= '0';
      end read_n;

      procedure write_n(n  : in integer;
                        bgn : in integer) is
      begin
         wait until (clk_wr'event and clk_wr='1');
         wr <= '1';
         for i in bgn to bgn+n-1 loop
            di <= conv_std_logic_vector(i, di'length);
            wait until (clk_wr'event and clk_wr='1');
         end loop;
         wr <= '0';
      end write_n;

      procedure mark_p is
      begin
         wait until (clk_wr'event and clk_wr='1');
         mark <= '1';
         wait until (clk_wr'event and clk_wr='1');
         mark <= '0';
      end mark_p;

      procedure release_p is
      begin
         wait until (clk_wr'event and clk_wr='1');
         release <= '1';
         wait until (clk_wr'event and clk_wr='1');
         release <= '0';
      end release_p;

   begin
      --! init
      mark <= '0';
      release <= '0';
      di <= (others => '0');
      wr <= '0';
      rd <= '0';
      wait until reset = '0';

      --! start test
      write_n(5,0);
      mark_p;
      write_n(65,5);
      read_n(10);
      write_n(9,70);
      release_p;
      read_n(10);
      mark_p;
      read_n(10);
      write_n(5,10);
      read_n(10);
      mark_p;
      read_n(10);
      write_n(5,15);
      read_n(10);
      release_p;
      read_n(10);

   end process;

end architecture behavioral;
