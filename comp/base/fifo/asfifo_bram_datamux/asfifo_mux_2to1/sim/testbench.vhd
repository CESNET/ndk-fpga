-- testbench.vhd: Testbench
-- Copyright (C) 2014 CESNET
-- Author(s): Viktor Pus <pus@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH   : integer := 512;
   constant clkper_rd    : time    := 8 ns;
   constant clkper_wr    : time    := 2 ns;

   signal clk_wr   : std_logic;
   signal rst_wr   : std_logic;
   signal di       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal wr       : std_logic;
   signal wr_h     : std_logic;
   signal full     : std_logic;
   signal afull    : std_logic;
   signal clk_rd   : std_logic;
   signal rst_rd   : std_logic;
   signal do       : std_logic_vector(TEST_WIDTH/2 - 1 downto 0);
   signal rd       : std_logic;
   signal do_vld   : std_logic;
   signal aempty   : std_logic;
   signal empty    : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.ASFIFO_MUX_2TO1
port map(
   -- Write interface
   CLK_WR   => clk_wr,
   RST_WR   => rst_wr,
   DI       => di,
   WR       => wr,
   WR_H     => wr_h,
   AFULL    => afull,
   FULL     => full,

   -- Read interface
   CLK_RD   => clk_rd,
   RST_RD   => rst_rd,
   DO       => do,
   DO_VLD   => do_vld,
   RD       => rd,
   AEMPTY   => aempty,
   EMPTY    => empty
);

-- ----------------------------------------------------
-- CLK clock generator
wr_h <= '1';
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

rst_wr_p: process
begin
   rst_wr <= '1';
   wait for 10*clkper_wr;
   wait for 1 ns;
   rst_wr <= '0';
   wait;
end process;

rst_rd_p: process
begin
   rst_rd <= '1';
   wait for 10*clkper_rd;
   wait for 1 ns;
   rst_rd <= '0';
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb_rd : process
begin
   rd <= '0';
   wait for 37 ns;
   wait until (clk_rd'event and clk_rd='1' and rst_rd='0');
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
   wr_h <='1';
   di <= (others => '0');
   wr <= '0';
   wait until (clk_wr'event and clk_wr='1' and rst_wr='0');
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

-- ----------------------------------------------------------------------------
end architecture behavioral;
