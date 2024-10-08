-- testbench.vhd: I2C slave MI32 controller testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <Pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RESET_TIME     : time      := 10*CLKPER + 1 ns;

constant BYTE_TIME      : time      := 600*CLKPER;

signal clk           : std_logic;
signal reset         : std_logic;

signal dwr   : std_logic_vector(31 downto 0);
signal addr  : std_logic_vector(31 downto 0);
signal rd    : std_logic;
signal wr    : std_logic;
signal be    : std_logic_vector( 3 downto 0);
signal drd   : std_logic_vector(31 downto 0);
signal ardy  : std_logic;
signal drdy  : std_logic;

signal scl_i   : std_logic;  -- i2c clock line input
signal scl_o   : std_logic; -- i2c clock line output
signal scl_oen : std_logic; -- i2c clock line output enable, active low
signal sda_i   : std_logic;  -- i2c data line input
signal sda_o   : std_logic; -- i2c data line output
signal sda_oen : std_logic;  -- i2c data line output enable, active low

signal master_scl_i   : std_logic;  -- i2c clock line input
signal master_scl_o   : std_logic; -- i2c clock line output
signal master_scl_oen_o : std_logic; -- i2c clock line output enable, active low
signal master_sda_i   : std_logic;  -- i2c data line input
signal master_sda_o   : std_logic; -- i2c data line output
signal master_sda_oen_o : std_logic;  -- i2c data line output enable, active low

signal master_be  : std_logic_vector( 7 downto 0);
signal master_dwr : std_logic_vector(63 downto 0);
signal master_drd : std_logic_vector(63 downto 0);
signal master_wen : std_logic;	              --
signal master_int : std_logic;

signal tristate_scl : std_logic;
signal tristate_sda : std_logic;

begin

uut: entity work.I2C_SLAVE_TOP
   generic map(
      FILTER_LENGTH => 4,
      FILTER_SAMPLING => 2,
      DEV_ADDR    => "1010101"
   )
   port map(
      CLK         => clk,
      RESET       => reset,

      DWR         => dwr,
      ADDR        => addr,
      RD          => rd,
      WR          => wr,
      BE          => be,
      DRD         => drd,
      ARDY        => ardy,
      DRDY        => drdy,

      SCL_I       => scl_i,
      SCL_O       => scl_o,
      SCL_OEN     => scl_oen,
      SDA_I       => sda_i,
      SDA_O       => sda_o,
      SDA_OEN     => sda_oen
   );
tristate_scl <= scl_o when (scl_oen = '0') else 'Z';
tristate_sda <= sda_o when (sda_oen = '0') else 'Z';
scl_i <= '1' when (tristate_scl = 'Z') else tristate_scl;
sda_i <= '1' when (tristate_sda = 'Z') else tristate_sda;

master : entity work.i2c_master_top
   generic map(
      PRER_INIT   => "0000000000001000"
   )
   port map(
      CLK           => CLK,
		RST_SYNC      => RESET,
		RST_ASYNC     => '0',
		-- generic       -- generic
		BE            => master_be,
		DWR           => master_dwr,
		DRD           => master_drd,
		WEN           => master_wen,
		INT           => master_int,
		-- i2c lines     -- i2c lines,
		SCL_PAD_I     => master_scl_i,
		SCL_PAD_O     => master_scl_o,
		SCL_PADOEN_O  => master_scl_oen_o,
		SDA_PAD_I     => master_sda_i,
		SDA_PAD_O     => master_sda_o,
		SDA_PADOEN_O  => master_sda_oen_o
   );
tristate_scl <= master_scl_o when (master_scl_oen_o = '0') else 'Z';
tristate_sda <= master_sda_o when (master_sda_oen_o = '0') else 'Z';
master_scl_i <= '1' when (tristate_scl = 'Z') else tristate_scl;
master_sda_i <= '1' when (tristate_sda = 'Z') else tristate_sda;

clkgen: process
   begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
   end process;

reset_gen : process
   begin
      RESET <= '1';
      wait for RESET_TIME;
      RESET <= '0';
      wait;
   end process reset_gen;

tb_main:process
begin

   drd <= X"00000000";
   ardy <= '0';
   drdy <= '0';

   master_be <= X"00";
   master_dwr <= X"0000000000000000";
   master_wen <= '0';

   wait for RESET_TIME;
   wait for 20*clkper;

   -- Enable master
   master_be <= "00000100";
   master_dwr <= X"00000000" & X"00" & "10000000" & X"0000";
   master_wen <= '1';
   wait for clkper;
   master_wen <= '0';

   wait for 8*clkper;

   -- Set master to send device address and WRITE bit, START
   master_be <= "00110000";
   master_dwr <= X"0000" & "10101010" & "10010000" & X"00000000";
                         -- Data   WR    S  WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   wait for byte_time;

   -- Set master to send address low
   master_be <= "00110000";
   master_dwr <= X"0000" & "10111000" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   wait for byte_time;

   -- Set master to send address high
   master_be <= "00110000";
   master_dwr <= X"0000" & "10111011" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   wait for byte_time;

   -- Set master to send first data byte
   master_be <= "00110000";
   master_dwr <= X"0000" & "00000001" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   -- Reply with ARDY
   wait until wr = '1';
   wait for clkper; ardy <= '1'; wait for clkper; ardy <= '0';

   wait for 50*clkper;

   -- Set master to send second data byte
   master_be <= "00110000";
   master_dwr <= X"0000" & "00000010" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   -- Reply with ARDY
   wait until wr = '1';
   wait for clkper; ardy <= '1'; wait for clkper; ardy <= '0';

   wait for 50*clkper;

   -- Set master to send third data byte
   master_be <= "00110000";
   master_dwr <= X"0000" & "00000011" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   -- Reply with ARDY
   wait until wr = '1';
   wait for clkper; ardy <= '1'; wait for clkper; ardy <= '0';

   wait for 50*clkper;

   -- Set master to send fourth data byte
   master_be <= "00110000";
   master_dwr <= X"0000" & "00000100" & "00010000" & X"00000000";
                         -- Data            WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   -- Reply with ARDY
   wait until wr = '1';
   wait for clkper; ardy <= '1'; wait for clkper; ardy <= '0';

   wait for 50*clkper;

   -- Set master to send fifth data byte, STOP
   master_be <= "00110000";
   master_dwr <= X"0000" & "00000101" & "01010000" & X"00000000";
                         -- Data          P WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';
   -- Reply with ARDY
   wait until wr = '1';
   wait for clkper; ardy <= '1'; wait for clkper; ardy <= '0';

   wait for 150*clkper;

   -- Set master to send device address and READ bit, START
   master_be <= "00110000";
   master_dwr <= X"0000" & "10101011" & "10010000" & X"00000000";
                         -- Data   RD    S  WR
   master_wen <= '1';   wait for clkper;   master_wen <= '0';

   -- Read data at MI32
   wait until rd = '1';
   ardy <= '1';
   drd <= X"01020304"; drdy <= '1' ;
   wait for clkper;
   ardy <= '0';
   --wait for 2*clkper;
   --wait for clkper;
   drdy <= '0';

   wait for 50*clkper;

   -- Set master to recieve first byte
   master_be <= "00010000";
   master_dwr <= X"0000" & X"00" & "00100000" & X"00000000";
               --          Data       R Ack
   master_wen <= '1';   wait for clkper;   master_wen <= '0';

   -- Read data at MI32
   wait until rd = '1';
   ardy <= '1'; wait for clkper; ardy <= '0';
   wait for 2*clkper; drd <= X"11121314"; drdy <= '1';
   wait for clkper; drdy <= '0';

   wait for 50*clkper;
   -- Set master to recieve second byte, STOP
   master_be <= "00010000";
   master_dwr <= X"0000" & X"00" & "01101000" & X"00000000";
               --          Data      PR NAck
   master_wen <= '1';   wait for clkper;   master_wen <= '0';

   wait for byte_time;


   wait;
end process;


end;
