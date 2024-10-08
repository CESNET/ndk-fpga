-- testbench.vhd: I2C slave byte controller testbench file
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

signal clk           : std_logic;
signal reset         : std_logic;

signal cmd      : std_logic_vector(1 downto 0);
signal din      : std_logic_vector(7 downto 0);
signal dev_addr : std_logic_vector(7 downto 0);
signal dev_addr_mask:std_logic_vector(7 downto 0);
signal ack_in   : std_logic;
signal cmd_vld  : std_logic;
signal cmd_rdy  : std_logic;

signal cmd_ack  : std_logic; -- command done
signal ack_out  : std_logic;
signal dout     : std_logic_vector(7 downto 0);

signal start    : std_logic;
signal stop     : std_logic;

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

constant I2C_ACCEPT_BYTE      : std_logic_vector(1 downto 0) := "01";
constant I2C_REPLY_BYTE       : std_logic_vector(1 downto 0) := "10";

begin

uut: entity work.I2C_SLAVE_BYTE_CTRL
   port map(
      CLK         => clk,
      RESET       => reset,

      CMD         => cmd,
      DIN         => din,
      DEV_ADDR    => dev_addr,
      DEV_ADDR_MASK=>dev_addr_mask,
      ACK_IN      => ack_in,
      CMD_VLD     => cmd_vld,
      CMD_RDY     => cmd_rdy,

      CMD_ACK     => cmd_ack,
      ACK_OUT     => ack_out,
      DOUT        => dout,

      START       => start,
      STOP        => stop,

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
   cmd <= I2C_ACCEPT_BYTE;
   cmd_vld <= '0';
   din <= X"00";
   dev_addr <= X"00";
   dev_addr_mask <= X"00";
   ack_in <= '0';

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

   -- Set master to send device address
   master_be <= "00110000";
   master_dwr <= X"0000" & "10101010" & "10010000" & X"00000000";
                         -- Data   RD    S  WR
   master_wen <= '1';
   wait for clkper;
   master_wen <= '0';

   wait until start = '1';
   wait for 2*clkper + 1 ns;

   -- Set slave to accept device address
   cmd <= I2C_ACCEPT_BYTE;
   dev_addr <= "10101111";
   dev_addr_mask <= "00001111"; -- Four lower bits are masked
   ack_in <= '0'; -- 0 = Acknowledged
   cmd_vld <= '1';
   wait for clkper;
   cmd_vld <= '0';

   wait until cmd_ack = '1';
   wait for 100*clkper;

   -- Set slave to reply some data
   cmd <= I2C_REPLY_BYTE;
   din <= X"55";
   cmd_vld <= '1';
   wait for clkper;
   cmd_vld <= '0';
   wait for clkper;

   wait for 100*clkper;

   -- Set master to recieve one byte
   master_be <= "00010000";
   master_dwr <= X"0000" & X"00" & "01100000" & X"00000000";
               --         Data      PR  Nack
   master_wen <= '1';
   wait for clkper;
   master_wen <= '0';



   wait;
end process;


end;
