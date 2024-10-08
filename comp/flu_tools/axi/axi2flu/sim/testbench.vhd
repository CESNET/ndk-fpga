-- Copyright (C) 2014 CESNET
-- Author(s): Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.math_pack.all;

entity testbench is
end entity testbench;

architecture behavioral of testbench is

   -- Simulation constants
	constant DATA_WIDTH	    : integer := 256;
   constant SOP_POS_WIDTH   : integer := 5;
   constant IN_PIPE_EN      : boolean := false;
   constant IN_PIPE_OUTREG  : boolean := false;
   constant OUT_PIPE_EN     : boolean := false;
   constant OUT_PIPE_OUTREG : boolean := false;
   constant clkper          : time    := 8 ns;              --Clock period
   constant reset_time      : time    := 10*clkper + 1 ns;  --Reset duration


   -- common interface
   signal   CLK           : std_logic;
   signal   RESET         : std_logic;

	--AXI input interface
   signal   RX_TDATA      :  std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   RX_TKEEP      :  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
   signal   RX_TVALID     :  std_logic;
	signal   RX_TLAST      :  std_logic;
	signal   RX_TREADY     :  std_logic;

   -- Frame Link Unaligned output interface
	signal   TX_DATA       :  std_logic_vector(DATA_WIDTH-1 downto 0);
	signal   TX_SOP_POS    :  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
	signal   TX_EOP_POS    :  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
	signal   TX_SOP        :  std_logic;
	signal   TX_EOP        :  std_logic;
	signal   TX_SRC_RDY    :  std_logic;
	signal   TX_DST_RDY    :  std_logic;


begin
   UUT :  entity work.axi2flu
   generic map (
      DATA_WIDTH      => DATA_WIDTH,
      SOP_POS_WIDTH   => SOP_POS_WIDTH,
      IN_PIPE_EN      => IN_PIPE_EN,
      IN_PIPE_OUTREG  => IN_PIPE_OUTREG,
      OUT_PIPE_EN     => OUT_PIPE_EN,
      OUT_PIPE_OUTREG => OUT_PIPE_OUTREG
   )
   port map (
      -- common interface
      CLK           =>   CLK,
      RESET         =>   RESET,

      -- AXI input interface
      RX_TDATA      =>   RX_TDATA,
	   RX_TKEEP      =>   RX_TKEEP,
	   RX_TVALID     =>   RX_TVALID,
	   RX_TLAST      =>   RX_TLAST,
	   RX_TREADY     =>   RX_TREADY,

      -- Frame Link Unaligned output interface
	   TX_DATA       =>   TX_DATA,
	   TX_SOP_POS    =>   TX_SOP_POS,
	   TX_EOP_POS    =>   TX_EOP_POS,
	   TX_SOP        =>   TX_SOP,
	   TX_EOP        =>   TX_EOP,
	   TX_SRC_RDY    =>   TX_SRC_RDY,
	   TX_DST_RDY    =>   TX_DST_RDY
   );

   --Generate clock
   clk_gen : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen;

    --Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   -- Simulating input flow
   input_flow : process
   begin

      -- Initialize input interface
      RX_TVALID   <= '0';
      RX_TLAST    <= '0';
      TX_DST_RDY  <= '0';
      RX_TDATA    <= conv_std_logic_vector(0, DATA_WIDTH);
      RX_TKEEP    <= (others => '1');

      wait for reset_time;
      wait for 10*clkper;

      -- Generate some packets
      RX_TVALID  <= '1';
      wait for clkper;

      TX_DST_RDY <= '1';
      RX_TDATA   <= conv_std_logic_vector(1, DATA_WIDTH);
      RX_TKEEP   <= ((DATA_WIDTH/8)-1 downto 4 => '1') & (3 downto 0 => '0');
      wait for clkper;

      RX_TVALID  <= '0';
      TX_DST_RDY <= '0';
      wait for 5*clkper;

      RX_TVALID  <= '1';
      TX_DST_RDY <= '1';
      RX_TDATA 	 <= conv_std_logic_vector(2, DATA_WIDTH);
      wait for clkper;

      RX_TVALID  <= '0';
      TX_DST_RDY <= '0';
      wait for 5*clkper;

      RX_TVALID  <= '1';
      TX_DST_RDY <= '1';
      RX_TLAST   <= '1';
      RX_TKEEP   <= ((DATA_WIDTH/8)-1 downto 20  => '1')&(19 downto 10 => '0')&(9 downto 0 => '1');
      RX_TDATA   <= conv_std_logic_vector(3, DATA_WIDTH);
      wait for clkper;

      RX_TVALID  <= '0';
      TX_DST_RDY <= '0';
      RX_TLAST   <= '0';
      wait for 5*clkper;

      RX_TVALID  <= '1';
      TX_DST_RDY <= '1';
      RX_TLAST   <= '1';
      RX_TKEEP    <= (others => '1');
      RX_TDATA   <= conv_std_logic_vector(4, DATA_WIDTH);
      wait for clkper;

      RX_TVALID  <= '0';
      TX_DST_RDY <= '0';
      RX_TLAST   <= '0';
      wait for 5*clkper;

      RX_TVALID  <= '1';
      TX_DST_RDY <= '1';
      RX_TLAST   <= '1';
      RX_TKEEP   <= ((DATA_WIDTH/8)-1 downto 20  => '0')&(19 downto 10 => '1')&(9 downto 0 => '0');
      RX_TDATA   <= conv_std_logic_vector(5, DATA_WIDTH);
      wait for clkper;

      RX_TVALID  <= '0';
      TX_DST_RDY <= '0';
      RX_TLAST   <= '0';
      wait;

   end process input_flow;

end architecture;
