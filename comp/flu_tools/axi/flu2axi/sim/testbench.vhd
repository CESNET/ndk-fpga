-- testbench.vhd: Testbench for flu2axi
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

   --! Simulation constants
   constant DATA_WIDTH     : integer := 256;
   constant SOP_POS_WIDTH  : integer := 3;
   constant IN_PIPE_EN     : boolean := false;
   constant IN_PIPE_OUTREG : boolean := false;
   constant OUT_PIPE_EN    : boolean := false;
   constant OUT_PIPE_OUTREG: boolean := false;
   constant clkper         : time    := 8 ns;              --Clock period
   constant reset_time     : time    := 10*clkper + 1 ns;  --Reset duration

   --! Common interface
   signal   CLK           : std_logic;
   signal   RESET         : std_logic;

   --! Frame Link Unaligned input interface
   signal   RX_DATA       :  std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   RX_SOP_POS    :  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal   RX_EOP_POS    :  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal   RX_SOP        :  std_logic;
   signal   RX_EOP        :  std_logic;
   signal   RX_SRC_RDY    :  std_logic;
   signal   RX_DST_RDY    :  std_logic;

   --! AXI output interface
   signal  TX_TDATA      :  std_logic_vector(DATA_WIDTH-1 downto 0);
   signal  TX_TKEEP      :  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
   signal  TX_TVALID     :  std_logic;
   signal  TX_TLAST      :  std_logic;
   signal  TX_TREADY     :  std_logic;

begin
   UUT :  entity work.flu2axi
   generic map (DATA_WIDTH => DATA_WIDTH,
                SOP_POS_WIDTH => SOP_POS_WIDTH,
                IN_PIPE_EN => IN_PIPE_EN,
                IN_PIPE_OUTREG => IN_PIPE_OUTREG,
                OUT_PIPE_EN => OUT_PIPE_EN,
                OUT_PIPE_OUTREG => OUT_PIPE_OUTREG
)
   port map (
      --! Common interface
      CLK          =>   CLK,
      RESET        =>   RESET,

      --! Frame Link Unaligned input interface
      RX_DATA       =>   RX_DATA,
      RX_SOP_POS    =>   RX_SOP_POS,
      RX_EOP_POS    =>   RX_EOP_POS,
      RX_SOP        =>   RX_SOP,
      RX_EOP        =>   RX_EOP,
      RX_SRC_RDY    =>   RX_SRC_RDY,
      RX_DST_RDY    =>   RX_DST_RDY,
      --! AXI output interface
      TX_TDATA      =>   TX_TDATA,
      TX_TKEEP      =>   TX_TKEEP,
      TX_TVALID     =>   TX_TVALID,
      TX_TLAST      =>   TX_TLAST,
      TX_TREADY     =>   TX_TREADY
);

   --! Generate clock
   clk_gen : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen;

   --! Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;


   --! Simulating input flow
   input_flow : process
   begin


      --! Initialize input interface
      RX_SOP         <= '0';
      RX_EOP         <= '0';
      RX_SRC_RDY     <= '0';
      TX_TREADY      <= '0';
      RX_DATA        <= conv_std_logic_vector(0, DATA_WIDTH);
      RX_SOP_POS     <= conv_std_logic_vector(0, SOP_POS_WIDTH);
      RX_EOP_POS     <= conv_std_logic_vector(0, log2(DATA_WIDTH/8));

      wait for reset_time;
      wait for 10*clkper;


      --! Generate some packets
      wait for clkper;
      RX_SRC_RDY <= '1';
      TX_TREADY  <= '1';
      RX_SOP     <= '1';
      RX_SOP_POS <= conv_std_logic_vector(1, SOP_POS_WIDTH);
      RX_DATA    <= conv_std_logic_vector(1, DATA_WIDTH);
      wait for clkper;

      RX_SRC_RDY <= '0';
      TX_TREADY  <= '0';
      RX_SOP     <= '0';
      RX_EOP     <= '0';
      wait for 5*clkper;

      RX_SRC_RDY <= '1';
      TX_TREADY  <= '1';
      RX_SOP     <= '1';
      RX_EOP     <= '1';
      RX_SOP_POS <= conv_std_logic_vector(4, SOP_POS_WIDTH);
      RX_EOP_POS <= conv_std_logic_vector(8, log2(DATA_WIDTH/8));
      RX_DATA    <= conv_std_logic_vector(2, DATA_WIDTH);
      wait for clkper;

      RX_SRC_RDY <= '0';
      TX_TREADY  <= '0';
      RX_SOP     <= '0';
      RX_EOP     <= '0';
      wait for  5*clkper;

      RX_SRC_RDY <= '1';
      TX_TREADY  <= '1';
      RX_EOP     <= '1';
      RX_EOP_POS <= conv_std_logic_vector(4, log2(DATA_WIDTH/8));
      RX_DATA    <= conv_std_logic_vector(3, DATA_WIDTH);
      wait for clkper;

      RX_SRC_RDY <= '0';
      TX_TREADY  <= '0';
      RX_EOP     <= '0';
      wait for  5*clkper;

      RX_SRC_RDY <= '1';
      TX_TREADY  <= '1';
      RX_SOP     <= '1';
      RX_EOP     <= '1';
      RX_SOP_POS <= conv_std_logic_vector(2, SOP_POS_WIDTH);
      RX_EOP_POS <= conv_std_logic_vector(20, log2(DATA_WIDTH/8));
      RX_DATA    <= conv_std_logic_vector(4, DATA_WIDTH);
      wait for clkper;

      RX_SRC_RDY <= '0';
      TX_TREADY  <= '0';
      RX_SOP     <= '0';
      RX_EOP     <= '0';
      wait;

   end process input_flow;

end architecture;
