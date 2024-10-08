-- testbench.vhd: Testbench of distrib entity
-- Copyright (C) 2014 CESNET
-- Author(s): Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   --FrameLinkUnaligned generics
   constant DATA_WIDTH     : integer := 256;
   constant SOP_POS_WIDTH  : integer := 2;

   --Time constants
	constant CLKPER         : time := 10 ns;
	constant RESET_TIME     : time := 10*CLKPER;

	--clk signals
   signal clk       : std_logic;
   signal reset     : std_logic;

	-- Signals ---------------------------------------
   -- Input interface
   signal rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal rx_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal rx_sop        : std_logic;
   signal rx_eop        : std_logic;
   signal rx_src_rdy    : std_logic;
   signal rx_dst_rdy    : std_logic;

   -- Output interface (lane 0)
   signal tx_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_sop_pos0   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal tx_eop_pos0   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal tx_sop0       : std_logic;
   signal tx_eop0       : std_logic;
   signal tx_src_rdy0   : std_logic;
   signal tx_dst_rdy0   : std_logic;

   -- Output interface (lane 1)
   signal tx_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_sop_pos1   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal tx_eop_pos1   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal tx_sop1       : std_logic;
   signal tx_eop1       : std_logic;
   signal tx_src_rdy1   : std_logic;
   signal tx_dst_rdy1   : std_logic;

begin

--------------------------
--	Clocks & Resets
--------------------------
   --User clock generator
   clkgen:process
   begin
      clk <= '1';
      wait for CLKPER/2;
      clk <= '0';
      wait for CLKPER/2;
   end process;

   --Reset generator
   reset_gen : process
   begin
      reset <= '1';
      wait for RESET_TIME;
      wait for 1 ns;
      reset <= '0';
      wait;
   end process reset_gen;

	-----------
	--	UUT	--
	-----------
   uut:entity work.DISTRIB
      generic map(
          --! FLU protocol generics
          DATA_WIDTH    => DATA_WIDTH,
          SOP_POS_WIDTH => SOP_POS_WIDTH
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => reset,
         CLK            => clk,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA        => rx_data,
         RX_SOP_POS     => rx_sop_pos,
         RX_EOP_POS     => rx_eop_pos,
         RX_SOP         => rx_sop,
         RX_EOP         => rx_eop,
         RX_SRC_RDY     => rx_src_rdy,
         RX_DST_RDY     => rx_dst_rdy,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface (lane 0)
         -- --------------------------------------------------
         TX_DATA0       => tx_data0,
         TX_SOP_POS0    => tx_sop_pos0,
         TX_EOP_POS0    => tx_eop_pos0,
         TX_SOP0        => tx_sop0,
         TX_EOP0        => tx_eop0,
         TX_SRC_RDY0    => tx_src_rdy0,
         TX_DST_RDY0    => tx_dst_rdy0,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface (lane 1)
         -- --------------------------------------------------
         TX_DATA1       => tx_data1,
         TX_SOP_POS1    => tx_sop_pos1,
         TX_EOP_POS1    => tx_eop_pos1,
         TX_SOP1        => tx_sop1,
         TX_EOP1        => tx_eop1,
         TX_SRC_RDY1    => tx_src_rdy1,
         TX_DST_RDY1    => tx_dst_rdy1
      );

	-----------------
	--	Testbench	--
	-----------------
   --MI32 simulatiuon
   tb:process
   begin
      -- Default signal values
      rx_data     <= (others=>'0');
      rx_sop_pos  <= (others=>'0');
      rx_eop_pos  <= (others=>'0');
      rx_sop      <= '0';
      rx_eop      <= '0';
      rx_src_rdy  <= '0';

      tx_dst_rdy0 <= '0';
      tx_dst_rdy1 <= '0';

      wait until reset = '0';

      --1] One frame without waiting (both outputs ready
      tx_dst_rdy0 <= '1';
      tx_dst_rdy1 <= '1';
         --First packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "01";
      rx_sop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "00";
      rx_eop_pos  <= (others=>'1');
      rx_sop      <= '0';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
         --Second packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "01";
      rx_sop      <= '1';
      rx_eop      <= '0';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "00";
      rx_eop_pos  <= (others=>'1');
      rx_sop      <= '0';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
         --Third short packet
      rx_data <= x"BBBBBBBBBBBBBBBBAAAAAAAAAAAAAAAA99999999999999998888888888888888";
      rx_sop_pos  <= "11";
      rx_eop_pos  <= (others=>'1');
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_src_rdy  <= '0';
      rx_sop      <= '0';
      rx_eop      <= '0';
      wait for 10*CLKPER;

      --2] Transfer with shared word
         --First packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "00";
      rx_sop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop   <= '0';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "10";
      rx_eop_pos  <= conv_std_logic_vector(8,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
         --Second packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "11";
      rx_eop_pos  <= conv_std_logic_vector(20,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop   <= '0';
      rx_eop   <= '0';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "01";
      rx_eop_pos  <= conv_std_logic_vector(6,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop   <= '0';
      rx_eop   <= '0';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "00";
      rx_eop_pos  <= (others=>'1');
      rx_sop      <= '0';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_eop      <= '0';
      rx_src_rdy  <= '0';
      rx_eop_pos  <= (others=>'0');
      rx_sop_pos  <= (others=>'0');
      wait for 10*CLKPER;

      --3] Transfer with shared word + waiting in and after frames
         --First packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "00";
      rx_sop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop      <= '0';
      rx_src_rdy  <= '0';
      wait for 2*CLKPER;
      rx_src_rdy  <= '1';
      tx_dst_rdy0 <= '0';
      wait for 5*CLKPER;
      tx_dst_rdy0 <= '1';
      tx_dst_rdy1 <= '0';
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "10";
      rx_eop_pos  <= conv_std_logic_vector(8,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      tx_dst_rdy1 <= '1';
      wait for CLKPER;
         --Second packet
      rx_data <= x"3333333333333333222222222222222211111111111111110000000000000000";
      rx_sop_pos  <= "11";
      rx_eop_pos  <= conv_std_logic_vector(20,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop   <= '0';
      rx_eop   <= '0';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "01";
      rx_eop_pos  <= conv_std_logic_vector(6,log2(DATA_WIDTH/8));
      rx_sop      <= '1';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_data  <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop   <= '0';
      rx_eop   <= '0';
      wait for CLKPER;
      rx_data <= x"7777777777777777666666666666666655555555555555554444444444444444";
      rx_sop_pos  <= "00";
      rx_eop_pos  <= (others=>'1');
      rx_sop      <= '0';
      rx_eop      <= '1';
      rx_src_rdy  <= '1';
      wait for CLKPER;
      rx_eop      <= '0';
      rx_src_rdy  <= '0';
      rx_eop_pos  <= (others=>'0');
      rx_sop_pos  <= (others=>'0');



      wait;
   end process;

end architecture behavioral;
