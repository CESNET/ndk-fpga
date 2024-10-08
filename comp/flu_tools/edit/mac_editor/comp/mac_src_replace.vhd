-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity SRC_REPLACE is
   generic(
      DATA_WIDTH 	   : integer := 512;
      --support <4
      SOP_POS_WIDTH 	: integer := 3
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      --! Frame Link Unaligned input interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in std_logic;
      RX_EOP         : in std_logic;
      RX_SRC_RDY     : in std_logic;
      RX_DST_RDY     : out std_logic;

      --! Frame Link Unaligned output interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic;

      MAC_W          : in  std_logic;
      MAC_DATA       : in  std_logic_vector(6*8-1 downto 0);
      MAC_MASK       : in  std_logic_vector(6-1 downto 0)
   );
end entity;

architecture full of SRC_REPLACE is
   constant block_width : integer := (DATA_WIDTH) / (2**SOP_POS_WIDTH);
   constant num_blocks  : integer := 2**SOP_POS_WIDTH;

   signal demux_in      : std_logic;
   signal sel_block     : std_logic_vector(num_blocks-1 downto 0);
begin

   TX_SOP_POS  <= RX_SOP_POS;
   TX_EOP_POS  <= RX_EOP_POS;
   TX_SOP      <= RX_SOP;
   TX_EOP      <= RX_EOP;
   TX_SRC_RDY  <= RX_SRC_RDY;
   RX_DST_RDY  <= TX_DST_RDY;

   demux_in <= MAC_W and RX_SOP;
   DEMUX_i : entity work.GEN_DEMUX
   generic map(
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => num_blocks
   )
   port map(
      DATA_IN(0)  => demux_in,
      SEL         => RX_SOP_POS,
      DATA_OUT    => sel_block
   );

   gen_sop_others : if(DATA_WIDTH / (2**SOP_POS_WIDTH) > 64) generate
      gne_muxs : for I in 0 to num_blocks-1 generate
         signal in_block   : std_logic_vector(block_width-1 downto 0);
         signal out_block  : std_logic_vector(block_width-1 downto 0);
      begin
         in_block <= RX_DATA(block_width*(I+1)-1 downto block_width*I);
         out_block(block_width-1 downto 8*12) <= in_block(block_width-1 downto 8*12);
         out_block(8*6-1 downto 0) <= in_block(8*6-1 downto 0);
         TX_DATA(block_width*(I+1)-1 downto block_width*I) <= out_block;

         MAC_REPLACE_i : entity work.MAC_REPLACE
         port map (
            CLK            => CLK,
            RESET          => RESET,

            MAC_W          => sel_block(I),
            MAC_DATA       => MAC_DATA,
            MAC_MASK       => MAC_MASK,

            DATA_IN        => in_block(8*12-1 downto 8*6),
            DATA_OUT       => out_block(8*12-1 downto 8*6)
         );
      end generate;
   end generate;

   gen_sop_3 : if(DATA_WIDTH / (2**SOP_POS_WIDTH) = 64) generate
      signal last_two_bytes_in  : std_logic_vector(8*2-1 downto 0);
      signal last_two_bytes_out : std_logic_vector(8*2-1 downto 0);

      signal pipe_mac_mask      : std_logic_vector(4-1 downto 0);
      signal pipe_mac           : std_logic_vector(4*8-1 downto 0);
      signal pipe_sel_block     : std_logic;
   begin

      gne_muxs : for I in 0 to num_blocks-2 generate
         signal in_block   : std_logic_vector(block_width-1 downto 0);
         signal out_block  : std_logic_vector(block_width-1 downto 0);
      begin
         in_block <= RX_DATA(block_width*(I+1)+(6*8)-1 downto block_width*I+(6*8));
         out_block(block_width-1 downto 8*6) <= in_block(block_width-1 downto 8*6);
         TX_DATA(block_width*(I+1)+(6*8)-1 downto block_width*I+(6*8)) <= out_block;

         MAC_REPLACE_i : entity work.MAC_REPLACE
         port map (
            CLK            => CLK,
            RESET          => RESET,

            MAC_W          => sel_block(I),
            MAC_DATA       => MAC_DATA,
            MAC_MASK       => MAC_MASK,

            DATA_IN        => in_block(8*6-1 downto 0),
            DATA_OUT       => out_block(8*6-1 downto 0)
         );
      end generate;

      last_two_bytes_in <= RX_DATA(DATA_WIDTH-1 downto DATA_WIDTH-16);
      TX_DATA(DATA_WIDTH-1 downto DATA_WIDTH-16) <= last_two_bytes_out;

      gne_mux_last_two : for I in 0 to 1 generate
         signal mux_in1 : std_logic_vector(7 downto 0);
         signal mux_in2 : std_logic_vector(7 downto 0);
         signal mux_out : std_logic_vector(7 downto 0);
      begin
         mux_in1 <= last_two_bytes_in(8*(I+1)-1 downto 8*I);
         mux_in2 <= MAC_DATA(8*(I+1)-1 downto 8*I);

         last_two_bytes_out(8*(I+1)-1 downto 8*I) <= mux_in2 when MAC_MASK(I) = '1' and
                                                                  sel_block(sel_block'length-1) = '1'
                                                     else mux_in1;
      end generate;

      process(CLK)
      begin
         if (CLK'event) and (CLK='1') then
            if(RESET = '1') then
               pipe_sel_block <= '0';
            elsif(RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
               pipe_mac_mask  <= MAC_MASK(6-1 downto 2);
               pipe_mac       <= MAC_DATA(8*6-1 downto 8*2);
               pipe_sel_block <= sel_block(sel_block'length-1);
            end if;
         end if;
      end process;

      gne_mux_last_four : for I in 0 to 3 generate
         signal mux_in1 : std_logic_vector(7 downto 0);
         signal mux_in2 : std_logic_vector(7 downto 0);
         signal mux_out : std_logic_vector(7 downto 0);
      begin
         mux_in1 <= RX_DATA(8*(I+1)-1 downto 8*I);
         mux_in2 <= pipe_mac(8*(I+1)-1 downto 8*I);

         TX_DATA(8*(I+1)-1 downto 8*I) <= mux_in2 when pipe_mac_mask(I) = '1' and
                                                       pipe_sel_block = '1'
                                                  else mux_in1;
      end generate;
      TX_DATA(8*6-1 downto 8*4) <= RX_DATA(8*6-1 downto 8*4);

   end generate;
end architecture;

