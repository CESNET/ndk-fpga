-- Copyright (C) 2016 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of EXTRACT_4B_VER is
   signal in_src_rdy  : std_logic;
   signal out_src_rdy : std_logic;
   signal in_dst_rdy  : std_logic;
   signal out_dst_rdy : std_logic;
   signal out_data    : std_logic_vector((8*4)-1 downto 0);

   signal in_fifo_wtite  : std_logic;
   signal out_fifo_wtite : std_logic;
   signal in_fifo_empty  : std_logic;
   signal out_fifo_empty : std_logic;
   signal fifo_read      : std_logic;
begin

   in_src_rdy <= RX_SRC_RDY;
   RX_DST_RDY <= in_dst_rdy;
   EXTRACT_4B_inst: entity work.EXTRACT_4B
   generic map(
      OFFSET_WIDTH => 10
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      OFFSET      => OFFSET,
      RX_DATA     => RX_DATA,
      RX_SOP_POS  => RX_SOP_POS,
      RX_EOP_POS  => RX_EOP_POS,
      RX_SOP      => RX_SOP,
      RX_EOP      => RX_EOP,
      RX_SRC_RDY  => in_src_rdy,
      RX_DST_RDY  => in_dst_rdy,

      TX_DATA     => out_data,
      TX_SRC_RDY  => out_src_rdy,
      TX_DST_RDY  => out_dst_rdy
   );


   in_fifo_wtite <= RX_EOP and in_src_rdy and in_dst_rdy;
   in_fifo : entity work.fifo
   generic map(
      STATUS_ENABLED => false,
      ITEMS          => 64,
      BLOCK_SIZE     => 0,
      DATA_WIDTH     => 1
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      DATA_IN(0)  => '1',
      WRITE_REQ   => in_fifo_wtite,
      FULL        => open,
      DATA_OUT    => open,
      READ_REQ    => fifo_read,
      EMPTY       => in_fifo_empty
   );

   out_dst_rdy    <= TX_DST_RDY;
   out_fifo_wtite <= out_src_rdy and out_dst_rdy;
   out_fifo : entity work.fifo
   generic map(
      STATUS_ENABLED => false,
      ITEMS          => 64,
      BLOCK_SIZE     => 0,
      DATA_WIDTH     => 8*4
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      DATA_IN     => out_data,
      WRITE_REQ   => out_fifo_wtite,
      FULL        => open,
      DATA_OUT    => TX_DATA,
      READ_REQ    => fifo_read,
      EMPTY       => out_fifo_empty
   );

   TX_SRC_RDY <= not out_fifo_empty and not in_fifo_empty;
   fifo_read  <= not out_fifo_empty and not in_fifo_empty and TX_DST_RDY;

   TX_EOP <= '1';
   TX_SOP <= '1';
   TX_EOP_POS <= (others => '1');
   TX_SOP_POS <= (others => '0');
end architecture;
