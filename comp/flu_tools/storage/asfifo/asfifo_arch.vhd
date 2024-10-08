-- asfifo_arch_full.vhd: Frame Link protocol generic ASFIFO (full archiecture)
-- Copyright (C) 2012 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;

architecture full of FLU_ASFIFO is
-- Constants declaration

-- SOP+EOP
constant JUICE_WIDTH   : integer := 2;
constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
--                              DATA       EOP_POS       SOP_POS       FLU_JUICE
constant MEM_WIDTH : integer := DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+JUICE_WIDTH;

-- Signals declaration
signal sig_full      : std_logic;   -- FIFO is full
signal sig_empty     : std_logic;   -- FIFO is empty
signal sig_status    : std_logic_vector(STATUS_WIDTH-1 downto 0); -- Free items
signal sig_vld       : std_logic;   -- Data valid at the output of the fifo
signal sig_tx_src_rdy:std_logic;
signal sig_rd        : std_logic;   -- Read from FIFO
signal sig_wr        : std_logic;   -- Write to FIFO
signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO
signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO

begin

   --! Read signal generation
   sig_rd      <= TX_DST_RDY;
   --! Write signal generation
   sig_wr      <= RX_SRC_RDY and not sig_full;

   --! Signal TX_SRC_RDY
   sig_tx_src_rdy <= sig_vld;

   --! Data to write
   sig_data_wr <= RX_SOP & RX_EOP & RX_SOP_POS & RX_EOP_POS & RX_DATA;

   DATA_ASFIFO_I:entity work.asfifo_bram
    generic map(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS          => ITEMS,

      -- Data Width
      DATA_WIDTH   => MEM_WIDTH,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
     STATUS_WIDTH    => STATUS_WIDTH,
     AUTO_PIPELINE   => AUTO_PIPELINE
   )
   port map(
      -- Write interface
      CLK_WR      => RX_CLK,
      RST_WR      => RX_RESET,
      WR          => sig_wr,
      DI          => sig_data_wr,
      FULL        => sig_full,
      STATUS      => sig_status,

      -- Read interface
      CLK_RD      => TX_CLK,
      RST_RD      => TX_RESET,
      RD          => sig_rd,
      DO          => sig_data_rd,
      DO_DV       => sig_vld,
      EMPTY       => sig_empty
   );

   --------------------------------------------------------
   --RX signal map
   --------------------------------------------------------
   RX_DST_RDY  <= not(sig_full or RX_RESET);
   RX_STATUS   <= sig_status;

   --------------------------------------------------------
   --TX signal map
   --------------------------------------------------------
   TX_SRC_RDY  <= sig_tx_src_rdy;
   TX_DATA     <= sig_data_rd(DATA_WIDTH-1 downto 0);
   TX_EOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH-1 downto DATA_WIDTH);
   TX_SOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH-1 downto DATA_WIDTH+EOP_POS_WIDTH);
   TX_EOP      <= sig_data_rd(MEM_WIDTH-2);
   TX_SOP      <= sig_data_rd(MEM_WIDTH-1);

end architecture full;
