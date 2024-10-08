-- fifo_arch_full.vhd: Frame Link protocol generic FIFO (full archiecture)
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
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

architecture full of FLU_FIFO is
-- Constants declaration

-- SOP+EOP
constant JUICE_WIDTH   : integer := 2;
constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
--                              DATA       EOP_POS       SOP_POS       FLU_JUICE
constant MEM_WIDTH : integer := DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+JUICE_WIDTH;

-- Signals declaration
signal sig_full      : std_logic;   -- FIFO is full
signal sig_empty     : std_logic;   -- FIFO is empty
signal sig_status    : std_logic_vector(log2(ITEMS) downto 0); -- Free items
signal sig_vld       : std_logic;   -- Data valid at the output of the fifo
signal sig_tx_src_rdy:std_logic;
signal sig_rd        : std_logic;   -- Read from FIFO
signal sig_wr        : std_logic;   -- Write to FIFO
signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO
signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO

signal sig_sop_rd    : std_logic;   -- Start of packet at the output

signal cnt_frame     : std_logic_vector(log2(ITEMS)downto 0);
signal sig_frame_rdy : std_logic;

begin

sig_rd      <= TX_DST_RDY or not sig_vld;
sig_wr      <= RX_SRC_RDY and not sig_full;

sig_tx_src_rdy <= sig_vld;

sig_data_wr <= RX_SOP & RX_EOP & RX_SOP_POS & RX_EOP_POS & RX_DATA;


bram_cond: if USE_BRAMS = true generate   -- use BlockRAMs
   fifo_inst: entity work.fifo_bram
   generic map(
      STATUS_ENABLED => STATUS_WIDTH > 0,
      ITEMS       => ITEMS,
      BLOCK_SIZE  => BLOCK_SIZE,
      DATA_WIDTH  => MEM_WIDTH,
      DO_REG      => OUTPUT_REG,
      AUTO_PIPELINE => true
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      DI          => sig_data_wr,
      WR          => sig_wr,
      FULL        => sig_full,
      LSTBLK      => LSTBLK,
      STATUS      => sig_status,

      -- Read interface
      DO          => sig_data_rd,
      RD          => sig_rd,
      EMPTY       => sig_empty,
      DV          => sig_vld
   );
end generate;

dist_cond: if USE_BRAMS = false generate  -- use SelectRAMs
   fifo_inst: entity work.fifo
   generic map(
      STATUS_ENABLED => STATUS_WIDTH > 0,
      ITEMS          => ITEMS,
      BLOCK_SIZE     => BLOCK_SIZE,
      DATA_WIDTH     => MEM_WIDTH,
      DO_REG         => OUTPUT_REG
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      DATA_IN     => sig_data_wr,
      WRITE_REQ   => sig_wr,
      FULL        => sig_full,
      LSTBLK      => LSTBLK,
      STATUS      => sig_status,

      -- Read interface
      DATA_OUT    => sig_data_rd,
      READ_REQ    => sig_rd,
      EMPTY       => sig_empty
   );

   sig_vld <= not sig_empty;
end generate;

-- This up-down counter keeps information about number of whole frames.
-- It starts at the value 1, because if one frame is not fully written
-- and it is allready being read, this counter goes to 0.
cnt_frame_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         cnt_frame <= conv_std_logic_vector(1, cnt_frame'length);
      elsif sig_full = '0' and RX_SRC_RDY = '1' and RX_EOP = '1' then
         -- Frame end is written
         if sig_tx_src_rdy = '1' and TX_DST_RDY = '1' and sig_sop_rd= '1' then
            -- Frame start is read and end is written - no change
            cnt_frame <= cnt_frame;
         else
            -- Frame start is not read and end is written - increment counter
            cnt_frame <= cnt_frame + 1;
         end if;
      else
         if sig_tx_src_rdy = '1' and TX_DST_RDY = '1' and sig_sop_rd = '1' then
            -- Frame start is read and end is not written - decrement counter
            cnt_frame <= cnt_frame - 1;
         end if;
      end if;
   end if;
end process;
sig_sop_rd  <= sig_data_rd(MEM_WIDTH-1);
sig_frame_rdy <= '0' when (cnt_frame = 0) or (cnt_frame = 1) else
                 '1';

RX_DST_RDY  <= not(sig_full or RESET);
TX_SRC_RDY  <= sig_tx_src_rdy;

TX_DATA     <= sig_data_rd(DATA_WIDTH-1 downto 0);
TX_EOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH-1 downto DATA_WIDTH);
TX_SOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH-1 downto DATA_WIDTH+EOP_POS_WIDTH);
TX_EOP      <= sig_data_rd(MEM_WIDTH-2);
TX_SOP      <= sig_data_rd(MEM_WIDTH-1);

EMPTY    <= sig_empty;
FULL     <= sig_full;
STATUS   <= sig_status(log2(ITEMS) downto log2(ITEMS)-STATUS_WIDTH+1);
FRAME_RDY<= sig_frame_rdy;
end architecture full;
