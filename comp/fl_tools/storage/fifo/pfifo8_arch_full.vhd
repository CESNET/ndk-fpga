-- pfifo8_arch_full.vhd: 8 bit Frame Link protocol generic packet FIFO (full arch)
-- Copyright (C) 2007 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

-- library with get_juice_width function
use work.fl_fifo_pkg.all;

architecture full of FL_PFIFO8 is

component fifo_bram_discard is
   generic(
      -- ITEMS = Numer of items in FIFO
      ITEMS       : integer;

      -- BLOCK_SIZE = Number of items in one block
      BLOCK_SIZE  : integer := 0;

      -- Data Width
      DATA_WIDTH  : integer;

      STATUS_WIDTH: integer := 4;

      -- AUTO_PIPELINE:boolean := false

      -- Maximal blocks
      MAX_DISCARD_BLOCKS : integer := 10
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Write interface
      WR       : in  std_logic;
      EOB      : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL     : out std_logic;
      LSTBLK   : out std_logic;
      STATUS   : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      RD       : in  std_logic;
      DISCARD  : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DV       : out std_logic;
      EMPTY    : out std_logic;
      FRAME_RDY: out std_logic
   );
end component fifo_bram_discard;

-- Constants declaration

constant JUICE_WIDTH : integer := 1;

constant MEM_WIDTH : integer := 9;

-- Signals declaration
signal sig_fifo_eob  : std_logic;   -- End of block detection for FIFO
signal sig_full      : std_logic;   -- FIFO is full
signal sig_empty     : std_logic;   -- FIFO is empty
signal sig_status    : std_logic_vector(STATUS_WIDTH-1 downto 0); -- Free items
signal sig_vld       : std_logic;   -- Data valid at the output of the fifo
signal sig_tx_src_rdy_n:std_logic;
signal sig_rd        : std_logic;   -- Read from FIFO
signal sig_wr        : std_logic;   -- Write to FIFO
signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO
signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0); -- data from FIFO

signal sig_sof_n_rd  : std_logic;   -- Start of frame at the output
signal sig_sop_n_rd  : std_logic;   -- Start of packet at the output
signal sig_eop_n_rd  : std_logic;   -- End of packet at the output
signal sig_eof_n_rd  : std_logic;   -- End of frame at the output

signal sig_juice_in  : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_juice_out : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_frame_part: std_logic;

begin

sig_rd      <= (not TX_DST_RDY_N) or not sig_vld;
sig_wr      <= (not RX_SRC_RDY_N) and not sig_full;

sig_tx_src_rdy_n <= not sig_vld;

sig_data_wr <= sig_juice_in & RX_DATA;

-- Compress FrameLink control signals to sig_juice_in
fl_compress_inst : entity work.fl_compress
generic map(
   WIRES       => JUICE_WIDTH
)
port map(
   CLK         => CLK,
   RESET       => RESET,

   RX_SRC_RDY_N=> RX_SRC_RDY_N,
   RX_DST_RDY_N=> sig_full,
   RX_SOP_N    => RX_SOP_N,
   RX_EOP_N    => RX_EOP_N,
   RX_SOF_N    => RX_SOF_N,
   RX_EOF_N    => RX_EOF_N,
   FL_JUICE    => sig_juice_in,
   FRAME_PART  => sig_frame_part
);

-- Decompress FrameLink signals from sig_juice_out
fl_decompress_inst : entity work.fl_decompress_any
generic map(
   WIRES    => JUICE_WIDTH,
   PARTS    => PARTS
)
port map(
   -- Common interface
   CLK         => CLK,
   RESET       => RESET,

   TX_SRC_RDY_N=> sig_tx_src_rdy_n,
   TX_DST_RDY_N=> TX_DST_RDY_N,
   TX_SOP_N    => sig_sop_n_rd,
   TX_EOP_N    => sig_eop_n_rd,
   TX_SOF_N    => sig_sof_n_rd,
   TX_EOF_N    => sig_eof_n_rd,
   FL_JUICE    => sig_juice_out,
   DISCARD     => DISCARD
);

-- Store whole FrameLink protocol flow in the FIFO
fifo_inst: fifo_bram_discard
generic map(
   ITEMS       => ITEMS,
   BLOCK_SIZE  => BLOCK_SIZE,
   STATUS_WIDTH=> STATUS_WIDTH,
   DATA_WIDTH  => MEM_WIDTH
)
port map(
   RESET       => RESET,
   CLK         => CLK,

   -- Write interface
   DI          => sig_data_wr,
   EOB         => sig_fifo_eob,
   WR          => sig_wr,
   FULL        => sig_full,
   LSTBLK      => LSTBLK,
   STATUS      => sig_status,

   -- Read interface
   DO          => sig_data_rd,
   DISCARD     => DISCARD,
   RD          => sig_rd,
   EMPTY       => sig_empty,
   DV          => sig_vld,
   FRAME_RDY   => FRAME_RDY
);

sig_fifo_eob <= not RX_EOF_N;

RX_DST_RDY_N  <= sig_full or RESET;
TX_SRC_RDY_N  <= sig_tx_src_rdy_n;

TX_DATA     <= sig_data_rd(7 downto 0);
sig_juice_out<=sig_data_rd(MEM_WIDTH-1 downto MEM_WIDTH-JUICE_WIDTH);

TX_SOF_N <= sig_sof_n_rd;
TX_EOF_N <= sig_eof_n_rd;
TX_SOP_N <= sig_sop_n_rd;
TX_EOP_N <= sig_eop_n_rd;

EMPTY    <= sig_empty;
FULL     <= sig_full;
STATUS   <= sig_status;
end architecture full;
