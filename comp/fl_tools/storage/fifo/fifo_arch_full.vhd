-- fifo_arch_full.vhd
--! \file
--! \brief Frame Link protocol generic FIFO (full archiecture)
--! \author Viktor Pus <pus@liberouter.org>
--! \section License
--! Copyright (C) 2006 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! library containing log2 and min functions
use work.math_pack.all;

--! library with get_juice_width function
use work.fl_fifo_pkg.all;

architecture full of FL_FIFO is

--! Non-FrameLink synchronous BlockRAM FIFO
component fifo_bram is
   generic(
      -- ITEMS = Numer of items in FIFO
      ITEMS       : integer := 1024;

      -- BLOCK_SIZE = Number of items in one block
      BLOCK_SIZE  : integer := 4;

      -- Data Width
      DATA_WIDTH  : integer := 36;

      -- Automatic transfer of valid data to the output of the FIFO
      AUTO_PIPELINE : boolean := false;

      -- compute value of status signal
      STATUS_ENABLED : boolean := false;

      -- for better timing on output
      DO_REG         : boolean := true
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Write interface
      WR       : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL     : out std_logic;
      LSTBLK   : out std_logic;
      STATUS   : out std_logic_vector(log2(ITEMS) downto 0);

      -- Read interface
      RD       : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DV       : out std_logic;
      EMPTY    : out std_logic
   );
end component fifo_bram;

-- Constants declaration

--! Width of FL_JUICE signal
constant JUICE_WIDTH : integer := get_juice_width(DATA_WIDTH, USE_BRAMS);

--! Width of storage memory (data+control)
constant MEM_WIDTH : integer := DATA_WIDTH+log2(DATA_WIDTH/8)+JUICE_WIDTH;
                           --   DATA       REM                FL_JUICE

-- Signals declaration
signal sig_full      : std_logic;   --! FIFO is full
signal sig_empty     : std_logic;   --! FIFO is empty
signal sig_status    : std_logic_vector(log2(ITEMS) downto 0); --! Free items
signal sig_vld       : std_logic;   --! Data valid at the output of the fifo
signal sig_tx_src_rdy_n:std_logic;
signal sig_rd        : std_logic;   --! Read from FIFO
signal sig_wr        : std_logic;   --! Write to FIFO
signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0);--! data from FIFO
signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0);--! data to FIFO

signal sig_sof_n_rd  : std_logic;   --! Start of frame at the output
signal sig_sop_n_rd  : std_logic;   --! Start of packet at the output
signal sig_eop_n_rd  : std_logic;   --! End of packet at the output
signal sig_eof_n_rd  : std_logic;   --! End of frame at the output

signal sig_juice_in  : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_juice_out : std_logic_vector(JUICE_WIDTH-1 downto 0);
signal sig_frame_part: std_logic;

signal cnt_frame     : std_logic_vector(log2(ITEMS)downto 0);
signal sig_frame_rdy : std_logic;

begin

sig_rd      <= (not TX_DST_RDY_N) or not sig_vld;
sig_wr      <= (not RX_SRC_RDY_N) and not sig_full;

sig_tx_src_rdy_n <= not sig_vld;

sig_data_wr <= sig_juice_in & RX_REM & RX_DATA;

--! Compress FrameLink control signals to sig_juice_in
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

--! Decompress FrameLink signals from sig_juice_out
fl_decompress_inst : entity work.fl_decompress_any
generic map(
   WIRES       => JUICE_WIDTH,
   PARTS       => PARTS
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
   DISCARD     => '0'
);


bram_cond: if USE_BRAMS = true generate   -- use BlockRAMs
   --! Non-FrameLink synchronous BlockRAM FIFO
   bram_fifo_inst: fifo_bram
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
   --! Non-FrameLink synchronous DistRAM FIFO
   dist_fifo_inst: entity work.FIFO
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

--! \brief This up-down counter keeps information about number of whole frames.
--! \details It starts at the value 1, because if one frame is not fully written
--! and it is allready being read, this counter goes to 0.
cnt_frame_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         cnt_frame <= conv_std_logic_vector(1, cnt_frame'length);
      elsif sig_full = '0' and RX_SRC_RDY_N = '0' and RX_EOF_N = '0' then
         -- Frame end is written
         if sig_tx_src_rdy_n = '0' and TX_DST_RDY_N = '0' and sig_sof_n_rd
         = '0' then
            -- Frame start is read and end is written - no change
            cnt_frame <= cnt_frame;
         else
            -- Frame start is not read and end is written - increment counter
            cnt_frame <= cnt_frame + 1;
         end if;
      else
         if sig_tx_src_rdy_n = '0' and TX_DST_RDY_N = '0' and sig_sof_n_rd
         = '0' then
            -- Frame start is read and end is not written - decrement counter
            cnt_frame <= cnt_frame - 1;
         end if;
      end if;
   end if;
end process;

sig_frame_rdy <= '0' when (cnt_frame = 0) or (cnt_frame = 1) else
                 '1';

RX_DST_RDY_N  <= sig_full or RESET;
TX_SRC_RDY_N  <= sig_tx_src_rdy_n;

TX_DATA     <= sig_data_rd(DATA_WIDTH-1 downto 0);
TX_REM      <= sig_data_rd(DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto DATA_WIDTH);
sig_juice_out<=sig_data_rd(MEM_WIDTH-1 downto MEM_WIDTH-JUICE_WIDTH);

TX_SOF_N <= sig_sof_n_rd;
TX_EOF_N <= sig_eof_n_rd;
TX_SOP_N <= sig_sop_n_rd;
TX_EOP_N <= sig_eop_n_rd;

EMPTY    <= sig_empty;
FULL     <= sig_full;
STATUS   <= sig_status(log2(ITEMS) downto log2(ITEMS)-STATUS_WIDTH+1);
FRAME_RDY<= sig_frame_rdy;
end architecture full;
