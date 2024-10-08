-- binder_full.vhd: FrameLink FULL Binder top architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- Binder declarations
use work.fl_binder_decl.all;

-- library with get_juice_width function
use work.fl_fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BINDER_NFIFO2FIFO is
   generic(
      INPUT_WIDTH    : integer;
      INPUT_COUNT    : integer;
      OUTPUT_WIDTH   : integer;
      LUT_MEMORY     : boolean;
      LUT_BLOCK_SIZE : integer;
      FRAME_PARTS    : integer;
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1
                                                                     downto 0);
      RX_REM         : in  std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                                     downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)
   );
end entity FL_BINDER_NFIFO2FIFO;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER_NFIFO2FIFO is

   -- ------------------ Constants declaration --------------------------------
   constant STATUS_WIDTH         : integer := 4;
   constant CHANNEL_WIDTH        : integer := INPUT_WIDTH + INPUT_WIDTH/8;
   constant NFIFO2FIFO_WIDTH     : integer := CHANNEL_WIDTH * INPUT_COUNT;
   constant MEM_DATA_WIDTH       : integer := INPUT_WIDTH * INPUT_COUNT;
   constant BRAM_SIZE            : integer := 2048;
   constant BRAM_BLOCK_SIZE      : integer := BRAM_SIZE / (MEM_DATA_WIDTH/8);

   function BLOCK_SIZE
      return integer is
   begin
      if (LUT_MEMORY = true) then return LUT_BLOCK_SIZE;
      else return BRAM_BLOCK_SIZE;
      end if;
   end function;

   function OUTPUT_REG
      return boolean is
   begin
      if (LUT_MEMORY = true) then return true;
      else return false;
      end if;
   end function;

   -- set to cover situation, when memory is full of one-word frames
   constant FRAMECOUNTER_WIDTH   : integer := log2(BLOCK_SIZE+1);

   -- NFIFO2FIFO interface
   signal nfifo2fifo_data_in     : std_logic_vector(NFIFO2FIFO_WIDTH-1 downto 0);
   signal nfifo2fifo_write       : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal nfifo2fifo_full        : std_logic_vector(INPUT_COUNT-1 downto 0);

   signal nfifo2fifo_data_out    : std_logic_vector(NFIFO2FIFO_WIDTH-1 downto 0);
   signal nfifo2fifo_data_vld    : std_logic;
   signal nfifo2fifo_block_addr  : std_logic_vector(abs(log2(INPUT_COUNT)-1) downto 0);
   signal nfifo2fifo_read        : std_logic;
   signal nfifo2fifo_empty       : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal nfifo2fifo_status      : std_logic_vector(log2(BLOCK_SIZE+1)*INPUT_COUNT-1 downto 0);

   -- Output block input interface signals
   signal out_rx_sof_n         : std_logic;
   signal out_rx_sop_n         : std_logic;
   signal out_rx_eop_n         : std_logic;
   signal out_rx_eof_n         : std_logic;
   signal out_rx_src_rdy_n     : std_logic;
   signal out_rx_dst_rdy_n     : std_logic;
   signal out_rx_data          : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_rx_rem           : std_logic_vector(log2(OUTPUT_WIDTH/8)-1
                                downto 0);
   signal out_tx_sof_n         : std_logic;
   signal out_tx_sop_n         : std_logic;
   signal out_tx_eop_n         : std_logic;
   signal out_tx_eof_n         : std_logic;
   signal out_tx_src_rdy_n     : std_logic;
   signal out_tx_dst_rdy_n     : std_logic;
   signal out_tx_data          : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_tx_rem           : std_logic_vector(log2(OUTPUT_WIDTH/8)-1
                                downto 0);

   signal out_frame_done       : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal out_frame_part       : std_logic;
   signal out_status           : std_logic_vector(INPUT_COUNT*STATUS_WIDTH-1
                                downto 0);
   signal out_empty            : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal out_ifc              : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);

   -- frame counters' signals
   signal fc_frame_rdy        : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fc_no_frame         : std_logic;
   signal fc_newframe         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fc_frame_done       : std_logic_vector(INPUT_COUNT-1 downto 0);
begin

   -- -------------------------------------------------------------------------
   --                      INPUT DATA TRANSFORMATION
   -- -------------------------------------------------------------------------
   -- generate frame aligner for every input interface
   GEN_ALIGN_FRAME : for i in 0 to INPUT_COUNT-1 generate
      ALIGN_FRAME_I : entity work.FLB_ALIGN_FRAME
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            FRAME_PARTS    => FRAME_PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input interface
            RX_SOF_N       => RX_SOF_N(i),
            RX_SOP_N       => RX_SOP_N(i),
            RX_EOP_N       => RX_EOP_N(i),
            RX_EOF_N       => RX_EOF_N(i),
            RX_SRC_RDY_N   => RX_SRC_RDY_N(i),
            RX_DST_RDY_N   => RX_DST_RDY_N(i),
            RX_DATA        => RX_DATA((i+1)*INPUT_WIDTH-1 downto i*INPUT_WIDTH),
            RX_REM         => RX_REM((i+1)*log2(INPUT_WIDTH/8)-1 downto i*log2(INPUT_WIDTH/8)),
            -- output interface
            DATA_OUT       => nfifo2fifo_data_in((i+1)*CHANNEL_WIDTH-1 downto i*CHANNEL_WIDTH),
            WRITE          => nfifo2fifo_write(i),
            FULL           => nfifo2fifo_full(i),
            -- other
            NEW_FRAME      => fc_newframe(i),
            FRAME_PART     => open
         );
   end generate;

   -- -------------------------------------------------------------------------
   --                              NFIFO2FIFO
   -- -------------------------------------------------------------------------
   NFIFO2FIFO_I : entity work.NFIFO2FIFO
   generic map(
      DATA_WIDTH => NFIFO2FIFO_WIDTH,
      FLOWS      => INPUT_COUNT,
      BLOCK_SIZE => BLOCK_SIZE,
      LUT_MEMORY => LUT_MEMORY,
      OUTPUT_REG => OUTPUT_REG,
      GLOB_STATE => false
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,
      -- Write interface
      DATA_IN    => nfifo2fifo_data_in,
      WRITE      => nfifo2fifo_write,
      FULL       => nfifo2fifo_full,
      -- Read interface
      DATA_OUT   => nfifo2fifo_data_out,
      DATA_VLD   => nfifo2fifo_data_vld,
      BLOCK_ADDR => nfifo2fifo_block_addr,
      READ       => nfifo2fifo_read,
      PIPE_EN    => nfifo2fifo_read,
      EMPTY      => nfifo2fifo_empty,
      STATUS     => nfifo2fifo_status
   );

   DATA_TRANSFORMER_I : entity work.FLB_DATA_TRANSFORMER
      generic map(
         INPUT_WIDTH    => INPUT_WIDTH,
         INPUT_COUNT    => INPUT_COUNT,
         OUTPUT_WIDTH   => OUTPUT_WIDTH,
         STATUS_WIDTH   => STATUS_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FRAME_PARTS    => FRAME_PARTS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- NFIFO2FIFO interface
         DATA_OUT       => nfifo2fifo_data_out,
         DATA_VLD       => nfifo2fifo_data_vld,
         BLOCK_ADDR     => nfifo2fifo_block_addr,
         READ           => nfifo2fifo_read,
         EMPTY          => nfifo2fifo_empty,
         STATUS         => nfifo2fifo_status,
         -- Output data
         TX_SOF_N       => out_rx_sof_n,
         TX_SOP_N       => out_rx_sop_n,
         TX_EOP_N       => out_rx_eop_n,
         TX_EOF_N       => out_rx_eof_n,
         TX_SRC_RDY_N   => out_rx_src_rdy_n,
         TX_DST_RDY_N   => out_rx_dst_rdy_n,
         TX_DATA        => out_rx_data,
         TX_REM         => out_rx_rem,
         -- Output block interface
         TX_STATUS      => out_status,
         TX_EMPTY       => out_empty,
         TX_IFC         => out_ifc,
         -- Other
         FRAME_DONE     => fc_frame_done
      );

   -- -------------------------------------------------------------------------
   --                              OUTPUT PART
   -- -------------------------------------------------------------------------
   GEN_OUTPUT : if (QUEUE_CHOOSING = most_occupied) generate
      OUTPUT_BLOCK : entity work.FLB_OUTPUT(most_occupied)
         generic map(
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            STATUS_WIDTH   => STATUS_WIDTH,
            COUNT          => INPUT_COUNT,
            QUEUE_CHOOSING => QUEUE_CHOOSING,
            LOW_STATUS_LOW_SPACE => false
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- Data transformation block interface
            RX_SOF_N       => out_rx_sof_n,
            RX_SOP_N       => out_rx_sop_n,
            RX_EOP_N       => out_rx_eop_n,
            RX_EOF_N       => out_rx_eof_n,
            RX_SRC_RDY_N   => out_rx_src_rdy_n,
            RX_DST_RDY_N   => out_rx_dst_rdy_n,
            RX_DATA        => out_rx_data,
            RX_REM         => out_rx_rem,
            STATUS         => out_status,
            EMPTY          => out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => out_tx_sof_n,
            TX_SOP_N       => out_tx_sop_n,
            TX_EOP_N       => out_tx_eop_n,
            TX_EOF_N       => out_tx_eof_n,
            TX_SRC_RDY_N   => out_tx_src_rdy_n,
            TX_DST_RDY_N   => out_tx_dst_rdy_n,
            TX_DATA        => out_tx_data,
            TX_REM         => out_tx_rem,
            -- Frame Counters' output
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );
   end generate;

   GEN_OUTPUT_ROBIN : if (QUEUE_CHOOSING = round_robin) generate
      OUTPUT_BLOCK : entity work.FLB_OUTPUT(round_robin)
         generic map(
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            STATUS_WIDTH   => STATUS_WIDTH,
            COUNT          => INPUT_COUNT,
            QUEUE_CHOOSING => QUEUE_CHOOSING,
            LOW_STATUS_LOW_SPACE => false
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- Data transformation block interface
            RX_SOF_N       => out_rx_sof_n,
            RX_SOP_N       => out_rx_sop_n,
            RX_EOP_N       => out_rx_eop_n,
            RX_EOF_N       => out_rx_eof_n,
            RX_SRC_RDY_N   => out_rx_src_rdy_n,
            RX_DST_RDY_N   => out_rx_dst_rdy_n,
            RX_DATA        => out_rx_data,
            RX_REM         => out_rx_rem,
            STATUS         => out_status,
            EMPTY          => out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => out_tx_sof_n,
            TX_SOP_N       => out_tx_sop_n,
            TX_EOP_N       => out_tx_eop_n,
            TX_EOF_N       => out_tx_eof_n,
            TX_SRC_RDY_N   => out_tx_src_rdy_n,
            TX_DST_RDY_N   => out_tx_dst_rdy_n,
            TX_DATA        => out_tx_data,
            TX_REM         => out_tx_rem,
            -- Frame Counters' output
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );

      FRAME_COUNTERS : entity work.FLB_FRAME_COUNTERS
         generic map(
            COUNTER_WIDTH  => FRAMECOUNTER_WIDTH,
            COUNT          => INPUT_COUNT
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,

            -- input interface
            INC            => fc_newframe,
            DEC            => fc_frame_done,

            -- output interface
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );
   end generate;

   GEN_OUTPUT_FRAMED : if (QUEUE_CHOOSING = framed) generate
      OUTPUT_BLOCK : entity work.FLB_OUTPUT(framed)
         generic map(
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            STATUS_WIDTH   => STATUS_WIDTH,
            COUNT          => INPUT_COUNT,
            QUEUE_CHOOSING => QUEUE_CHOOSING,
            LOW_STATUS_LOW_SPACE => false
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- Data transformation block interface
            RX_SOF_N       => out_rx_sof_n,
            RX_SOP_N       => out_rx_sop_n,
            RX_EOP_N       => out_rx_eop_n,
            RX_EOF_N       => out_rx_eof_n,
            RX_SRC_RDY_N   => out_rx_src_rdy_n,
            RX_DST_RDY_N   => out_rx_dst_rdy_n,
            RX_DATA        => out_rx_data,
            RX_REM         => out_rx_rem,
            STATUS         => out_status,
            EMPTY          => out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => out_tx_sof_n,
            TX_SOP_N       => out_tx_sop_n,
            TX_EOP_N       => out_tx_eop_n,
            TX_EOF_N       => out_tx_eof_n,
            TX_SRC_RDY_N   => out_tx_src_rdy_n,
            TX_DST_RDY_N   => out_tx_dst_rdy_n,
            TX_DATA        => out_tx_data,
            TX_REM         => out_tx_rem,
            -- Frame Counters' output
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );

      FRAME_COUNTERS : entity work.FLB_FRAME_COUNTERS
         generic map(
            COUNTER_WIDTH  => FRAMECOUNTER_WIDTH,
            COUNT          => INPUT_COUNT
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,

            -- input interface
            INC            => fc_newframe,
            DEC            => fc_frame_done,

            -- output interface
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );
   end generate;


   -- generate FrameLink pipe to achieve better timinh
   GEN_PIPE: if (INPUT_WIDTH*INPUT_COUNT = OUTPUT_WIDTH) generate
      OUTPUT_PIPE : entity work.FL_PIPE
         generic map(
            -- FrameLink Data Width
            DATA_WIDTH     => OUTPUT_WIDTH,
            USE_OUTREG     => false
         )
         port map(
            -- Common interface
            CLK            => CLK,
            RESET          => RESET,
            -- Input interface
            RX_SOF_N       => out_tx_sof_n,
            RX_SOP_N       => out_tx_sop_n,
            RX_EOP_N       => out_tx_eop_n,
            RX_EOF_N       => out_tx_eof_n,
            RX_SRC_RDY_N   => out_tx_src_rdy_n,
            RX_DST_RDY_N   => out_tx_dst_rdy_n,
            RX_DATA        => out_tx_data,
            RX_REM         => out_tx_rem,

            -- Output interface
            TX_SOF_N       => TX_SOF_N,
            TX_EOP_N       => TX_EOP_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

   GEN_NOPIPE: if (INPUT_WIDTH*INPUT_COUNT /= OUTPUT_WIDTH) generate
      TX_SOF_N       <= out_tx_sof_n;
      TX_EOP_N       <= out_tx_eop_n;
      TX_SOP_N       <= out_tx_sop_n;
      TX_EOF_N       <= out_tx_eof_n;
      TX_SRC_RDY_N   <= out_tx_src_rdy_n;
      out_tx_dst_rdy_n   <= TX_DST_RDY_N;
      TX_DATA        <= out_tx_data;
      TX_REM         <= out_tx_rem;
   end generate;
end architecture full;
