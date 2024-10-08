-- binder_simple.vhd: FrameLink SIMPLE Binder architecture
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
use work.math_pack.all;
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BINDER_SIMPLE is
   generic(
      INPUT_WIDTH    : integer;
      INPUT_COUNT    : integer;
      OUTPUT_WIDTH   : integer;
      FRAME_PARTS    : integer;
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied
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
end entity FL_BINDER_SIMPLE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER_SIMPLE is

   -- ------------------ Constants declaration --------------------------------
   constant STATUS_WIDTH         : integer := 4;
   constant ITEM_COUNT           : integer := 2048 / (OUTPUT_WIDTH / 8);
   -- set to cover situation, when memory is full of one-word frames
   constant FRAMECOUNTER_WIDTH   : integer := log2(ITEM_COUNT+1);


   -- ------------------ Signals declaration ----------------------------------
   -- TRANSFORMER <-> FL_FIFO signals
   signal trans_sof_n         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_sop_n         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_eop_n         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_eof_n         : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_src_rdy_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_dst_rdy_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal trans_data          : std_logic_vector(INPUT_COUNT*OUTPUT_WIDTH-1
                                downto 0);
   signal trans_rem           : std_logic_vector(INPUT_COUNT*
                                log2(OUTPUT_WIDTH/8)-1 downto 0);

   -- FL_FIFO signals
   signal fifo_sof_n          : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_sop_n          : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_eop_n          : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_eof_n          : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_src_rdy_n      : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_dst_rdy_n      : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fifo_data           : std_logic_vector(INPUT_COUNT*OUTPUT_WIDTH-1
                                downto 0);
   signal fifo_rem            : std_logic_vector
                                 (INPUT_COUNT*log2(OUTPUT_WIDTH/8)-1
                                downto 0);

    -- output block block signals
   signal out_rx_sof_n        : std_logic;
   signal out_rx_sop_n        : std_logic;
   signal out_rx_eop_n        : std_logic;
   signal out_rx_eof_n        : std_logic;
   signal out_rx_src_rdy_n    : std_logic;
   signal out_rx_dst_rdy_n    : std_logic;
   signal out_rx_data         : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_rx_rem          : std_logic_vector(log2(OUTPUT_WIDTH/8)-1
                                downto 0);
   signal out_frame_done      : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal out_frame_part      : std_logic;
   signal out_status          : std_logic_vector(INPUT_COUNT*STATUS_WIDTH-1
                                downto 0);
   signal out_empty           : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal out_ifc             : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);

   -- frame counters' signals
   signal fc_frame_rdy        : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fc_no_frame         : std_logic;
   signal fc_inc              : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fc_dec              : std_logic_vector(INPUT_COUNT-1 downto 0);

   -- others
   signal sig_rx_dst_rdy_n    : std_logic_vector(INPUT_COUNT-1 downto 0);
begin

   RX_DST_RDY_N  <= sig_rx_dst_rdy_n;
   fc_inc        <= not (sig_rx_dst_rdy_n or RX_SRC_RDY_N or RX_EOF_N);
   fc_dec        <= not (fifo_src_rdy_n or fifo_dst_rdy_n or fifo_sof_n);

   -- generate TRANSFORMERs for each interface
   GEN_IBLOCKS : for i in 0 to INPUT_COUNT-1 generate
      CON_TX_TRANS_I : entity work.FL_TRANSFORMER
         generic map(
            RX_DATA_WIDTH  => INPUT_WIDTH,
            TX_DATA_WIDTH  => OUTPUT_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,

            -- RX interface
            RX_SOF_N       => RX_SOF_N(i),
            RX_SOP_N       => RX_SOP_N(i),
            RX_EOP_N       => RX_EOP_N(i),
            RX_EOF_N       => RX_EOF_N(i),
            RX_SRC_RDY_N   => RX_SRC_RDY_N(i),
            RX_DST_RDY_N   => sig_rx_dst_rdy_n(i),
            RX_DATA        =>
               RX_DATA((i+1)*INPUT_WIDTH-1 downto i*INPUT_WIDTH),
            RX_REM         =>
               RX_REM((i+1)*log2(INPUT_WIDTH/8)-1 downto i*log2(INPUT_WIDTH/8)),
            -- TX interface
            TX_DATA        => trans_data((i+1)*OUTPUT_WIDTH-1 downto i*OUTPUT_WIDTH),
            TX_REM         => trans_rem((i+1)*log2(OUTPUT_WIDTH/8)-1 downto i*log2(OUTPUT_WIDTH/8)),
            TX_SOF_N       => trans_sof_n(i),
            TX_EOF_N       => trans_eof_n(i),
            TX_SOP_N       => trans_sop_n(i),
            TX_EOP_N       => trans_eop_n(i),
            TX_SRC_RDY_N   => trans_src_rdy_n(i),
            TX_DST_RDY_N   => trans_dst_rdy_n(i)
         );

      -- mapping FL_FIFO for incoming contexts
      CON_RX_FIFO_I : entity work.FL_FIFO
         generic map(
            DATA_WIDTH     => OUTPUT_WIDTH,
            USE_BRAMS      => true,
            ITEMS          => ITEM_COUNT,
            BLOCK_SIZE     => 0,
            STATUS_WIDTH   => STATUS_WIDTH,
            PARTS          => FRAME_PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => trans_data((i+1)*OUTPUT_WIDTH-1 downto i*OUTPUT_WIDTH),
            RX_REM         => trans_rem((i+1)*log2(OUTPUT_WIDTH/8)-1 downto i*log2(OUTPUT_WIDTH/8)),
            RX_SRC_RDY_N   => trans_src_rdy_n(i),
            RX_DST_RDY_N   => trans_dst_rdy_n(i),
            RX_SOP_N       => trans_sop_n(i),
            RX_EOP_N       => trans_eop_n(i),
            RX_SOF_N       => trans_sof_n(i),
            RX_EOF_N       => trans_eof_n(i),
            -- read interface
            TX_DATA        => fifo_data((i+1)*OUTPUT_WIDTH-1 downto i*OUTPUT_WIDTH),
            TX_REM         => fifo_rem((i+1)*log2(OUTPUT_WIDTH/8)-1 downto i*log2(OUTPUT_WIDTH/8)),
            TX_SRC_RDY_N   => fifo_src_rdy_n(i),
            TX_DST_RDY_N   => fifo_dst_rdy_n(i),
            TX_SOP_N       => fifo_sop_n(i),
            TX_EOP_N       => fifo_eop_n(i),
            TX_SOF_N       => fifo_sof_n(i),
            TX_EOF_N       => fifo_eof_n(i),
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => out_empty(i),
            STATUS         => out_status((i+1)*STATUS_WIDTH-1
                              downto i*STATUS_WIDTH)
         );
   end generate;

   CROSSBAR_I : entity work.FLB_CROSSBAR
      generic map(
         DATA_WIDTH     => OUTPUT_WIDTH,
         COUNT          => INPUT_COUNT
      )
      port map(
         -- input FrameLink interface
         RX_SOF_N       => fifo_sof_n,
         RX_SOP_N       => fifo_sop_n,
         RX_EOP_N       => fifo_eop_n,
         RX_EOF_N       => fifo_eof_n,
         RX_SRC_RDY_N   => fifo_src_rdy_n,
         RX_DST_RDY_N   => fifo_dst_rdy_n,
         RX_DATA        => fifo_data,
         RX_REM         => fifo_rem,
         -- output FrameLink interface
         TX_SOF_N       => out_rx_sof_n,
         TX_SOP_N       => out_rx_sop_n,
         TX_EOP_N       => out_rx_eop_n,
         TX_EOF_N       => out_rx_eof_n,
         TX_SRC_RDY_N   => out_rx_src_rdy_n,
         TX_DST_RDY_N   => out_rx_dst_rdy_n,
         TX_DATA        => out_rx_data,
         TX_REM         => out_rx_rem,
         -- control signals
         IFC            => out_ifc
      );

   GEN_OUTPUT : if (QUEUE_CHOOSING = most_occupied) generate
      OUTPUT_BLOCK : entity work.FLB_OUTPUT(most_occupied)
         generic map(
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            STATUS_WIDTH   => STATUS_WIDTH,
            COUNT          => INPUT_COUNT,
            QUEUE_CHOOSING => QUEUE_CHOOSING,
            LOW_STATUS_LOW_SPACE => true
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
            EMPTY          => fifo_src_rdy_n,   -- out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
            -- Frame Counters output
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );

      fc_frame_rdy   <= (others => '1');
      fc_no_frame    <= '0';
   end generate;

   GEN_OUTPUT_ROBIN : if (QUEUE_CHOOSING = round_robin) generate
      OUTPUT_BLOCK : entity work.FLB_OUTPUT(round_robin)
         generic map(
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            STATUS_WIDTH   => STATUS_WIDTH,
            COUNT          => INPUT_COUNT,
            QUEUE_CHOOSING => QUEUE_CHOOSING,
            LOW_STATUS_LOW_SPACE => true
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
            EMPTY          => fifo_src_rdy_n,   -- out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
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
            INC            => fc_inc,
            DEC            => fc_dec,

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
            LOW_STATUS_LOW_SPACE => true
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
            EMPTY          => fifo_src_rdy_n,   -- out_empty,
            IFC            => out_ifc,
            -- FrameLink Binder output
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
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
            INC            => fc_inc,
            DEC            => fc_dec,

            -- output interface
            FRAME_RDY      => fc_frame_rdy,
            NO_FRAME       => fc_no_frame
         );
   end generate;

end architecture full;
