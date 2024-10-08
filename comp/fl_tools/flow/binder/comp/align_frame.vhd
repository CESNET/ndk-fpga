-- align_frame.vhd: FrameLink Binder input frame align
-- Copyright (C) 2008 CESNET
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_ALIGN_FRAME is
   generic(
      INPUT_WIDTH    : integer;
      INPUT_COUNT    : integer;  -- total count of blocks
      FRAME_PARTS    : integer
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(INPUT_WIDTH/8)-1 downto 0);

      -- output interface
      DATA_OUT       : out std_logic_vector(INPUT_WIDTH+(INPUT_WIDTH/8)-1 downto 0);
      WRITE          : out std_logic;
      FULL           : in  std_logic;

      -- other
      NEW_FRAME      : out std_logic;
      FRAME_PART     : out std_logic
   );
end entity FLB_ALIGN_FRAME;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_ALIGN_FRAME is

   -- ------------------ Constants declaration --------------------------------
   constant JUICE_WIDTH       : integer := minimum(INPUT_WIDTH/16, 4);
   constant ROW_MAX           : std_logic_vector(log2(INPUT_COUNT)-1 downto 0)
                              := (others => '1');

   -- ------------------ Signals declaration ----------------------------------
   -- FSM signals
   signal fsm_dv              : std_logic;
   signal fsm_cnt_row_max     : std_logic;
   signal fsm_eop             : std_logic;
   signal fsm_fifo_full       : std_logic;
   signal fsm_insert_idle     : std_logic;

   -- counters
   signal cnt_row             : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);
   signal cnt_row_ce          : std_logic;

   -- FIFO signals
   signal fifo_data           : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal fifo_rem            : std_logic_vector(log2(INPUT_WIDTH/8) - 1 downto 0);
   signal fifo_src_rdy_n      : std_logic;
   signal fifo_dst_rdy_n      : std_logic;
   signal fifo_sop_n          : std_logic;
   signal fifo_eop_n          : std_logic;
   signal fifo_sof_n          : std_logic;
   signal fifo_eof_n          : std_logic;

   -- others
   signal fl_juice            : std_logic_vector(JUICE_WIDTH-1 downto 0);
   signal idle_data           : std_logic_vector(INPUT_WIDTH+(INPUT_WIDTH/8)-1
                                downto 0);
   signal data_out_i          : std_logic_vector(INPUT_WIDTH+(INPUT_WIDTH/8)-1
                                downto 0);

begin
   -- ------------------ Directly mapped signals ------------------------------
   -- FSM inputs
   fsm_dv               <= not (fifo_dst_rdy_n or fifo_src_rdy_n);
   fsm_eop              <= not fifo_eop_n;
   fsm_fifo_full        <= FULL;
   fsm_cnt_row_max      <= '1' when cnt_row = ROW_MAX else '0';

   -- input FIFO control
   fifo_dst_rdy_n       <= FULL or fsm_insert_idle;

   -- counts in which part of row we write the data word. Note that FL part has
   -- to be aligned to one memory row -> idle words have to be inserted
   cnt_row_ce           <= fsm_dv or (fsm_insert_idle and not FULL);

   -- output interface signals
   WRITE                <= not fifo_src_rdy_n or fsm_insert_idle;
   DATA_OUT             <= idle_data when fsm_insert_idle = '1' else
                           data_out_i;
   NEW_FRAME            <= not (fifo_eof_n or fifo_dst_rdy_n or fifo_src_rdy_n);

   -- generate idle data signal
   idle_data(INPUT_WIDTH+log2(INPUT_WIDTH/8)-1 downto 0) <= (others => '0');
   idle_data(INPUT_WIDTH+(INPUT_WIDTH/8)-1 downto
      INPUT_WIDTH+log2(INPUT_WIDTH/8)) <= (others => '1');

   -- generate data out signal
   data_out_i(INPUT_WIDTH-1 downto 0) <= fifo_data;
   data_out_i(INPUT_WIDTH+log2(INPUT_WIDTH/8)-1 downto INPUT_WIDTH)
      <= fifo_rem;
   data_out_i(INPUT_WIDTH+log2(INPUT_WIDTH/8)+JUICE_WIDTH-1
      downto INPUT_WIDTH+log2(INPUT_WIDTH/8))
      <= fl_juice;

   GEN_IDLE_BITS : if INPUT_WIDTH+log2(INPUT_WIDTH/8)+JUICE_WIDTH <
   INPUT_WIDTH + (INPUT_WIDTH/8) generate
      data_out_i(INPUT_WIDTH + (INPUT_WIDTH/8)-1 downto
         INPUT_WIDTH+log2(INPUT_WIDTH/8)+JUICE_WIDTH)
         <= (others => '0');
   end generate;

   -- FSM mapping
   FLB_ALIGN_FRAME_FSM_I : entity work.FLB_ALIGN_FRAME_FSM
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input signals
         DV             => fsm_dv,
         CNT_ROW_MAX    => fsm_cnt_row_max,
         EOP            => fsm_eop,
         FIFO_FULL      => fsm_fifo_full,
         -- output signals
         INSERT_IDLE    => fsm_insert_idle
      );

   INPUT_BUFFER : entity work.FL_PIPE
         generic map(
            -- FrameLink Data Width
            DATA_WIDTH     => INPUT_WIDTH,
            USE_OUTREG     => false
         )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_SOF_N       => RX_SOF_N,
         RX_EOF_N       => RX_EOF_N,
         -- read interface
         TX_DATA        => fifo_data,
         TX_REM         => fifo_rem,
         TX_SRC_RDY_N   => fifo_src_rdy_n,
         TX_DST_RDY_N   => fifo_dst_rdy_n,
         TX_SOP_N       => fifo_sop_n,
         TX_EOP_N       => fifo_eop_n,
         TX_SOF_N       => fifo_sof_n,
         TX_EOF_N       => fifo_eof_n
      );

   FL_COMPRESSOR : entity work.fl_compress
      generic map(
         WIRES          => JUICE_WIDTH
      )
      port map(
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Recieve interface
         RX_SRC_RDY_N   => fifo_src_rdy_n,
         RX_DST_RDY_N   => fifo_dst_rdy_n,
         RX_SOP_N       => fifo_sop_n,
         RX_EOP_N       => fifo_eop_n,
         RX_SOF_N       => fifo_sof_n,
         RX_EOF_N       => fifo_eof_n,
         FL_JUICE       => fl_juice,
            -- Compressed FL control signals
         FRAME_PART     => FRAME_PART
            -- Every cycle in '1' means one frame part
      );

   -- ------------------ counter cnt_row --------------------------------------
   cnt_rowp: process (CLK)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cnt_row <= (others => '0');
         elsif cnt_row_ce = '1' then
            cnt_row <= cnt_row + 1;
         end if;
      end if;
   end process;

end architecture full;

