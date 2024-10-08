-- flu2qdr_arch.vhd
--!
--! \file
--! \brief FLU2QDR module TOP LEVEL entity
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! General FLU_ADAPTER package
use work.flu_adapter_pkg.all;

--! \brief Implementation of FLU2QDR
architecture FULL of FLU2QDR is

   --! \brief constant declaration

   --! \brief signal declaration
   --! FIFO registers, counters
   signal fifo_start        : std_logic_vector(ADDR_WIDTH-3 downto 0); --! 72Mb = 576*2^17
   signal fifo_start_inc    : std_logic;
   signal fifo_end          : std_logic_vector(ADDR_WIDTH-3 downto 0);
   signal fifo_end_inc      : std_logic;
   signal fifo_end_plus1    : std_logic_vector(ADDR_WIDTH-3 downto 0); --! fifo_end + 1
   signal fifo_end_minus1   : std_logic_vector(ADDR_WIDTH-3 downto 0); --! fifo_end - 1
   signal fifo_empty        : std_logic;
   signal fifo_full         : std_logic;

   signal fifo_pointer      : std_logic_vector(ADDR_WIDTH-3 downto 0);
   signal fifo_pointer_init : std_logic;
   signal fifo_pointer_ov   : std_logic;
   signal fifo_pointer_inc  : std_logic;

   signal cnt_delay         : std_logic_vector(2 downto 0);
   signal cnt_delay_inc     : std_logic;
   signal cnt_delay_ov      : std_logic;

   --! input FLU registers
   signal flu_reg0          : std_logic_vector(523 downto 0);
   signal flu_reg1          : std_logic_vector(523 downto 0);
   signal flu_reg2          : std_logic_vector(523 downto 0);
   signal flu_reg_we        : std_logic_vector(2 downto 0);
   signal flu_reg_vld       : std_logic_vector(2 downto 0);

   --! input multiplexor
   signal flu_mux_in        : std_logic_vector(1571 downto 0);
   signal flu_mux_out       : std_logic_vector(785 downto 0);
   signal flu_mux_sel       : std_logic_vector(0 downto 0);

   --! input FSM
   type fsmin_t is (fsmin_default, fsmin_word0, fsmin_word1, fsmin_word2, fsmin_word2_wait);
   signal current_statein  : fsmin_t;
   signal next_statein     : fsmin_t;

   --! qdr read request FSM
   type fsmrd_t is (fsmrd_disable, fsmrd_fifo_word0, fsmrd_fifo_word1, fsmrd_capture, fsmrd_replay,
                    fsmrd_replay_word0, fsmrd_replay_word1, fsmrd_replay_repeated,
                    fsmrd_replay_repeated_word0, fsmrd_replay_repeated_word1, fsmrd_clear);

   signal current_staterd  : fsmrd_t;
   signal next_staterd     : fsmrd_t;

   --! qdr read request counter
   signal rd_cnt           : std_logic_vector(8 downto 0);
   signal rd_cnt_inc       : std_logic;
   signal rd_cnt_dec       : std_logic;
   signal rd_cnt_full      : std_logic;
   signal rd_addr_lsb      : std_logic;
   signal rd_addr          : std_logic_vector(ADDR_WIDTH-3 downto 0);

   --! Storage state
   signal next_state_disable         : std_logic;
   signal next_state_fifo            : std_logic;
   signal next_state_capture         : std_logic;
   signal next_state_replay          : std_logic;
   signal next_state_replay_repeated : std_logic;
   signal next_state_clear           : std_logic;

   signal state_disable         : std_logic;
   signal state_fifo            : std_logic;
   signal state_capture         : std_logic;
   signal state_replay          : std_logic;
   signal state_replay_repeated : std_logic;
   signal state_clear           : std_logic;

   --! output QDR registers
   signal qdr_reg0          : std_logic_vector(785 downto 0);
   signal qdr_reg1          : std_logic_vector(785 downto 0);
   signal qdr_reg_we        : std_logic_vector(1 downto 0);
   signal qdr_reg_vld       : std_logic_vector(2 downto 0);

   --! output multiplexor
   signal qdr_mux_in        : std_logic_vector(1568 downto 0);
   signal qdr_mux_out       : std_logic_vector(522 downto 0);
   signal qdr_mux_sel       : std_logic_vector(1 downto 0);

   --! output FSM
   type fsmout_t is (fsmout_default, fsmout_word0, fsmout_word1, fsmout_word1_wait, fsmout_word2);
   signal current_stateout  : fsmout_t;
   signal next_stateout     : fsmout_t;


begin

   --! FIFO logic --------------------------------------------------------------

   fifo_startp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RST = '1' or state_clear = '1') then
            fifo_start <= (others => '0');
         elsif (fifo_start_inc = '1') then
            fifo_start <= fifo_start + 1;
         end if;
      end if;
   end process;

   fifo_endp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RST = '1' or state_clear = '1') then
            fifo_end <= (others => '0');
         elsif (fifo_end_inc = '1') then
            fifo_end <= fifo_end + 1;
         end if;
      end if;
   end process;

   fifo_pointerp: process(CLK) --! probably no reset needed, must init before use
                               --! fifo must not be empty!
   begin
      if (CLK'event and CLK = '1') then
         fifo_pointer_ov <= '0';
         if (fifo_pointer_init = '1') then
            fifo_pointer <= fifo_start;
         elsif (fifo_pointer_inc = '1') then
            if (fifo_pointer = fifo_end_minus1) then
               fifo_pointer <= fifo_start;
               fifo_pointer_ov <= '1';
            else
               fifo_pointer <=  fifo_pointer + 1;
            end if;
         end if;
      end if;
   end process;

   fifo_end_plus1 <= fifo_end + 1;

   fifo_end_minus1 <= fifo_end - 1;

   fifo_empty <= '1' when (fifo_start = fifo_end) else '0';

   fifo_full <= '1' when (fifo_start = fifo_end_plus1) else '0';

   MEMORY_EMPTY <= fifo_empty;
   MEMORY_FULL <= fifo_full;
   MEMORY_START <= fifo_start;
   MEMORY_END <= fifo_end;
   MEMORY_POINTER <= fifo_pointer;

   --! Delay counter process
   cnt_delayp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         cnt_delay_ov <= '0';
         if (RST = '1') then
            cnt_delay <= (others => '0');
         elsif (cnt_delay_inc = '1') then
            cnt_delay <= cnt_delay + 1;
            if (cnt_delay = "111") then
               cnt_delay_ov <= '1';
            end if;
         end if;
      end if;
   end process;

   --! input registers ---------------------------------------------------------
   flu_reg0p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (flu_reg_we(0) = '1') then
            flu_reg0 <= FLU_RX_EOP & FLU_RX_SOP & FLU_RX_EOP_POS & FLU_RX_SOP_POS & FLU_RX_DATA
                        & flu_reg_vld(0);
         end if;
      end if;
   end process;

   flu_reg1p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (flu_reg_we(1) = '1') then
            flu_reg1 <= FLU_RX_EOP & FLU_RX_SOP & FLU_RX_EOP_POS & FLU_RX_SOP_POS & FLU_RX_DATA
            & flu_reg_vld(1);
         end if;
      end if;
   end process;

   flu_reg2p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (flu_reg_we(2) = '1') then
            flu_reg2 <= FLU_RX_EOP & FLU_RX_SOP & FLU_RX_EOP_POS & FLU_RX_SOP_POS & FLU_RX_DATA
            & flu_reg_vld(2);
         end if;
      end if;
   end process;

   --! input multiplexor

   flu_mux_in <= flu_reg2 & flu_reg1 & flu_reg0;

   flu_muxe:entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 786,
      MUX_WIDTH   => 2   -- multiplexer width (number of inputs)
   )
   port map(
      DATA_IN     => flu_mux_in,
      SEL         => flu_mux_sel,
      DATA_OUT    => flu_mux_out
   );

   --! Connect input multiplexor output to entity interface
   QDR_TX_WR_DATA(785 downto 0) <= flu_mux_out;
   QDR_TX_WR_DATA(863 downto 786) <= (others => 'X');

   --! input FSM ---------------------------------------------------------------
   --! FSM process
   fsminp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RST = '1') then
            current_statein <= fsmin_default;
         else
            current_statein <= next_statein;
         end if;
      end if;
   end process;
   --! FSM output/next state logic
   next_state_logicinp: process (current_statein, fifo_full, FLU_RX_SRC_RDY, QDR_TX_WR_DST_RDY,
                                 FLU_TX_DST_RDY, fifo_end, state_disable, state_replay,
                                 state_replay_repeated, state_clear)
   begin
      --! Default values
      flu_reg_we <= (others => '0');
      flu_reg_vld <= (others => '0');
      flu_mux_sel <= "0";
      fifo_end_inc <= '0';
      FLU_RX_DST_RDY <= '0';
      QDR_TX_WR_SRC_RDY <= '0';
      QDR_TX_WR_ADDR <= (others => 'X');

      case current_statein is
         when fsmin_default => --! trying to write flu_word0
            if (state_clear = '0') then
               next_statein <= current_statein;
               if (state_disable = '0' and state_replay = '0' and state_replay_repeated = '0') then
                  FLU_RX_DST_RDY <= '1';
                  if (FLU_RX_SRC_RDY = '1') then
                     flu_reg_we(0) <= '1';
                     flu_reg_vld(0) <= '1';
                     next_statein <= fsmin_word0;
                  end if;
               end if;
            else
               next_statein <= fsmin_default;
            end if;
         when fsmin_word0 => --! flu_word0 written, trying to write flu_word1
            if (state_clear = '0') then
               next_statein <= current_statein;
               FLU_RX_DST_RDY <= '1';
               if (FLU_RX_SRC_RDY = '1') then
                  flu_reg_we(1) <= '1';
                  flu_reg_vld(1) <= '1';
                  next_statein <= fsmin_word1;
               elsif (FLU_TX_DST_RDY = '1' or state_disable = '1' or state_replay = '1'
                      or state_replay_repeated = '1') then
                  --! no input, but output is waiting, insert non-valid word
                  flu_reg_we(1) <= '1';
                  next_statein <= fsmin_word1;
               end if;
            else
               next_statein <= fsmin_default;
            end if;
         when fsmin_word1 => --! flu_word1 written, trying to write flu_word2
                             --! and trying to write qdr_word0
            if (state_clear = '0') then
               next_statein <= current_statein;
               if (fifo_full = '0') then
                  QDR_TX_WR_SRC_RDY <= '1';
                  if (QDR_TX_WR_DST_RDY = '1') then
                     QDR_TX_WR_ADDR <= fifo_end & "0";
                     FLU_RX_DST_RDY <= '1';
                     if (FLU_RX_SRC_RDY = '1') then
                        flu_reg_we(2) <= '1';
                        flu_reg_vld(2) <= '1';
                        next_statein <= fsmin_word2;
                     elsif (FLU_TX_DST_RDY = '1' or state_disable = '1' or state_replay = '1'
                           or state_replay_repeated = '1') then
                        --! no input, but output is waiting, insert non-valid word
                        flu_reg_we(2) <= '1';
                        next_statein <= fsmin_word2;
                     else
                        next_statein <= fsmin_word2_wait;
                     end if;
                  end if;
               end if;
            else
               next_statein <= fsmin_default;
            end if;
         when fsmin_word2_wait => --! qdr_word0 written, trying to write flu_word2
            if (state_clear = '0') then
               next_statein <= current_statein;
               FLU_RX_DST_RDY <= '1';
               if (FLU_RX_SRC_RDY = '1') then
                  flu_reg_we(2) <= '1';
                  flu_reg_vld(2) <= '1';
                  next_statein <= fsmin_word2;
               elsif (FLU_TX_DST_RDY = '1' or state_disable = '1' or state_replay = '1'
                     or state_replay_repeated = '1') then
                  --! no input, but output is waiting, insert non-valid word
                  flu_reg_we(2) <= '1';
                  next_statein <= fsmin_word2;
               end if;
            else
               next_statein <= fsmin_default;
            end if;
         when fsmin_word2 => --! qdr_word0 written, flu_word2 written, trying to write qdr_word1,
                             --! trying to write flu_word0
            if (state_clear = '0') then
               next_statein <= current_statein;
               flu_mux_sel <= "1";
               if (fifo_full = '0') then
                  QDR_TX_WR_SRC_RDY <= '1';
                  if (QDR_TX_WR_DST_RDY = '1') then
                     QDR_TX_WR_ADDR <= fifo_end & "1";
                     fifo_end_inc <= '1';
                     if (state_disable = '0' and state_replay = '0' and state_replay_repeated = '0') then
                        FLU_RX_DST_RDY <= '1';
                        if (FLU_RX_SRC_RDY = '1') then
                           flu_reg_we(0) <= '1';
                           flu_reg_vld(0) <= '1';
                           next_statein <= fsmin_word0;
                        else
                           next_statein <= fsmin_default;
                        end if;
                     else
                        next_statein <= fsmin_default;
                     end if;
                  end if;
               end if;
            else
               next_statein <= fsmin_default;
            end if;
      end case;
   end process;

   --! QDR read request FSM
   --! FSM process
   fsmrdp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RST = '1') then
            current_staterd <= fsmrd_disable;
         else
            current_staterd <= next_staterd;
         end if;
      end if;
   end process;

   --! FSM output/next state logic
   next_state_logicrdp: process (current_staterd, QDR_TX_RD_DST_RDY, fifo_empty, rd_cnt_full,
                                 next_state_disable, next_state_fifo, next_state_capture,
                                 next_state_replay, next_state_replay_repeated, next_state_clear,
                                 NEXT_STATE_SRC_RDY, fifo_start, fifo_pointer, fifo_pointer_ov,
                                 cnt_delay_ov)
   begin
      --! Default values
      fifo_start_inc <= '0';
      rd_addr <= fifo_start;
      rd_addr_lsb <= '0';
      rd_cnt_inc <= '0';
      QDR_TX_RD_SRC_RDY <= '0';
      NEXT_STATE_DST_RDY <= '0';
      CURRENT_STATE <= STORAGE_DISABLE;
      state_disable <= '0';
      state_fifo <= '0';
      state_capture <= '0';
      state_replay <= '0';
      state_replay_repeated <= '0';
      state_clear <= '0';
      fifo_pointer_init <= '0';
      fifo_pointer_inc <= '0';
      cnt_delay_inc <= '0';

      case current_staterd is

         when fsmrd_disable =>
            next_staterd <= current_staterd;
            state_disable <= '1';
            NEXT_STATE_DST_RDY <= '1';
            if (NEXT_STATE_SRC_RDY = '1') then
               if (next_state_fifo = '1') then
                  next_staterd <= fsmrd_fifo_word0;
               elsif (next_state_capture = '1') then
                  next_staterd <= fsmrd_capture;
               elsif (next_state_replay = '1') then
                  next_staterd <= fsmrd_replay;
                  fifo_pointer_init <= '1';
               elsif (next_state_replay_repeated = '1') then
                  next_staterd <= fsmrd_replay_repeated;
                  fifo_pointer_init <= '1';
               elsif (next_state_clear = '1') then
                  next_staterd <= fsmrd_clear;
               end if;
            end if;

         when fsmrd_fifo_word0 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_FIFO;
            state_fifo <= '1';
            NEXT_STATE_DST_RDY <= '1';
            if (NEXT_STATE_SRC_RDY = '1' and next_state_fifo = '0') then
               if (next_state_disable = '1') then
                  next_staterd <= fsmrd_disable;
               elsif (next_state_capture = '1') then
                  next_staterd <= fsmrd_capture;
               elsif (next_state_replay = '1') then
                  next_staterd <= fsmrd_replay;
                  fifo_pointer_init <= '1';
               elsif (next_state_replay_repeated = '1') then
                  next_staterd <= fsmrd_replay_repeated;
                  fifo_pointer_init <= '1';
               elsif (next_state_clear = '1') then
                  next_staterd <= fsmrd_clear;
               end if;
            else
               if (fifo_empty = '0' and rd_cnt_full = '0') then
                  QDR_TX_RD_SRC_RDY <= '1';
                  if (QDR_TX_RD_DST_RDY = '1') then
                     next_staterd <= fsmrd_fifo_word1;
                     rd_cnt_inc <= '1';
                  end if;
               end if;
            end if;

         when fsmrd_fifo_word1 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_FIFO;
            state_fifo <= '1';
            if (fifo_empty = '0' and rd_cnt_full = '0') then
               QDR_TX_RD_SRC_RDY <= '1';
               rd_addr_lsb <= '1';
               if (QDR_TX_RD_DST_RDY = '1') then
                  next_staterd <= fsmrd_fifo_word0;
                  rd_cnt_inc <= '1';
                  fifo_start_inc <= '1';
               end if;
            end if;

         when fsmrd_capture =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_CAPTURE;
            state_capture <= '1';
            NEXT_STATE_DST_RDY <= '1';
            if (NEXT_STATE_SRC_RDY = '1') then
               if (next_state_disable = '1') then
                  next_staterd <= fsmrd_disable;
               elsif (next_state_fifo = '1') then
                  next_staterd <= fsmrd_fifo_word0;
               elsif (next_state_replay = '1') then
                  next_staterd <= fsmrd_replay;
                  fifo_pointer_init <= '1';
               elsif (next_state_replay_repeated = '1') then
                  next_staterd <= fsmrd_replay_repeated;
                  fifo_pointer_init <= '1';
               elsif (next_state_clear = '1') then
                  next_staterd <= fsmrd_clear;
               end if;
            end if;

         when fsmrd_replay =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY;
            state_replay <= '1';
            if (cnt_delay_ov = '1') then
               next_staterd <= fsmrd_replay_word0;
            else
               cnt_delay_inc <= '1';
            end if;

         when fsmrd_replay_word0 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY;
            state_replay <= '1';
            rd_addr <= fifo_pointer;
            if (fifo_pointer_ov = '1') then
                  next_staterd <= fsmrd_disable;
            else
               if (fifo_empty = '0') then
                  if (rd_cnt_full = '0') then
                     QDR_TX_RD_SRC_RDY <= '1';
                     if (QDR_TX_RD_DST_RDY = '1') then
                        next_staterd <= fsmrd_replay_word1;
                        rd_cnt_inc <= '1';
                     end if;
                  end if;
               else
                  next_staterd <= fsmrd_disable;
               end if;
            end if;

         when fsmrd_replay_word1 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY;
            state_replay <= '1';
            rd_addr <= fifo_pointer;
            if (fifo_empty = '0' and rd_cnt_full = '0') then
               QDR_TX_RD_SRC_RDY <= '1';
               rd_addr_lsb <= '1';
               if (QDR_TX_RD_DST_RDY = '1') then
                  next_staterd <= fsmrd_replay_word0;
                  rd_cnt_inc <= '1';
                  fifo_pointer_inc <= '1';
               end if;
            end if;

         when fsmrd_replay_repeated =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY_REPEATED;
            state_replay_repeated <= '1';
            if (cnt_delay_ov = '1') then
               next_staterd <= fsmrd_replay_repeated_word0;
            else
               cnt_delay_inc <= '1';
            end if;

         when fsmrd_replay_repeated_word0 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY_REPEATED;
            state_replay_repeated <= '1';
            rd_addr <= fifo_pointer;
            if (fifo_pointer_ov = '1' and NEXT_STATE_SRC_RDY = '1'
                and next_state_replay_repeated = '0') then
               NEXT_STATE_DST_RDY <= '1';
               if (next_state_disable = '1') then
                  next_staterd <= fsmrd_disable;
               elsif (next_state_capture = '1') then
                  next_staterd <= fsmrd_capture;
               elsif (next_state_replay = '1') then
                  next_staterd <= fsmrd_replay;
                  fifo_pointer_init <= '1';
               elsif (next_state_fifo = '1') then
                  next_staterd <= fsmrd_fifo_word0;
               elsif (next_state_clear = '1') then
                  next_staterd <= fsmrd_clear;
               end if;
            else
               if (fifo_empty = '0') then
                  if (rd_cnt_full = '0') then
                     QDR_TX_RD_SRC_RDY <= '1';
                     if (QDR_TX_RD_DST_RDY = '1') then
                        next_staterd <= fsmrd_replay_repeated_word1;
                        rd_cnt_inc <= '1';
                     end if;
                  end if;
               else
                  next_staterd <= fsmrd_disable;
               end if;
            end if;

         when fsmrd_replay_repeated_word1 =>
            next_staterd <= current_staterd;
            CURRENT_STATE <= STORAGE_REPLAY_REPEATED;
            state_replay_repeated <= '1';
            rd_addr <= fifo_pointer;
            if (fifo_empty = '0' and rd_cnt_full = '0') then
               QDR_TX_RD_SRC_RDY <= '1';
               rd_addr_lsb <= '1';
               if (QDR_TX_RD_DST_RDY = '1') then
                  next_staterd <= fsmrd_replay_repeated_word0;
                  rd_cnt_inc <= '1';
                  fifo_pointer_inc <= '1';
               end if;
            end if;

         when fsmrd_clear =>
            next_staterd <= fsmrd_disable;
            CURRENT_STATE <= STORAGE_CLEAR;
            state_clear <= '1';

      end case;
   end process;

   --! Connect read request to entity interface
   QDR_TX_RD_ADDR <= rd_addr & rd_addr_lsb;

   --! Read request counter
   rd_cntp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RST = '1') then
            rd_cnt <= (others => '0');
         elsif (rd_cnt_inc = '1' and rd_cnt_dec = '0') then
            rd_cnt <= rd_cnt + 1;
         elsif (rd_cnt_dec = '1' and rd_cnt_inc = '0') then
            rd_cnt <= rd_cnt - 1;
         end if;
      end if;
   end process;

   rd_cnt_full <= '1' when (rd_cnt = "111111111") else '0';

   --! Next state comparators
   next_state_disable         <= '1' when (NEXT_STATE = STORAGE_DISABLE) else '0';
   next_state_fifo            <= '1' when (NEXT_STATE = STORAGE_FIFO) else '0';
   next_state_capture         <= '1' when (NEXT_STATE = STORAGE_CAPTURE) else '0';
   next_state_replay          <= '1' when (NEXT_STATE = STORAGE_REPLAY) else '0';
   next_state_replay_repeated <= '1' when (NEXT_STATE = STORAGE_REPLAY_REPEATED) else '0';
   next_state_clear           <= '1' when (NEXT_STATE = STORAGE_CLEAR) else '0';

   --! output registers --------------------------------------------------------
   qdr_reg0p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (qdr_reg_we(0) = '1') then
            qdr_reg0 <= QDR_RX_DATA(785 downto 0);
         end if;
      end if;
   end process;

   qdr_reg1p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (qdr_reg_we(1) = '1') then
            qdr_reg1 <= QDR_RX_DATA(785 downto 0);
         end if;
      end if;
   end process;

   --! output multiplexor

   qdr_mux_in <= qdr_reg1(785 downto 263) & qdr_reg1(261 downto 0) & qdr_reg0(785 downto 525)
                 & qdr_reg0(523 downto 1);
   qdr_reg_vld(0) <= qdr_reg0(0);
   qdr_reg_vld(1) <= qdr_reg0(524);
   qdr_reg_vld(2) <= qdr_reg1(262);

   qdr_muxe:entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 523,
      MUX_WIDTH   => 3   -- multiplexer width (number of inputs)
   )
   port map(
      DATA_IN     => qdr_mux_in,
      SEL         => qdr_mux_sel,
      DATA_OUT    => qdr_mux_out
   );

   --! Connect output multiplexor output to entity interface
   FLU_TX_DATA <= qdr_mux_out(511 downto 0);
   FLU_TX_SOP_POS <= qdr_mux_out(514 downto 512);
   FLU_TX_EOP_POS <= qdr_mux_out(520 downto 515);
   FLU_TX_SOP <= qdr_mux_out(521);
   FLU_TX_EOP <= qdr_mux_out(522);

   --! output FSM
   --! FSM process
   fsmoutp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RST = '1') then
            current_stateout <= fsmout_default;
         else
            current_stateout <= next_stateout;
         end if;
      end if;
   end process;

   --! FSM output next state logic
   next_state_logicoutp: process (current_stateout, qdr_reg_vld, FLU_TX_DST_RDY, QDR_RX_SRC_RDY)
   begin
      --! Default values
      qdr_reg_we <= (others => '0');
      qdr_mux_sel <= "00";
      FLU_TX_SRC_RDY <= '1';
      QDR_RX_DST_RDY <= '1';
      rd_cnt_dec <= '0';
      case current_stateout is
         when fsmout_default => --! trying to write qdr_word0
            next_stateout <= current_stateout;
            FLU_TX_SRC_RDY <= '0';
            if (QDR_RX_SRC_RDY = '1') then
               qdr_reg_we(0) <= '1';
               rd_cnt_dec <= '1';
               next_stateout <= fsmout_word0;
            end if;
         when fsmout_word0 => --! qdr_word0 written, trying to write flu_word0, trying to write qdr_word1
            next_stateout <= current_stateout;
            FLU_TX_SRC_RDY <= qdr_reg_vld(0);
            if (FLU_TX_DST_RDY = '1' or qdr_reg_vld(0) = '0') then
               if (QDR_RX_SRC_RDY = '1') then
                  qdr_reg_we(1) <= '1';
                  rd_cnt_dec <= '1';
                  next_stateout <= fsmout_word1;
               else
                  next_stateout <= fsmout_word1_wait;
               end if;
            else
               QDR_RX_DST_RDY <= '0';
            end if;
         when fsmout_word1_wait => --! qdr_word0 written, trying to write qdr_word1
            next_stateout <= current_stateout;
            FLU_TX_SRC_RDY <= '0';
            if (QDR_RX_SRC_RDY = '1') then
               qdr_reg_we(1) <= '1';
               rd_cnt_dec <= '1';
               next_stateout <= fsmout_word1;
            end if;
         when fsmout_word1 => --! qdr_word1 written, trying to write flu_word1
            next_stateout <= current_stateout;
            qdr_mux_sel <= "01";
            QDR_RX_DST_RDY <= '0';
            FLU_TX_SRC_RDY <= qdr_reg_vld(1);
            if (FLU_TX_DST_RDY = '1' or qdr_reg_vld(1) = '0') then
               next_stateout <= fsmout_word2;
            end if;
         when fsmout_word2 =>
            next_stateout <= current_stateout;
            qdr_mux_sel <= "10";
            FLU_TX_SRC_RDY <= qdr_reg_vld(2);
            if (FLU_TX_DST_RDY = '1' or qdr_reg_vld(2) = '0') then
               if (QDR_RX_SRC_RDY = '1') then
                  qdr_reg_we(0) <= '1';
                  rd_cnt_dec <= '1';
                  next_stateout <= fsmout_word0;
               else
                  next_stateout <= fsmout_default;
               end if;
            else
               QDR_RX_DST_RDY <= '0';
            end if;
      end case;
   end process;

end architecture;
