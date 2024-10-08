-- discard_stat_arch.vhd: FrameLink Discard entity.
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_discard_stat is

   constant MEM_ITEMS   : integer := 2**log2(CHANNELS);

   signal stat_rd       : std_logic;
   signal stat_pass     : std_logic;
   signal stat_drop     : std_logic;
   signal stat_chan     : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal stat_len      : std_logic_vector(15 downto 0);
   signal stat_free     : std_logic_vector(15 downto 0);

   signal reg_stat_pass : std_logic;
   signal reg_stat_drop : std_logic;
   signal reg_stat_len  : std_logic_vector(15 downto 0);
   signal reg_stat_chan : std_logic_vector(log2(CHANNELS)-1 downto 0);

   signal pass_we       : std_logic;
   signal drop_we       : std_logic;
   signal stat_we       : std_logic;

   signal drop_do       : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_do       : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal drop_len_do   : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_len_do   : std_logic_vector(CNT_WIDTH-1 downto 0);

   signal reg_drop_do   : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_pass_do   : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_drop_len_do:std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_pass_len_do:std_logic_vector(CNT_WIDTH-1 downto 0);

   signal drop_add      : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_add      : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal drop_len_add  : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_len_add  : std_logic_vector(CNT_WIDTH-1 downto 0);

   signal drop_di_mx    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_di_mx    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal drop_len_di_mx:std_logic_vector(CNT_WIDTH-1 downto 0);
   signal pass_len_di_mx:std_logic_vector(CNT_WIDTH-1 downto 0);

   signal addr_wr_mx    : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal addr_rd_mx    : std_logic_vector(log2(CHANNELS)-1 downto 0);

   -- Register clearing in progress
   signal clr_running   : std_logic;
   -- Register clearing counter
   signal clr_cnt_chan  : std_logic_vector(log2(CHANNELS)-1 downto 0);

   -- Count enable register
   signal reg_run       : std_logic;

   -- MI32 signals
   signal mi_reg1_drdy  : std_logic;
   signal mi_reg2_drdy  : std_logic;
   signal mi_reg3_drdy  : std_logic;
   signal sig_mi_ardy   : std_logic;
   signal mi_rd_ok      : std_logic;

   -- MI read address
   signal mi_addr_chan  : std_logic_vector(log2(CHANNELS)-1 downto 0);

   signal mi_drop       : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal mi_pass       : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal mi_pass_len   : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal mi_drop_len   : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_mi_drop    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_mi_pass    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_mi_pass_len: std_logic_vector(CNT_WIDTH-1 downto 0);
   signal reg_mi_drop_len: std_logic_vector(CNT_WIDTH-1 downto 0);

   signal reg_mi_addr1  : std_logic_vector(31 downto 0);
   signal reg_mi_addr2  : std_logic_vector(31 downto 0);

   -- output muxing
   signal mi_cnt_mux    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal mi_cnt_mux64  : std_logic_vector(63 downto 0);
   signal reg_mi_cnt_mux64 : std_logic_vector(63 downto 0);
   signal mi_word_mux   : std_logic_vector(31 downto 0);
   signal mi_top_mux    : std_logic_vector(31 downto 0);
   signal mi_reg_top_mux: std_logic_vector(31 downto 0);

   signal zeros         : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal zeros64       : std_logic_vector(63 downto 0);
   signal ones          : std_logic_vector(log2(CHANNELS)-1 downto 0);

begin

   assert CNT_WIDTH >= 16
      report "FL_DISCARD_STAT: CNT_WIDTH must be >= 16!"
      severity ERROR;

   assert CNT_WIDTH <= 64
      report "FL_DISCARD_STAT: CNT_WIDTH must be <= 64!"
      severity ERROR;

   zeros <= (others => '0');
   zeros64 <= (others => '0');
   ones <= (others => '1');

   fl_discard_i : entity work.fl_discard
   generic map (
      -- FrameLink data width
      DATA_WIDTH  => DATA_WIDTH,
      -- Number of channels
      CHANNELS    => CHANNELS,
      -- Width of the STATUS signal for each channel, up to 16 bits
      STATUS_WIDTH  => STATUS_WIDTH,
      -- Generate output register on output FrameLink
      OUTPUT_REG    => OUTPUT_REG
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      -- Write interf-- Write inace
      RX_DATA     => RX_DATA,
      RX_DREM     => RX_DREM,
      RX_SRC_RDY_N=> RX_SRC_RDY_N,
      RX_DST_RDY_N=> RX_DST_RDY_N,
      RX_SOP_N    => RX_SOP_N,
      RX_EOP_N    => RX_EOP_N,
      RX_SOF_N    => RX_SOF_N,
      RX_EOF_N    => RX_EOF_N,
      -- Must be vali-- Must be d with SOF
      RX_CHAN     => RX_CHAN,
      -- Read interfa-- Read intces
      TX_DATA     => TX_DATA,
      TX_DREM     => TX_DREM,
      TX_SRC_RDY_N=> TX_SRC_RDY_N,
      --TX_DST_RDY_N=> TX_DST_RDY_N,
      TX_SOP_N    => TX_SOP_N,
      TX_EOP_N    => TX_EOP_N,
      TX_SOF_N    => TX_SOF_N,
      TX_EOF_N    => TX_EOF_N,
      -- Is valid dur-- Is validing the whole frame
      TX_CHAN     => TX_CHAN,
      -- Signal STATUS indikates filling of buffer for each channel
      STATUS      => STATUS,

      STAT_PASS   => stat_pass,
      STAT_DROP   => stat_drop,
         -- Channel number (active with PASS od DROP)
      STAT_CHAN   => stat_chan,
         -- Frame length (active with PASS od DROP)
      STAT_LEN    => stat_len,
         -- Free space (active with PASS od DROP)
      STAT_FREE   => stat_free,

      STAT_CLEARING => clr_running
   );

   -- Delay inputs for one cycle
   reg_stat_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_stat_drop <= '0';
            reg_stat_pass <= '0';
         else
            reg_stat_drop <= stat_drop;
            reg_stat_pass <= stat_pass;
         end if;
         -- No reset needed for data signals
         reg_stat_len <= stat_len;
         reg_stat_chan <= stat_chan;
      end if;
   end process;

   -- Write if event occured in discard (with 1 cycle delay) or if clearing
   drop_we <= (reg_run and reg_stat_drop) or clr_running;
   pass_we <= (reg_run and reg_stat_pass) or clr_running;

   stat_rd <= stat_pass or stat_drop;

   -- Present normal (read) address if not clearing
   with clr_running select
      addr_wr_mx <= clr_cnt_chan  when '1',
                    reg_stat_chan when others;

   -- Present current read address if reading, mi address else
   with stat_rd select
      addr_rd_mx <= stat_chan    when '1',
                    mi_addr_chan when others;

   gen_count_drop : if COUNT_DROP = true generate
      --* Counters of dropped frames
      count_drop_i : entity work.DP_DISTMEM
      generic map(
         DATA_WIDTH  => CNT_WIDTH,
         ITEMS       => MEM_ITEMS
      )
      port map(
         DI          => drop_di_mx,
         WE          => drop_we,
         WCLK        => CLK,
         ADDRA       => addr_wr_mx,
         DOA         => open,

         ADDRB       => addr_rd_mx,
         DOB         => drop_do
      );

      reg_drop_do_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            reg_drop_do <= drop_do;
         end if;
      end process;

      drop_add <= reg_drop_do + 1;
      mi_drop <= drop_do;

      with clr_running select
         drop_di_mx <= drop_add when '0',
                       zeros when others;
   end generate;

   gen_not_count_drop : if COUNT_DROP = false generate
      mi_drop <= zeros;
   end generate;

   gen_count_pass : if COUNT_PASS = true generate
      --* Counters of passed frames
      count_pass_i : entity work.DP_DISTMEM
      generic map(
         DATA_WIDTH  => CNT_WIDTH,
         ITEMS       => MEM_ITEMS
      )
      port map(
         DI          => pass_di_mx,
         WE          => pass_we,
         WCLK        => CLK,
         ADDRA       => addr_wr_mx,
         DOA         => open,

         ADDRB       => addr_rd_mx,
         DOB         => pass_do
      );

      reg_pass_do_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            reg_pass_do <= pass_do;
         end if;
      end process;

      pass_add <= reg_pass_do + 1;
      mi_pass <= pass_do;

      with clr_running select
         pass_di_mx <= pass_add when '0',
                       zeros when others;
   end generate;

   gen_not_pass_drop : if COUNT_PASS = false generate
      mi_pass <= zeros;
   end generate;

   gen_count_drop_len : if COUNT_DROP_LEN = true generate
      --* Counters of dropped bytes
      count_drop_len_i : entity work.DP_DISTMEM
      generic map(
         DATA_WIDTH  => CNT_WIDTH,
         ITEMS       => MEM_ITEMS
      )
      port map(
         DI          => drop_len_di_mx,
         WE          => drop_we,
         WCLK        => CLK,
         ADDRA       => addr_wr_mx,
         DOA         => open,

         ADDRB       => addr_rd_mx,
         DOB         => drop_len_do
      );

      reg_drop_len_do_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            reg_drop_len_do <= drop_len_do;
         end if;
      end process;

      drop_len_add <= reg_drop_len_do + reg_stat_len;
      mi_drop_len <= drop_len_do;

      with clr_running select
         drop_len_di_mx <= drop_len_add when '0',
                           zeros when others;
   end generate;

   gen_not_count_drop_len : if COUNT_DROP_LEN = false generate
      mi_drop_len <= zeros;
   end generate;

   gen_cnt_pass_len : if COUNT_PASS_LEN = true generate
      --* Counters of passed bytes
      count_pass_len_i : entity work.DP_DISTMEM
      generic map(
         DATA_WIDTH  => CNT_WIDTH,
         ITEMS       => MEM_ITEMS
      )
      port map(
         DI          => pass_len_di_mx,
         WE          => pass_we,
         WCLK        => CLK,
         ADDRA       => addr_wr_mx,
         DOA         => open,

         ADDRB       => addr_rd_mx,
         DOB         => pass_len_do
      );

      reg_pass_len_do_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            reg_pass_len_do <= pass_len_do;
         end if;
      end process;

      pass_len_add <= reg_pass_len_do + reg_stat_len;
      mi_pass_len <= pass_len_do;

      with clr_running select
         pass_len_di_mx <= pass_len_add when '0',
                           zeros when others;
   end generate;

   gen_not_pass_len_drop : if COUNT_PASS_LEN = false generate
      mi_pass_len <= zeros;
   end generate;

   -- ----------------------------------------------------
   -- MI32 read interface
   -- ----------------------------------------------------

   -- Couter address
   mi_addr_chan <= MI_ADDR(3+log2(CHANNELS)-1 downto 3);

   reg_mi_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         reg_mi_drop    <= mi_drop;
         reg_mi_pass    <= mi_pass;
         reg_mi_pass_len<= mi_pass_len;
         reg_mi_drop_len<= mi_drop_len;

         reg_mi_addr2 <= reg_mi_addr1;
         reg_mi_addr1 <= MI_ADDR;
      end if;
   end process;

   -- Select channel
   mi_cnt_mux_p : process(reg_mi_addr1, reg_mi_drop, reg_mi_pass,
                          reg_mi_drop_len, reg_mi_pass_len)
   begin
      case reg_mi_addr1(10 downto 9) is
         when "00" => mi_cnt_mux <= reg_mi_drop;
         when "01" => mi_cnt_mux <= reg_mi_pass;
         when "10" => mi_cnt_mux <= reg_mi_drop_len;
         when others => mi_cnt_mux <= reg_mi_pass_len;
      end case;
   end process;

   width64_gen : if CNT_WIDTH = 64 generate
      mi_cnt_mux64 <= mi_cnt_mux;
   end generate;

   not_width64_gen : if CNT_WIDTH < 64 generate
      mi_cnt_mux64 <= zeros64(63 downto CNT_WIDTH) & mi_cnt_mux;
   end generate;

   reg_mi_cnt_mux64_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         reg_mi_cnt_mux64 <= mi_cnt_mux64;
      end if;
   end process;

   -- Select low or high word
   mi_word_mux_p : process(reg_mi_addr2, reg_mi_cnt_mux64)
   begin
      if reg_mi_addr2(2) = '0' then
         mi_word_mux <= reg_mi_cnt_mux64(31 downto 0);
      else
         mi_word_mux <= reg_mi_cnt_mux64(63 downto 32);
      end if;
   end process;

   -- Select counters or stat/ctrl register
   mi_top_mux_p : process(mi_word_mux, reg_mi_addr2, clr_running, reg_run)
   begin
      if reg_mi_addr2(11) = '0' then
         mi_top_mux <= mi_word_mux;
      else
         mi_top_mux <= zeros64(31 downto 2) & clr_running & reg_run;
      end if;
   end process;

   -- Register MI output
   -- Delay RD for one cycle
   mi_reg_top_mux_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         mi_reg_top_mux <= mi_top_mux;
         mi_reg3_drdy <= mi_reg2_drdy;
         mi_reg2_drdy <= mi_reg1_drdy;
         mi_reg1_drdy <= mi_rd_ok;
      end if;
   end process;

   MI_DRD <= mi_reg_top_mux;
   MI_DRDY <= mi_reg3_drdy;

   -- Respond on ARDY immediately, but only if not reading
   sig_mi_ardy <= (MI_RD and not stat_rd) or MI_WR;
   MI_ARDY <= sig_mi_ardy;

   mi_rd_ok <= sig_mi_ardy and MI_RD;

   -- ----------------------------------------------------
   -- MI32 write interface
   -- ----------------------------------------------------
   reg_run_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_run <= '1';
         else
            if MI_ADDR = X"00000800" and MI_BE(0) = '1' and MI_WR = '1' then
               reg_run <= MI_DWR(0);
            end if;
         end if;
      end if;
   end process;

   clr_running_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            clr_running <= '1'; -- Clear all after reset
         else
            if MI_ADDR = X"00000800" and MI_BE(0) = '1' and
               MI_WR = '1' and MI_DWR(1) = '1' then
               clr_running <= '1';
            elsif clr_cnt_chan = ones then
               clr_running <= '0';
            end if;
         end if;
      end if;
   end process;

   -- Counter for clearing all counters
   clr_cnt_chan_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            clr_cnt_chan <= (others => '0');
         else
            if clr_running = '1' then
               clr_cnt_chan <= clr_cnt_chan + 1;
            end if;
         end if;
      end if;
   end process;

end architecture full;
