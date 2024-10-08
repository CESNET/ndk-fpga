-- watch_arch_norec.vhd: Frame Link watch component to gather statistics with no records inside
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--       Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_WATCH_NOREC is

-- Number of 32 bit fields accesible from MI interface
-- There must be space for two sets of counters, rounded up to 32 bits, and
-- Status and Command register and
-- DRY signals.
constant items   : integer := ((CNTR_WIDTH-1)/32+1) * INTERFACES * 2 +
                              2 +
                              (INTERFACES-1)/16+1;

-- Effective address width (counters and Status register)
constant addr_w  : integer := log2(items);

type t_cnt_arr is array (0 to (INTERFACES-1)) of
                          std_logic_vector(CNTR_WIDTH-1 downto 0);

type t_pipe is array (0 to (PIPELINE_LEN-1)) of
                        std_logic_vector(INTERFACES-1 downto 0);

signal counters      : t_cnt_arr;
signal g_counters    : t_cnt_arr;
signal reg_en        : std_logic;   -- counters enable
signal reg_sel       : std_logic;   -- sample enable
signal reg_hs        : std_logic;   -- have sample

signal pipe_sof_n    : t_pipe;
signal pipe_eof_n    : t_pipe;
signal pipe_sop_n    : t_pipe;
signal pipe_eop_n    : t_pipe;
signal pipe_src_rdy_n: t_pipe;
signal pipe_dst_rdy_n: t_pipe;

signal invalid       : std_logic_vector(INTERFACES-1 downto 0);

signal sig_sof_n     : std_logic_vector(INTERFACES-1 downto 0);
signal sig_eof_n     : std_logic_vector(INTERFACES-1 downto 0);
signal sig_sop_n     : std_logic_vector(INTERFACES-1 downto 0);
signal sig_eop_n     : std_logic_vector(INTERFACES-1 downto 0);
signal sig_src_rdy_n : std_logic_vector(INTERFACES-1 downto 0);
signal sig_dst_rdy_n : std_logic_vector(INTERFACES-1 downto 0);

signal reg_drdy      : std_logic;
signal reg_drd       : std_logic_vector(31 downto 0);
signal out_mux       : std_logic_vector(31 downto 0);

signal zeros         : std_logic_vector(31 downto 0);

signal mux_counters_in_a      : std_logic_vector(32*2*INTERFACES*((CNTR_WIDTH-1)/32+1)-1 downto 0);
signal mux_counters_in_s      : std_logic_vector(32*2*INTERFACES*((CNTR_WIDTH-1)/32+1)-1 downto 0);
signal mux_control       : std_logic_vector(31 downto 0);
signal mux_counters      : std_logic_vector(32*2*INTERFACES*((CNTR_WIDTH-1)/32+1)-1 downto 0);
signal mux_rdy           : std_logic_vector(32*((INTERFACES-1)/16+1)-1 downto 0);

signal mux_in_nice       : std_logic_vector(32*(2+2*INTERFACES*((CNTR_WIDTH-1)/32+1)+(INTERFACES-1)/16+1)-1 downto 0);
signal mux_in_sample     : std_logic_vector(2*32*2*INTERFACES*((CNTR_WIDTH-1)/32+1)-1 downto 0);

begin

-- Debug asserts:
-- assert false report "addr_w: " & integer'image(addr_w) severity note;
-- assert false report "items: " & integer'image(items) severity note;

-- pipeline inputs to get rid of troubles with frequency
process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         pipe_sof_n(0) <= (others => '1');
         pipe_eof_n(0) <= (others => '1');
         pipe_sop_n(0) <= (others => '1');
         pipe_eop_n(0) <= (others => '1');
         pipe_dst_rdy_n(0) <= (others => '1');
         pipe_src_rdy_n(0) <= (others => '1');
      else
         pipe_sof_n(0) <= SOF_N;
         pipe_eof_n(0) <= EOF_N;
         pipe_sop_n(0) <= SOP_N;
         pipe_eop_n(0) <= EOP_N;
         pipe_dst_rdy_n(0) <= DST_RDY_N;
         pipe_src_rdy_n(0) <= SRC_RDY_N;
      end if;
   end if;
end process;
pipe : for i in 2 to PIPELINE_LEN generate
   process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            pipe_sof_n(i-1) <= (others => '1');
            pipe_eof_n(i-1) <= (others => '1');
            pipe_sop_n(i-1) <= (others => '1');
            pipe_eop_n(i-1) <= (others => '1');
            pipe_dst_rdy_n(i-1) <= (others => '1');
            pipe_src_rdy_n(i-1) <= (others => '1');
         else
            pipe_sof_n(i-1) <= pipe_sof_n(i-2);
            pipe_eof_n(i-1) <= pipe_eof_n(i-2);
            pipe_sop_n(i-1) <= pipe_sop_n(i-2);
            pipe_eop_n(i-1) <= pipe_eop_n(i-2);
            pipe_dst_rdy_n(i-1) <= pipe_dst_rdy_n(i-2);
            pipe_src_rdy_n(i-1) <= pipe_src_rdy_n(i-2);
         end if;
      end if;
   end process;
end generate;

sig_sof_n <= pipe_sof_n(PIPELINE_LEN-1);
sig_eof_n <= pipe_eof_n(PIPELINE_LEN-1);
sig_sop_n <= pipe_sop_n(PIPELINE_LEN-1);
sig_eop_n <= pipe_eop_n(PIPELINE_LEN-1);
sig_dst_rdy_n <= pipe_dst_rdy_n(PIPELINE_LEN-1);
sig_src_rdy_n <= pipe_src_rdy_n(PIPELINE_LEN-1);

cntr_gen : for i in 0 to INTERFACES-1 generate
   -- Counters of frames
   cntr_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if ((RESET = '1') or (MI_WR = '1' and MI_BE(0) = '1' and MI_ADDR(addr_w+1 downto 2) = 0 and MI_DWR(1) = '1')) then
            counters(i) <= (others => '0');
         elsif sig_eof_n(i) = '0' and sig_dst_rdy_n(i) = '0' and
            sig_src_rdy_n(i) = '0' and reg_en = '1' then
            counters(i) <= counters(i) + 1;
         end if;
      end if;
   end process;

   -- Guard funcion is enabled
   guard_gen : if GUARD = true generate
      -- Counters of invalid frames
      g_cntr_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if ((RESET = '1') or (MI_WR = '1' and MI_BE(0) = '1' and MI_ADDR(addr_w+1 downto 2) = 0 and MI_DWR(1) = '1')) then
               g_counters(i) <= (others => '0');
            elsif reg_en = '1' and invalid(i) = '1' then
               g_counters(i) <= g_counters(i) + 1;
            end if;
         end if;
      end process;

      -- Array of FL_GUARDS to detect invalid frames
      guard_inst : entity work.FL_GUARD
      generic map(
         HEADER      => HEADER,
         FOOTER      => FOOTER,
         CHECK_PARTS => CHECK_PARTS
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,
         SOF_N       => sig_sof_n(i),
         EOF_N       => sig_eof_n(i),
         SOP_N       => sig_sop_n(i),
         EOP_N       => sig_eop_n(i),
         DST_RDY_N   => sig_dst_rdy_n(i),
         SRC_RDY_N   => sig_src_rdy_n(i),
         INVALID     => invalid(i)
      );
   end generate;

   -- Guard function is disabled - invlalid frame counters are set to zeros
   guard_n_gen : if GUARD = false generate
      g_counters(i) <= (others => '0');
   end generate;

end generate;

-- sample
have_sample_gen : if SAMPLE = true generate
   reg_hs <= '1';
   reg_sel_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_sel <= '0';
         elsif MI_WR = '1' and MI_BE(0) = '1' and MI_ADDR(addr_w+1 downto 2) = 0 then
            reg_sel <= MI_DWR(2);
         end if;
      end if;
   end process;
end generate;
have_sample_n_gen : if SAMPLE = false generate
   reg_hs <= '0';
   reg_sel <= '0';
end generate;

-- This register enables counters. After RESET it is enabled (1)
-- And enables sample. After RESET it is disabled (0)
reg_en_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_en <= '1';
      elsif MI_WR = '1' and MI_BE(0) = '1' and MI_ADDR(addr_w+1 downto 2) = 0 then
         reg_en <= MI_DWR(0);
      end if;
   end if;
end process;

-- sample
sample_p : process(CLK, MI_WR, MI_BE, MI_ADDR, MI_DWR, mux_counters_in_a)
begin
   if CLK'event and CLK = '1' then
      if MI_WR = '1' and MI_BE(0) = '1' and MI_ADDR(addr_w+1 downto 2) = 0 and MI_DWR(3) = '1' then
         mux_counters_in_s <= mux_counters_in_a;
      end if;
   end if;
end process;

-- Reading has one cycle latency
reg_drdy_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_drdy <= '0';
      else
         reg_drdy <= MI_RD;
      end if;
   end if;
end process;

zeros <= (others => '0');

-- Sample or not sample
mux_in_sample <= mux_counters_in_s & mux_counters_in_a;
mux_sample : entity work.gen_mux
generic map(
   DATA_WIDTH  => 32*2*INTERFACES*((CNTR_WIDTH-1)/32+1),
   MUX_WIDTH   => 2
)
port map(
   DATA_IN     => mux_in_sample,
   SEL(0)      => reg_sel,
   DATA_OUT    => mux_counters
);

-- What a nice mux!
mux_in_nice <= mux_rdy & mux_counters & zeros & mux_control;
mux_new : entity work.gen_mux
generic map(
   DATA_WIDTH  => 32,
   MUX_WIDTH   => 2+2*INTERFACES*((CNTR_WIDTH-1)/32+1)+INTERFACES/16+1
)
port map(
   DATA_IN     => mux_in_nice,
   SEL         => MI_ADDR(addr_w+1 downto 2),
   DATA_OUT    => out_mux
);

muxp_new : process(counters, g_counters, reg_en, MI_ADDR, zeros, sig_dst_rdy_n, sig_src_rdy_n, reg_sel, reg_hs)
begin
   -- if SAMPLE = false or reg_sel = '0'' then
      mux_control <= zeros(31 downto 5) & reg_hs & '0' & reg_sel & '0' & reg_en;
      for i in 0 to INTERFACES-1 loop -- i is index of counter
         for j in 0 to (CNTR_WIDTH-1)/32 loop -- j is index of 32 bit part of cntr
            if 32*(j+1) > CNTR_WIDTH then
               mux_counters_in_a(32*(i*((CNTR_WIDTH-1)/32+1) + j + 1) - 1 downto 32*(i*((CNTR_WIDTH-1)/32+1) + j)) <= zeros(31 downto CNTR_WIDTH mod 32) & counters(i)(CNTR_WIDTH-1 downto 32*j);
            else
               mux_counters_in_a(32*(i*((CNTR_WIDTH-1)/32+1) + j + 1) - 1 downto 32*(i*((CNTR_WIDTH-1)/32+1) + j)) <= counters(i)(32*(j+1)-1 downto 32*j);
            end if;
         end loop;
      end loop;
      for i in 0 to INTERFACES-1 loop -- i is index of counter
         for j in 0 to (CNTR_WIDTH-1)/32 loop -- j is index of 32 bit part of cntr
            if 32*(j+1) > CNTR_WIDTH then
               mux_counters_in_a(32*(INTERFACES*((CNTR_WIDTH-1)/32+1) + i*((CNTR_WIDTH-1)/32+1) + j + 1) - 1 downto 32*(INTERFACES*((CNTR_WIDTH-1)/32+1) + i*((CNTR_WIDTH-1)/32+1) + j)) <= zeros(31 downto CNTR_WIDTH mod 32) & g_counters(i)(CNTR_WIDTH-1 downto 32*j);
            else
               mux_counters_in_a(32*(INTERFACES*((CNTR_WIDTH-1)/32+1) + i*((CNTR_WIDTH-1)/32+1) + j + 1) - 1 downto 32*(INTERFACES*((CNTR_WIDTH-1)/32+1) + i*((CNTR_WIDTH-1)/32+1) + j)) <= g_counters(i)(32*(j+1)-1 downto 32*j);
            end if;
         end loop;
      end loop;
      mux_rdy(32*((INTERFACES-1)/16 + 1) - 1 downto 0) <= zeros;
      for i in 0 to INTERFACES-1 loop -- i is index of counter
         mux_rdy(2*i+1 downto 2*i) <= sig_src_rdy_n(i) & sig_dst_rdy_n(i);
      end loop;
   -- end if;
end process;

-- Register mux output
reg_drd_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_drd <= (others => '0');
      else
         reg_drd <= out_mux;
      end if;
   end if;
end process;

MI_DRD  <= reg_drd;
MI_ARDY <= '1';
MI_DRDY <= reg_drdy;

FRAME_ERR <= invalid;

end architecture full;
