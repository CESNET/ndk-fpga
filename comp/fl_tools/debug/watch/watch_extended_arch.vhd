-- fl_watch_arch.vhd: Frame Link watch component to gather statistics
-- Copyright (C) 2006 CESNET
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

-- library with MI_32 interface definition
use work.mi32_pkg.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_WATCH_EXTENDED is

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

begin

-- Debug asserts:
-- assert false report "addr_w: " & integer'image(addr_w) severity note;
-- assert false report "items: " & integer'image(items) severity note;

-- pipeline inputs to get rid of troubles with frequency
process(CLK, RESET)
begin
   if RESET = '1' then
      pipe_sof_n(0) <= (others => '1');
      pipe_eof_n(0) <= (others => '1');
      pipe_sop_n(0) <= (others => '1');
      pipe_eop_n(0) <= (others => '1');
      pipe_dst_rdy_n(0) <= (others => '1');
      pipe_src_rdy_n(0) <= (others => '1');
   elsif CLK'event and CLK = '1' then
      pipe_sof_n(0) <= SOF_N;
      pipe_eof_n(0) <= EOF_N;
      pipe_sop_n(0) <= SOP_N;
      pipe_eop_n(0) <= EOP_N;
      pipe_dst_rdy_n(0) <= DST_RDY_N;
      pipe_src_rdy_n(0) <= SRC_RDY_N;
   end if;
end process;
pipe : for i in 2 to PIPELINE_LEN generate
   process(CLK, RESET)
   begin
      if RESET = '1' then
         pipe_sof_n(i-1) <= (others => '1');
         pipe_eof_n(i-1) <= (others => '1');
         pipe_sop_n(i-1) <= (others => '1');
         pipe_eop_n(i-1) <= (others => '1');
         pipe_dst_rdy_n(i-1) <= (others => '1');
         pipe_src_rdy_n(i-1) <= (others => '1');
      elsif CLK'event and CLK = '1' then
         pipe_sof_n(i-1) <= pipe_sof_n(i-2);
         pipe_eof_n(i-1) <= pipe_eof_n(i-2);
         pipe_sop_n(i-1) <= pipe_sop_n(i-2);
         pipe_eop_n(i-1) <= pipe_eop_n(i-2);
         pipe_dst_rdy_n(i-1) <= pipe_dst_rdy_n(i-2);
         pipe_src_rdy_n(i-1) <= pipe_src_rdy_n(i-2);
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
   cntr_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         counters(i) <= (others => '0');
      elsif CLK'event and CLK = '1' then
         if sig_eof_n(i) = '0' and sig_dst_rdy_n(i) = '0' and
            sig_src_rdy_n(i) = '0' and reg_en = '1' then
            counters(i) <= counters(i) + 1;
         end if;
      end if;
   end process;

   -- Guard funcion is enabled
   guard_gen : if GUARD = true generate
      -- Counters of invalid frames
      g_cntr_p : process(CLK, RESET)
      begin
         if RESET = '1' then
            g_counters(i) <= (others => '0');
         elsif CLK'event and CLK = '1' then
            if reg_en = '1' and invalid(i) = '1' then
               g_counters(i) <= g_counters(i) + 1;
            end if;
         end if;
      end process;

      -- Array of FL_GUARDS to detect invalid frames
      guard_inst : entity work.FL_GUARD_EXTENDED
      generic map(
         PARTS       => PARTS
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

-- This register enables counters. After RESET it is enabled (1)
reg_en_p : process(CLK, RESET)
begin
   if RESET = '1' then
      reg_en <= '1';
   elsif CLK'event and CLK = '1' then
      if MI.WR = '1' and MI.BE(0) = '1' and MI.ADDR(addr_w+1 downto 2) = 0 then
         reg_en <= MI.DWR(0);
      end if;
   end if;
end process;

-- Reading has one cycle latency
reg_drdy_p : process(CLK, RESET)
begin
   if RESET = '1' then
      reg_drdy <= '0';
   elsif CLK'event and CLK = '1' then
      reg_drdy <= MI.RD;
   end if;
end process;

zeros <= (others => '0');

-- What an ugly mux!
muxp : process(counters, g_counters, reg_en, MI.ADDR, zeros)
begin
   out_mux <= zeros;

   -- Map Enable register
   if MI.ADDR(addr_w+1 downto 2) = 0 then
      out_mux <= zeros(31 downto 1) & reg_en;
   end if;
   -- Leave 32 bits for future purposes
   if MI.ADDR(addr_w+1 downto 2) = 1 then
      out_mux <= zeros;
   end if;
   -- Map frame counters
   for i in 0 to INTERFACES-1 loop -- i is index of counter
      for j in 0 to (CNTR_WIDTH-1)/32 loop -- j is index of 32 bit part of cntr
         if MI.ADDR(addr_w+1 downto 2) = 2 + -- offset by first two registers
                                         i*((CNTR_WIDTH-1)/32+1) -- cntr offset
                                         + j then -- part of counter
            if 32*(j+1) > CNTR_WIDTH then
               out_mux <= zeros(31 downto CNTR_WIDTH mod 32) &
                          counters(i)(CNTR_WIDTH-1 downto 32*j);
            else
               out_mux <= counters(i)(32*(j+1)-1 downto 32*j);
            end if;
         end if;
      end loop;
   end loop;
   -- Map invalid frame counters
   for i in 0 to INTERFACES-1 loop -- i is index of counter
      for j in 0 to (CNTR_WIDTH-1)/32 loop -- j is index of 32 bit part of cntr
         if MI.ADDR(addr_w+1 downto 2) = 2 + -- offset by first two registers
                                         INTERFACES*((CNTR_WIDTH-1)/32+1) +
                                             -- offset from frame counters
                                         i*((CNTR_WIDTH-1)/32+1) -- cntr offset
                                         + j then -- part of counter
            if 32*(j+1) > CNTR_WIDTH then
               out_mux <= zeros(31 downto CNTR_WIDTH mod 32) &
                          g_counters(i)(CNTR_WIDTH-1 downto 32*j);
            else
               out_mux <= g_counters(i)(32*(j+1)-1 downto 32*j);
            end if;
         end if;
      end loop;
   end loop;
      -- Map RDY signals
   for i in 0 to INTERFACES-1 loop -- i is index of counter
      if MI.ADDR(addr_w+1 downto 2) = 2 + -- offset by first two registers
                                      INTERFACES*((CNTR_WIDTH-1)/32+1) +
                                             -- offset from frame counters
                                      INTERFACES*((CNTR_WIDTH-1)/32+1) +
                                             -- offset from invalid frame counters
                                      (i)/16 then
                                             -- offset of this set of RDY signals
         if (i < INTERFACES) then
            out_mux(2*(i mod 16)+1 downto 2*(i mod 16)) <= sig_src_rdy_n(i) & sig_dst_rdy_n(i);
         else
            out_mux(2*(i mod 16)+1 downto 2*(i mod 16)) <= "00";
         end if;
      end if;
   end loop;
end process;

-- Register mux output
reg_drd_p : process(CLK, RESET)
begin
   if RESET = '1' then
      reg_drd <= (others => '0');
   elsif CLK'event and CLK = '1' then
      reg_drd <= out_mux;
   end if;
end process;

MI.DRD  <= reg_drd;
MI.ARDY <= '1';
MI.DRDY <= reg_drdy;

end architecture full;
