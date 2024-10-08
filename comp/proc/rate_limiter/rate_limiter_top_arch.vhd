-- rate_limiter_top_arch.vhd
--!
--! \file  rate_limiter_top_arch.vhd
--! \brief The packet flow rate limiter, based on connection speed and tokens
--!        Top level architecture
--!
--! \Author: Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

architecture top of rate_lim_top is

   constant data_width     : integer := LIMIT_WIDTH + SPEED_WIDTH + CONST_WIDTH;
   constant addr_width     : integer := log2(ITEMS_IN_MEM);

   signal read_enable      : std_logic;
   signal limit_data       : std_logic_vector(data_width-1 downto 0);

   signal stage1_en        : std_logic;
   signal reg_in_src_rdy   : std_logic;
   signal reg_addr_vld     : std_logic;
   signal reg_packet_len   : std_logic_vector(15 downto 0);
   signal reg_packet_ts    : std_logic_vector(63 downto 0);
   signal reg_record_addr  : std_logic_vector(addr_width-1 downto 0);

   signal in_dst_rdy_mem   : std_logic;

begin

   read_enable <= IN_SRC_RDY and stage1_en; --TODO

   MI32: entity work.rate_lim_mi32
      generic map (
         ADDR_WIDTH  => addr_width,
         LIMIT_WIDTH => LIMIT_WIDTH,
         SPEED_WIDTH => SPEED_WIDTH,
         CONST_WIDTH => CONST_WIDTH
      )
      port map (
         CLK         => CLK,
         RESET       => RESET,
         MI32_ADDR   => MI32_ADDR,
         MI32_WR     => MI32_WR,
         MI32_DWR    => MI32_DWR,
         MI32_RD     => MI32_RD,
         MI32_DRD    => MI32_DRD,
         MI32_DRDY   => MI32_DRDY,
         MI32_ARDY   => MI32_ARDY,
         MI32_BE     => MI32_BE,

         USER_ADDR   => RECORD_ADDR,
         USER_RD     => read_enable,
         USER_DRD    => limit_data
      );

   --! Pipeline enable/disable logic - DST/SRC ready propagation
   IN_DST_RDY <= stage1_en;
   stage1_en <= '0' when in_dst_rdy_mem = '0' and reg_in_src_rdy = '1' else
                '1';

   --! Pipeline - input data
   --! stage 1
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg_in_src_rdy    <= '0';
            reg_packet_len    <= (others => '0');
            reg_packet_ts     <= (others => '0');
            reg_record_addr   <= (others => '0');
         elsif stage1_en = '1' then
            reg_in_src_rdy    <= IN_SRC_RDY;
            reg_packet_len    <= PACKET_LEN;
            reg_packet_ts     <= PACKET_TS;
            reg_record_addr   <= RECORD_ADDR;
            reg_addr_vld      <= ADDR_VLD;
         end if;
      end if;
   end process;

   RATE_LIMITER: entity work.rate_lim_mem
      generic map (
         ADDR_WIDTH_M   => addr_width,
         LIMIT_WIDTH_M  => LIMIT_WIDTH,
         SPEED_WIDTH_M  => SPEED_WIDTH,
         CONST_WIDTH_M  => CONST_WIDTH
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         PACKET_LEN     => reg_packet_len,
         PACKET_TS      => reg_packet_ts,
         RECORD_ADDR    => reg_record_addr,
         ADDR_VLD       => reg_addr_vld,
         BUCKET_LIMIT   => limit_data(data_width-1 downto data_width-LIMIT_WIDTH),
         SPEED          => limit_data(data_width-LIMIT_WIDTH-1 downto CONST_WIDTH),
         TIME_CONST     => limit_data(CONST_WIDTH-1 downto 0),

         PASS           => PASS,

         IN_SRC_RDY     => reg_in_src_rdy,
         IN_DST_RDY     => in_dst_rdy_mem,
         OUT_SRC_RDY    => OUT_SRC_RDY,
         OUT_DST_RDY    => OUT_DST_RDY
      );

end top;
