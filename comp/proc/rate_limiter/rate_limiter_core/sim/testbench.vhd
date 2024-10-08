-- testbench.vhd
--!
--! \file  testbench.vhd
--! \brief Testbench for rate_limiter
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

entity testbench is

end testbench;

architecture behavioral of testbench is

   --! simulation constants
   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset duration
   constant ADDR_WIDTH     : integer := 4;
   constant LIMIT_WIDTH    : integer := 16;
   constant SPEED_WIDTH    : integer := 20;
   constant CONST_WIDTH    : integer := 10;

   constant time_width     : integer := 64;
   constant bucket_width   : integer := SPEED_WIDTH + LIMIT_WIDTH;

   --! clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   --! input and output
   signal PACKET_LEN   : std_logic_vector(15 downto 0);
   signal PACKET_TS    : std_logic_vector(time_width-1 downto 0);
   signal RECORD_ADDR  : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal BUCKET_LIMIT : std_logic_vector(15 downto 0);
   signal SPEED        : std_logic_vector(SPEED_WIDTH-1 downto 0);
   signal TIME_CONST   : std_logic_vector(CONST_WIDTH-1 downto 0);

   signal PASS         : std_logic;

   signal IN_SRC_RDY   : std_logic;
   signal IN_DST_RDY   : std_logic;
   signal OUT_SRC_RDY  : std_logic;
   signal OUT_DST_RDY  : std_logic;

begin

   --! rate_limiter - core and memory
   UUT : entity work.rate_lim_mem
   generic map (
      ADDR_WIDTH_M   => ADDR_WIDTH,
      LIMIT_WIDTH_M  => LIMIT_WIDTH,
      SPEED_WIDTH_M  => SPEED_WIDTH,
      CONST_WIDTH_M  => CONST_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      PACKET_LEN     => PACKET_LEN,
      PACKET_TS      => PACKET_TS,
      RECORD_ADDR    => RECORD_ADDR,
      BUCKET_LIMIT   => BUCKET_LIMIT,
      SPEED          => SPEED,
      TIME_CONST     => TIME_CONST,

      PASS           => PASS,

      IN_SRC_RDY     => IN_SRC_RDY,
      IN_DST_RDY     => IN_DST_RDY,
      OUT_SRC_RDY    => OUT_SRC_RDY,
      OUT_DST_RDY    => OUT_DST_RDY
   );

   --! generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   --! generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   --! simulating input flow
   input_flow : process
      --! flow 1
      --! speed: 30 MB/s, packet length 1024 B
      constant flow1_speed    : integer := 34133;
      constant flow1_len      : integer := 1024;
      --! speed limit: 3 MB/s
      constant flow1_addr     : integer := 0;
      constant flow1_limit    : integer := 1000;
      constant flow1_t_const  : integer := 3;
      --! flow 2
      --! speed: 200 MB/s, packet length 550 B
      constant flow2_speed    : integer := 2750;
      constant flow2_len      : integer := 550;
      --! speed limit: 10 MB/s
      constant flow2_addr     : integer := 1;
      constant flow2_limit    : integer := 100;
      constant flow2_t_const  : integer := 1;
      --! flow 3
      --! speed: 200 MB/s, packet length 550 B
      constant flow3_speed    : integer := 2750;
      constant flow3_len      : integer := 550;
      --! speed limit: 40 MB/s
      constant flow3_addr     : integer := 2;
      constant flow3_limit    : integer := 25;
      constant flow3_t_const  : integer := 1;
      --! flow 4
      --! speed: 200 MB/s, packet length 550 B
      constant flow4_speed    : integer := 2750;
      constant flow4_len      : integer := 550;
      --! speed limit: 50 MB/s
      constant flow4_addr     : integer := 3;
      constant flow4_limit    : integer := 20;
      constant flow4_t_const  : integer := 1;
      --! flow 5
      --! speed: 200 MB/s, packet length 550 B
      constant flow5_speed    : integer := 2750;
      constant flow5_len      : integer := 550;
      --! speed limit: flow is disabled
      constant flow5_addr     : integer := 4;
      constant flow5_limit    : integer := 1;
      constant flow5_t_const  : integer := 0;
      --! flow 6
      --! speed: 200 MB/s, packet length 550 B
      constant flow6_speed    : integer := 2750;
      constant flow6_len      : integer := 550;
      --! speed limit: flow is disabled
      constant flow6_addr     : integer := 5;
      constant flow6_limit    : integer := 1;
      constant flow6_t_const  : integer := 0;
      --! flow 7
      --! speed: 200 MB/s, packet length 550 B
      constant flow7_speed    : integer := 2750;
      constant flow7_len      : integer := 550;
      --! speed limit: flow is disabled
      constant flow7_addr     : integer := 6;
      constant flow7_limit    : integer := 1;
      constant flow7_t_const  : integer := 0;
      --! flow 8
      --! speed: 200 MB/s, packet length 550 B
      constant flow8_speed    : integer := 2750;
      constant flow8_len      : integer := 550;
      --! speed limit: OFF
      constant flow8_addr     : integer := 7;
      constant flow8_limit    : integer := 0;
      constant flow8_t_const  : integer := 0;
      --! flow 9
      --! speed: 200 MB/s, packet length 550 B
      constant flow9_speed    : integer := 2750;
      constant flow9_len      : integer := 550;
      --! speed limit: OFF
      constant flow9_addr     : integer := 8;
      constant flow9_limit    : integer := 0;
      constant flow9_t_const  : integer := 1;
      --! flow 10
      --! speed: 200 MB/s, packet length 550 B
      constant flow10_speed    : integer := 2750;
      constant flow10_len      : integer := 550;
      --! speed limit: OFF
      constant flow10_addr     : integer := 9;
      constant flow10_limit    : integer := 0;
      constant flow10_t_const  : integer := 1;
      --! flow 11
      --! speed: 200 MB/s, packet length 550 B
      constant flow11_speed    : integer := 2750;
      constant flow11_len      : integer := 550;
      --! speed limit: OFF
      constant flow11_addr     : integer := 10;
      constant flow11_limit    : integer := 0;
      constant flow11_t_const  : integer := 1;

   begin

      --! initialize input interface
      IN_SRC_RDY   <= '0';
      OUT_DST_RDY  <= '1';

      PACKET_LEN   <= std_logic_vector(to_unsigned(1024, PACKET_LEN'length));
      PACKET_TS    <= (others => '0');
      RECORD_ADDR  <= (others => '0');
      BUCKET_LIMIT <= (others => '1');
      SPEED        <= (others => '0');
      TIME_CONST   <= std_logic_vector(to_unsigned(1, CONST_WIDTH));

      wait for reset_time;

      IN_SRC_RDY <= '1';

      for i in 1 to 20 loop

         --! flow 1
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow1_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow1_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow1_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow1_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow1_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 2
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow2_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow2_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow2_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow2_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow2_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 3
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow3_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow3_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow3_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow3_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow3_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 4
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow4_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow4_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow4_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow4_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow4_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 5
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow5_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow5_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow5_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow5_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow5_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 6
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow6_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow6_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow6_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow6_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow6_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 7
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow7_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow7_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow7_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow7_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow7_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 8
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow8_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow8_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow8_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow8_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow8_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 9
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow9_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow9_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow9_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow9_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow9_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 10
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow10_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow10_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow10_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow10_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow10_t_const, CONST_WIDTH));

         wait for clkper;

         --! flow 11
         PACKET_LEN   <= std_logic_vector(to_unsigned(flow11_len, PACKET_LEN'length));
         PACKET_TS    <= std_logic_vector(to_unsigned(i*flow11_speed, time_width));
         RECORD_ADDR  <= std_logic_vector(to_unsigned(flow11_addr, ADDR_WIDTH));
         SPEED        <= std_logic_vector(to_unsigned(flow11_limit, SPEED_WIDTH));
         TIME_CONST   <= std_logic_vector(to_unsigned(flow11_t_const, CONST_WIDTH));

         wait for clkper;

      end loop;

      IN_SRC_RDY   <= '0';
      PACKET_TS    <= (others => '0');
      BUCKET_LIMIT <= (others => '1');
      SPEED        <= (others => '0');
      TIME_CONST   <= (others => '0');

      wait for clkper*5;

      IN_SRC_RDY <= '1';

      --! speed and limit are used from flow 2

      --! token level above BUCKET_LIMIT
      --! long time difference
      PACKET_LEN   <= std_logic_vector(to_unsigned(flow2_len, PACKET_LEN'length));
      PACKET_TS    <= x"0000007C00000000";
      RECORD_ADDR  <= std_logic_vector(to_unsigned(10, ADDR_WIDTH));
      SPEED        <= std_logic_vector(to_unsigned(flow2_limit, SPEED_WIDTH));
      TIME_CONST   <= std_logic_vector(to_unsigned(flow2_t_const, CONST_WIDTH));

      wait for clkper;
      IN_SRC_RDY <= '0';
      wait for clkper;

      IN_SRC_RDY <= '1';

      --! large BUCKET_LIMIT, high speed limit and long time difference
      PACKET_LEN   <= std_logic_vector(to_unsigned(flow3_len, PACKET_LEN'length));
      PACKET_TS    <= x"000000000000F000";
      RECORD_ADDR  <= std_logic_vector(to_unsigned(20, ADDR_WIDTH));
      SPEED        <= std_logic_vector(to_unsigned(flow3_limit, SPEED_WIDTH));
      TIME_CONST   <= std_logic_vector(to_unsigned(flow3_t_const, CONST_WIDTH));

      wait for clkper;

      IN_SRC_RDY <= '0';

      wait;

   end process input_flow;

end architecture;
