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
use work.math_pack.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   --! simulation constants
   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset duration
   constant ITEMS_IN_MEM   : integer := 16;
   constant LIMIT_WIDTH    : integer := 16;
   constant SPEED_WIDTH    : integer := 20;
   constant CONST_WIDTH    : integer := 10;

   constant time_width     : integer := 64;
   constant addr_width     : integer := log2(ITEMS_IN_MEM);

   --! clock and reset signals
   signal CLK           : std_logic;
   signal RESET         : std_logic;

   --! input and output
   signal PACKET_LEN    : std_logic_vector(15 downto 0);
   signal PACKET_TS     : std_logic_vector(time_width-1 downto 0);
   signal RECORD_ADDR   : std_logic_vector(addr_width-1 downto 0);

   signal PASS          : std_logic;

   signal IN_SRC_RDY    : std_logic;
   signal IN_DST_RDY    : std_logic;
   signal OUT_SRC_RDY   : std_logic;
   signal OUT_DST_RDY   : std_logic;

   signal ADDR_VLD      : std_logic;

   --! MI32
   signal MI32_ADDR     : std_logic_vector(31 downto 0);
   signal MI32_WR       : std_logic;
   signal MI32_DWR      : std_logic_vector(31 downto 0);
   signal MI32_RD       : std_logic;
   signal MI32_DRD      : std_logic_vector(31 downto 0);
   signal MI32_DRDY     : std_logic;
   signal MI32_ARDY     : std_logic;
   signal MI32_BE       : std_logic_vector(3 downto 0);

   function int2vec(int, width: integer) return std_logic_vector is
   begin
      return std_logic_vector(to_unsigned(int, width));
   end int2vec;

   function decaddr32(addr: integer; pos: std_logic_vector) return std_logic_vector is
      variable addr_ret : std_logic_vector(31 downto 0);
      constant zeros    : std_logic_vector(31 downto 0) := X"00000000";
   begin
      addr_ret := zeros(31 downto addr_width+4) & int2vec(addr, addr_width) & pos & zeros(1 downto 0);
      return addr_ret;
   end decaddr32;

   --! addresses
   constant flow1_addr  : integer := 0;
   constant flow2_addr  : integer := 1;
   constant flow3_addr  : integer := 2;
   constant flow4_addr  : integer := 3;
   constant flow5_addr  : integer := 4;
   constant flow6_addr  : integer := 5;
   constant flow7_addr  : integer := 6;
   constant flow8_addr  : integer := 7;
   constant flow9_addr  : integer := 8;
   constant flow10_addr : integer := 9;
   constant flow11_addr : integer := 10;

begin

   --! rate_limiter_top
   UUT : entity work.rate_lim_top
   generic map (
      ITEMS_IN_MEM => ITEMS_IN_MEM,
      LIMIT_WIDTH  => LIMIT_WIDTH,
      SPEED_WIDTH  => SPEED_WIDTH,
      CONST_WIDTH  => CONST_WIDTH
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      PACKET_LEN  => PACKET_LEN,
      PACKET_TS   => PACKET_TS,
      RECORD_ADDR => RECORD_ADDR,
      ADDR_VLD    => ADDR_VLD,

      PASS        => PASS,

      IN_SRC_RDY  => IN_SRC_RDY,
      IN_DST_RDY  => IN_DST_RDY,
      OUT_SRC_RDY => OUT_SRC_RDY,
      OUT_DST_RDY => OUT_DST_RDY,

      MI32_ADDR   => MI32_ADDR,
      MI32_WR     => MI32_WR,
      MI32_DWR    => MI32_DWR,
      MI32_RD     => MI32_RD,
      MI32_DRD    => MI32_DRD,
      MI32_DRDY   => MI32_DRDY,
      MI32_ARDY   => MI32_ARDY,
      MI32_BE     => MI32_BE
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

   --! simulating MI32 communication
   MI32 : process
      --! flow 1
      --! speed limit: 3 MB/s
      constant flow1_s_limit  : integer := 1000;
      constant flow1_t_const  : integer := 3;
      --! flow 2
      --! speed limit: 10 MB/s
      constant flow2_s_limit  : integer := 100;
      constant flow2_t_const  : integer := 1;
      --! flow 3
      --! speed limit: 40 MB/s
      constant flow3_s_limit  : integer := 25;
      constant flow3_t_const  : integer := 1;
      --! flow 4
      --! speed limit: 50 MB/s
      constant flow4_s_limit  : integer := 20;
      constant flow4_t_const  : integer := 1;
      --! flow 5
      --! speed limit: flow is disabled
      constant flow5_s_limit  : integer := 1;
      constant flow5_t_const  : integer := 0;
      --! flow 6
      --! speed limit: flow is disabled
      constant flow6_s_limit  : integer := 1;
      constant flow6_t_const  : integer := 0;
      --! flow 7
      --! speed limit: flow is disabled
      constant flow7_s_limit  : integer := 1;
      constant flow7_t_const  : integer := 0;
      --! flow 8
      --! speed limit: OFF
      constant flow8_s_limit  : integer := 0;
      constant flow8_t_const  : integer := 1;
      -- not set !, BRAM is initialized to zeros in simulation
      --! flow 9
      --! speed limit: OFF
      constant flow9_s_limit  : integer := 0;
      constant flow9_t_const  : integer := 0;
      --! flow 10
      --! speed limit: OFF
      constant flow10_s_limit : integer := 0;
      constant flow10_t_const : integer := 0;
      --! flow 11
      --! speed limit: OFF
      constant flow11_s_limit : integer := 0;
      constant flow11_t_const : integer := 0;

   begin

      --! initialize input interface
      MI32_ADDR   <= (others => '0');
      MI32_WR     <= '0';
      MI32_DWR    <= (others => '0');
      MI32_RD     <= '0';
      MI32_BE     <= (others => '0');

      wait for reset_time;

      --! initialize BRAM with MI32 interface

      MI32_WR     <= '1';

      --! flow 1
      MI32_ADDR   <= decaddr32(flow1_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow1_addr, "01");
      MI32_DWR    <= int2vec(flow1_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow1_addr, "10");
      MI32_DWR    <= int2vec(flow1_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow1_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow1_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 2
      --! write parts in wrong order
      MI32_ADDR   <= decaddr32(flow2_addr, "01");
      MI32_DWR    <= int2vec(flow2_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow2_addr, "10");
      MI32_DWR    <= int2vec(flow2_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow2_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow2_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow2_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 3
      --! try write one part of item twice
      MI32_ADDR   <= decaddr32(flow3_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow3_addr, "01");
      MI32_DWR    <= int2vec(flow3_s_limit, MI32_DWR'length);
      wait for clkper;
      wait for clkper;  --! second attempt
      MI32_ADDR   <= decaddr32(flow3_addr, "10");
      MI32_DWR    <= int2vec(flow3_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow3_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow3_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 4
      --! interrupted write of one item
      MI32_ADDR   <= decaddr32(flow4_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_WR     <= '0';
      wait for clkper;
      MI32_WR     <= '1';
      MI32_ADDR   <= decaddr32(flow4_addr, "01");
      MI32_DWR    <= int2vec(flow4_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow4_addr, "10");
      MI32_DWR    <= int2vec(flow4_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow4_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow4_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 5
      MI32_ADDR   <= decaddr32(flow5_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow5_addr, "01");
      MI32_DWR    <= int2vec(flow5_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow5_addr, "10");
      MI32_DWR    <= int2vec(flow5_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow5_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow5_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 6
      MI32_ADDR   <= decaddr32(flow6_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow6_addr, "01");
      MI32_DWR    <= int2vec(flow6_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow6_addr, "10");
      MI32_DWR    <= int2vec(flow6_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow6_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow6_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 7
      MI32_ADDR   <= decaddr32(flow7_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow7_addr, "01");
      MI32_DWR    <= int2vec(flow7_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow7_addr, "10");
      MI32_DWR    <= int2vec(flow7_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow7_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow7_addr, MI32_DWR'length-1);
      wait for clkper;

      --! flow 8
      MI32_ADDR   <= decaddr32(flow8_addr, "00");
      MI32_DWR    <= (others => '1');
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow8_addr, "01");
      MI32_DWR    <= int2vec(flow8_s_limit, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow8_addr, "10");
      MI32_DWR    <= int2vec(flow8_t_const, MI32_DWR'length);
      wait for clkper;
      MI32_ADDR   <= decaddr32(flow8_addr, "11");
      MI32_DWR    <= MI32_WR & int2vec(flow8_addr, MI32_DWR'length-1);
      wait for clkper;

      MI32_WR     <= '0';
      wait for clkper*5;

      --! read values in BRAM with MI32 interface

      --! read values of flow4
      MI32_WR     <= '1';
      MI32_ADDR   <= decaddr32(0, "11");
      MI32_DWR    <= '0' & int2vec(flow4_addr, MI32_DWR'length-1);
      wait for clkper;
      MI32_WR     <= '0';
      MI32_RD     <= '1';
      MI32_ADDR   <= decaddr32(0, "00");
      wait for clkper;
      MI32_ADDR   <= decaddr32(0, "01");
      wait for clkper;
      MI32_ADDR   <= decaddr32(0, "10");
      wait for clkper;

      MI32_RD     <= '0';
      wait for clkper;

      --! read settings of generic parameters
      MI32_RD     <= '1';
      MI32_ADDR   <= x"00000010";
      wait for clkper;

      MI32_RD     <= '0';

      wait;

   end process MI32;

   --! simulating input flow
   input_flow : process
      --! flow 1
      --! speed: 30 MB/s, packet length 1024 B
      constant flow1_speed    : integer := 34133;
      constant flow1_len      : integer := 1024;
      --! flow 2
      --! speed: 200 MB/s, packet length 550 B
      constant flow2_speed    : integer := 2750;
      constant flow2_len      : integer := 550;
      --! flow 3
      --! speed: 200 MB/s, packet length 550 B
      constant flow3_speed    : integer := 2750;
      constant flow3_len      : integer := 10240;
      --! flow 4
      --! speed: 200 MB/s, packet length 550 B
      constant flow4_speed    : integer := 2750;
      constant flow4_len      : integer := 550;
      --! flow 5
      --! speed: 200 MB/s, packet length 550 B
      constant flow5_speed    : integer := 2750;
      constant flow5_len      : integer := 550;
      --! flow 6
      --! speed: 200 MB/s, packet length 550 B
      constant flow6_speed    : integer := 2750;
      constant flow6_len      : integer := 550;
      --! flow 7
      --! speed: 200 MB/s, packet length 550 B
      constant flow7_speed    : integer := 2750;
      constant flow7_len      : integer := 550;
      --! flow 8
      --! speed: 200 MB/s, packet length 550 B
      constant flow8_speed    : integer := 10000;
      constant flow8_len      : integer := 50;
      --! flow 9
      --! speed: 200 MB/s, packet length 550 B
      constant flow9_speed    : integer := 2750;
      constant flow9_len      : integer := 550;
      --! flow 10
      --! speed: 200 MB/s, packet length 550 B
      constant flow10_speed    : integer := 2750;
      constant flow10_len      : integer := 550;
      --! flow 11
      --! speed: 200 MB/s, packet length 550 B
      constant flow11_speed    : integer := 2750;
      constant flow11_len      : integer := 550;

   begin

      --! initialize input interface
      IN_SRC_RDY  <= '0';
      OUT_DST_RDY <= '1';
      ADDR_VLD <= '1';
      PACKET_LEN  <= int2vec(1024, PACKET_LEN'length);
      PACKET_TS   <= (others => '0');
      RECORD_ADDR <= (others => '0');

      wait for reset_time;

      IN_SRC_RDY <= '1';

      for i in 1 to 25 loop

         if(i >= 15 and i <= 17) then
            ADDR_VLD <= '0';
         else
            ADDR_VLD <= '1';
         end if;

         --! flow 1
         PACKET_LEN   <= int2vec(flow1_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow1_speed, time_width);
         RECORD_ADDR  <= int2vec(flow1_addr, addr_width);

         wait for clkper;

         --! flow 2
         PACKET_LEN   <= int2vec(flow2_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow2_speed, time_width);
         RECORD_ADDR  <= int2vec(flow2_addr, addr_width);

         wait for clkper;

         --! flow 3
         PACKET_LEN   <= int2vec(flow3_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow3_speed, time_width);
         RECORD_ADDR  <= int2vec(flow3_addr, addr_width);

         wait for clkper;

         --! flow 4
         PACKET_LEN   <= int2vec(flow4_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow4_speed, time_width);
         RECORD_ADDR  <= int2vec(flow4_addr, addr_width);

         wait for clkper;

         --! flow 5
         PACKET_LEN   <= int2vec(flow5_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow5_speed, time_width);
         RECORD_ADDR  <= int2vec(flow5_addr, addr_width);

         wait for clkper;

         --! flow 6
         PACKET_LEN   <= int2vec(flow6_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow6_speed, time_width);
         RECORD_ADDR  <= int2vec(flow6_addr, addr_width);

         wait for clkper;

         --! flow 7
         PACKET_LEN   <= int2vec(flow7_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow7_speed, time_width);
         RECORD_ADDR  <= int2vec(flow7_addr, addr_width);

         wait for clkper;

         --! flow 8
         PACKET_LEN   <= int2vec(flow8_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow8_speed, time_width);
         RECORD_ADDR  <= int2vec(flow8_addr, addr_width);

         wait for clkper;

         --! flow 9
         PACKET_LEN   <= int2vec(flow9_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow9_speed, time_width);
         RECORD_ADDR  <= int2vec(flow9_addr, addr_width);

         wait for clkper;

         --! flow 10
         PACKET_LEN   <= int2vec(flow10_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow10_speed, time_width);
         RECORD_ADDR  <= int2vec(flow10_addr, addr_width);

         wait for clkper;

         --! flow 11
         PACKET_LEN   <= int2vec(flow11_len, PACKET_LEN'length);
         PACKET_TS    <= int2vec(i*flow11_speed, time_width);
         RECORD_ADDR  <= int2vec(flow11_addr, addr_width);

         wait for clkper;

      end loop;

      IN_SRC_RDY <= '0';

      wait;

   end process input_flow;

end architecture;
