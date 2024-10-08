--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice ALU entity
entity STATS is
   generic (
      EN_DSP            : boolean := true;
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      PACKET_LENGTH_WD  : integer := 16;
      REG_OUT           : integer := 0;
      ADDRESS_WIDTH     : integer := 10
   );
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      CNT_ADDRESS       : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      PACKET_LENGTH     : in  std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET        : in  std_logic;
      RST_COUNTERS      : in  std_logic;

      R_NUM_BYTES       : out std_logic_vector(NUM_BYTES_WD-1 downto 0);
      R_NUM_PACKETS     : out std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      R_VLD             : out std_logic;
      R_NEXT            : in  std_logic
   );
end entity;

architecture FULL of STATS is
   signal cnt_num_bytes         : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal cnt_num_packets       : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal pipe0_num_bytes       : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal pipe0_num_packets     : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal pipe1_num_bytes       : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal pipe1_num_packets     : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal mem_num_bytes         : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal mem_num_packets       : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal pipe_mem_num_bytes    : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal pipe_mem_num_packets  : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal mux_num_bytes         : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal mux_num_packets       : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal mux_sel               : std_logic_vector(1 downto 0);
   signal pipe0_mux_sel         : std_logic_vector(1 downto 0);
   signal pipe1_mux_sel         : std_logic_vector(1 downto 0);

   signal pipe0_cnt_address     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal pipe0_packet_length   : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
   signal pipe0_add_packet      : std_logic;
   signal pipe0_rst_countesr    : std_logic;
   signal pipe1_cnt_address     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal pipe1_packet_length   : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
   signal pipe1_add_packet      : std_logic;
   signal pipe1_rst_countesr    : std_logic;
   signal pipe2_cnt_address     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal pipe2_packet_length   : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
   signal pipe2_add_packet      : std_logic;
   signal pipe2_rst_countesr    : std_logic;

   signal cmp_addr0             : std_logic;
   signal cmp_addr1             : std_logic;
   signal mem_rw_addr           : std_logic_vector(ADDRESS_WIDTH-1 downto 0);

   signal tmp_r_vld             : std_logic;
   signal pipe_r_vld            : std_logic;
begin

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(RESET = '1') then
            pipe0_add_packet    <= '0';
            pipe0_rst_countesr  <= '0';
            pipe1_add_packet    <= '0';
            pipe1_rst_countesr  <= '0';
            pipe2_add_packet    <= '0';
            pipe2_rst_countesr  <= '0';
         else
            pipe0_cnt_address   <= CNT_ADDRESS;
            pipe0_packet_length <= PACKET_LENGTH;
            pipe0_add_packet    <= ADD_PACKET;
            pipe0_rst_countesr  <= RST_COUNTERS;
            pipe1_cnt_address   <= pipe0_cnt_address;
            pipe1_packet_length <= pipe0_packet_length;
            pipe1_add_packet    <= pipe0_add_packet;
            pipe1_rst_countesr  <= pipe0_rst_countesr;
            pipe2_cnt_address   <= pipe1_cnt_address;
            pipe2_packet_length <= pipe1_packet_length;
            pipe2_add_packet    <= pipe1_add_packet;
            pipe2_rst_countesr  <= pipe1_rst_countesr;
            pipe_mem_num_bytes  <= mem_num_bytes;
            pipe_mem_num_packets<= mem_num_packets;
         end if;
      end if;
   end process;

   MEM_i : entity work.MEM_STATS
   generic map (
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      ADDRESS_WIDTH     => ADDRESS_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,
      RD_NUM_BYTES      => mem_num_bytes,
      RD_NUM_PACKETS    => mem_num_packets,
      RD_ADDRESS        => pipe0_cnt_address,
      WR_NUM_BYTES      => pipe0_num_bytes,
      WR_NUM_PACKETS    => pipe0_num_packets,
      WR_ADDRESS        => mem_rw_addr
   );

   CNT_i : entity work.CNT_STATS
   generic map(
      EN_DSP            => EN_DSP,
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      REG_OUT           => REG_OUT
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,
      PACKET_LENGTH     => pipe2_packet_length,
      ADD_PACKET        => pipe2_add_packet,
      RST_COUNTERS      => pipe2_rst_countesr,
      IN_NUM_BYTES      => mux_num_bytes,
      IN_NUM_PACKETS    => mux_num_packets,
      OUT_NUM_BYTES     => cnt_num_bytes,
      OUT_NUM_PACKETS   => cnt_num_packets
   );

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         pipe0_num_bytes   <= cnt_num_bytes;
         pipe0_num_packets <= cnt_num_packets;
         pipe1_num_bytes   <= pipe0_num_bytes;
         pipe1_num_packets <= pipe0_num_packets;

         mem_rw_addr       <= pipe2_cnt_address;
         pipe0_mux_sel     <= mux_sel;
         pipe1_mux_sel     <= pipe0_mux_sel;
      end if;
   end process;

   cmp_addr0 <= '1' when pipe0_cnt_address = pipe1_cnt_address else
                '0';

   cmp_addr1 <= '1' when pipe0_cnt_address = pipe2_cnt_address else
                '0';

   mux_sel <= "10" when cmp_addr0 = '0' and cmp_addr1 = '0' else
              "01" when cmp_addr0 = '0' and cmp_addr1 = '1' else
              "00";

   mux_num_bytes <= pipe0_num_bytes when pipe1_mux_sel = "00" else
                    pipe1_num_bytes when pipe1_mux_sel = "01" else
                    pipe_mem_num_bytes;

   mux_num_packets <= pipe0_num_packets when pipe1_mux_sel = "00" else
                      pipe1_num_packets when pipe1_mux_sel = "01" else
                      pipe_mem_num_packets;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(pipe2_add_packet = '1' and pipe2_rst_countesr = '1') then
            R_NUM_BYTES    <= mux_num_bytes;
            R_NUM_PACKETS  <= mux_num_packets;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            R_VLD <= '0';
         else
            if(pipe2_add_packet = '1' and pipe2_rst_countesr = '1') then
               R_VLD <= '1';
            elsif(R_NEXT = '1') then
               R_VLD <= '0';
            end if;
         end if;
      end if;
   end process;

end architecture;
