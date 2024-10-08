-- rate_limiter_mem.vhd
--!
--! \file  rate_limiter_mem.vhd
--! \brief Memory modul for rate_limiter_core
--!        BUCKET_VALUE and BUCKET_TS are saved in BRAMs
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

use WORK.cnt_types.all;

-- -----------------------------------------------------------------------------
--                            Entity declaration
-- -----------------------------------------------------------------------------
entity rate_lim_mem is

   generic (
      ADDR_WIDTH_M   : integer := 8;
      LIMIT_WIDTH_M  : integer := 16;  --! maximal value: 17
      SPEED_WIDTH_M  : integer := 20;  --! maximal value: 24
      CONST_WIDTH_M  : integer := 10   --! maximal value: 17
   );
   port (
      CLK          : in std_logic;
      RESET        : in std_logic;
      --! packet info
      PACKET_LEN   : in std_logic_vector(15 downto 0);
      PACKET_TS    : in std_logic_vector(63 downto 0); --! time stemp, unit: ns
      --! bucket record
      RECORD_ADDR  : in std_logic_vector(ADDR_WIDTH_M-1 downto 0);
      ADDR_VLD     : in std_logic;
      BUCKET_LIMIT : in std_logic_vector(LIMIT_WIDTH_M-1 downto 0);
      SPEED        : in std_logic_vector(SPEED_WIDTH_M-1 downto 0); --! unit: TOKENS per BYTE
      TIME_CONST   : in std_logic_vector(CONST_WIDTH_M-1 downto 0); --! unit: TOKENs per ns

      --! packet passed signal
      PASS         : out std_logic;

      IN_SRC_RDY   : in  std_logic;
      IN_DST_RDY   : out std_logic;
      OUT_SRC_RDY  : out std_logic;
      OUT_DST_RDY  : in  std_logic
   );

end rate_lim_mem;

-- -----------------------------------------------------------------------------
--                          Architecture declaration
-- -----------------------------------------------------------------------------
architecture mem_modul of rate_lim_mem is

   constant bucket_width   : integer := SPEED_WIDTH_M + LIMIT_WIDTH_M;
   constant data_width     : integer := bucket_width + 64;

   signal zeros            : std_logic_vector(63 downto 0);
   signal zero             : std_logic;
   signal one              : std_logic;

   signal cnt              : std_logic_vector(ADDR_WIDTH_M downto 0);
   signal init             : std_logic;
   signal write_init       : std_logic_vector(1+ADDR_WIDTH_M+data_width-1 downto 0);
   signal write_data       : std_logic_vector(1+ADDR_WIDTH_M+data_width-1 downto 0);
   signal write_mux_out    : std_logic_vector(1+ADDR_WIDTH_M+data_width-1 downto 0);
   signal in_src_rdy_check : std_logic;
   signal read_enable      : std_logic;

   signal data_valid       : std_logic;
   signal mem_read         : std_logic_vector(data_width-1 downto 0);
   signal mem_write        : std_logic_vector(data_width-1 downto 0);

   signal pass_core        : std_logic;
   signal bucket_we        : std_logic;
   signal record_addr_out  : std_logic_vector(ADDR_WIDTH_M-1 downto 0);
   signal bucket_val_out   : std_logic_vector(bucket_width-1 downto 0);
   signal bucket_ts_out    : std_logic_vector(63 downto 0);
   signal in_src_rdy_core  : std_logic;
   signal in_dst_rdy_core  : std_logic;
   signal out_src_rdy_core : std_logic;
   signal out_dst_rdy_core : std_logic;

   signal stage1_en        : std_logic;
   signal stage2_en        : std_logic;

   signal reg1_addr_vld    : std_logic;
   signal reg_addr_vld     : std_logic;

   signal reg1_in_src_rdy  : std_logic;
   signal reg_in_src_rdy   : std_logic;

   signal reg1_packet_len  : std_logic_vector(15 downto 0);
   signal reg_packet_len   : std_logic_vector(15 downto 0);

   signal reg1_packet_ts   : std_logic_vector(63 downto 0); --! time stemp, unit: ns
   signal reg_packet_ts    : std_logic_vector(63 downto 0); --! time stemp, unit: ns

   signal reg1_record_addr : std_logic_vector(ADDR_WIDTH_M-1 downto 0);
   signal reg_record_addr  : std_logic_vector(ADDR_WIDTH_M-1 downto 0);

   signal reg1_limit       : std_logic_vector(LIMIT_WIDTH_M-1 downto 0);
   signal reg_limit        : std_logic_vector(LIMIT_WIDTH_M-1 downto 0);

   signal reg1_speed       : std_logic_vector(SPEED_WIDTH_M-1 downto 0); --! unit: TOKENS per BYTE
   signal reg_speed        : std_logic_vector(SPEED_WIDTH_M-1 downto 0); --! unit: TOKENS per BYTE

   signal reg1_const       : std_logic_vector(CONST_WIDTH_M-1 downto 0); --! unit: TOKENs per ns
   signal reg_const        : std_logic_vector(CONST_WIDTH_M-1 downto 0); --! unit: TOKENs per ns

   signal stage1_out_en    : std_logic;
   signal reg_pass         : std_logic;
   signal reg_we           : std_logic;
   signal reg_addr_write   : std_logic_vector(ADDR_WIDTH_M-1 downto 0);
   signal reg_mem_write    : std_logic_vector(data_width-1 downto 0);
   signal reg_out_src_rdy  : std_logic;

begin

   zeros <= X"0000000000000000";
   zero  <= '0';
   one   <= '1';

   --! MEM init logic, saves zeros to BRAM after RESET
   INIT_CNT: entity work.cnt
      generic map(
         WIDTH => ADDR_WIDTH_M + 1
      )
      port map(
         RESET => RESET,
         CLK   => CLK,
         CE    => init,
         CLR   => zero,
         DO    => cnt
      );

   init <= not cnt(ADDR_WIDTH_M);
   --! switch between init and data write mod
   write_init <= '1' & cnt(ADDR_WIDTH_M-1 downto 0) & zeros(bucket_width-1 downto 0) & zeros;
   write_data <= reg_we & reg_addr_write & reg_mem_write;
   write_mux_out <= write_init when init = '1' else
                    write_data;

   in_src_rdy_check <= IN_SRC_RDY and cnt(ADDR_WIDTH_M);

   read_enable <= in_src_rdy_check and stage1_en; --TODO

   MEM: entity work.DP_BRAM_V7
      generic map(
         DATA_WIDTH     => data_width,
         ADDRESS_WIDTH  => ADDR_WIDTH_M,
         ENABLE_OUT_REG => true
      )
      port map(
         -- interface A - reading
         CLKA     => CLK,
         RSTA     => RESET,
         PIPE_ENA => stage2_en,
         REA      => read_enable,
         WEA      => zero,
         ADDRA    => RECORD_ADDR,
         DIA      => (others => '0'),
         DOA_DV   => data_valid,
         DOA      => mem_read,
         -- interface B - writing
         CLKB     => CLK,
         RSTB     => RESET,
         PIPE_ENB => one,
         REB      => zero,
         WEB      => write_mux_out(ADDR_WIDTH_M+data_width),
         ADDRB    => write_mux_out(ADDR_WIDTH_M+data_width-1 downto data_width),
         DIB      => write_mux_out(data_width-1 downto 0),
         DOB_DV   => open,
         DOB      => open
      );

   --! Pipeline enable/disable logic - DST/SRC ready propagation
   -- output IN_DST_RDY signal, component can receive new data after it initialize BRAM
   -- and its core can receive data too
   IN_DST_RDY <= cnt(ADDR_WIDTH_M) and stage1_en;
   stage1_en <= '0' when stage2_en = '0' and reg1_in_src_rdy = '1' else
                '1';
   stage2_en <= '0' when in_dst_rdy_core = '0' and reg_in_src_rdy = '1' else
                '1';

   --! Pipeline - input data
   --! stage 1
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg1_in_src_rdy   <= '0';
            reg1_packet_len   <= (others => '0');
            reg1_packet_ts    <= (others => '0');
            reg1_record_addr  <= (others => '0');
            reg1_limit        <= (others => '0');
            reg1_speed        <= (others => '0');
            reg1_const        <= (others => '0');
            reg1_addr_vld     <= '0';
         elsif stage1_en = '1' then
            reg1_in_src_rdy   <= in_src_rdy_check;
            reg1_packet_len   <= PACKET_LEN;
            reg1_packet_ts    <= PACKET_TS;
            reg1_record_addr  <= RECORD_ADDR;
            reg1_addr_vld     <= ADDR_VLD;
            reg1_limit        <= BUCKET_LIMIT;
            reg1_speed        <= SPEED;
            reg1_const        <= TIME_CONST;
         end if;
      end if;
   end process;

   --! stage 2
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg_in_src_rdy    <= '0';
            reg_packet_len    <= (others => '0');
            reg_packet_ts     <= (others => '0');
            reg_record_addr   <= (others => '0');
            reg_limit         <= (others => '0');
            reg_speed         <= (others => '0');
            reg_const         <= (others => '0');
            reg_addr_vld      <= '0';
         elsif stage2_en = '1' then
            reg_in_src_rdy    <= reg1_in_src_rdy;
            reg_packet_len    <= reg1_packet_len;
            reg_packet_ts     <= reg1_packet_ts;
            reg_record_addr   <= reg1_record_addr;
            reg_addr_vld      <= reg1_addr_vld;
            reg_limit         <= reg1_limit;
            reg_speed         <= reg1_speed;
            reg_const         <= reg1_const;
         end if;
      end if;
   end process;

   in_src_rdy_core <= reg_in_src_rdy and data_valid;

   CORE: entity work.rate_lim
      generic map (
         ADDR_WIDTH  => ADDR_WIDTH_M,
         LIMIT_WIDTH => LIMIT_WIDTH_M,
         SPEED_WIDTH => SPEED_WIDTH_M,
         CONST_WIDTH => CONST_WIDTH_M
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         PACKET_LEN     => reg_packet_len,
         PACKET_TS      => reg_packet_ts,
         RECORD_ADDR    => reg_record_addr,
         ADDR_VLD       => reg_addr_vld,
         BUCKET_VALUE   => mem_read(data_width-1 downto 64),
         BUCKET_TS      => mem_read(63 downto 0),
         BUCKET_LIMIT   => reg_limit,
         SPEED          => reg_speed,
         TIME_CONST     => reg_const,

         PASS           => pass_core,
         BUCKET_WE      => bucket_we,
         RECORD_ADDR_OUT=> record_addr_out,
         BUCKET_VAL_OUT => bucket_val_out,
         BUCKET_TS_OUT  => bucket_ts_out,

         IN_SRC_RDY     => in_src_rdy_core,
         IN_DST_RDY     => in_dst_rdy_core,
         OUT_SRC_RDY    => out_src_rdy_core,
         OUT_DST_RDY    => out_dst_rdy_core
      );

   mem_write <= (bucket_val_out & bucket_ts_out);

   --! Pipeline enable/disable logic - DST/SRC ready propagation
   out_dst_rdy_core <= stage1_out_en;
   stage1_out_en <= '0' when OUT_DST_RDY = '0' and reg_out_src_rdy = '1' else
                    '1';

   --! Pipeline - output data
   --! stage 1
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg_pass          <= '0';
            reg_we            <= '0';
            reg_addr_write    <= (others => '0');
            reg_mem_write     <= (others => '0');
            reg_out_src_rdy   <= '0';
         elsif stage1_out_en = '1' then
            reg_pass          <= pass_core;
            reg_we            <= bucket_we;
            reg_addr_write    <= record_addr_out;
            reg_mem_write     <= mem_write;
            reg_out_src_rdy   <= out_src_rdy_core;
         end if;
      end if;
   end process;

   PASS <= reg_pass;

   OUT_SRC_RDY <= reg_out_src_rdy;

end mem_modul;
