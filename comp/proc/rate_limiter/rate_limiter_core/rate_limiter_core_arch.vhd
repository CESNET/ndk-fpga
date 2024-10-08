-- rate_limiter_core_arch.vhd
--!
--! \file  rate_limiter_core_arch.vhd
--! \brief The packet flow rate limiter, based on connection speed and tokens
--!        Core component with arithmetic operations
--!        DSP component are used for those arithmetic operations
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

architecture limiter of rate_lim is

   constant bucket_width   : integer := SPEED_WIDTH + LIMIT_WIDTH;
   constant delta_width    : integer := 64;

   signal delta_t          : std_logic_vector(63 downto 0);
   signal bucket_limit_t   : std_logic_vector(47 downto 0);
   signal needed_tokens    : std_logic_vector(47 downto 0);
   signal new_tokens       : std_logic_vector((delta_width+CONST_WIDTH-1) downto 0);
   signal token_level      : std_logic_vector((delta_width+CONST_WIDTH) downto 0);
   signal bucket_level     : std_logic_vector((delta_width+CONST_WIDTH) downto 0);
   signal flag             : std_logic;
   signal carry            : std_logic;

   signal zeros            : std_logic_vector(63 downto 0);
   signal zero             : std_logic;
   signal one              : std_logic;
   signal add              : std_logic_vector(3 downto 0);
   signal sub              : std_logic_vector(3 downto 0);

   signal add_b            : std_logic_vector((delta_width+CONST_WIDTH-1) downto 0);
   signal sub_b            : std_logic_vector(delta_width+CONST_WIDTH downto 0);
   signal speed_25         : std_logic_vector(24 downto 0);
   signal bucket_lim_18    : std_logic_vector(17 downto 0);
   signal packet_len_18    : std_logic_vector(17 downto 0);
   signal cmp_a            : std_logic_vector((delta_width+CONST_WIDTH) downto 0);
   signal sel              : std_logic_vector(1 downto 0);

   signal stage1_en        : std_logic;
   signal stage2_en        : std_logic;
   signal stage3_en        : std_logic;
   signal stage4_en        : std_logic;
   signal stage5_en        : std_logic;
   signal stage6_en        : std_logic;
   signal stage7_en        : std_logic;

   signal reg1_in_src_rdy  : std_logic;
   signal reg2_in_src_rdy  : std_logic;
   signal reg3_in_src_rdy  : std_logic;
   signal reg4_in_src_rdy  : std_logic;
   signal reg5_in_src_rdy  : std_logic;
   signal reg6_in_src_rdy  : std_logic;
   signal reg_in_src_rdy   : std_logic;

   signal reg1_packet_ts   : std_logic_vector(63 downto 0);
   signal reg2_packet_ts   : std_logic_vector(63 downto 0);
   signal reg3_packet_ts   : std_logic_vector(63 downto 0);
   signal reg4_packet_ts   : std_logic_vector(63 downto 0);
   signal reg5_packet_ts   : std_logic_vector(63 downto 0);
   signal reg6_packet_ts   : std_logic_vector(63 downto 0);
   signal reg_packet_ts    : std_logic_vector(63 downto 0);

   signal reg1_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg2_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg3_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg4_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg5_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg6_addr        : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg_addr         : std_logic_vector(ADDR_WIDTH-1 downto 0);

   signal reg1_addr_vld    : std_logic;
   signal reg2_addr_vld    : std_logic;
   signal reg3_addr_vld    : std_logic;
   signal reg4_addr_vld    : std_logic;
   signal reg5_addr_vld    : std_logic;
   signal reg6_addr_vld    : std_logic;
   signal reg_addr_vld     : std_logic;

   signal reg1_b_value     : std_logic_vector(bucket_width-1 downto 0);
   signal reg2_b_value     : std_logic_vector(bucket_width-1 downto 0);
   signal reg3_b_value     : std_logic_vector(bucket_width-1 downto 0);
   signal reg4_b_value     : std_logic_vector(bucket_width-1 downto 0);
   signal reg_b_value      : std_logic_vector(bucket_width-1 downto 0);

   signal reg3_b_lim       : std_logic_vector(bucket_width-1 downto 0);
   signal reg4_b_lim       : std_logic_vector(bucket_width-1 downto 0);
   signal reg5_b_lim       : std_logic_vector(bucket_width-1 downto 0);
   signal reg6_b_lim       : std_logic_vector(bucket_width-1 downto 0);
   signal reg_b_lim        : std_logic_vector(bucket_width-1 downto 0);

   signal reg_time_const   : std_logic_vector(CONST_WIDTH-1 downto 0);

   signal reg3_needed_tokens  : std_logic_vector(bucket_width-1 downto 0);
   signal reg4_needed_tokens  : std_logic_vector(bucket_width-1 downto 0);
   signal reg5_needed_tokens  : std_logic_vector(bucket_width-1 downto 0);
   signal reg_needed_tokens   : std_logic_vector(bucket_width-1 downto 0);

begin

   zeros <= X"0000000000000000";
   zero  <= '0';
   one   <= '1';
   --! ALU modes
   add   <= "0000";
   sub   <= "0001";

   --! Pipeline enable/disable logic - DST/SRC ready propagation
   IN_DST_RDY <= stage1_en;
   stage1_en <= '0' when stage2_en = '0' and reg1_in_src_rdy = '1' else
                '1';
   stage2_en <= stage3_en;
   stage3_en <= stage4_en;
   stage4_en <= stage5_en;
   -- stage2_en <= '0' when stage3_en = '0' and reg2_in_src_rdy = '1' else
   --              '1';
   -- stage3_en <= '0' when stage4_en = '0' and reg3_in_src_rdy = '1' else
   --              '1';
   -- stage4_en <= '0' when stage5_en = '0' and reg4_in_src_rdy = '1' else
   --              '1';
   stage5_en <= '0' when stage6_en = '0' and reg5_in_src_rdy = '1' else
                '1';
   stage6_en <= '0' when stage7_en = '0' and reg6_in_src_rdy = '1' else
                '1';
   stage7_en <= '0' when OUT_DST_RDY = '0' and reg_in_src_rdy = '1' else
                '1';

   --! Pipeline
   --! stage 1
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg1_in_src_rdy      <= '0';
            reg1_packet_ts       <= (others => '0');
            reg1_addr            <= (others => '0');
            reg1_b_value         <= (others => '0');
            reg_time_const       <= (others => '0');
            reg1_addr_vld        <= '0';
         elsif stage1_en = '1' then
            reg1_in_src_rdy      <= IN_SRC_RDY;
            reg1_packet_ts       <= PACKET_TS;
            reg1_addr            <= RECORD_ADDR;
            reg1_addr_vld        <= ADDR_VLD;
            reg1_b_value         <= BUCKET_VALUE;
            reg_time_const       <= TIME_CONST;
         end if;
      end if;
   end process;
   --! stage 2
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg2_in_src_rdy      <= '0';
            reg2_packet_ts       <= (others => '0');
            reg2_addr            <= (others => '0');
            reg2_b_value         <= (others => '0');
            reg2_addr_vld        <= '0';
         elsif stage2_en = '1' then
            reg2_in_src_rdy      <= reg1_in_src_rdy;
            reg2_packet_ts       <= reg1_packet_ts;
            reg2_addr            <= reg1_addr;
            reg2_addr_vld        <= reg1_addr_vld;
            reg2_b_value         <= reg1_b_value;
         end if;
      end if;
   end process;
   --! stage 3
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg3_in_src_rdy      <= '0';
            reg3_packet_ts       <= (others => '0');
            reg3_addr            <= (others => '0');
            reg3_b_value         <= (others => '0');
            reg3_b_lim           <= (others => '0');
            reg3_needed_tokens   <= (others => '0');
            reg3_addr_vld        <= '0';
         elsif stage3_en = '1' then
            reg3_in_src_rdy      <= reg2_in_src_rdy;
            reg3_packet_ts       <= reg2_packet_ts;
            reg3_addr            <= reg2_addr;
            reg3_addr_vld        <= reg2_addr_vld;
            reg3_b_value         <= reg2_b_value;
            reg3_b_lim           <= bucket_limit_t(bucket_width-1 downto 0);
            reg3_needed_tokens   <= needed_tokens(bucket_width-1 downto 0);
         end if;
      end if;
   end process;
   --! stage 4
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg4_in_src_rdy      <= '0';
            reg4_packet_ts       <= (others => '0');
            reg4_addr            <= (others => '0');
            reg4_b_value         <= (others => '0');
            reg4_b_lim           <= (others => '0');
            reg4_needed_tokens   <= (others => '0');
            reg4_addr_vld        <= '0';
         elsif stage4_en = '1' then
            reg4_in_src_rdy      <= reg3_in_src_rdy;
            reg4_packet_ts       <= reg3_packet_ts;
            reg4_addr            <= reg3_addr;
            reg4_addr_vld        <= reg3_addr_vld;
            reg4_b_value         <= reg3_b_value;
            reg4_b_lim           <= reg3_b_lim;
            reg4_needed_tokens   <= reg3_needed_tokens;
         end if;
      end if;
   end process;
   --! stage 5
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg5_in_src_rdy      <= '0';
            reg5_packet_ts       <= (others => '0');
            reg5_addr            <= (others => '0');
            reg_b_value          <= (others => '0');
            reg5_b_lim           <= (others => '0');
            reg5_needed_tokens   <= (others => '0');
            reg5_addr_vld        <= '0';
         elsif stage5_en = '1' then
            reg5_in_src_rdy      <= reg4_in_src_rdy;
            reg5_packet_ts       <= reg4_packet_ts;
            reg5_addr            <= reg4_addr;
            reg5_addr_vld        <= reg4_addr_vld;
            reg_b_value          <= reg4_b_value;
            reg5_b_lim           <= reg4_b_lim;
            reg5_needed_tokens   <= reg4_needed_tokens;
         end if;
      end if;
   end process;
   --! stage 6
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg6_in_src_rdy      <= '0';
            reg6_packet_ts       <= (others => '0');
            reg6_addr            <= (others => '0');
            reg6_b_lim           <= (others => '0');
            reg_needed_tokens    <= (others => '0');
            reg6_addr_vld        <= '0';
         elsif stage6_en = '1' then
            reg6_in_src_rdy      <= reg5_in_src_rdy;
            reg6_packet_ts       <= reg5_packet_ts;
            reg6_addr            <= reg5_addr;
            reg6_addr_vld        <= reg5_addr_vld;
            reg6_b_lim           <= reg5_b_lim;
            reg_needed_tokens    <= reg5_needed_tokens;
         end if;
      end if;
   end process;
   --! stage 7
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg_in_src_rdy       <= '0';
            reg_packet_ts        <= (others => '0');
            reg_addr             <= (others => '0');
            reg_b_lim            <= (others => '0');
            reg_addr_vld         <= '0';
         elsif stage7_en = '1' then
            reg_in_src_rdy       <= reg6_in_src_rdy;
            reg_packet_ts        <= reg6_packet_ts;
            reg_addr             <= reg6_addr;
            reg_addr_vld         <= reg6_addr_vld;
            reg_b_lim            <= reg6_b_lim;
         end if;
      end if;
   end process;

   OUT_SRC_RDY <= reg_in_src_rdy;

   --! difference between time stemps
   ----------------------------------------------------------------------------
   -- delta_t <= PACKET_TS - BUCKET_TS;
   ----------------------------------------------------------------------------
   SUB1_inst: entity work.ALU_DSP
      generic map (
         DATA_WIDTH => 64,
         REG_IN     => 0,
         REG_OUT    => 1
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,
         A         => PACKET_TS,
         B         => BUCKET_TS,
         CE_IN     => one,
         CE_OUT    => stage1_en,
         ALUMODE   => sub,
         CARRY_IN  => zero,
         CARRY_OUT => open,
         P         => delta_t
      );

   --! time is converted to tokens
   ----------------------------------------------------------------------------
   -- new_tokens <= delta_t * reg_time_const;
   ----------------------------------------------------------------------------

   MUL64_inst: entity work.MUL_DSP
      generic map (
         A_DATA_WIDTH => CONST_WIDTH,
         B_DATA_WIDTH => delta_width,
         REG_IN     => 1,
         REG_OUT    => 1
      )
      port map (
         CLK    => CLK,
         RESET  => RESET,
         A      => reg_time_const,
         B      => delta_t,
         CE     => stage5_en,
         P      => new_tokens
      );

   --! BUCKET_LIMIT in bytes converted to tokens
   ----------------------------------------------------------------------------
   -- bucket_limit_t <= BUCKET_LIMIT * SPEED;
   ----------------------------------------------------------------------------
   speed_25      <= (zeros(24 downto SPEED_WIDTH) & SPEED);
   bucket_lim_18 <= (zeros(17 downto LIMIT_WIDTH) & BUCKET_LIMIT);
   MUL1_inst: entity work.MUL48
      generic map (
         REG_IN  => 1,
         REG_OUT => 1
      )
      port map (
         CLK    => CLK,
         RESET  => RESET,
         A      => speed_25,
         B      => bucket_lim_18,
         CE_IN  => stage1_en,
         CE_OUT => stage2_en,
         P      => bucket_limit_t
      );

   --! packet of length PACKET_LEN is converted to tokens
   ----------------------------------------------------------------------------
   -- needed_tokens <= SPEED * PACKET_LEN;
   ----------------------------------------------------------------------------
   packet_len_18 <= (zeros(1 downto 0) & PACKET_LEN);
   MUL2_inst: entity work.MUL48
      generic map (
         REG_IN  => 1,
         REG_OUT => 1
      )
      port map (
         CLK    => CLK,
         RESET  => RESET,
         A      => speed_25,
         B      => packet_len_18,
         CE_IN  => stage1_en,
         CE_OUT => stage2_en,
         P      => needed_tokens
      );

   --! token level is set when packet arrives
   ----------------------------------------------------------------------------
   -- token_level <= new_tokens + BUCKET_VALUE
   ----------------------------------------------------------------------------
   add_b <= (zeros((delta_width+CONST_WIDTH-bucket_width)-1 downto 0) & reg_b_value);
   ADD_inst: entity work.ALU_DSP
      generic map (
         DATA_WIDTH => delta_width+CONST_WIDTH,
         REG_IN     => 0,
         REG_OUT    => 1
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,
         A         => std_logic_vector(new_tokens),
         B         => add_b,
         CE_IN     => one,
         CE_OUT    => stage6_en,
         ALUMODE   => add,
         CARRY_IN  => zero,
         CARRY_OUT => token_level(delta_width+CONST_WIDTH),
         P         => token_level((delta_width+CONST_WIDTH)-1 downto 0)
      );

   --! packet validity is checked and packet get GREEN(1) or RED(0) flag
   ----------------------------------------------------------------------------
   -- bucket_level <= token_level - needed_tokens;
   -- flag <= '0' when (bucket_level <= 0) else
   --         '1';
   ----------------------------------------------------------------------------
   sub_b <= (zeros((delta_width+CONST_WIDTH-bucket_width) downto 0) & reg_needed_tokens);
   SUB2_inst: entity work.ALU_DSP
      generic map (
         DATA_WIDTH => delta_width+CONST_WIDTH+1, --! +1 because of CARRY_OUT
         REG_IN     => 0,
         REG_OUT    => 1
      )
      port map (
         CLK       => CLK,
         RESET     => RESET,
         A         => token_level,
         B         => sub_b,
         CE_IN     => one,
         CE_OUT    => stage7_en,
         ALUMODE   => sub,
         CARRY_IN  => zero,
         CARRY_OUT => carry,
         P         => bucket_level
      );

   ----------------------------------------------------------------------------
   -- PASS <= flag;
   ----------------------------------------------------------------------------
   converted_carry : if ((delta_width+CONST_WIDTH+1) mod 48) = 0 generate
      flag <= carry;
   end generate;

   normal_carry : if ((delta_width+CONST_WIDTH+1) mod 48) /= 0 generate
      flag <= not carry;
   end generate;

   PASS <= flag when reg_addr_vld = '1' else
           '1';

   --! rewrite values in bucket

   BUCKET_WE <= flag and reg_in_src_rdy and reg_addr_vld;
   RECORD_ADDR_OUT <= reg_addr;

   ----------------------------------------------------------------------------
   -- BUCKET_VAL_OUT <= bucket_limit_t when (bucket_limit_t <= bucket_level ) else
   --                   bucket_level(bucket_width-1 downto 0);
   ----------------------------------------------------------------------------
   cmp_a <= (zeros((delta_width+CONST_WIDTH-bucket_width) downto 0) & reg_b_lim);
   CMP_inst: entity work.CMP_DSP
      generic map (
         DATA_WIDTH => delta_width+CONST_WIDTH+1, --! +1 because of CARRY_OUT
         REG_IN     => 0,
         REG_OUT    => 0
      )
      port map (
         CLK    => CLK,
         RESET  => RESET,
         A      => cmp_a,
         B      => bucket_level,
         CE_IN  => one,
         CE_OUT => one,
         P      => sel
      );

   --! bucket_limit_t <= bucket_level when sel(1) is '1'
   BUCKET_VAL_OUT <= reg_b_lim when (sel(1) = '1') else
                     bucket_level(bucket_width-1 downto 0);

   BUCKET_TS_OUT <= reg_packet_ts;

end architecture limiter;
