-- rate_limiter_mi32_arch.vhd
--!
--! \file  rate_limiter_mi32_arch.vhd
--! \brief Memory modul with MI32 interface for rate_limiter
--!        BUCKET_LIMIT, SPEED and TIME_CONST are saved in BRAMs
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

architecture mi32_interface of rate_lim_mi32 is

   constant data_width  : integer := LIMIT_WIDTH + SPEED_WIDTH + CONST_WIDTH;

   constant zeros       : std_logic_vector(31 downto 0) := X"00000000";
   constant zero        : std_logic := '0';
   constant one         : std_logic := '1';

   signal addr          : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal we            : std_logic;
   signal we_BRAM       : std_logic;
   signal re_BRAM       : std_logic;
   signal sel           : std_logic_vector(1 downto 0);
   signal decoded_part  : std_logic_vector(3 downto 0);
   signal mux_in_input  : std_logic_vector(data_width-1 downto 0);
   signal mux_in_read   : std_logic_vector(data_width-1 downto 0);
   signal mux_reg_data  : std_logic_vector(data_width-1 downto 0);

   signal data_read     : std_logic;
   signal sel_out       : std_logic_vector(2 downto 0);
   signal limit_out     : std_logic_vector(31 downto 0);
   signal speed_out     : std_logic_vector(31 downto 0);
   signal const_out     : std_logic_vector(31 downto 0);
   signal reg_generics  : std_logic_vector(31 downto 0);

   signal reg_limit     : std_logic_vector(LIMIT_WIDTH-1 downto 0);
   signal reg_speed     : std_logic_vector(SPEED_WIDTH-1 downto 0);
   signal reg_const     : std_logic_vector(CONST_WIDTH-1 downto 0);
   signal reg_data_all  : std_logic_vector(data_width-1 downto 0);

   function int2vec(int, width: integer) return std_logic_vector is
   begin
      return std_logic_vector(to_unsigned(int, width));
   end int2vec;

begin

   addr <= MI32_DWR(ADDR_WIDTH-1 downto 0);
   we   <= MI32_DWR(31);
   sel  <= MI32_ADDR(3 downto 2);
   -- sel: 00 - write/read limit register
   --      01 - write/read speed register
   --      10 - write/read const register
   --      11 - write/read to/from BRAM, use address in MI32_DWR

   decoded_part <= ("0001") when sel = "00" else
                   ("0010") when sel = "01" else
                   ("0100") when sel = "10" else
                   ("1000");

   --! Writing logic

   we_BRAM <= decoded_part(3) and MI32_WR and we;

   --! select data for regs
   mux_in_input <= (MI32_DWR(LIMIT_WIDTH-1 downto 0)) & (MI32_DWR(SPEED_WIDTH-1 downto 0)) & (MI32_DWR(CONST_WIDTH-1 downto 0));
   mux_reg_data <= mux_in_input when data_read = '0' else
                   mux_in_read;

   --! Pipeline - write/read data
   process(CLK)
   begin
      if rising_edge(CLK) then
         if RESET = '1' then
            reg_limit <= (others => '0');
            reg_speed <= (others => '0');
            reg_const <= (others => '0');
         else
            if ((decoded_part(0) and MI32_WR) or data_read) = '1' then
               reg_limit <= mux_reg_data(data_width-1 downto data_width-LIMIT_WIDTH);
            end if;
            if ((decoded_part(1) and MI32_WR) or data_read) = '1' then
               reg_speed <= mux_reg_data(data_width-LIMIT_WIDTH-1 downto CONST_WIDTH);
            end if;
            if ((decoded_part(2) and MI32_WR) or data_read) = '1' then
               reg_const <=mux_reg_data (CONST_WIDTH-1 downto 0);
            end if;
         end if;
      end if;
   end process;

   --! Reading logic

   re_BRAM <= decoded_part(3) and MI32_WR and (not we);

   sel_out <= MI32_ADDR(4) & sel;

   limit_out <= zeros(31 downto LIMIT_WIDTH) & reg_limit;
   speed_out <= zeros(31 downto SPEED_WIDTH) & reg_speed;
   const_out <= zeros(31 downto CONST_WIDTH) & reg_const;

   reg_generics <= int2vec(ADDR_WIDTH, 8) & int2vec(LIMIT_WIDTH, 8) & int2vec(SPEED_WIDTH, 8) & int2vec(CONST_WIDTH, 8);

   MI32_DRD <= limit_out    when sel_out = "000" else
               speed_out    when sel_out = "001" else
               const_out    when sel_out = "010" else
               reg_generics when sel_out = "100" else
               (others => '0');

   MI32_DRDY <= (decoded_part(0) or decoded_part(1) or decoded_part(2)) and MI32_RD;

   reg_data_all <= reg_limit & reg_speed & reg_const;

   MEM_MI32: entity work.DP_BRAM_V7
      generic map(
         DATA_WIDTH     => data_width,
         ADDRESS_WIDTH  => ADDR_WIDTH,
         ENABLE_OUT_REG => false
      )
      port map(
         -- interface A - read only
         CLKA     => CLK,
         RSTA     => RESET,
         PIPE_ENA => one,
         REA      => USER_RD,
         WEA      => zero,
         ADDRA    => USER_ADDR,
         DIA      => (others => '0'),
         DOA_DV   => open,
         DOA      => USER_DRD,
         -- interface B - MI32
         CLKB     => CLK,
         RSTB     => RESET,
         PIPE_ENB => one,
         REB      => re_BRAM,
         WEB      => we_BRAM,
         ADDRB    => addr,
         DIB      => reg_data_all,
         DOB_DV   => data_read,
         DOB      => mux_in_read
      );

   --! Output
   MI32_ARDY <= MI32_RD or MI32_WR;

end mi32_interface;
