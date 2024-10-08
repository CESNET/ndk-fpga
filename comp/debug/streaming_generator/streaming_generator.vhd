--! \file:   streaming-generator.vhd
--! \brief:  The module is used to send test data in hardware.  Control via MI32.
--!          Is it accessible control SW Tool (in preparation).
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use IEEE.numeric_std.all;
Library UNISIM;
use UNISIM.vcomponents.all;
use work.math_pack.all;

entity STREAMING_GENERATOR is
   generic (
      --! Data width of input/output value
      DATA_WIDTH   : integer := 544;
      --! Number of items in memory
      ITEMS        : integer := 1024;
      --! size counters for gnerated SRC_RDY output
      CNT_WIDTH    : integer := 10;
      --! Random generated SRC_RDY support
      RANDOM       : boolean := true
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data output
      DATA     : out  std_logic_vector(DATA_WIDTH - 1 downto 0);
      --! ready signals
      SRC_RDY  : out  std_logic;
      DST_RDY  : in  std_logic;

      --! MI32 input interface -------------------------------------------------
      --! Input Data
      MI_DWR                        : in  std_logic_vector(31 downto 0);
      --! Address
      MI_ADDR                       : in  std_logic_vector(31 downto 0);
      --! Read Request
      MI_RD                         : in  std_logic;
      --! Write Request
      MI_WR                         : in  std_logic;
      --! Byte Enable
      MI_BE                         : in  std_logic_vector(3  downto 0);
      --! Output Data
      MI_DRD                        : out std_logic_vector(31 downto 0);
      --! Address Ready
      MI_ARDY                       : out std_logic;
      --! Data Ready
      MI_DRDY                       : out std_logic
   );
end STREAMING_GENERATOR;

architecture full of STREAMING_GENERATOR is
   --! Value for all items (BRAM, REGISTERS)
   constant ITEMS_ALL : integer := ITEMS + 16;
   --! convert  generic parameters  to std_logic
   signal settings1 : std_logic_vector(31 downto 0);
   signal settings2 : std_logic_vector(31 downto 0);
   --! pipe MI_RD, MI_BE
   signal rd_reg     : std_logic_vector(1 downto 0);
   signal be_reg     : std_logic_vector(3 downto 0);
   --! MI_ADDR right shift 2 bits (/4)
   signal addr_div  : std_logic_vector(29 downto 0);
   --! addr_div sub 16 - for address BRAM
   signal addr_bram : std_logic_vector(log2(ITEMS_ALL)-1 downto 0);
   --! decode addr_div for address registers from MI_32
   signal addr_dec  : std_logic_vector(4 downto 0);

   --! multiplexed settings, configs registers for read with MI_32
   signal mux_data_in : std_logic_vector((32*7)-1 downto 0);
   signal mux_out     : std_logic_vector(31 downto 0);
   --! pipe mux_out
   signal mux_reg_out : std_logic_vector(31 downto 0);

   signal mux_drd_mem : std_logic_vector(31 downto 0);
   --! multiplexed BRAM or registers on MI_DRD
   signal mux_addr_out : std_logic_vector(31 downto 0);

   --! enable write to BRAM;
   signal bram_wr     : std_logic;

   --! contorl write to BRAM with support BE
   signal dia  : std_logic_vector(31 downto 0);
   signal wea  : std_logic;
   signal rea  : std_logic;
   signal ardy : std_logic;

   --! read from BRAM on port B - generator
   signal bram_b_data : std_logic_vector(32*div_roundup(DATA_WIDTH, 32)-1 downto 0);
   signal bram_b_addr : std_logic_vector(log2(ITEMS)-1 downto 0);
   signal bram_b_rd   : std_logic;

   --! control signal for generator
   signal cmd_run     :std_logic;
   --! signal of generator - stop generate
   signal cmd_run_off :std_logic;

   --! signals from configs registers
   signal config_pom_1 : std_logic_vector(31 downto 0);
   signal config_pom_2 : std_logic_vector(31 downto 0);
   signal config_pom_3 : std_logic_vector(31 downto 0);
   signal config_pom_4 : std_logic_vector(31 downto 0);

begin
   addr_bram <= addr_div(log2(ITEMS_ALL)-1 downto 0);
   --! CONFINGS DATA
   config_pom_1  <= mux_data_in(95+(0*32) downto 64+(0*32));
   config_pom_2  <= mux_data_in(95+(1*32) downto 64+(1*32));
   config_pom_3  <= mux_data_in(95+(2*32) downto 64+(2*32));
   config_pom_4  <= mux_data_in(95+(3*32) downto 64+(3*32));

   settings1(7 downto 0)   <= X"11";
   settings1(8) <= '0';
   settings1(15 downto 9)  <= (others => '0');
   settings1(31 downto 16) <= conv_std_logic_vector(CNT_WIDTH, 16);

   settings2(15 downto 0)  <= conv_std_logic_vector(ITEMS, 16);
   settings2(31 downto 16) <= conv_std_logic_vector(DATA_WIDTH, 16);

   --! pipe signals
   pipe_signals: process(CLK)
   begin
      if(CLK'event) and (CLK='1') then
         if (RESET='1') then
            rd_reg(0) <= '0';
            rd_reg(1) <= '0';
         else
            rd_reg(0) <= MI_RD;
            rd_reg(1) <= rd_reg(0);
            be_reg(3 downto 0) <= MI_BE;
            mux_reg_out <= mux_out;
            MI_DRD <= mux_addr_out;
         end if;
      end if;
   end process;

   MI_DRDY <= rd_reg(1);
   addr_div(29 downto 0) <= MI_ADDR(31 downto 2);

   --! read, write register or BRAM
   control_ardy: process(addr_bram, MI_WR, MI_RD, ardy)
   begin
      if (addr_bram < 16) then
         MI_ARDY <= MI_WR or MI_RD;
      else
         MI_ARDY <= (MI_WR and ardy) or MI_RD;
      end if;
   end process;

   --! decode for write registers (comads, configs 1,2,3...)
   WITH addr_div(2 downto 0) SELECT
      addr_dec <= "00001" WHEN "010",
                  "00010" WHEN "011",
                  "00100" WHEN "100",
                  "01000" WHEN "101",
                  "10000" WHEN "110",
                  "00000" WHEN OTHERS;

   --! generate registers with support MI_BE
   GEN_REGS: for I in 0 to 3 generate
      signal regs_enable : std_logic;
      signal reg_out     : std_logic_vector(31 downto 0);
   begin

      en_mem_regs: process(MI_WR, addr_dec(I), addr_bram)
      begin
         if(addr_bram < 16) then
            regs_enable <= MI_WR and addr_dec(I);
         else
            regs_enable <= '0';
         end if;
      end process;

      RW_RWGISTERS_inst : entity work.RW_REGISTER
      port map (
         CLK => CLK,
         --! MI32 BE signal
         BE => MI_BE,
         --! input data
         DATA  => MI_DWR,
         --! enbale signal
         ENABLE => regs_enable,
         --! reset signal
         RESET => RESET,
         --! output data
         P => reg_out
      );

      mux_data_in(95+(I*32) downto 64+(I*32)) <= reg_out;
   end generate;

   --! command register (RUN);
   GEN_CMD_REG : if(true) generate
      signal r_out : std_logic_vector(31 downto 0);
   begin
      control_run: process(CLK)
      begin
         if(CLK'event) and (CLK='1') then
            if (RESET = '1' or cmd_run_off = '1') then
                cmd_run <= '0';
            elsif (MI_WR = '1' and addr_dec(4) = '1' and MI_BE(0) = '1' and (addr_bram < 16)) then
                cmd_run  <= MI_DWR(0);
            end if;
         end if;
      end process;

      r_out(0) <= cmd_run and (not cmd_run_off);
      r_out(1) <= DST_RDY;
      r_out(2) <= RESET;
      r_out(31 downto 3) <= (others => '0');

      mux_data_in(95+(4*32) downto 64+(4*32)) <= r_out;
   end generate;

   mux_data_in(31 downto 0)   <= settings1;
   mux_data_in(63 downto 32)  <= settings2;

   --! mux register
   GEN_MUX_inst : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 32,
      MUX_WIDTH  => 7   -- multiplexer width (number of inputs)
   )
   port map(
      DATA_IN    => mux_data_in,
      SEL        => addr_div(2 downto 0),
      DATA_OUT   => mux_out
   );

   --! mux REGISTER or BRAM
   mux_regs_bram: process(mux_reg_out, mux_drd_mem, addr_bram)
   begin
      if (addr_bram < 16) then
         mux_addr_out <= mux_reg_out;
      else
         mux_addr_out <= mux_drd_mem;
      end if;
   end process;

   control_miwr: process(MI_WR, addr_bram )
   begin
      if(addr_bram < ITEMS_ALL and addr_bram >= 16) then
         bram_wr <= MI_WR;
      else
         bram_wr <= '0';
      end if;
   end process;

   --! write data to BRAM with support MI_BE
   CMP_WR_BRAM_inst : entity work.CMP_WR_BRAM
   port map(
      CLK  => CLK,
      --! MI32 BE signal
      BE   => MI_BE,
      MI_WR  => bram_wr,
      --MI_RD       : in  std_logic;
      --! input data
      MI_DATA  => MI_DWR,
      BRAM_DATA   => mux_drd_mem,
      --! enbale signal
      --ENABLE      : in  std_logic;
      --! reset signal
      RESET   => RESET,
      --! output data
      P  => dia,
      WR => wea,
      RD => rea,
      ARDY => ardy
   );

   --! generate BRAMs
   BRAM_GENERATOR_inst : entity work.BRAM_GENERATOR
   generic map (
      ITEMS      => ITEMS,
      --! Input data width
      DATA_WIDTH => DATA_WIDTH
      --! Address bus width
   )
   port map (
      --! \name Common interface
      RESET => RESET,
      CLK => CLK,

      --! \name Interface A
      --! Read Enable
      REA   => rea,
      --! Write enable
      WEA   => wea,
      --! Address A
      ADDRA => addr_div,
      --! Data A In
      DIA   => dia,
      --! Data A Out
      DOA   => mux_drd_mem,

      --! \name Interface B
      --! Read Enable
      REB   => bram_b_rd,
      --! Address B
      ADDRB => bram_b_addr,
      --! Data B out
      DOB   => bram_b_data
   );

  --! connect data output generator
  GENERATOR_inst : entity work.GENERATOR
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      ITEMS       => ITEMS,
      CNT_WIDTH   => CNT_WIDTH,
      RANDOM      => RANDOM
   )
   port map (
      --! Clock input
      CLK        => CLK,
      --! Reset input
      RESET      => RESET,

      --! BRAM data
      BRAM_DATA  => bram_b_data,
      BRAM_RD    => bram_b_rd,
      BRAM_ADDR  => bram_b_addr,

      --! Data out
      DATA_OUT   => DATA,

      --! ready signals
      SRC_RDY  => SRC_RDY,
      DST_RDY  => DST_RDY,

      --! Config Data
      CONFIG_1  => config_pom_1,
      CONFIG_2  => config_pom_2,
      CONFIG_3  => config_pom_3,
      CONFIG_4  => config_pom_4,

      --! Commands
      CMD_RUN      => mux_data_in(64+(4*32)),
      CMD_RUN_OFF  => cmd_run_off
   );
end full;
