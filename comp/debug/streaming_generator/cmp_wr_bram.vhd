--! \file:   cmp_wr_bram.vhd
--! \brief:  Control writing MI32 data to bram with support BE
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
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! decoder entity
entity CMP_WR_BRAM is
   port (
      CLK         : in  std_logic;
      --! MI32 BE signal
      BE          : in  std_logic_vector(3 downto 0);
      MI_WR       : in  std_logic;
      --! input data
      MI_DATA           : in  std_logic_vector(31 downto 0);
      BRAM_DATA         : in  std_logic_vector(31 downto 0);
      --! reset signal
      RESET       : in  std_logic;
      --! output data
      P           : out std_logic_vector(31 downto 0);
      WR          : out std_logic;
      RD          : out std_logic;
      ARDY        : out std_logic
   );
end CMP_WR_BRAM;

--! architecture of CMP_DECODE
architecture full of CMP_WR_BRAM is
   signal mi_data_reg : std_logic_vector(31 downto 0);
   signal be_reg : std_logic_vector(3 downto 0);
   signal reg_pom : std_logic;
begin

   --! generate multiplexer - 4 * 8 bit
   GEN_REG : for I in 0 to 3 generate
   begin
      gen_reg_width_be: process(be_reg(I), mi_data_reg(7+(8*I) downto 0+(8*I)), BRAM_DATA(7+(8*I) downto 0+(8*I)))
      begin
            if (be_reg(I) = '1') then
               P(7+(8*I) downto 0+(8*I)) <= mi_data_reg(7+(8*I) downto 0+(8*I));
            else
               P(7+(8*I) downto 0+(8*I)) <= BRAM_DATA(7+(8*I) downto 0+(8*I));
            end if;
      end process;
   end generate;

   --! pipe sinals
   pipe_signals: process(CLK)
   begin
      if(CLK'event) and (CLK='1') then
         be_reg <= BE;
         mi_data_reg <= MI_DATA;
      end if;
   end process;

   --! generate control signal
   control_bram_wr: process(CLK)
   begin
      if(CLK'event) and (CLK='1') then
         if (RESET='1' or reg_pom='1') then
            reg_pom <= '0';
         else
            reg_pom <= MI_WR;
         end if;
      end if;
   end process;

   --! control BRAMs and ARDY
   mux_out: process(reg_pom)
   begin
      if(reg_pom = '1') then
        WR <= '1';
        RD <= '0';
        ARDY <= '1';
      else
        WR <= '0';
        RD <= '1';
        ARDY <= '0';
      end if;
   end process;
end full;
