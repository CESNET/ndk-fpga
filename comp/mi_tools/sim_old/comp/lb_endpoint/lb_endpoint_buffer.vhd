--
-- lb_endpoint_buffer.vhd: Local Bus ADC Buffer
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ENDPOINT_BUFFER is
   port (
      -- Common Interface
      CLK          : in  std_logic;
      RESET        : in  std_logic;

      -- Input Interface
      ADDR_SEL     : in  std_logic;
      DATA_IN      : in  std_logic_vector(15 downto 0);
      BE_IN        : in  std_logic_vector(1 downto 0);
      WR_IN        : in  std_logic;
      RD_IN        : in  std_logic;

      --Output Interface
      DATA_OUT     : out std_logic_vector(15 downto 0);
      BE_OUT       : out std_logic_vector(1 downto 0);
      WR_OUT       : out std_logic;
      RD_OUT       : out std_logic;
      DATA_OUT_VLD : out std_logic;
      BUFFER_RD    : in  std_logic
      );
end entity LB_ENDPOINT_BUFFER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ENDPOINT_BUFFER_ARCH of LB_ENDPOINT_BUFFER is

-- Signal Declaration ---------------------------------------------------------
   signal srl_data_in     : std_logic_vector(19 downto 0);
   signal srl_data_out    : std_logic_vector(19 downto 0);
   signal srl_en          : std_logic;
   signal srl_addr        : std_logic_vector(3 downto 0);
   signal counter         : std_logic_vector(4 downto 0);
   signal cntr_reg_up     : std_logic;
   signal cntr_reg_down   : std_logic;


-- component declaration ------------------------------------------------------
component SRL16E
   generic(
      INIT : bit_vector(15 downto 0) := X"0000"
   );
   port (
      D    : in std_logic;
      CE   : in std_logic;
      CLK  : in std_logic;
      A0   : in std_logic;
      A1   : in std_logic;
      A2   : in std_logic;
      A3   : in std_logic;
      Q    : out std_logic
   );
end component;


begin
DATA_OUT     <= srl_data_out(15 downto 0);
BE_OUT       <= srl_data_out(17 downto 16);
WR_OUT       <= srl_data_out(18);
RD_OUT       <= srl_data_out(19);
DATA_OUT_VLD <= '0' when counter = "00000" else '1'; -- Not empty
srl_data_in  <= RD_IN & WR_IN & BE_IN & DATA_IN;
srl_en       <= (not RD_IN or not WR_IN) and ADDR_SEL;

-- srl_addr decoder -----------------------------------------------------------
srl_addr_decp: process(counter)
begin
   case counter is
      when "00000" => srl_addr <= "0000";
      when "00001" => srl_addr <= "0000";
      when "00010" => srl_addr <= "0001";
      when "00011" => srl_addr <= "0010";
      when "00100" => srl_addr <= "0011";
      when "00101" => srl_addr <= "0100";
      when "00110" => srl_addr <= "0101";
      when "00111" => srl_addr <= "0110";
      when "01000" => srl_addr <= "0111";
      when "01001" => srl_addr <= "1000";
      when "01010" => srl_addr <= "1001";
      when "01011" => srl_addr <= "1010";
      when "01100" => srl_addr <= "1011";
      when "01101" => srl_addr <= "1100";
      when "01110" => srl_addr <= "1101";
      when "01111" => srl_addr <= "1110";
      when "10000" => srl_addr <= "1111";
      when others => srl_addr <= "1111";
   end case;
end process;

-- Count Up when DATA_IN_VLD and (BUFFER_NOT_RD or Counter = 0)
cntr_reg_up   <= '1' when (srl_en = '1' and (BUFFER_RD = '0' or counter = "00000") ) else '0';
-- Count Down when BUFFER_RD and DATA_IN_NOT_VLD and Counter > 0
cntr_reg_down <= '1' when (srl_en = '0' and BUFFER_RD = '1' and counter /= "00000") else '0';

-- data couner ------------------------------------------------------------------
-- Actual count of item in SHR
datacounterp: process(RESET, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         counter <= "00000";
      else
         if (cntr_reg_up = '1') then
            counter <= counter + 1;
         end if;
         if (cntr_reg_down = '1') then
            counter <= counter - 1;
         end if;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
-- Generate Shift Register
SH_REG_GEN : for i in 0 to 19 generate
  U_SRL16E: SRL16E
    port map (
	   D      => srl_data_in(i),
	   CE     => srl_en,
	   CLK    => CLK,
	   A0     => srl_addr(0),
	   A1     => srl_addr(1),
	   A2     => srl_addr(2),
	   A3     => srl_addr(3),
	   Q      => srl_data_out(i)
      );
end generate;

end architecture LB_ENDPOINT_BUFFER_ARCH;

