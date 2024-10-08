--
-- lb_endpoint_be.vhd: Internal Bus BE generator
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_BE is
   port(
      -- Common Interface
      CLK             : in  std_logic;
      RESET           : in  std_logic;
      -- Control Interface
      SLAVE_INIT      : in  std_logic;
      SLAVE_LENGHT    : in  std_logic_vector(2 downto 0);
      SLAVE_ALIGN     : in  std_logic_vector(2 downto 0);
      MASTER_INIT     : in  std_logic;
      MASTER_LENGHT   : in  std_logic_vector(2 downto 0);
      MASTER_ALIGN    : in  std_logic_vector(2 downto 0);
      SOF             : in  std_logic;
      EOF             : in  std_logic;
      -- Output Interface
      BE              : out std_logic_vector(7 downto 0)
      );
end entity IB_ENDPOINT_BE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_BE_ARCH of IB_ENDPOINT_BE is

   signal be_mux_sel        : std_logic_vector(1 downto 0);
   signal be_mux            : std_logic_vector(7 downto 0);
   signal be_sof_dec        : std_logic_vector(7 downto 0);
   signal be_eof_dec        : std_logic_vector(7 downto 0);
   signal align_reg         : std_logic_vector(2 downto 0);
   signal last_be_reg       : std_logic_vector(2 downto 0);

begin

BE <= be_mux;

-- align_reg ------------------------------------------------------------
align_regp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (SLAVE_INIT = '1') then
      align_reg <= SLAVE_ALIGN;
    end if;
    if (MASTER_INIT = '1') then
      align_reg <= MASTER_ALIGN;
    end if;
  end if;
end process;

-- last_be_reg ----------------------------------------------------------
last_be_regp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (SLAVE_INIT = '1') then
      last_be_reg <= SLAVE_LENGHT + SLAVE_ALIGN;
    end if;
    if (MASTER_INIT = '1') then
      last_be_reg <= MASTER_LENGHT + MASTER_ALIGN;
    end if;
  end if;
end process;

-- be_sof decoder--------------------------------------------------------
be_sof_decp: process(align_reg)
begin
   case align_reg is
      when "000"  => be_sof_dec <= "11111111";
      when "001"  => be_sof_dec <= "11111110";
      when "010"  => be_sof_dec <= "11111100";
      when "011"  => be_sof_dec <= "11111000";
      when "100"  => be_sof_dec <= "11110000";
      when "101"  => be_sof_dec <= "11100000";
      when "110"  => be_sof_dec <= "11000000";
      when "111"  => be_sof_dec <= "10000000";
      when others => be_sof_dec <= "XXXXXXXX";
   end case;
end process;

-- be_eof decoder ---------------------------------------------------------
be_eof_decp: process(last_be_reg)
begin
   case last_be_reg is
      when "000"  => be_eof_dec <= "11111111";
      when "001"  => be_eof_dec <= "00000001";
      when "010"  => be_eof_dec <= "00000011";
      when "011"  => be_eof_dec <= "00000111";
      when "100"  => be_eof_dec <= "00001111";
      when "101"  => be_eof_dec <= "00011111";
      when "110"  => be_eof_dec <= "00111111";
      when "111"  => be_eof_dec <= "01111111";
      when others => be_eof_dec <= "XXXXXXXX";
   end case;
end process;

be_mux_sel <= EOF & SOF;

-- multiplexor be_mux ---------------------------------------------------
be_muxp: process(be_mux_sel, be_sof_dec, be_eof_dec)
begin
   case be_mux_sel is
      when "00" => be_mux <= "11111111";
      when "01" => be_mux <= be_sof_dec;
      when "10" => be_mux <= be_eof_dec;
      when "11" => be_mux <= (be_sof_dec and be_eof_dec);
      when others => be_mux <= (others => 'X');
   end case;
end process;


end architecture IB_ENDPOINT_BE_ARCH;

