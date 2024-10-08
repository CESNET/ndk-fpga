--
-- ib_endpoint_write_align.vhd: Internal Bus Write Align
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
entity IB_ENDPOINT_WRITE_ALIGN is
   port(
      -- Common Interface
      CLK                : in  std_logic;
      RESET              : in  std_logic;

      -- Input Interface
      RD_DATA_IN         : in  std_logic_vector(63 downto 0);
      RD_SRC_RDY_IN      : in  std_logic;
      RD_DST_RDY_IN      : out std_logic;
      RD_EOF_IN          : in  std_logic;

      -- Output Interface
      RD_DATA_OUT        : out std_logic_vector(63 downto 0);
      RD_SRC_RDY_OUT     : out std_logic;
      RD_DST_RDY_OUT     : in  std_logic;
      RD_EOF_OUT         : out std_logic;

      -- Align Control Interface
      MASTER_ALIGN       : in  std_logic_vector(2 downto 0);
      MASTER_LENGTH      : in  std_logic_vector(2 downto 0);
      MASTER_INIT        : in  std_logic;
      SLAVE_ALIGN        : in  std_logic_vector(2 downto 0);
      SLAVE_ALIGN_VLD    : in  std_logic;
      SLAVE_LENGTH       : in  std_logic_vector(2 downto 0);
      SLAVE_LENGTH_VLD   : in  std_logic;
      SLAVE_INIT         : in  std_logic
      );
end entity IB_ENDPOINT_WRITE_ALIGN;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_WRITE_ALIGN_ARCH of IB_ENDPOINT_WRITE_ALIGN is

   signal data_reg0      : std_logic_vector(63 downto 0);
   signal data_reg1      : std_logic_vector(63 downto 0);
   signal data_reg_we    : std_logic;

   signal data_out_mux0  : std_logic_vector(7 downto 0);
   signal data_out_mux1  : std_logic_vector(7 downto 0);
   signal data_out_mux2  : std_logic_vector(7 downto 0);
   signal data_out_mux3  : std_logic_vector(7 downto 0);
   signal data_out_mux4  : std_logic_vector(7 downto 0);
   signal data_out_mux5  : std_logic_vector(7 downto 0);
   signal data_out_mux6  : std_logic_vector(7 downto 0);
   signal data_out_mux7  : std_logic_vector(7 downto 0);
   signal write_last_sel : std_logic_vector(5 downto 0);
   signal write_last     : std_logic;
   signal write_last_reg : std_logic;
   signal align_reg      : std_logic_vector(2 downto 0);
   signal length_reg     : std_logic_vector(2 downto 0);

begin

RD_DATA_OUT     <= data_out_mux7 & data_out_mux6 & data_out_mux5 &
                   data_out_mux4 & data_out_mux3 & data_out_mux2 &
                   data_out_mux1 & data_out_mux0;
RD_SRC_RDY_OUT  <= (write_last_reg or RD_SRC_RDY_IN);
RD_EOF_OUT      <= (not write_last and RD_EOF_IN) or write_last_reg;
RD_DST_RDY_IN   <= RD_DST_RDY_OUT;
data_reg1       <= RD_DATA_IN;
data_reg_we     <= RD_SRC_RDY_IN and RD_DST_RDY_OUT;



write_last_sel <= align_reg & length_reg;
-- decoder write_last ------------------------------------------------------
write_last_decp: process(write_last_sel)
begin
   case write_last_sel is
      when "000000" => write_last <= '0';
      when "000001" => write_last <= '0';
      when "000010" => write_last <= '0';
      when "000011" => write_last <= '0';
      when "000100" => write_last <= '0';
      when "000101" => write_last <= '0';
      when "000110" => write_last <= '0';
      when "000111" => write_last <= '0';

      when "001000" => write_last <= '1';
      when "001001" => write_last <= '0';
      when "001010" => write_last <= '0';
      when "001011" => write_last <= '0';
      when "001100" => write_last <= '0';
      when "001101" => write_last <= '0';
      when "001110" => write_last <= '0';
      when "001111" => write_last <= '0';

      when "010000" => write_last <= '1';
      when "010001" => write_last <= '0';
      when "010010" => write_last <= '0';
      when "010011" => write_last <= '0';
      when "010100" => write_last <= '0';
      when "010101" => write_last <= '0';
      when "010110" => write_last <= '0';
      when "010111" => write_last <= '1';

      when "011000" => write_last <= '1';
      when "011001" => write_last <= '0';
      when "011010" => write_last <= '0';
      when "011011" => write_last <= '0';
      when "011100" => write_last <= '0';
      when "011101" => write_last <= '0';
      when "011110" => write_last <= '1';
      when "011111" => write_last <= '1';

      when "100000" => write_last <= '1';
      when "100001" => write_last <= '0';
      when "100010" => write_last <= '0';
      when "100011" => write_last <= '0';
      when "100100" => write_last <= '0';
      when "100101" => write_last <= '1';
      when "100110" => write_last <= '1';
      when "100111" => write_last <= '1';

      when "101000" => write_last <= '1';
      when "101001" => write_last <= '0';
      when "101010" => write_last <= '0';
      when "101011" => write_last <= '0';
      when "101100" => write_last <= '1';
      when "101101" => write_last <= '1';
      when "101110" => write_last <= '1';
      when "101111" => write_last <= '1';

      when "110000" => write_last <= '1';
      when "110001" => write_last <= '0';
      when "110010" => write_last <= '0';
      when "110011" => write_last <= '1';
      when "110100" => write_last <= '1';
      when "110101" => write_last <= '1';
      when "110110" => write_last <= '1';
      when "110111" => write_last <= '1';

      when "111000" => write_last <= '1';
      when "111001" => write_last <= '0';
      when "111010" => write_last <= '1';
      when "111011" => write_last <= '1';
      when "111100" => write_last <= '1';
      when "111101" => write_last <= '1';
      when "111110" => write_last <= '1';
      when "111111" => write_last <= '1';

      when others   => write_last <= 'X';
   end case;
end process;

-- -------------------------------------------------------------------------
--                           ALIGN REGISTERS
-- -------------------------------------------------------------------------

-- register align_reg ------------------------------------------------------
align_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      align_reg <= "000";
   elsif (CLK'event AND CLK = '1') then
      if (MASTER_INIT = '1') then
         align_reg <= MASTER_ALIGN;
      end if;
      if (SLAVE_ALIGN_VLD = '1') then
         align_reg <= SLAVE_ALIGN;
      end if;
   end if;
end process;

-- register length_reg ----------------------------------------------------
length_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      length_reg <= "000";
   elsif (CLK'event AND CLK = '1') then
      if (MASTER_INIT = '1') then
         length_reg <= MASTER_LENGTH;
      end if;
      if (SLAVE_LENGTH_VLD = '1') then
         length_reg <= SLAVE_LENGTH;
      end if;
   end if;
end process;

-- register write_last_reg -------------------------------------------------
write_last_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      write_last_reg <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (RD_EOF_IN = '1' and data_reg_we = '1') then
         write_last_reg <= write_last;
      end if;
      if (SLAVE_INIT = '1' or MASTER_INIT = '1') then
         write_last_reg <= '0';
      end if;
   end if;
end process;


-- register data_reg0 ------------------------------------------------------
data_reg0p: process(RESET, CLK)
begin
   if (RESET = '1') then
      data_reg0 <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (data_reg_we = '1') then
         data_reg0 <= data_reg1;
      end if;
      if (SLAVE_INIT = '1' or MASTER_INIT = '1') then
         data_reg0 <= (others => '0');
      end if;
   end if;
end process;

-- -------------------------------------------------------------------------
--                         DATA ALIGN MULTIPLEXORS
-- -------------------------------------------------------------------------

-- multiplexor data_out_mux0 -----------------------------------------------
data_out_mux0p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux0 <= data_reg1(7 downto 0);
      when "001" => data_out_mux0 <= data_reg0(63 downto 56);
      when "010" => data_out_mux0 <= data_reg0(55 downto 48);
      when "011" => data_out_mux0 <= data_reg0(47 downto 40);
      when "100" => data_out_mux0 <= data_reg0(39 downto 32);
      when "101" => data_out_mux0 <= data_reg0(31 downto 24);
      when "110" => data_out_mux0 <= data_reg0(23 downto 16);
      when "111" => data_out_mux0 <= data_reg0(15 downto 8);
      when others => data_out_mux0 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux1 -----------------------------------------------
data_out_mux1p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux1 <= data_reg1(15 downto 8);
      when "001" => data_out_mux1 <= data_reg1(7 downto 0);
      when "010" => data_out_mux1 <= data_reg0(63 downto 56);
      when "011" => data_out_mux1 <= data_reg0(55 downto 48);
      when "100" => data_out_mux1 <= data_reg0(47 downto 40);
      when "101" => data_out_mux1 <= data_reg0(39 downto 32);
      when "110" => data_out_mux1 <= data_reg0(31 downto 24);
      when "111" => data_out_mux1 <= data_reg0(23 downto 16);
      when others => data_out_mux1 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux2 -----------------------------------------------
data_out_mux2p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux2 <= data_reg1(23 downto 16);
      when "001" => data_out_mux2 <= data_reg1(15 downto 8);
      when "010" => data_out_mux2 <= data_reg1(7 downto 0);
      when "011" => data_out_mux2 <= data_reg0(63 downto 56);
      when "100" => data_out_mux2 <= data_reg0(55 downto 48);
      when "101" => data_out_mux2 <= data_reg0(47 downto 40);
      when "110" => data_out_mux2 <= data_reg0(39 downto 32);
      when "111" => data_out_mux2 <= data_reg0(31 downto 24);
      when others => data_out_mux2 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux3 -----------------------------------------------
data_out_mux3p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux3 <= data_reg1(31 downto 24);
      when "001" => data_out_mux3 <= data_reg1(23 downto 16);
      when "010" => data_out_mux3 <= data_reg1(15 downto 8);
      when "011" => data_out_mux3 <= data_reg1(7 downto 0);
      when "100" => data_out_mux3 <= data_reg0(63 downto 56);
      when "101" => data_out_mux3 <= data_reg0(55 downto 48);
      when "110" => data_out_mux3 <= data_reg0(47 downto 40);
      when "111" => data_out_mux3 <= data_reg0(39 downto 32);
      when others => data_out_mux3 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux4 -----------------------------------------------
data_out_mux4p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux4 <= data_reg1(39 downto 32);
      when "001" => data_out_mux4 <= data_reg1(31 downto 24);
      when "010" => data_out_mux4 <= data_reg1(23 downto 16);
      when "011" => data_out_mux4 <= data_reg1(15 downto 8);
      when "100" => data_out_mux4 <= data_reg1(7 downto 0);
      when "101" => data_out_mux4 <= data_reg0(63 downto 56);
      when "110" => data_out_mux4 <= data_reg0(55 downto 48);
      when "111" => data_out_mux4 <= data_reg0(47 downto 40);
      when others => data_out_mux4 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux5 -----------------------------------------------
data_out_mux5p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux5 <= data_reg1(47 downto 40);
      when "001" => data_out_mux5 <= data_reg1(39 downto 32);
      when "010" => data_out_mux5 <= data_reg1(31 downto 24);
      when "011" => data_out_mux5 <= data_reg1(23 downto 16);
      when "100" => data_out_mux5 <= data_reg1(15 downto 8);
      when "101" => data_out_mux5 <= data_reg1(7 downto 0);
      when "110" => data_out_mux5 <= data_reg0(63 downto 56);
      when "111" => data_out_mux5 <= data_reg0(55 downto 48);
      when others => data_out_mux5 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux6 -----------------------------------------------
data_out_mux6p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux6 <= data_reg1(55 downto 48);
      when "001" => data_out_mux6 <= data_reg1(47 downto 40);
      when "010" => data_out_mux6 <= data_reg1(39 downto 32);
      when "011" => data_out_mux6 <= data_reg1(31 downto 24);
      when "100" => data_out_mux6 <= data_reg1(23 downto 16);
      when "101" => data_out_mux6 <= data_reg1(15 downto 8);
      when "110" => data_out_mux6 <= data_reg1(7 downto 0);
      when "111" => data_out_mux6 <= data_reg0(63 downto 56);
      when others => data_out_mux6 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux7 -----------------------------------------------
data_out_mux7p: process(align_reg, data_reg1, data_reg0)
begin
   case align_reg is
      when "000" => data_out_mux7 <= data_reg1(63 downto 56);
      when "001" => data_out_mux7 <= data_reg1(55 downto 48);
      when "010" => data_out_mux7 <= data_reg1(47 downto 40);
      when "011" => data_out_mux7 <= data_reg1(39 downto 32);
      when "100" => data_out_mux7 <= data_reg1(31 downto 24);
      when "101" => data_out_mux7 <= data_reg1(23 downto 16);
      when "110" => data_out_mux7 <= data_reg1(15 downto 8);
      when "111" => data_out_mux7 <= data_reg1(7 downto 0);
      when others => data_out_mux7 <= (others => 'X');
   end case;
end process;


end architecture IB_ENDPOINT_WRITE_ALIGN_ARCH;

