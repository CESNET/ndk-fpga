--
-- write_align.vhd: Internal Bus Shift Register
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
use work.ib_pkg.all; -- Internal Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity WRITE_ALIGN is
   port(
      -- Common Interface
      CLK             : in  std_logic;
      RESET           : in  std_logic;

      -- Input Interface
      DATA_IN         : in  std_logic_vector(63 downto 0);
      DATA_IN_VLD     : in  std_logic;
      EOP             : in  std_logic;
      ALIGN_REG       : in  std_logic_vector(2 downto 0);
      ALIGN_INIT      : in  std_logic;
      LENGTH          : in  std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);

      --Output Interface
      DWR             : out std_logic_vector(63 downto 0);
      BE_WR           : out std_logic_vector(7 downto 0);
      EOP_WR          : out std_logic;
      WR              : out std_logic
      );
end entity WRITE_ALIGN;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture WRITE_ALIGN_ARCH of WRITE_ALIGN is

   signal data_reg0      : std_logic_vector(63 downto 0);
   signal data_reg1      : std_logic_vector(63 downto 0);
   signal data_reg_we    : std_logic;
   signal be_reg1        : std_logic_vector(7 downto 0);
   signal be_reg0        : std_logic_vector(7 downto 0);
   signal be_reg_we      : std_logic;
   signal be_decoder     : std_logic_vector(7 downto 0);

   signal data_out_mux0  : std_logic_vector(7 downto 0);
   signal data_out_mux1  : std_logic_vector(7 downto 0);
   signal data_out_mux2  : std_logic_vector(7 downto 0);
   signal data_out_mux3  : std_logic_vector(7 downto 0);
   signal data_out_mux4  : std_logic_vector(7 downto 0);
   signal data_out_mux5  : std_logic_vector(7 downto 0);
   signal data_out_mux6  : std_logic_vector(7 downto 0);
   signal data_out_mux7  : std_logic_vector(7 downto 0);
   signal be_out_mux0    : std_logic;
   signal be_out_mux1    : std_logic;
   signal be_out_mux2    : std_logic;
   signal be_out_mux3    : std_logic;
   signal be_out_mux4    : std_logic;
   signal be_out_mux5    : std_logic;
   signal be_out_mux6    : std_logic;
   signal be_out_mux7    : std_logic;
   signal writen_len       : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
   signal write_lenght_reg : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
   signal actual_lenght_reg : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
   signal write_last       : std_logic;
   signal eop_reg          : std_logic;
   signal be7_reg          : std_logic;
   signal be_out           : std_logic_vector(7 downto 0);
   signal be_writen_len    : std_logic_vector(3 downto 0);

begin
WR              <= (write_last or DATA_IN_VLD);

DWR             <= data_out_mux7 & data_out_mux6 & data_out_mux5 &
                   data_out_mux4 & data_out_mux3 & data_out_mux2 &
                   data_out_mux1 & data_out_mux0;

BE_WR           <= be_out_mux7 & be_out_mux6 & be_out_mux5 &
                   be_out_mux4 & be_out_mux3 & be_out_mux2 &
                   be_out_mux1 & be_out_mux0;

be_out          <= be_out_mux7 & be_out_mux6 & be_out_mux5 &
                   be_out_mux4 & be_out_mux3 & be_out_mux2 &
                   be_out_mux1 & be_out_mux0;

EOP_WR          <= '1' when (actual_lenght_reg - be_writen_len) = 0 else '0';


data_reg1       <= DATA_IN;
be_reg1         <= be_decoder;
data_reg_we     <= DATA_IN_VLD;
be_reg_we       <= DATA_IN_VLD;


-- register write_lenght_reg --------------------------------------------------
write_lenght_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      write_lenght_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (ALIGN_INIT = '1') then
         write_lenght_reg <= LENGTH;
      end if;
      if (write_last='1' or DATA_IN_VLD='1') then
        write_lenght_reg <= write_lenght_reg - writen_len;
      end if;
   end if;
end process;


-- -------------------------------------------------------------------------
--                            BE DECODER
-- -------------------------------------------------------------------------

-- -------------------------------------------------------------------------
be_writen_lenp: process(be_out)
  variable aux_count : std_logic_vector(3 downto 0);
begin
  aux_count := "0000";
  for i in 0 to 7 loop
     if (be_out(i) = '1') then
       aux_count := aux_count + 1;
     end if;
  end loop;
  be_writen_len <= aux_count;
end process;

-- register actual_lenght_reg ----------------------------------------------
actual_lenght_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      actual_lenght_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (ALIGN_INIT = '1') then
         actual_lenght_reg <= LENGTH;
      end if;
      if (write_last='1' or DATA_IN_VLD='1') then
        actual_lenght_reg <= actual_lenght_reg - be_writen_len;
      end if;
   end if;
end process;


-- be decoder --------------------------------------------------------------
be_decoderp: process(write_lenght_reg)
begin
   case write_lenght_reg is
      when "000000000000" => be_decoder <= "00000000";
      when "000000000001" => be_decoder <= "00000001";
      when "000000000010" => be_decoder <= "00000011";
      when "000000000011" => be_decoder <= "00000111";
      when "000000000100" => be_decoder <= "00001111";
      when "000000000101" => be_decoder <= "00011111";
      when "000000000110" => be_decoder <= "00111111";
      when "000000000111" => be_decoder <= "01111111";
      when others => be_decoder <= "11111111";
   end case;
end process;

-- -------------------------------------------------------------------------
--                            WRITEN_LEN
-- -------------------------------------------------------------------------

-- len_decoder -------------------------------------------------------------
len_decoderp: process(be_decoder)
begin
   case be_decoder is
      when "00000000" => writen_len <= "000000000000";
      when "00000001" => writen_len <= "000000000001";
      when "00000011" => writen_len <= "000000000010";
      when "00000111" => writen_len <= "000000000011";
      when "00001111" => writen_len <= "000000000100";
      when "00011111" => writen_len <= "000000000101";
      when "00111111" => writen_len <= "000000000110";
      when "01111111" => writen_len <= "000000000111";
      when "11111111" => writen_len <= "000000001000";
      when others => writen_len     <= "XXXXXXXXXXXX";
   end case;
end process;


-- -------------------------------------------------------------------------
--                       WRITE ENABLE GENERATION
-- -------------------------------------------------------------------------

-- register data_reg1 ------------------------------------------------------
eop_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      eop_reg <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (data_reg_we = '1') then
        eop_reg <= EOP;
      end if;
      if ( (write_last = '1') or ALIGN_INIT = '1') then
         eop_reg <= '0';
      end if;
   end if;
end process;


-- Used for last we generation(not generate when be7=0)
write_last <= '1' when eop_reg = '1' and actual_lenght_reg /= 0 else '0';


-- -------------------------------------------------------------------------
--                           ALIGN REGISTERS
-- -------------------------------------------------------------------------

-- register data_reg0 ------------------------------------------------------
data_reg0p: process(RESET, CLK)
begin
   if (RESET = '1') then
      data_reg0 <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (data_reg_we = '1') then
         data_reg0 <= data_reg1;
      end if;
      if (ALIGN_INIT = '1') then
         data_reg0 <= (others => '0');
      end if;
   end if;
end process;

-- register be_reg0 ------------------------------------------------------
be_reg0p: process(RESET, CLK)
begin
   if (RESET = '1') then
      be_reg0 <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (be_reg_we = '1') then
         be_reg0 <= be_reg1;
      end if;
      if (ALIGN_INIT = '1') then
         be_reg0 <= (others => '0');
      end if;
   end if;
end process;


-- -------------------------------------------------------------------------
--                         DATA ALIGN MULTIPLEXORS
-- -------------------------------------------------------------------------

-- multiplexor data_out_mux0 -----------------------------------------------
data_out_mux0p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux1p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux2p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux3p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux4p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux5p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux6p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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
data_out_mux7p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
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

-- -------------------------------------------------------------------------
--                             BE MULTIPLEXORS
-- -------------------------------------------------------------------------


-- multiplexor be_out_mux0 -------------------------------------------------
be_out_mux0p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux0 <= be_reg1(0);
      when "001" => be_out_mux0 <= be_reg0(7);
      when "010" => be_out_mux0 <= be_reg0(6);
      when "011" => be_out_mux0 <= be_reg0(5);
      when "100" => be_out_mux0 <= be_reg0(4);
      when "101" => be_out_mux0 <= be_reg0(3);
      when "110" => be_out_mux0 <= be_reg0(2);
      when "111" => be_out_mux0 <= be_reg0(1);
      when others => be_out_mux0 <= '0';
   end case;
end process;

-- multiplexor be_out_mux1 -------------------------------------------------
be_out_mux1p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux1 <= be_reg1(1);
      when "001" => be_out_mux1 <= be_reg1(0);
      when "010" => be_out_mux1 <= be_reg0(7);
      when "011" => be_out_mux1 <= be_reg0(6);
      when "100" => be_out_mux1 <= be_reg0(5);
      when "101" => be_out_mux1 <= be_reg0(4);
      when "110" => be_out_mux1 <= be_reg0(3);
      when "111" => be_out_mux1 <= be_reg0(2);
      when others => be_out_mux1 <= '0';
   end case;
end process;

-- multiplexor be_out_mux2 -------------------------------------------------
be_out_mux2p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux2 <= be_reg1(2);
      when "001" => be_out_mux2 <= be_reg1(1);
      when "010" => be_out_mux2 <= be_reg1(0);
      when "011" => be_out_mux2 <= be_reg0(7);
      when "100" => be_out_mux2 <= be_reg0(6);
      when "101" => be_out_mux2 <= be_reg0(5);
      when "110" => be_out_mux2 <= be_reg0(4);
      when "111" => be_out_mux2 <= be_reg0(3);
      when others => be_out_mux2 <= '0';
   end case;
end process;

-- multiplexor be_out_mux3 -------------------------------------------------
be_out_mux3p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux3 <= be_reg1(3);
      when "001" => be_out_mux3 <= be_reg1(2);
      when "010" => be_out_mux3 <= be_reg1(1);
      when "011" => be_out_mux3 <= be_reg1(0);
      when "100" => be_out_mux3 <= be_reg0(7);
      when "101" => be_out_mux3 <= be_reg0(6);
      when "110" => be_out_mux3 <= be_reg0(5);
      when "111" => be_out_mux3 <= be_reg0(4);
      when others => be_out_mux3 <= '0';
   end case;
end process;

-- multiplexor be_out_mux4 -------------------------------------------------
be_out_mux4p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux4 <= be_reg1(4);
      when "001" => be_out_mux4 <= be_reg1(3);
      when "010" => be_out_mux4 <= be_reg1(2);
      when "011" => be_out_mux4 <= be_reg1(1);
      when "100" => be_out_mux4 <= be_reg1(0);
      when "101" => be_out_mux4 <= be_reg0(7);
      when "110" => be_out_mux4 <= be_reg0(6);
      when "111" => be_out_mux4 <= be_reg0(5);
      when others => be_out_mux4 <= '0';
   end case;
end process;

-- multiplexor be_out_mux5 -------------------------------------------------
be_out_mux5p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux5 <= be_reg1(5);
      when "001" => be_out_mux5 <= be_reg1(4);
      when "010" => be_out_mux5 <= be_reg1(3);
      when "011" => be_out_mux5 <= be_reg1(2);
      when "100" => be_out_mux5 <= be_reg1(1);
      when "101" => be_out_mux5 <= be_reg1(0);
      when "110" => be_out_mux5 <= be_reg0(7);
      when "111" => be_out_mux5 <= be_reg0(6);
      when others => be_out_mux5 <= '0';
   end case;
end process;

-- multiplexor be_out_mux6 -------------------------------------------------
be_out_mux6p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux6 <= be_reg1(6);
      when "001" => be_out_mux6 <= be_reg1(5);
      when "010" => be_out_mux6 <= be_reg1(4);
      when "011" => be_out_mux6 <= be_reg1(3);
      when "100" => be_out_mux6 <= be_reg1(2);
      when "101" => be_out_mux6 <= be_reg1(1);
      when "110" => be_out_mux6 <= be_reg1(0);
      when "111" => be_out_mux6 <= be_reg0(7);
      when others => be_out_mux6 <= '0';
   end case;
end process;

-- multiplexor be_out_mux7 -------------------------------------------------
be_out_mux7p: process(ALIGN_REG, be_reg1, be_reg0)
begin
   case ALIGN_REG is
      when "000" => be_out_mux7 <= be_reg1(7);
      when "001" => be_out_mux7 <= be_reg1(6);
      when "010" => be_out_mux7 <= be_reg1(5);
      when "011" => be_out_mux7 <= be_reg1(4);
      when "100" => be_out_mux7 <= be_reg1(3);
      when "101" => be_out_mux7 <= be_reg1(2);
      when "110" => be_out_mux7 <= be_reg1(1);
      when "111" => be_out_mux7 <= be_reg0(0);
      when others => be_out_mux7 <= '0';
   end case;
end process;

end architecture WRITE_ALIGN_ARCH;

