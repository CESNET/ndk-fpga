--
-- lb_endpoint_read_align.vhd: Internal Bus Shift Register
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
entity IB_ENDPOINT_READ_ALIGN is
   port(
      -- Common Interface
      CLK             : in  std_logic;
      RESET           : in  std_logic;
      -- RD_DATA_IN Interface
      RD_DATA_IN      : in  std_logic_vector(63 downto 0);
      RD_SRC_RDY_IN   : in  std_logic;
      RD_DST_RDY_IN   : out std_logic;
      -- Internal Bus Interface
      RD_DATA_OUT     : out std_logic_vector(63 downto 0);
      RD_SRC_RDY_OUT  : out std_logic;
      RD_DST_RDY_OUT  : in  std_logic;
      RD_EOF          : out std_logic;
      -- Align Control Interface
      SLAVE_INIT      : in  std_logic;
      SLAVE_LENGTH    : in  std_logic_vector(11 downto 0);
      SLAVE_ALIGN     : in  std_logic_vector(2 downto 0);
      MASTER_INIT     : in  std_logic;
      MASTER_LENGTH   : in  std_logic_vector(11 downto 0);
      MASTER_ALIGN    : in  std_logic_vector(2 downto 0);
      ALIGN_REG       : in  std_logic_vector(2 downto 0)
      );
end entity IB_ENDPOINT_READ_ALIGN;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_READ_ALIGN_ARCH of IB_ENDPOINT_READ_ALIGN is

   -- Data register signals
   signal data_reg0               : std_logic_vector(63 downto 0);
   signal data_reg1               : std_logic_vector(63 downto 0);
   signal data_reg0_vld           : std_logic;
   signal data_reg_we             : std_logic;

   -- Align multiplexors
   signal data_out_mux0           : std_logic_vector(7 downto 0);
   signal data_out_mux1           : std_logic_vector(7 downto 0);
   signal data_out_mux2           : std_logic_vector(7 downto 0);
   signal data_out_mux3           : std_logic_vector(7 downto 0);
   signal data_out_mux4           : std_logic_vector(7 downto 0);
   signal data_out_mux5           : std_logic_vector(7 downto 0);
   signal data_out_mux6           : std_logic_vector(7 downto 0);
   signal data_out_mux7           : std_logic_vector(7 downto 0);

   -- Read Counter
   signal length_reg_one          : std_logic;
   signal length_reg_one_dec      : std_logic;
   signal length_reg              : std_logic_vector(C_IB_LENGTH_WIDTH-4 downto 0);
   signal length_reg_dec          : std_logic;
   signal write_last              : std_logic;
   signal length_reg_mux          : std_logic_vector(C_IB_LENGTH_WIDTH-4 downto 0);
   signal length_reg_one_mux      : std_logic;
   signal slave_length_one        : std_logic;
   signal master_length_one       : std_logic;

   signal must_src_rdy            : std_logic;
   signal must_src_rdy_slave      : std_logic;
   signal must_src_rdy_master     : std_logic;
   signal slave_dec_in            : std_logic_vector(5 downto 0);
   signal master_dec_in           : std_logic_vector(5 downto 0);

begin

RD_DATA_OUT          <= data_out_mux7 & data_out_mux6 & data_out_mux5 &
                        data_out_mux4 & data_out_mux3 & data_out_mux2 &
                        data_out_mux1 & data_out_mux0;

RD_SRC_RDY_OUT       <= (RD_SRC_RDY_IN or write_last) and data_reg0_vld and ((must_src_rdy and RD_SRC_RDY_IN)or not must_src_rdy) ;
RD_EOF               <= (write_last and data_reg0_vld and must_src_rdy and RD_SRC_RDY_IN)
                        or (write_last and data_reg0_vld and not must_src_rdy);

RD_DST_RDY_IN        <= RD_DST_RDY_OUT or not data_reg0_vld;
data_reg_we          <= (RD_DST_RDY_OUT and RD_SRC_RDY_IN) or (not data_reg0_vld and RD_SRC_RDY_IN);
data_reg1            <= RD_DATA_IN;


-- -------------------------------------------------------------------------
--                         LEN WRITE COUNTER
-- -------------------------------------------------------------------------


--must_src_rdy_slave  <= '1' when (SLAVE_ALIGN >= ((SLAVE_LENGTH(2 downto 0)+SLAVE_ALIGN))) and ((SLAVE_LENGTH(2 downto 0)+SLAVE_ALIGN)/="000")
--                      else '0';

--must_src_rdy_master <= '1' when (MASTER_ALIGN >= ((MASTER_LENGTH(2 downto 0)+MASTER_ALIGN))) and ((MASTER_LENGTH(2 downto 0)+MASTER_ALIGN)/="000")
--                      else '0';

slave_dec_in  <= SLAVE_ALIGN & SLAVE_LENGTH(2 downto 0);
master_dec_in <= MASTER_ALIGN & MASTER_LENGTH(2 downto 0);

-- last word must src rdy master ----------------------------------------
must_src_rdy_master_decp: process(master_dec_in)
begin
   case master_dec_in is
     when "001000"  => must_src_rdy_master <= '1';
     when "010000"  => must_src_rdy_master <= '1';
     when "010111"  => must_src_rdy_master <= '1';
     when "011000"  => must_src_rdy_master <= '1';
     when "011110"  => must_src_rdy_master <= '1';
     when "011111"  => must_src_rdy_master <= '1';
     when "100000"  => must_src_rdy_master <= '1';
     when "100101"  => must_src_rdy_master <= '1';
     when "100110"  => must_src_rdy_master <= '1';
     when "100111"  => must_src_rdy_master <= '1';
     when "101000"  => must_src_rdy_master <= '1';
     when "101100"  => must_src_rdy_master <= '1';
     when "101101"  => must_src_rdy_master <= '1';
     when "101110"  => must_src_rdy_master <= '1';
     when "101111"  => must_src_rdy_master <= '1';
     when "110000"  => must_src_rdy_master <= '1';
     when "110011"  => must_src_rdy_master <= '1';
     when "110100"  => must_src_rdy_master <= '1';
     when "110101"  => must_src_rdy_master <= '1';
     when "110110"  => must_src_rdy_master <= '1';
     when "110111"  => must_src_rdy_master <= '1';
     when "111000"  => must_src_rdy_master <= '1';
     when "111010"  => must_src_rdy_master <= '1';
     when "111011"  => must_src_rdy_master <= '1';
     when "111100"  => must_src_rdy_master <= '1';
     when "111101"  => must_src_rdy_master <= '1';
     when "111110"  => must_src_rdy_master <= '1';
     when "111111"  => must_src_rdy_master <= '1';
     when others    => must_src_rdy_master <= '0';
   end case;
end process;

-- last word must src rdy slave  ----------------------------------------
must_src_rdy_slave_decp: process(slave_dec_in)
begin
   case slave_dec_in is
     when "001000"  => must_src_rdy_slave <= '1';
     when "010000"  => must_src_rdy_slave <= '1';
     when "010111"  => must_src_rdy_slave <= '1';
     when "011000"  => must_src_rdy_slave <= '1';
     when "011110"  => must_src_rdy_slave <= '1';
     when "011111"  => must_src_rdy_slave <= '1';
     when "100000"  => must_src_rdy_slave <= '1';
     when "100101"  => must_src_rdy_slave <= '1';
     when "100110"  => must_src_rdy_slave <= '1';
     when "100111"  => must_src_rdy_slave <= '1';
     when "101000"  => must_src_rdy_slave <= '1';
     when "101100"  => must_src_rdy_slave <= '1';
     when "101101"  => must_src_rdy_slave <= '1';
     when "101110"  => must_src_rdy_slave <= '1';
     when "101111"  => must_src_rdy_slave <= '1';
     when "110000"  => must_src_rdy_slave <= '1';
     when "110011"  => must_src_rdy_slave <= '1';
     when "110100"  => must_src_rdy_slave <= '1';
     when "110101"  => must_src_rdy_slave <= '1';
     when "110110"  => must_src_rdy_slave <= '1';
     when "110111"  => must_src_rdy_slave <= '1';
     when "111000"  => must_src_rdy_slave <= '1';
     when "111010"  => must_src_rdy_slave <= '1';
     when "111011"  => must_src_rdy_slave <= '1';
     when "111100"  => must_src_rdy_slave <= '1';
     when "111101"  => must_src_rdy_slave <= '1';
     when "111110"  => must_src_rdy_slave <= '1';
     when "111111"  => must_src_rdy_slave <= '1';
     when others    => must_src_rdy_slave <= '0';
   end case;
end process;


-- register must_src_rdy ---------------------------------------------------
must_src_rdyp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if ( SLAVE_INIT = '1') then
      must_src_rdy  <= must_src_rdy_slave;
    end if;
    if ( MASTER_INIT = '1' ) then
      must_src_rdy <= must_src_rdy_master;
    end if;
  end if;
end process;

write_last <= '1' when ( (length_reg = 1 and length_reg_one = '0') or
                         (length_reg = 0 and length_reg_one = '1')
                       ) else '0';


-- multiplexor length_mux --------------------------------------------------------------
length_muxp: process(MASTER_INIT, SLAVE_LENGTH, MASTER_LENGTH)
begin
   case MASTER_INIT is
      when '0'    => length_reg_mux <= SLAVE_LENGTH(11 downto 3);
      when '1'    => length_reg_mux <= MASTER_LENGTH(11 downto 3);
      when others => length_reg_mux <= (others => 'X');
   end case;
end process;

slave_length_one  <= SLAVE_LENGTH(2)  or SLAVE_LENGTH(1)  or SLAVE_LENGTH(0);
master_length_one <= MASTER_LENGTH(2) or MASTER_LENGTH(1) or MASTER_LENGTH(0);
-- multiplexor length_reg_one_mux -----------------------------------------------------
length_reg_one_muxp: process(MASTER_INIT, slave_length_one, master_length_one)
begin
   case MASTER_INIT is
      when '0'    => length_reg_one_mux <= slave_length_one;
      when '1'    => length_reg_one_mux <= master_length_one;
      when others => length_reg_one_mux <= 'X';
   end case;
end process;


length_reg_dec     <= '1' when ( (RD_DST_RDY_OUT='1' and data_reg0_vld ='1') and RD_SRC_RDY_IN ='1' and length_reg_one = '0') else '0';
length_reg_one_dec <= '1' when ( (RD_DST_RDY_OUT='1' and data_reg0_vld ='1') and RD_SRC_RDY_IN ='1' and length_reg_one = '1') else '0';
-- register length_reg --------------------------------------------------------
-- No of data items to send out
length_regp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (SLAVE_INIT = '1' or MASTER_INIT = '1') then
      length_reg       <= length_reg_mux;
      length_reg_one   <= length_reg_one_mux;
    end if;
    if (length_reg_dec = '1') then
      length_reg <= length_reg - 1;
    end if;
    if (length_reg_one_dec = '1') then
      length_reg_one <= not length_reg_one;
    end if;
  end if;
end process;
-- -------------------------------------------------------------------------
--                           ALIGN REGISTERS
-- -------------------------------------------------------------------------
-- register data_reg0_vld --------------------------------------------------
-- Register 0 must be loaded before first data_vld is generated
data_reg0_vldp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (data_reg_we = '1') then
      data_reg0_vld <= '1';
    end if;
    if (RESET = '1') or (write_last = '1' and RD_DST_RDY_OUT = '1' and ((RD_SRC_RDY_IN='1' and must_src_rdy='1') or must_src_rdy='0')) then
      data_reg0_vld <= '0';
    end if;
  end if;
end process;

-- register data_reg0 ------------------------------------------------------
data_reg0p: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
    if (data_reg_we = '1') then
      data_reg0 <= data_reg1;
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
      when "000" => data_out_mux0 <= data_reg0(7 downto 0);
      when "001" => data_out_mux0 <= data_reg0(15 downto 8);
      when "010" => data_out_mux0 <= data_reg0(23 downto 16);
      when "011" => data_out_mux0 <= data_reg0(31 downto 24);
      when "100" => data_out_mux0 <= data_reg0(39 downto 32);
      when "101" => data_out_mux0 <= data_reg0(47 downto 40);
      when "110" => data_out_mux0 <= data_reg0(55 downto 48);
      when "111" => data_out_mux0 <= data_reg0(63 downto 56);
      when others => data_out_mux0 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux1 -----------------------------------------------
data_out_mux1p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux1 <= data_reg0(15 downto 8);
      when "001" => data_out_mux1 <= data_reg0(23 downto 16);
      when "010" => data_out_mux1 <= data_reg0(31 downto 24);
      when "011" => data_out_mux1 <= data_reg0(39 downto 32);
      when "100" => data_out_mux1 <= data_reg0(47 downto 40);
      when "101" => data_out_mux1 <= data_reg0(55 downto 48);
      when "110" => data_out_mux1 <= data_reg0(63 downto 56);
      when "111" => data_out_mux1 <= data_reg1(7 downto 0);
      when others => data_out_mux1 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux2 -----------------------------------------------
data_out_mux2p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux2 <= data_reg0(23 downto 16);
      when "001" => data_out_mux2 <= data_reg0(31 downto 24);
      when "010" => data_out_mux2 <= data_reg0(39 downto 32);
      when "011" => data_out_mux2 <= data_reg0(47 downto 40);
      when "100" => data_out_mux2 <= data_reg0(55 downto 48);
      when "101" => data_out_mux2 <= data_reg0(63 downto 56);
      when "110" => data_out_mux2 <= data_reg1(7 downto 0);
      when "111" => data_out_mux2 <= data_reg1(15 downto 8);
      when others => data_out_mux2 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux3 -----------------------------------------------
data_out_mux3p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux3 <= data_reg0(31 downto 24);
      when "001" => data_out_mux3 <= data_reg0(39 downto 32);
      when "010" => data_out_mux3 <= data_reg0(47 downto 40);
      when "011" => data_out_mux3 <= data_reg0(55 downto 48);
      when "100" => data_out_mux3 <= data_reg0(63 downto 56);
      when "101" => data_out_mux3 <= data_reg1(7 downto 0);
      when "110" => data_out_mux3 <= data_reg1(15 downto 8);
      when "111" => data_out_mux3 <= data_reg1(23 downto 16);
      when others => data_out_mux3 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux4 -----------------------------------------------
data_out_mux4p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux4 <= data_reg0(39 downto 32);
      when "001" => data_out_mux4 <= data_reg0(47 downto 40);
      when "010" => data_out_mux4 <= data_reg0(55 downto 48);
      when "011" => data_out_mux4 <= data_reg0(63 downto 56);
      when "100" => data_out_mux4 <= data_reg1(7 downto 0);
      when "101" => data_out_mux4 <= data_reg1(15 downto 8);
      when "110" => data_out_mux4 <= data_reg1(23 downto 16);
      when "111" => data_out_mux4 <= data_reg1(31 downto 24);
      when others => data_out_mux4 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux5 -----------------------------------------------
data_out_mux5p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux5 <= data_reg0(47 downto 40);
      when "001" => data_out_mux5 <= data_reg0(55 downto 48);
      when "010" => data_out_mux5 <= data_reg0(63 downto 56);
      when "011" => data_out_mux5 <= data_reg1(7 downto 0);
      when "100" => data_out_mux5 <= data_reg1(15 downto 8);
      when "101" => data_out_mux5 <= data_reg1(23 downto 16);
      when "110" => data_out_mux5 <= data_reg1(31 downto 24);
      when "111" => data_out_mux5 <= data_reg1(39 downto 32);
      when others => data_out_mux5 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux6 -----------------------------------------------
data_out_mux6p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux6 <= data_reg0(55 downto 48);
      when "001" => data_out_mux6 <= data_reg0(63 downto 56);
      when "010" => data_out_mux6 <= data_reg1(7 downto 0);
      when "011" => data_out_mux6 <= data_reg1(15 downto 8);
      when "100" => data_out_mux6 <= data_reg1(23 downto 16);
      when "101" => data_out_mux6 <= data_reg1(31 downto 24);
      when "110" => data_out_mux6 <= data_reg1(39 downto 32);
      when "111" => data_out_mux6 <= data_reg1(47 downto 40);
      when others => data_out_mux6 <= (others => 'X');
   end case;
end process;

-- multiplexor data_out_mux7 -----------------------------------------------
data_out_mux7p: process(ALIGN_REG, data_reg1, data_reg0)
begin
   case ALIGN_REG is
      when "000" => data_out_mux7 <= data_reg0(63 downto 56);
      when "001" => data_out_mux7 <= data_reg1(7 downto 0);
      when "010" => data_out_mux7 <= data_reg1(15 downto 8);
      when "011" => data_out_mux7 <= data_reg1(23 downto 16);
      when "100" => data_out_mux7 <= data_reg1(31 downto 24);
      when "101" => data_out_mux7 <= data_reg1(39 downto 32);
      when "110" => data_out_mux7 <= data_reg1(47 downto 40);
      when "111" => data_out_mux7 <= data_reg1(55 downto 48);
      when others => data_out_mux7 <= (others => 'X');
   end case;
end process;

end architecture IB_ENDPOINT_READ_ALIGN_ARCH;

