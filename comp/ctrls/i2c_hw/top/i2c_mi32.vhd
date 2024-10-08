--
-- I2C_HW.vhd: HW interface for I2C Protocol, MI32 interface
-- Copyright (C) 2009 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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

use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity I2C_HW_MI32 is
   generic (
      -- Number od controllers, max 8
      IFC_CNT   : integer := 4;
      -- 125MHz CLK ~ 100KHz SCL
      PRER_INIT : unsigned(15 downto 0) := X"00F9";
      -- Tristate SCK (enable clock stretching)
      SCL_TRISTATE : boolean := false
   );
   port(
      -- ==============
      -- CLK and RST
      -- ==============

      CLK       : in  std_logic;
      RESET     : in  std_logic;

      -- ==============
      -- I2C interfaces
      -- ==============

      -- I2C clock input
      SCL_I     : in  std_logic_vector(IFC_CNT-1 downto 0);
      -- I2C data input
      SDA_I     : in  std_logic_vector(IFC_CNT-1 downto 0);
      -- I2C clock output
      SCL_O     : out std_logic_vector(IFC_CNT-1 downto 0);
      -- I2C data output
      SDA_O     : out std_logic_vector(IFC_CNT-1 downto 0);
      -- I2C clock output enable, active low
      SCL_OEN   : out std_logic_vector(IFC_CNT-1 downto 0);
      -- I2C data output enable, active low
      SDA_OEN   : out std_logic_vector(IFC_CNT-1 downto 0);

      -- ==============
      -- MI32 interface
      -- ==============

      -- Input Data
      MI32_DWR  :  in std_logic_vector(31 downto 0);
      -- Address
      MI32_ADDR :  in std_logic_vector(31 downto 0);
      -- Read Request
      MI32_RD   :  in std_logic;
      -- Write Request
      MI32_WR   :  in std_logic;
      -- Byte Enable
      MI32_BE   :  in std_logic_vector(3  downto 0);
      -- Output Data
      MI32_DRD  : out std_logic_vector(31 downto 0);
      -- Address Ready
      MI32_ARDY : out std_logic;
      -- Data Ready
      MI32_DRDY : out std_logic
   );
end entity I2C_HW_MI32;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of I2C_HW_MI32 is

signal i2c_dwr     : std_logic_vector(63 downto 0);
signal i2c_be      : std_logic_vector( 7 downto 0);
signal i2c_wen     : std_logic_vector(IFC_CNT-1 downto 0);
signal i2c_drd     : std_logic_vector(64*(IFC_CNT-1)+63 downto 0);
signal rst_sync    : std_logic;
signal addr_index  : integer := 0;
signal sig_scl_o   : std_logic_vector(IFC_CNT-1 downto 0);
signal sig_scl_oen : std_logic_vector(IFC_CNT-1 downto 0);

begin

addr_index <= conv_integer(MI32_ADDR(log2(IFC_CNT)+2 downto 3));

i2c_dwr   <= MI32_DWR & MI32_DWR;
i2c_be    <= "0000" & MI32_BE when MI32_ADDR(2) = '0' else MI32_BE & "0000";
MI32_ARDY <= MI32_RD or MI32_WR;

GEN_I2C_WEN: process(addr_index, MI32_WR)
begin
   i2c_wen             <= (others => '0');
   i2c_wen(addr_index) <= MI32_WR;
end process;

-- DRD_MX_REG: process(CLK)
-- begin
--    if CLK'event and CLK = '1' then
--       if MI32_ADDR(2) = '0' then
--          MI32_DRD <= i2c_drd(64*addr_index+31 downto 64*addr_index);
--       else
--          MI32_DRD <= i2c_drd(64*addr_index+63 downto 64*addr_index+32);
--       end if;
--       MI32_DRDY <= MI32_RD;
--    end if;
-- end process;
   MI32_DRD  <= i2c_drd(64*addr_index+31 downto 64*addr_index)
                when (MI32_ADDR(2) = '0') else
                i2c_drd(64*addr_index+63 downto 64*addr_index+32);
   MI32_DRDY <= MI32_RD;

GEN_CTRL: for i in 0 to IFC_CNT-1 generate

   I2C_HW_CTRL: entity work.i2c_master_top
   generic map (
      PRER_INIT => PRER_INIT
   )
   port map (
      CLK       => CLK,
      RST_SYNC  => rst_sync,
      RST_ASYNC => rst_sync,
      -- generic bus
      BE        => i2c_be,
      DWR       => i2c_dwr,
      DRD       => i2c_drd(64*i+63 downto 64*i),
      WEN       => i2c_wen(i),
      INT       => open,
      -- i2c lines
      SCL_PAD_I    => SCL_I(i),   -- i2c clock line input
      SCL_PAD_O    => sig_scl_o(i),   -- i2c clock line output
      SCL_PADOEN_O => sig_scl_oen(i), -- i2c clock line output enable, active low
      SDA_PAD_I    => SDA_I(i),   -- i2c data line input
      SDA_PAD_O    => SDA_O(i),   -- i2c data line output
      SDA_PADOEN_O => SDA_OEN(i)  -- i2c data line output enable, active low
   );

   TRISTATE: if (SCL_TRISTATE) generate
      SCL_O(i) <= sig_scl_o(i);
      SCL_OEN(i) <= sig_scl_oen(i);
   end generate;

   NO_TRISTATE: if (not SCL_TRISTATE) generate
      SCL_OEN(i) <= '0';
      SCL_O(i) <= sig_scl_o(i) when sig_scl_oen(i) = '0' else '1';
   end generate;

end generate;

reset_async_i: entity work.ASYNC_RESET
generic map(
   TWO_REG => false --! For two reg = true, for three reg = false
)
port map(
   CLK        => CLK,
   ASYNC_RST  => RESET,
   OUT_RST(0) => rst_sync
);

end architecture behavioral;
