-- sp_rom_behav.vhd: Single Port ROM (Behavioral)
-- Copyright (C) 2024 CESNET
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity SP_ROM_BEHAV is
   Generic (
      -- Data word width in bits.
      DATA_WIDTH  : integer := 32;
      -- Depth of the ROM in number of data words.
      -- Max 2**31
      ITEMS       : integer := 512;
      -- Register the input address or through a register.
      ADDRESS_REG : boolean := True;
      -- Output directly from BRAM or through a register.
      OUTPUT_REG  : boolean := True;
      -- Array of values to initialize the ROM.
      ROM_DATA    : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0) := (others => (others => '0'))
   );
   Port (
      -- Clock
      CLK     : in  std_logic;
      -- Read enable, only for generation DO_DV
      RD_EN   : in  std_logic := '1';
      -- Input Address
      ADDR    : in  std_logic_vector(log2(ITEMS)-1 downto 0);
      -- Data out
      DO      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Data out valid
      DO_DV   : out std_logic
   );
end SP_ROM_BEHAV;

architecture behavioral of SP_ROM_BEHAV is

   type rom_t is array(ITEMS-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);

   function rom_init (init_arr : slv_array_t) return rom_t is
      variable ret : rom_t := (others => (others => '0'));
   begin
      for i in 0 to ITEMS-1 loop
         ret(i) := init_arr(init_arr'low+i);
      end loop;
      return ret;
   end function;

   signal rom     : rom_t := rom_init(ROM_DATA);
   signal address : natural;
   signal rd_ena  : std_logic;

   attribute ram_style : string; -- for Vivado
   attribute ram_style of rom : signal is "block";
   attribute ramstyle  : string; -- for Quartus
   attribute ramstyle  of rom : signal is "M20K";

begin

   input_reg_g : if (ADDRESS_REG) generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            address <= to_integer(unsigned(ADDR));
            rd_ena  <= RD_EN;
         end if;
      end process;
   else generate
      address <= to_integer(unsigned(ADDR));
      rd_ena  <= RD_EN;
   end generate;

   output_reg_g : if (OUTPUT_REG) generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            DO    <= rom(address);
            DO_DV <= rd_ena;
         end if;
      end process;
   else generate
      DO    <= rom(address);
      DO_DV <= rd_ena;
   end generate;

end behavioral;
