-- sp_bram_behav.vhd: Single Port Block RAM (Behavioral)
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity SP_BRAM_BEHAV is
   Generic (
      -- Data word width in bits.
      DATA_WIDTH : integer := 32;
      -- Depth of BRAM in number of the data words.
      ITEMS      : integer := 512;
      -- Output directly from BRAM or throw register (better timing).
      OUTPUT_REG : boolean := True;
      -- What operation will be performed first when write and read are active
      -- in same time and same port? Possible values are:
      -- "READ_FIRST"  - Default mode, works on Xilinx and Intel FPGAs.
      -- "WRITE_FIRST" - This mode is not fully supported on Intel FPGAs,
      --               - RAM requires extra logic and PIPE_EN must be set to '1'
      --               - else RAM will be implemented into logic on Intel FPGAs!
      RDW_MODE   : string := "READ_FIRST"
   );
   Port (
      CLK     : in  std_logic; -- Clock
      RST     : in  std_logic; -- Reset
      PIPE_EN : in  std_logic; -- Enable of BRAM port and output registers
      RE      : in  std_logic; -- Read enable, only for generation DO_DV
      WE      : in  std_logic; -- Write enable
      ADDR    : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Address
      DI      : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Data in
      DO      : out std_logic_vector(DATA_WIDTH-1 downto 0); -- Data out
      DO_DV   : out std_logic -- Data out valid
   );
end SP_BRAM_BEHAV;

architecture behavioral of SP_BRAM_BEHAV is

   type ram_t is array(ITEMS-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);

   signal bram         : ram_t := (others => (others => '0'));
   signal bram_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal bram_out_vld : std_logic;

   attribute ram_style : string; -- for Vivado
   attribute ram_style of bram : signal is "block";
   attribute ramstyle  : string; -- for Quartus
   attribute ramstyle  of bram : signal is "M20K";

begin

   assert (RDW_MODE = "WRITE_FIRST" or RDW_MODE = "READ_FIRST")
   report "SP_BRAM_BEHAV: Unknown value of RDW_MODE!" severity failure;

   -----------------------------------------------------------------------------
   -- BRAM READ FIRST (OLD DATA) MODE
   -----------------------------------------------------------------------------

   read_first_mode_g : if (RDW_MODE = "READ_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_EN = '1') then
               bram_out <= bram(to_integer(unsigned(ADDR)));
               if (WE = '1') then
                  bram(to_integer(unsigned(ADDR))) <= DI;
               end if;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- BRAM WRITE FIRST (NEW DATA) MODE
   -----------------------------------------------------------------------------

   write_first_mode_g : if (RDW_MODE = "WRITE_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_EN = '1') then
               if (WE = '1') then
                  bram(to_integer(unsigned(ADDR))) <= DI;
                  bram_out <= DI;
               else
                  bram_out <= bram(to_integer(unsigned(ADDR)));
               end if;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- VALID REGISTER
   -----------------------------------------------------------------------------

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            bram_out_vld <= '0';
         elsif (PIPE_EN = '1') then
            bram_out_vld <= RE;
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   out_reg_on_g : if (OUTPUT_REG = True) generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_EN = '1') then
               DO <= bram_out;
            end if;
         end if;
      end process;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RST = '1') then
               DO_DV <= '0';
            elsif (PIPE_EN = '1') then
               DO_DV <= bram_out_vld;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- NO OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   out_reg_off_g : if (OUTPUT_REG = False) generate
      DO    <= bram_out;
      DO_DV <= bram_out_vld;
   end generate;

end behavioral;
