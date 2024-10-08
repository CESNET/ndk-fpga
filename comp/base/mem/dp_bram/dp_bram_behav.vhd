-- dp_bram_behav.vhd: Synchronous Dual Port Block RAM (Behavioral)
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity DP_BRAM_BEHAV is
   Generic (
      -- Data word width in bits.
      DATA_WIDTH : integer := 32;
      -- Depth of BRAM in number of the data words.
      ITEMS      : integer := 512;
      -- Output directly from BRAM or throw register (better timing).
      OUTPUT_REG : boolean := True;
      -- What operation will be performed first when write and read are active
      -- in same time and same port? Possible values are:
      -- "WRITE_FIRST" - Default mode, works on Xilinx and Intel FPGAs.
      -- "READ_FIRST"  - This mode is not supported on Intel FPGAs, BRAM will be
      --               - implemented into logic!
      RDW_MODE_A : string := "WRITE_FIRST";
      RDW_MODE_B : string := "WRITE_FIRST"
   );
   Port (
      CLK      : in  std_logic; -- Clock
      RST      : in  std_logic; -- Reset
      -- =======================================================================
      -- Port A
      -- =======================================================================
      PIPE_ENA : in  std_logic; -- Enable of port A and output register, required extra logic on Intel FPGA
      REA      : in  std_logic; -- Read enable of port A, only for generation DOA_DV
      WEA      : in  std_logic; -- Write enable of port A
      ADDRA    : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Port A address
      DIA      : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Port A data in
      DOA      : out std_logic_vector(DATA_WIDTH-1 downto 0); -- Port A data out
      DOA_DV   : out std_logic; -- Port A data out valid
      -- =======================================================================
      -- Port B
      -- =======================================================================
      PIPE_ENB : in  std_logic; -- Enable of port B and output register, required extra logic on Intel FPGA
      REB      : in  std_logic; -- Read enable of port B, only for generation DOB_DV
      WEB      : in  std_logic; -- Write enable of port B
      ADDRB    : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Port B address
      DIB      : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Port B data in
      DOB      : out std_logic_vector(DATA_WIDTH-1 downto 0); -- Port B data out
      DOB_DV   : out std_logic -- Port B data out valid
   );
end DP_BRAM_BEHAV;

architecture behavioral of DP_BRAM_BEHAV is

   type ram_t is array(ITEMS-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);
   shared variable bram : ram_t := (others => (others => '0'));

   signal pa_bram_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pa_bram_out_vld : std_logic;
   signal pb_bram_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pb_bram_out_vld : std_logic;

   attribute ram_style : string; -- for Vivado
   attribute ram_style of bram : variable is "block";
   attribute ramstyle  : string; -- for Quartus
   attribute ramstyle  of bram : variable is "M20K";

begin

   assert (RDW_MODE_A = "WRITE_FIRST" or RDW_MODE_A = "READ_FIRST")
   report "DP_BRAM_BEHAV: Unknown value of RDW_MODE_A!" severity failure;

   assert (RDW_MODE_B = "WRITE_FIRST" or RDW_MODE_B = "READ_FIRST")
   report "DP_BRAM_BEHAV: Unknown value of RDW_MODE_B!" severity failure;

   -----------------------------------------------------------------------------
   -- BRAM PORT A
   -----------------------------------------------------------------------------

   -- WRITE FIRST (NEW DATA) MODE
   pa_write_first_mode_g : if (RDW_MODE_A = "WRITE_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_ENA = '1') then
               if (WEA = '1') then
                  bram(to_integer(unsigned(ADDRA))) := DIA;
               end if;
               pa_bram_out <= bram(to_integer(unsigned(ADDRA)));
            end if;
         end if;
      end process;
   end generate;

   -- READ FIRST (OLD DATA) MODE
   pa_read_first_mode_g : if (RDW_MODE_A = "READ_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_ENA = '1') then
               pa_bram_out <= bram(to_integer(unsigned(ADDRA)));
               if (WEA = '1') then
                  bram(to_integer(unsigned(ADDRA))) := DIA;
               end if;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- BRAM PORT B
   -----------------------------------------------------------------------------

   -- WRITE FIRST (NEW DATA) MODE
   pb_write_first_mode_g : if (RDW_MODE_B = "WRITE_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_ENB = '1') then
               if (WEB = '1') then
                  bram(to_integer(unsigned(ADDRB))) := DIB;
               end if;
               pb_bram_out <= bram(to_integer(unsigned(ADDRB)));
            end if;
         end if;
      end process;
   end generate;

   -- READ FIRST (OLD DATA) MODE
   pb_read_first_mode_g : if (RDW_MODE_B = "READ_FIRST") generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_ENB = '1') then
               pb_bram_out <= bram(to_integer(unsigned(ADDRB)));
               if (WEB = '1') then
                  bram(to_integer(unsigned(ADDRB))) := DIB;
               end if;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- VALID REGISTERS
   -----------------------------------------------------------------------------

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            pa_bram_out_vld <= '0';
         elsif (PIPE_ENA = '1') then
            pa_bram_out_vld <= REA;
         end if;
      end if;
   end process;

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            pb_bram_out_vld <= '0';
         elsif (PIPE_ENB = '1') then
            pb_bram_out_vld <= REB;
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
            if (PIPE_ENA = '1') then
               DOA <= pa_bram_out;
            end if;
         end if;
      end process;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (PIPE_ENB = '1') then
               DOB <= pb_bram_out;
            end if;
         end if;
      end process;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RST = '1') then
               DOA_DV <= '0';
            elsif (PIPE_ENA = '1') then
               DOA_DV <= pa_bram_out_vld;
            end if;
         end if;
      end process;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RST = '1') then
               DOB_DV <= '0';
            elsif (PIPE_ENB = '1') then
               DOB_DV <= pb_bram_out_vld;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- NO OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   out_reg_off_g : if (OUTPUT_REG = False) generate
      DOA    <= pa_bram_out;
      DOA_DV <= pa_bram_out_vld;
      DOB    <= pb_bram_out;
      DOB_DV <= pb_bram_out_vld;
   end generate;

end behavioral;
