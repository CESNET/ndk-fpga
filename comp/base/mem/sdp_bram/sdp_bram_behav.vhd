-- sdp_bram_behav.vhd: Simple Dual Port Block RAM (Behavioral)
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity SDP_BRAM_BEHAV is
   Generic (
      -- Data word width in bits.
      DATA_WIDTH  : integer := 32;
      -- Depth of BRAM in number of the data words.
      ITEMS       : integer := 512;
      -- Output directly from BRAM or throw register (better timing).
      OUTPUT_REG  : boolean := True
   );
   Port (
      -- =======================================================================
      -- WRITE INTERFACE
      -- =======================================================================
      WR_CLK      : in  std_logic; -- Write clock
      WR_EN       : in  std_logic; -- Enable of write port
      WR_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Write address
      WR_DIN      : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Write data input
      -- =======================================================================
      -- READ INTERFACE
      -- =======================================================================
      RD_CLK      : in  std_logic; -- Read clock
      RD_RST      : in  std_logic; -- Reset synchronous with read clock
      RD_CE       : in  std_logic; -- Clock enable of read port
      RD_REG_CE   : in  std_logic; -- Clock enable of output read data registers
      RD_EN       : in  std_logic; -- Read enable, only for generation RD_DOUT_VLD
      RD_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0); -- Read address
      RD_DOUT     : out std_logic_vector(DATA_WIDTH-1 downto 0); -- Read data output
      RD_DOUT_VLD : out std_logic  -- Valid of output read data
   );
end SDP_BRAM_BEHAV;

architecture behavioral of SDP_BRAM_BEHAV is

   type ram_t is array(ITEMS-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);

   signal bram         : ram_t := (others => (others => '0'));
   signal bram_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal bram_out_vld : std_logic;

   attribute ram_style : string; -- for Vivado
   attribute ram_style of bram : signal is "block";
   attribute ramstyle  : string; -- for Quartus
   attribute ramstyle  of bram : signal is "M20K";

begin

   -----------------------------------------------------------------------------
   -- BRAM PROCESS
   -----------------------------------------------------------------------------

   process (WR_CLK)
   begin
      if (rising_edge(WR_CLK)) then
         if (WR_EN = '1') then
            bram(to_integer(unsigned(WR_ADDR))) <= WR_DIN;
         end if;
      end if;
   end process;

   process (RD_CLK)
   begin
      if (rising_edge(RD_CLK)) then
         if (RD_CE = '1') then
            bram_out <= bram(to_integer(unsigned(RD_ADDR)));
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- BRAM OUT VALID
   -----------------------------------------------------------------------------

   -- data from BRAM are valid after one cycle
   bram_out_vld_p : process (RD_CLK)
   begin
      if (rising_edge(RD_CLK)) then
         if (RD_RST = '1') then
            bram_out_vld <= '0';
         elsif (RD_CE = '1') then
            bram_out_vld <= RD_EN;
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   out_reg_on_g : if (OUTPUT_REG = True) generate
      process (RD_CLK)
      begin
         if (rising_edge(RD_CLK)) then
            if (RD_REG_CE = '1') then
               RD_DOUT <= bram_out;
            end if;
         end if;
      end process;

      process (RD_CLK)
      begin
         if (rising_edge(RD_CLK)) then
            if (RD_RST = '1') then
               RD_DOUT_VLD <= '0';
            elsif (RD_REG_CE = '1') then
               RD_DOUT_VLD <= bram_out_vld;
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   -- NO OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   out_reg_off_g : if (OUTPUT_REG = False) generate
      RD_DOUT     <= bram_out;
      RD_DOUT_VLD <= bram_out_vld;
   end generate;

end behavioral;
