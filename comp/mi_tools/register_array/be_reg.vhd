--! \file:   rw_registers.vhd
--! \brief:  Memory register with support BE signal
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;

--! generic register with support MI_BI
entity BE_REG is
   generic (
      --! Data width max MI_WIDTH
      MI_WIDTH     : integer := 32;
      DATA_WIDTH   : integer := 32;
      BE_ENABLE    : boolean := true;
      NUM_REG      : integer;
      constant INICIAL      : std_logic_vector
   );
   port (
      CLK         : in  std_logic;
      --! MI32 BE signal
      BE          : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
      --! input data
      DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! enbale signal
      ENABLE      : in  std_logic;
      --! reset signal
      RESET       : in  std_logic;
      --! output data
      P           : out std_logic_vector(DATA_WIDTH-1 downto 0) := INICIAL((MI_WIDTH*(NUM_REG-1))+DATA_WIDTH-1 downto 0+(MI_WIDTH*(NUM_REG-1)))
   );
end BE_REG;

architecture full of BE_REG is
   constant d_div : integer := DATA_WIDTH/8;
   constant d_mod : integer := DATA_WIDTH mod 8;
   constant init_r : integer := MI_WIDTH*(NUM_REG-1);
begin

   GEN_REG_WITH_BE : if (BE_ENABLE = true) generate
   begin
      GEN_REG_DIV : for I in 0 to d_div-1 generate
      begin
         gen_regs_be: process(CLK)
         begin
            if(CLK'event) and (CLK='1') then
               if (RESET = '1') then
                  P(7+(8*I) downto 0+(8*I)) <= INICIAL(7+(8*I)+init_r downto 0+(8*I)+init_r);
               elsif (ENABLE = '1' and BE(I) = '1') then
                  P(7+(8*I) downto 0+(8*I)) <= DATA(7+(8*I) downto 0+(8*I));
               end if;
            end if;
         end process;
      end generate;

      GEN_REG_MOD: if (d_mod /= 0) generate
      begin
         gen_reg_be: process(CLK)
         begin
            if(CLK'event) and (CLK='1') then
               if (RESET = '1') then
                  P(DATA_WIDTH-1 downto DATA_WIDTH-d_mod) <= INICIAL(DATA_WIDTH-1+init_r downto DATA_WIDTH-d_mod+init_r);
               elsif (ENABLE = '1' and BE(d_div) = '1') then
                  P(DATA_WIDTH-1 downto DATA_WIDTH-d_mod) <= DATA(DATA_WIDTH-1 downto DATA_WIDTH-d_mod);
               end if;
            end if;
         end process;
      end generate;
   end generate;

   --! generate only register
   GEN_REG_NO_BE : if (BE_ENABLE = false) generate
   begin
      gen_reg_be: process(CLK)
      begin
         if(CLK'event) and (CLK='1') then
            if (RESET = '1') then
               P <= INICIAL(DATA_WIDTH-1+init_r downto 0+init_r);
            elsif (ENABLE = '1') then
               P <= DATA;
            end if;
         end if;
      end process;
   end generate;
end full;
