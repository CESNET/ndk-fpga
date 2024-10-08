-- glitch_filter.vhd: Glitch filter using sampling into shift registers
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Puš <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

entity glitch_filter is
   generic(
      --* Number of samples
      FILTER_LENGTH  : integer := 8;
      --* Width of sampling counter
      FILTER_SAMPLING: integer := 2;
      --* Initial value of samples
      INIT           : std_logic := '1'
   );
   port (
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      --* Glitchy input
      DIN      : in  std_logic;
      --* Glitch-free output
      DOUT     : out std_logic
   );
end entity glitch_filter;

architecture structural of glitch_filter is

   signal sh_filter  : std_logic_vector(FILTER_LENGTH-1 downto 0);
   signal cnt_sample : std_logic_vector(FILTER_SAMPLING downto 0);
   signal sample     : std_logic;
   signal sum        : std_logic_vector(log2(FILTER_LENGTH) downto 0);

begin

   -- Sampling disabled
   no_sample_gen : if FILTER_SAMPLING = 0 generate
      sample <= '1';
   end generate;

   -- Sampling enabled
   sample_gen : if FILTER_SAMPLING > 0 generate
      --* Sample counter
      cnt_sample_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               cnt_sample <= (others => '0');
            else
               cnt_sample(FILTER_SAMPLING-1 downto 0) <=
                  cnt_sample(FILTER_SAMPLING-1 downto 0) + 1;
            end if;
         end if;
      end process;

      --* Sample condition
      sample_p : process(cnt_sample)
      begin
         if cnt_sample(FILTER_SAMPLING-1 downto 0) = 0 then
            sample <= '1';
         else
            sample <= '0';
         end if;
      end process;
   end generate;

   --* Sample memory
   sh_filter_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            sh_filter <= (others => INIT);
         else
            if sample = '1' then
               sh_filter <= sh_filter(FILTER_LENGTH-2 downto 0) & DIN;
            end if;
         end if;
      end if;
   end process;

   --* Sum of all bits in sh_filter
   sum_p : process(sh_filter)
      variable p : std_logic_vector(log2(FILTER_LENGTH) downto 0);
   begin
      p := (others => '0');
      for i in 0 to FILTER_LENGTH-1 loop
         p := p + sh_filter(i);
      end loop;
      sum <= p;
   end process;

   --* Output signal
   dout_p : process(sum)
   begin
      if (sum > FILTER_LENGTH/2) then
         DOUT <= '1';
      else
         DOUT <= '0';
      end if;
   end process;

end architecture structural;
