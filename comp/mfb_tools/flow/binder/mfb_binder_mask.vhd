-- mfb_binder_mask.vhd: Masking module for MFB BINDER
-- Copyright (C) 2018 CESNET
-- Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_BINDER_MASK is
   generic(
      REGIONS : integer := 4
   );
   port(
      -- CLOCK AND RESET
      CLK                 : in std_logic;
      RST                 : in std_logic;
      -- INPUT
      IN_MASK_ENABLE      : in std_logic;
      IN_UNFINISHED_FRAME : in std_logic;
      IN_SOF              : in std_logic_vector(REGIONS-1 downto 0);
      IN_EOF              : in std_logic_vector(REGIONS-1 downto 0);
      -- OUTPUT
      OUT_NEED_MASK_FWORD : out std_logic;
      OUT_NEED_MASK_LWORD : out std_logic;
      OUT_SOF_MASKED      : out std_logic_vector(REGIONS-1 downto 0);
      OUT_EOF_MASKED      : out std_logic_vector(REGIONS-1 downto 0)
   );
end MFB_BINDER_MASK;

architecture behavioral of MFB_BINDER_MASK is

   signal sof_mask                : std_logic_vector(REGIONS-1 downto 0);
   signal eof_mask                : std_logic_vector(REGIONS-1 downto 0);
   signal sof_masked              : std_logic_vector(REGIONS-1 downto 0);
   signal eof_masked              : std_logic_vector(REGIONS-1 downto 0);
   signal last_sof_masked_in      : std_logic_vector(REGIONS-1 downto 0);
   signal last_sof_masked_out     : std_logic_vector(REGIONS-1 downto 0);
   signal last_sof_ce             : std_logic;

begin

   process(CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            last_sof_masked_out <= (others => '0');
         elsif (last_sof_ce = '1' and IN_MASK_ENABLE = '1') then
            last_sof_masked_out <= last_sof_masked_in;
         end if;
      end if;
   end process;

   -- Main Logic
   process(all)
   begin
      sof_mask <= (others => '1');
      eof_mask <= (others => '1');
      last_sof_masked_in <= (others => '0');
      last_sof_ce <= '0';
      for r in REGIONS-1 downto 0 loop
         if (last_sof_masked_out(r) = '0') then
            if (IN_UNFINISHED_FRAME = '0') then
               exit;
            end if;
            if (IN_SOF(r) = '1') then
               sof_mask(r) <= '0';
               last_sof_masked_in(r) <= '1';
               last_sof_ce <= '1';
               exit;
            end if;
         else
            sof_mask(r-1 downto 0) <= (others => '0');
            eof_mask(r downto 0) <= (others => '0');
            last_sof_masked_in <= (others => '0');
            last_sof_ce <= '1';
            exit;
         end if;
      end loop;
   end process;

   eof_masked <= IN_EOF and eof_mask;
   sof_masked <= IN_SOF and sof_mask;

   OUT_NEED_MASK_FWORD <= or last_sof_masked_out;
   OUT_NEED_MASK_LWORD <= or last_sof_masked_in;

   -- Output MUX
   OUT_SOF_MASKED <= sof_masked when (IN_MASK_ENABLE = '1') else IN_SOF;
   OUT_EOF_MASKED <= eof_masked when (IN_MASK_ENABLE = '1') else IN_EOF;

end architecture;
