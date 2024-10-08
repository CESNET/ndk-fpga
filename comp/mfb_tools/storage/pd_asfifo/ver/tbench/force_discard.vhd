-- force_discard.vhd:
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

--use work.math_pack.all;
--use work.type_pack.all;

entity FORCE_DISCARD is
generic (
   REGIONS : natural := 4
);
port (
   CLK                : in  std_logic;
   RESET              : in  std_logic;

   IN_SOF             : in  std_logic_vector(REGIONS-1 downto 0);
   IN_EOF             : in  std_logic_vector(REGIONS-1 downto 0);
   IN_SRC_RDY         : in  std_logic;
   IN_DST_RDY         : in  std_logic;
   IN_FORCE_DISCARD   : in  std_logic;

   OUT_FORCE_DISCARD  : out std_logic;
   OUT_PKT_FD         : out std_logic_vector(REGIONS-1 downto 0);
   OUT_PKT_FD_VLD     : out std_logic_vector(REGIONS-1 downto 0);
   OUT_PKT_FD_SRC_RDY : out std_logic
);
end FORCE_DISCARD;

architecture FULL of FORCE_DISCARD is

   signal s_inc_frame          : std_logic_vector(REGIONS downto 0);
   signal s_word_with_ok_start : std_logic;

   signal s_force_discard_reg  : std_logic;
   signal s_out_force_discard  : std_logic;

   signal s_fd_per_pkt         : std_logic_vector(REGIONS downto 0);
   signal s_fd_per_pkt_corr    : std_logic_vector(REGIONS-1 downto 0);

begin

   -- --------------------------------------------------------------------------
   --  FRAME STATE LOGIC
   -- --------------------------------------------------------------------------

   inc_frame_g : for r in 0 to REGIONS-1 generate
      s_inc_frame(r+1) <= (IN_SOF(r) and not IN_EOF(r) and not s_inc_frame(r)) or
                          (IN_SOF(r) and IN_EOF(r) and s_inc_frame(r)) or
                          (not IN_SOF(r) and not IN_EOF(r) and s_inc_frame(r));
   end generate;

   inc_frame_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_inc_frame(0) <= '0';
         elsif (IN_SRC_RDY = '1' and IN_DST_RDY = '1') then
            s_inc_frame(0) <= s_inc_frame(REGIONS);
         end if;
      end if;
   end process;

   s_word_with_ok_start <= not s_inc_frame(0);

   -- --------------------------------------------------------------------------
   --  FORCE DISCARD OUTPUT
   -- --------------------------------------------------------------------------

   force_discard_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_force_discard_reg <= '0';
         elsif (IN_FORCE_DISCARD = '1') then
            s_force_discard_reg <= '1';
         elsif (s_word_with_ok_start = '1') then
            s_force_discard_reg <= '0';
         end if;
      end if;
   end process;

   s_out_force_discard <= '1' WHEN (IN_FORCE_DISCARD = '1') ELSE
                          '0' WHEN (s_word_with_ok_start = '1') ELSE s_force_discard_reg;

   OUT_FORCE_DISCARD <= s_out_force_discard;

   -- --------------------------------------------------------------------------
   --  FORCE DISCARD MONITOR PER PACKET OUTPUT
   -- --------------------------------------------------------------------------

   fd_per_pkt_g : for r in 0 to REGIONS-1 generate
      s_fd_per_pkt(r+1) <= s_out_force_discard WHEN (IN_SOF(r) = '1') ELSE (s_fd_per_pkt(r) or s_out_force_discard);
      s_fd_per_pkt_corr(r) <= s_fd_per_pkt(r+1) WHEN (s_inc_frame(r+1) = '0') ELSE s_fd_per_pkt(r);
      OUT_PKT_FD(r) <= s_fd_per_pkt_corr(r) or s_out_force_discard;
   end generate;

   fd_per_pkt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_fd_per_pkt(0) <= '0';
         elsif (IN_SRC_RDY = '1' and IN_DST_RDY = '1') then
            s_fd_per_pkt(0) <= s_fd_per_pkt(REGIONS);
         end if;
      end if;
   end process;

   OUT_PKT_FD_VLD     <= IN_EOF;
   OUT_PKT_FD_SRC_RDY <= IN_SRC_RDY and IN_DST_RDY and (or IN_EOF);

end architecture;
