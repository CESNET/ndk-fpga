--! tsu_pps_processing.vhd
--!
--! @file
--! \brief timestamp unit - pps processing
--! \author Jakub Cabal <jakubcabal@gmail.com>
--! \date 2014
--!
--! @section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TSU_PPS_PROCESSING is
   port (
      CLK              : in  std_logic;
      RESET            : in  std_logic;
      PPS_N            : in  std_logic;
      DETECT_PPS_RESET : in  std_logic;
      CORE_PPS_N       : out std_logic;
      DETECT_PPS       : out std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of TSU_PPS_PROCESSING is

   --! PPS pipelines
   signal reg_pps                 : std_logic;
   signal reg_pps2                : std_logic;
   signal reg_pps3                : std_logic;
   signal pps_pipe                : std_logic_vector(2 downto 0);
   signal sync_pps_n              : std_logic;
   signal old_sync_pps_n          : std_logic;
   signal xor_sync_pps_n          : std_logic;
   signal clk_ref_xor             : std_logic;
   signal detect_pps_reg          : std_logic;

   --! PPS counters
   signal pps_cnt_reg             : std_logic_vector(28 downto 0);
   signal cnt_pps_n               : std_logic;

begin

   --! --------------------------------------------------------
   --!         Processing of PPS_N signal
   --! --------------------------------------------------------

   --! Registered PPS_N signal
   pps_n_reg : process(CLK)
   begin
      if (rising_edge(CLK)) then
         reg_pps  <= PPS_N;
         reg_pps2 <= reg_pps;
         reg_pps3 <= reg_pps2;
      end if;
   end process;

   --! PPS pulse pipeline (because transition might not be fast enough
   pps_pipe <= reg_pps & reg_pps2 & reg_pps3;

   --! Makes one single signal from PPS_N and pps0_pipe
   sync_pps : process(pps_pipe, reg_pps)
   begin
      case (pps_pipe) is
         when "000"  => sync_pps_n <= reg_pps;
         when others => sync_pps_n <= '1';
      end case;
   end process;

   --! Registering last value of PPS_N
   process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            old_sync_pps_n <= '1';
         else
            old_sync_pps_n <= sync_pps_n;
         end if;
      end if;
   end process;

   --! Counter for distinguishing if the source pulse per second is active or not
   pps0_counter : process(CLK)
   begin
      if (rising_edge(CLK)) then
         --! if RESET or PPS from GPS or pps0_cnt_reg is equal to X"10000000"
         if (RESET = '1' or xor_sync_pps_n = '1' or pps_cnt_reg(28) = '1') then
            pps_cnt_reg <= (others => '0');
         else
            pps_cnt_reg <= std_logic_vector(unsigned(pps_cnt_reg) + 1);
         end if;
      end if;
   end process;

   xor_sync_pps_n <= sync_pps_n xor old_sync_pps_n;
   CORE_PPS_N     <= sync_pps_n or not detect_pps_reg;

   --! Detection bit if PPS source is active or not
   detect_pps_register : process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1' or pps_cnt_reg(28) = '1' or DETECT_PPS_RESET = '1') then
            detect_pps_reg <= '0';
         elsif (xor_sync_pps_n = '1') then
            detect_pps_reg <= '1';
         end if;
      end if;
   end process;

   DETECT_PPS <= detect_pps_reg;

end architecture;
