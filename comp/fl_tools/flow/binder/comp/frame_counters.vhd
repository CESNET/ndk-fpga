-- frame_counters.vhd: Set of Frame Counters
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_FRAME_COUNTERS is
   generic(
      COUNTER_WIDTH  : integer;
      COUNT          : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      INC            : in std_logic_vector(COUNT-1 downto 0);
      DEC            : in std_logic_vector(COUNT-1 downto 0);

      -- output interface
      FRAME_RDY      : out std_logic_vector(COUNT-1 downto 0);
      NO_FRAME       : out std_logic
   );
end entity FLB_FRAME_COUNTERS;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FLB_FRAME_COUNTERS is

   signal sig_frame_rdy    : std_logic_vector(COUNT-1 downto 0);
begin
   -- output signals
   FRAME_RDY   <= sig_frame_rdy;

   -- generate frame counters
   GEN_COUNTER : for i in 0 to COUNT-1 generate
       FLB_FRAME_COUNTER_I : entity work.FLB_FRAME_COUNTER
         generic map(
            COUNTER_WIDTH  => COUNTER_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input interface
            INC            => INC(i),
            DEC            => DEC(i),
            -- output interface
            FRAME_RDY      => sig_frame_rdy(i)
         );
   end generate;

   -- NO_FRAME signal generic OR
   no_framep : process(sig_frame_rdy)
      variable or_int : std_logic;
   begin
      or_int := '0';

      for k in 0 to COUNT - 1 loop
         or_int := or_int or sig_frame_rdy(k);
      end loop;

      NO_FRAME <= not or_int;
   end process;

end architecture behavioral;

