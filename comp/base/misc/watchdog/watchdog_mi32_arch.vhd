-- watchdog_mi32_arch.vhd: watchdog m32 architecture
-- Copyright (C) 2015 CESNET
-- Author(s): Adam Piecek <xpiece00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;

architecture mi32 of WATCHDOG_MI32 is
--! output signal of D-type flip-flop register
signal reg_keep_alive        : std_logic;
--! enable write signal for keep_alive register
signal we                    : std_logic;
--! signal contains bits from the vectors locked and reg_keep_alive
signal read_0                : std_logic_vector(31 downto 0);
--! signal contains COUNTER bits
signal read_4                : std_logic_vector(31 downto 0);

signal counter_mi32          : std_logic_vector(COUNTER'range);
signal locked_mi32           : std_logic;

begin
   watch_comp: entity work.watchdog
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         EDGE_DETECT    => EDGE_DETECT,
         COUNT          => COUNT,
         COUNTER_WIDTH  => COUNTER_WIDTH,
         TIMING         => TIMING
         )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         DATA_IN        => DATA_IN,
         SRC_RDY_IN     => SRC_RDY_IN,
         DST_RDY_IN     => DST_RDY_IN,

         DATA_OUT       => DATA_OUT,
         SRC_RDY_OUT    => SRC_RDY_OUT,
         DST_RDY_OUT    => DST_RDY_OUT,
         KEEP_ALIVE     => reg_keep_alive,
         COUNTER        => counter_mi32,
         LOCKED         => locked_mi32
      );

   LOCKED <= locked_mi32;
   COUNTER <= counter_mi32;
   --------------------------
   --! Read section
   --------------------------
   ARDY <= '1';
   DRDY <= RD;

   read_0 <= (31 downto 2 => '0') & locked_mi32 & reg_keep_alive;
   read_4 <= (31 downto counter_mi32'length => '0') & counter_mi32;

   with ADDR(2) select
   DRD <= read_0 when '1',
          read_4 when '0',
          (DRD'range => '0')    when others;

   --------------------------
   --! Write section
   --------------------------

   we <= WR and BE(0) and ADDR(2);

   reg_d_keep_alive : process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if we = '1' then
            reg_keep_alive <= DWR(0);
         end if;
      end if;
   end process;

end mi32;
