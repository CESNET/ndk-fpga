-- watchdog_framelink_arch.vhd: watchdog FrameLink architecture
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
use WORK.math_pack.all;

architecture framelink of WATCHDOG_FRAMELINK_UNALIGNED is
--! DATA_WIDTH for watchdog must be recalculated
signal aux_data_width    : std_logic_vector
                           ((DATA_WIDTH-1 + RX_SOP_POS'length + RX_EOP_POS'length +2) downto 0);

--! input signal to DATA_IN
signal data_in       : std_logic_vector(aux_data_width'range);
--! output signal form DATA_OUT
signal data_out      : std_logic_vector(aux_data_width'range);

begin
   watch_comp: entity work.watchdog
      generic map (
         DATA_WIDTH     => aux_data_width'length,
         EDGE_DETECT    => EDGE_DETECT,
         COUNT          => COUNT,
         COUNTER_WIDTH  => COUNTER_WIDTH,
         TIMING         => TIMING
         )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         DATA_IN        => data_in,
         SRC_RDY_IN     => RX_SRC_RDY,
         DST_RDY_IN     => RX_DST_RDY,

         DATA_OUT       => data_out,
         SRC_RDY_OUT    => TX_SRC_RDY,
         DST_RDY_OUT    => TX_DST_RDY,

         KEEP_ALIVE     => KEEP_ALIVE,
         COUNTER        => COUNTER,
         LOCKED         => LOCKED
      );

   --! composition of DATA_IN
   data_in <= RX_EOP & RX_SOP & RX_EOP_POS & RX_SOP_POS & RX_DATA;

   --! decomposition of DATA_OUT
   TX_EOP       <= data_out(data_out'high);
   TX_SOP       <= data_out(data_out'high -1);
   TX_EOP_POS   <= data_out((data_out'high-2) downto
                   ((data_out'high-2) - (RX_EOP_POS'length-1)));
   TX_SOP_POS   <= data_out((RX_DATA'length + RX_SOP_POS'length -1) downto RX_DATA'length);
   TX_DATA      <= data_out(RX_DATA'range);


end framelink;
