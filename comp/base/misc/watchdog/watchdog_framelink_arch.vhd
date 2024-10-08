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

architecture framelink of WATCHDOG_FRAMELINK is
--! DATA_WIDTH for watchdog must be recalculated
signal aux_data_width    : std_logic_vector
                           ((DATA_WIDTH-1 + RX_REM'length +4) downto 0);

signal src_rdy_in        : std_logic;
signal src_rdy_out       : std_logic;
signal dst_rdy_in        : std_logic;
signal dst_rdy_out       : std_logic;

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
         SRC_RDY_IN     => src_rdy_in,
         DST_RDY_IN     => DST_RDY_IN,

         DATA_OUT       => data_out,
         SRC_RDY_OUT    => src_rdy_out,
         DST_RDY_OUT    => dst_rdy_out,

         KEEP_ALIVE     => KEEP_ALIVE,
         COUNTER        => COUNTER,
         LOCKED         => LOCKED
      );

   --! src_rdy is active in 0
   src_rdy_in <= not RX_SRC_RDY_IN;
   TX_SRC_RDY_OUT <= not src_rdy_out;

   --! dst_rdy is active in 0
   dst_rdy_out <= not TX_DST_RDY_OUT;
   RX_DST_RDY_IN <= not dst_rdy_in;

   --! composition of DATA_IN
   data_in <= RX_SOF_N & RX_SOP_N & RX_EOP_N & RX_EOF_N & RX_REM & RX_DATA;

   --! decomposition of DATA_OUT
   TX_SOF_N <= data_out(data_out'high);
   TX_SOP_N <= data_out(data_out'high -1);
   TX_EOP_N <= data_out(data_out'high -2);
   TX_EOF_N <= data_out(data_out'high -3);
   TX_REM   <= data_out((RX_DATA'length + RX_REM'length-1) downto RX_DATA'length);
   TX_DATA  <= data_out(RX_DATA'range);

end framelink;
