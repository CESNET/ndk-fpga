-- switch.vhd: FrameLink 1-N switch.
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

--* This is the full implementation of the fl_switch_1toN entity.
--* It is divided to two pieces.
--*
--* The first solves situation when the searched IFNUM is located
--* in the first word of every frame (when RX_SOF_N is active).
--*
--* The second solves other situations. It uses a FrameLink FIFO
--* to hold data that precedes the word where thee IFNUM is located.
--*
--* @author Jan Viktorin
architecture full of fl_switch_1toN is

   constant REM_WIDTH   : integer := log2(DATA_WIDTH / 8);

   -- connections to all output TX interfaces
   signal impl_tx_data    : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal impl_tx_rem     : std_logic_vector(REM_WIDTH - 1 downto 0);
   signal impl_tx_sof_n   : std_logic;
   signal impl_tx_eof_n   : std_logic;
   signal impl_tx_sop_n   : std_logic;
   signal impl_tx_eop_n   : std_logic;

   -- connects the extracted ifnum to a component that solves the switching
   signal ifnum   : std_logic_vector(IF_COUNT - 1 downto 0);

begin

   assert (IFNUM_OFFSET mod DATA_WIDTH) + IF_COUNT < DATA_WIDTH
      report "IFNUM must fit into one FrameLink word!"  severity failure;

-- extracts IFNUM from the RX_DATA signal
ifnum_extract : entity work.ifnum_extract
generic map (
   TX_COUNT       => IF_COUNT,
   DATA_WIDTH     => DATA_WIDTH,
   IFNUM_OFFSET   => IFNUM_OFFSET
)
port map (
   RX_DATA  => RX_DATA,
   RX_REM   => RX_REM,
   RX_EOP_N => RX_EOP_N,

   IFNUM    => ifnum
);

gen_switch_impl_nofifo :
if IFNUM_OFFSET < DATA_WIDTH generate

   -- No FIFO is needed here, the IFNUM is located
   -- immediately in the first FrameLink word.

   gen_switch_impl : entity work.fl_switch_impl(nofifo)
   generic map (
      TX_COUNT    => IF_COUNT,
      DATA_WIDTH  => DATA_WIDTH
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,

      RX_DATA  => RX_DATA,
      RX_REM   => RX_REM,
      RX_SOF_N => RX_SOF_N,
      RX_EOF_N => RX_EOF_N,
      RX_SOP_N => RX_SOP_N,
      RX_EOP_N => RX_EOP_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,

      TX_DATA  => impl_tx_data,
      TX_REM   => impl_tx_rem,
      TX_SOF_N => impl_tx_sof_n,
      TX_EOF_N => impl_tx_eof_n,
      TX_SOP_N => impl_tx_sop_n,
      TX_EOP_N => impl_tx_eop_n,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N,

      IFNUM    => ifnum
   );
end generate;

gen_switch_impl_fifo :
if IFNUM_OFFSET >= DATA_WIDTH generate

   -- Here the IFNUM is located in second word or further,
   -- so some FIFO is needed here.

   gen_switch_impl : entity work.fl_switch_impl(fifo)
   generic map (
      TX_COUNT    => IF_COUNT,
      DATA_WIDTH  => DATA_WIDTH,
      PARTS => PARTS
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,

      RX_DATA  => RX_DATA,
      RX_REM   => RX_REM,
      RX_SOF_N => RX_SOF_N,
      RX_EOF_N => RX_EOF_N,
      RX_SOP_N => RX_SOP_N,
      RX_EOP_N => RX_EOP_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,

      TX_DATA  => impl_tx_data,
      TX_REM   => impl_tx_rem,
      TX_SOF_N => impl_tx_sof_n,
      TX_EOF_N => impl_tx_eof_n,
      TX_SOP_N => impl_tx_sop_n,
      TX_EOP_N => impl_tx_eop_n,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N,

      IFNUM    => ifnum
   );

end generate;

--* Connects the ports from a fl_switch_impl to all TX interfaces.
--* The output is sent to every TX all the time. Only signals
--* TX_SRC_RDY_N and TX_DST_RDY_N controls to which interface the data
--* is provided and these signals are connected directly to sl_switch_impl.
connect_fl_1toN : process(impl_tx_data, impl_tx_rem, impl_tx_sof_n, impl_tx_eof_n, impl_tx_sop_n, impl_tx_eop_n)
begin
   for i in 0 to IF_COUNT - 1 loop
      TX_DATA(i * DATA_WIDTH + DATA_WIDTH - 1 downto i * DATA_WIDTH) <= impl_tx_data;
      TX_REM (i * REM_WIDTH  + REM_WIDTH  - 1 downto i * REM_WIDTH)  <= impl_tx_rem;

      TX_SOF_N(i) <= impl_tx_sof_n;
      TX_EOF_N(i) <= impl_tx_eof_n;
      TX_SOP_N(i) <= impl_tx_sop_n;
      TX_EOP_N(i) <= impl_tx_eop_n;
   end loop;
end process;

end architecture;
