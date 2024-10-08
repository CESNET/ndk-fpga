-- packet_binder_fl16.vhd: 16-bit FrameLink cover of PACKET_BINDER
-- Copyright (C) 2007 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- package with FL records
use work.fl_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity PACKET_BINDER_FL16 is
   generic(
      PRIMARY         : integer;
      IF0_BUFFER_SIZE : integer;
      IF1_BUFFER_SIZE : integer;
      IF0_PARTS       : integer;
      IF1_PARTS       : integer;
      OUTPUT_REG      : boolean
   );
   port(
      CLK             : in  std_logic;
      RESET           : in  std_logic;

      RX0             : inout t_fl16;
      RX1             : inout t_fl16;
      TX              : inout t_fl16
   );
end entity PACKET_BINDER_FL16;

architecture full of PACKET_BINDER_FL16 is
begin

   PACKET_BINDER : entity work.PACKET_BINDER
   generic map (
      FL_WIDTH        => 16,
      PRIMARY         => PRIMARY,
      IF0_BUFFER_SIZE => IF0_BUFFER_SIZE,
      IF1_BUFFER_SIZE => IF1_BUFFER_SIZE,
      IF0_PARTS       => IF0_PARTS,
      IF1_PARTS       => IF1_PARTS,
      OUTPUT_REG      => OUTPUT_REG
      )

   port map (
      -- Common interface
      CLK             => clk,
      RESET           => reset,

      -- RX interface 0
      RX_SOF_N_0        => RX0.sof_n,
      RX_SOP_N_0        => RX0.sop_n,
      RX_EOP_N_0        => RX0.eop_n,
      RX_EOF_N_0        => RX0.eof_n,
      RX_SRC_RDY_N_0    => RX0.src_rdy_n,
      RX_DST_RDY_N_0    => RX0.dst_rdy_n,
      RX_DATA_0         => RX0.data,
      RX_REM_0          => RX0.drem,


      -- RX interface 1
      RX_SOF_N_1        => RX1.sof_n,
      RX_SOP_N_1        => RX1.eop_n,
      RX_EOF_N_1        => RX1.eof_n,
      RX_EOP_N_1        => RX1.eop_n,
      RX_SRC_RDY_N_1    => RX1.src_rdy_n,
      RX_DST_RDY_N_1    => RX1.dst_rdy_n,
      RX_DATA_1         => RX1.data,
      RX_REM_1          => RX1.drem,

      -- TX interface
      TX_DATA           => TX.data,
      TX_REM            => TX.drem,
      TX_DST_RDY        => TX.dst_rdy_n,
      TX_EOF            => TX.eof_n,
      TX_EOP            => TX.eop_n,
      TX_SOF            => TX.sof_n,
      TX_SOP            => TX.sop_n,
      TX_SRC_RDY        => TX.src_rdy_n

   );

end architecture full;

