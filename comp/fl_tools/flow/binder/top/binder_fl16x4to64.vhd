-- binder_fl16x4to64.vhd: FrameLink Binder 4x16 -> 64
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl_binder_fl16x4to64 is
   generic(
      -- number of parts in one FrameLink frame
      FRAME_PARTS    : integer;
      -- select BlockRAM or LUT memory
      LUT_MEMORY     : boolean := false;
      -- Number of items (INPUT_WIDTH*INPUT_COUNT wide) in LUT memory that can
      -- be stored for each block
      LUT_BLOCK_SIZE : integer := 16;
      -- Queue choosing policy
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied;
      -- if TRUE simple version of FL_BINDER is used instead of complex one
      -- this version composes only from FL_FIFO, TRANSFORMERs and output logic
      SIMPLE_BINDER  : boolean := false
   );
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interfaces
      RX0            : inout t_fl16;
      RX1            : inout t_fl16;
      RX2            : inout t_fl16;
      RX3            : inout t_fl16;

      -- output interface
      TX             : inout t_fl64

   );
end entity fl_binder_fl16x4to64;

architecture full of fl_binder_fl16x4to64 is
begin

   -- FL_BINDER instantiation
   FL_BINDER_I: entity work.FL_BINDER
      generic map(
         INPUT_WIDTH    => 16,
         INPUT_COUNT    => 4,
         OUTPUT_WIDTH   => 64,
         FRAME_PARTS    => FRAME_PARTS,
         LUT_MEMORY     => LUT_MEMORY,
         LUT_BLOCK_SIZE => LUT_BLOCK_SIZE,
         QUEUE_CHOOSING => QUEUE_CHOOSING,
         SIMPLE_BINDER  => SIMPLE_BINDER
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- input interfaces
         RX_SOF_N(0)             => RX0.SOF_N,
         RX_SOF_N(1)             => RX1.SOF_N,
         RX_SOF_N(2)             => RX2.SOF_N,
         RX_SOF_N(3)             => RX3.SOF_N,

         RX_SOP_N(0)             => RX0.SOP_N,
         RX_SOP_N(1)             => RX1.SOP_N,
         RX_SOP_N(2)             => RX2.SOP_N,
         RX_SOP_N(3)             => RX3.SOP_N,

         RX_EOP_N(0)             => RX0.EOP_N,
         RX_EOP_N(1)             => RX1.EOP_N,
         RX_EOP_N(2)             => RX2.EOP_N,
         RX_EOP_N(3)             => RX3.EOP_N,

         RX_EOF_N(0)             => RX0.EOF_N,
         RX_EOF_N(1)             => RX1.EOF_N,
         RX_EOF_N(2)             => RX2.EOF_N,
         RX_EOF_N(3)             => RX3.EOF_N,

         RX_SRC_RDY_N(0)         => RX0.SRC_RDY_N,
         RX_SRC_RDY_N(1)         => RX1.SRC_RDY_N,
         RX_SRC_RDY_N(2)         => RX2.SRC_RDY_N,
         RX_SRC_RDY_N(3)         => RX3.SRC_RDY_N,

         RX_DST_RDY_N(0)         => RX0.DST_RDY_N,
         RX_DST_RDY_N(1)         => RX1.DST_RDY_N,
         RX_DST_RDY_N(2)         => RX2.DST_RDY_N,
         RX_DST_RDY_N(3)         => RX3.DST_RDY_N,

         RX_DATA(15 downto 0)    => RX0.DATA,
         RX_DATA(31 downto 16)   => RX1.DATA,
         RX_DATA(47 downto 32)   => RX2.DATA,
         RX_DATA(63 downto 48)   => RX3.DATA,

         RX_REM(0 downto 0)      => RX0.DREM,
         RX_REM(1 downto 1)      => RX1.DREM,
         RX_REM(2 downto 2)      => RX2.DREM,
         RX_REM(3 downto 3)      => RX3.DREM,

         -- output interface
         TX_SOF_N       => TX.SOF_N,
         TX_SOP_N       => TX.SOP_N,
         TX_EOP_N       => TX.EOP_N,
         TX_EOF_N       => TX.EOF_N,
         TX_SRC_RDY_N   => TX.SRC_RDY_N,
         TX_DST_RDY_N   => TX.DST_RDY_N,
         TX_DATA        => TX.DATA,
         TX_REM         => TX.DREM
      );

end architecture full;

