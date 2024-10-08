-- binder_x3_norec.vhd: FrameLink Binder 3 input interfaces, NO RECORDS
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BINDER_X3_NOREC is
   generic(
      -- Input width
      INPUT_WIDTH    : integer;
      -- Output width
      OUTPUT_WIDTH   : integer;
      -- number of parts in one FrameLink frame
      FRAME_PARTS    : integer;
      -- Queue choosing policy
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied
      -- if TRUE simple version of FL_BINDER is used instead of complex one
      -- this version composes only from FL_FIFO, TRANSFORMERs and output logic
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interfaces
      RX0_SOF_N      : in  std_logic;
      RX0_SOP_N      : in  std_logic;
      RX0_EOP_N      : in  std_logic;
      RX0_EOF_N      : in  std_logic;
      RX0_SRC_RDY_N  : in  std_logic;
      RX0_DST_RDY_N  : out std_logic;
      RX0_DATA       : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      RX0_REM        : in  std_logic_vector(log2(INPUT_WIDTH/8)-1 downto 0);

      RX1_SOF_N      : in  std_logic;
      RX1_SOP_N      : in  std_logic;
      RX1_EOP_N      : in  std_logic;
      RX1_EOF_N      : in  std_logic;
      RX1_SRC_RDY_N  : in  std_logic;
      RX1_DST_RDY_N  : out std_logic;
      RX1_DATA       : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      RX1_REM        : in  std_logic_vector(log2(INPUT_WIDTH/8)-1 downto 0);

      RX2_SOF_N      : in  std_logic;
      RX2_SOP_N      : in  std_logic;
      RX2_EOP_N      : in  std_logic;
      RX2_EOF_N      : in  std_logic;
      RX2_SRC_RDY_N  : in  std_logic;
      RX2_DST_RDY_N  : out std_logic;
      RX2_DATA       : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      RX2_REM        : in  std_logic_vector(log2(INPUT_WIDTH/8)-1 downto 0);

      -- output interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)

   );
end entity FL_BINDER_X3_NOREC;

architecture full of FL_BINDER_X3_NOREC is
   signal rx_data_i        : std_logic_vector(3*INPUT_WIDTH-1 downto 0);
   signal rx_rem_i         : std_logic_vector(3*log2(INPUT_WIDTH/8)-1 downto 0);
begin

   rx_data_i((0+1)*INPUT_WIDTH-1 downto 0*INPUT_WIDTH) <= RX0_DATA;
   rx_data_i((1+1)*INPUT_WIDTH-1 downto 1*INPUT_WIDTH) <= RX1_DATA;
   rx_data_i((2+1)*INPUT_WIDTH-1 downto 2*INPUT_WIDTH) <= RX2_DATA;

   rx_rem_i((0+1)*log2(INPUT_WIDTH/8)-1 downto 0*log2(INPUT_WIDTH/8))  <= RX0_REM;
   rx_rem_i((1+1)*log2(INPUT_WIDTH/8)-1 downto 1*log2(INPUT_WIDTH/8))  <= RX1_REM;
   rx_rem_i((2+1)*log2(INPUT_WIDTH/8)-1 downto 2*log2(INPUT_WIDTH/8))  <= RX2_REM;


   FL_BINDER_I: entity work.FL_BINDER
   generic map(
      INPUT_WIDTH    => INPUT_WIDTH,
      INPUT_COUNT    => 3,
      OUTPUT_WIDTH   => OUTPUT_WIDTH,
      FRAME_PARTS    => FRAME_PARTS,
      QUEUE_CHOOSING => QUEUE_CHOOSING,
      SIMPLE_BINDER  => true  -- 3 interfaces allowed only for SIMPLE_BINDER
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interfaces
      RX_SOF_N(0)             => RX0_SOF_N,
      RX_SOF_N(1)             => RX1_SOF_N,
      RX_SOF_N(2)             => RX2_SOF_N,

      RX_SOP_N(0)             => RX0_SOP_N,
      RX_SOP_N(1)             => RX1_SOP_N,
      RX_SOP_N(2)             => RX2_SOP_N,

      RX_EOP_N(0)             => RX0_EOP_N,
      RX_EOP_N(1)             => RX1_EOP_N,
      RX_EOP_N(2)             => RX2_EOP_N,

      RX_EOF_N(0)             => RX0_EOF_N,
      RX_EOF_N(1)             => RX1_EOF_N,
      RX_EOF_N(2)             => RX2_EOF_N,

      RX_SRC_RDY_N(0)         => RX0_SRC_RDY_N,
      RX_SRC_RDY_N(1)         => RX1_SRC_RDY_N,
      RX_SRC_RDY_N(2)         => RX2_SRC_RDY_N,

      RX_DST_RDY_N(0)         => RX0_DST_RDY_N,
      RX_DST_RDY_N(1)         => RX1_DST_RDY_N,
      RX_DST_RDY_N(2)         => RX2_DST_RDY_N,

      RX_DATA                 => rx_data_i,

      RX_REM                  => rx_rem_i,

      -- output interface
      TX_SOF_N       => TX_SOF_N,
      TX_SOP_N       => TX_SOP_N,
      TX_EOP_N       => TX_EOP_N,
      TX_EOF_N       => TX_EOF_N,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N,
      TX_DATA        => TX_DATA,
      TX_REM         => TX_REM
   );

end architecture full;

