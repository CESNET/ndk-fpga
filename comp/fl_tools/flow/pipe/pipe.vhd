--
-- pipe.vhd: FrameLink Pipeline
-- Copyright (C) 2013 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               ENTITY DECLARATION
-- ----------------------------------------------------------------------------

entity FL_PIPE is
   generic(
      -- FrameLink Data Width
      DATA_WIDTH     : integer:= 64;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register, optimization of
      --              mapping shreg on Xilinx FPGA can be set using OPT generic
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      PIPE_TYPE   : string  := "SHREG";
      -- Only for PIPE_TYPE = "SHREG"!
      USE_OUTREG     : boolean:= false;
      FAKE_PIPE      : boolean:= false;
      -- Only for PIPE_TYPE = "SHREG"!
      RESET_BY_INIT  : boolean:= false
   );
   port(
      -- ================
      -- Common interface
      -- ================

      CLK            : in std_logic;
      -- NOTE: also starts debug counters
      RESET          : in std_logic;

      -- ================
      -- Input interface
      -- ================

      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(tsel(DATA_WIDTH >= 8, log2(DATA_WIDTH/8) -1, -1) downto 0);

      -- ================
      -- Output interface
      -- ================

      TX_SOF_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(tsel(DATA_WIDTH >= 8, log2(DATA_WIDTH/8) -1, -1) downto 0);

      -- ==================
      -- Debuging interface
      -- ==================

      -- blocks data words on pipe's input interface
      DEBUG_BLOCK        : in  std_logic := '0';
      -- drops data words on pipe's input interface (higher priority than BLOCK)
      DEBUG_DROP         : in  std_logic := '0';
      -- source ready on pipe's input interface
      DEBUG_SRC_RDY      : out std_logic;
      -- destination ready on pipe's input interface
      DEBUG_DST_RDY      : out std_logic;
      -- start of transaction on pipe's input interface
      DEBUG_SOP          : out std_logic;
      -- end of transaction on pipe's input interface
      DEBUG_EOP          : out std_logic
    );
end entity FL_PIPE;

-- ----------------------------------------------------------------------------
--                            ARCHITECTURE DECLARATION
-- ----------------------------------------------------------------------------
architecture fl_pipe_arch of FL_PIPE is

   constant REM_WIDTH         : natural := TX_REM'length;
   constant PIPE_WIDTH        : natural := DATA_WIDTH + REM_WIDTH + 4;

   signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_in_src_rdy     : std_logic;
   signal pipe_in_dst_rdy     : std_logic;

   signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_out_src_rdy    : std_logic;
   signal pipe_out_dst_rdy    : std_logic;

   signal sig_rx_src_rdy_n    : std_logic;
   signal sig_rx_dst_rdy_n    : std_logic;
   signal sig_rx_sof_n        : std_logic;
   signal sig_rx_eof_n        : std_logic;

begin
   pipe_in_data      <= sig_rx_sof_n & RX_SOP_N & RX_EOP_N & sig_rx_eof_n & RX_REM & RX_DATA;
   pipe_in_src_rdy   <= not sig_rx_src_rdy_n;
   sig_rx_dst_rdy_n  <= not pipe_in_dst_rdy;

   TX_SOF_N          <= pipe_out_data(DATA_WIDTH+REM_WIDTH+3);
   TX_SOP_N          <= pipe_out_data(DATA_WIDTH+REM_WIDTH+2);
   TX_EOP_N          <= pipe_out_data(DATA_WIDTH+REM_WIDTH+1);
   TX_EOF_N          <= pipe_out_data(DATA_WIDTH+REM_WIDTH+0);
   TX_DATA           <= pipe_out_data(DATA_WIDTH-1 downto 0);
   TX_REM            <= pipe_out_data(DATA_WIDTH+REM_WIDTH-1
                        downto DATA_WIDTH);
   TX_SRC_RDY_N      <= not pipe_out_src_rdy;
   pipe_out_dst_rdy  <= not TX_DST_RDY_N;

   -- -------------------------------------------------------------------------
   --                                  PIPE                                  --
   -- -------------------------------------------------------------------------
   PIPE : entity work.PIPE
   generic map(
      DATA_WIDTH      => PIPE_WIDTH,
      USE_OUTREG      => USE_OUTREG,
      PIPE_TYPE       => PIPE_TYPE,
      FAKE_PIPE       => FAKE_PIPE,
      RESET_BY_INIT   => RESET_BY_INIT
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,

      IN_DATA      => pipe_in_data,
      IN_SRC_RDY   => pipe_in_src_rdy,
      IN_DST_RDY   => pipe_in_dst_rdy,

      OUT_DATA     => pipe_out_data,
      OUT_SRC_RDY  => pipe_out_src_rdy,
      OUT_DST_RDY  => pipe_out_dst_rdy
   );

   -- -------------------------------------------------------------------------
   --                                 DEBUG                                  --
   -- -------------------------------------------------------------------------
   debug_probe_n : entity work.STREAMING_DEBUG_PROBE_N
   port map (
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,
      RX_SOP_N       => RX_SOF_N,
      RX_EOP_N       => RX_EOF_N,
      TX_SRC_RDY_N   => sig_rx_src_rdy_n,
      TX_DST_RDY_N   => sig_rx_dst_rdy_n,
      TX_SOP_N       => sig_rx_sof_n,
      TX_EOP_N       => sig_rx_eof_n,
      DEBUG_BLOCK    => DEBUG_BLOCK,
      DEBUG_DROP     => DEBUG_DROP,
      DEBUG_SRC_RDY  => DEBUG_SRC_RDY,
      DEBUG_DST_RDY  => DEBUG_DST_RDY,
      DEBUG_SOP      => DEBUG_SOP,
      DEBUG_EOP      => DEBUG_EOP
   );
end fl_pipe_arch;

