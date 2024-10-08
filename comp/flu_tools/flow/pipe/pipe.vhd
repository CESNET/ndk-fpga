--
-- pipe.vhd: FrameLinkUnaligned Pipeline
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               ENTITY DECLARATION
-- ----------------------------------------------------------------------------

entity FLU_PIPE is
   generic(
      -- FrameLinkUnaligned Data Width
      DATA_WIDTH     : integer:= 256;
      SOP_POS_WIDTH  : integer:= 2;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register, optimization of
      --              mapping shreg on Xilinx FPGA can be set using OPT generic
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      PIPE_TYPE      : string  := "REG";
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

      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- ================
      -- Output interface
      -- ================

      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic;

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
end entity FLU_PIPE;

-- ----------------------------------------------------------------------------
--                            ARCHITECTURE DECLARATION
-- ----------------------------------------------------------------------------
architecture flu_pipe_arch of FLU_PIPE is

   constant PIPE_WIDTH        : integer := DATA_WIDTH+SOP_POS_WIDTH+log2(DATA_WIDTH/8)+2;

   signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_in_src_rdy     : std_logic;
   signal pipe_in_dst_rdy     : std_logic;

   signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);
   signal pipe_out_src_rdy    : std_logic;
   signal pipe_out_dst_rdy    : std_logic;

   signal reg_debug_sof_cnt     : std_logic_vector(63 downto 0);
   signal reg_debug_eof_cnt     : std_logic_vector(63 downto 0);
   signal debug_cnt_en          : std_logic;

   signal sig_rx_sop          : std_logic;
   signal sig_rx_eop          : std_logic;

begin
   pipe_in_data      <= RX_DATA & RX_SOP_POS & RX_EOP_POS & sig_rx_sop & sig_rx_eop ;

   TX_DATA           <= pipe_out_data(PIPE_WIDTH-1 downto SOP_POS_WIDTH+log2(DATA_WIDTH/8)+2);
   TX_SOP_POS        <= pipe_out_data(SOP_POS_WIDTH+log2(DATA_WIDTH/8)+1 downto log2(DATA_WIDTH/8)+2);
   TX_EOP_POS        <= pipe_out_data(log2(DATA_WIDTH/8)+1 downto 2);
   TX_SOP            <= pipe_out_data(1);
   TX_EOP            <= pipe_out_data(0);

   TX_SRC_RDY        <= pipe_out_src_rdy;
   pipe_out_dst_rdy  <= TX_DST_RDY;

   -- -------------------------------------------------------------------------
   --                                  PIPE                                  --
   -- -------------------------------------------------------------------------
   PIPE : entity work.PIPE
   generic map(
      DATA_WIDTH      => PIPE_WIDTH,
      PIPE_TYPE       => PIPE_TYPE,
      USE_OUTREG      => USE_OUTREG,
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
   debug_probe : entity work.STREAMING_DEBUG_PROBE
   port map (
      RX_SRC_RDY     => RX_SRC_RDY,
      RX_DST_RDY     => RX_DST_RDY,
      RX_SOP         => RX_SOP,
      RX_EOP         => RX_EOP,
      TX_SRC_RDY     => pipe_in_src_rdy,
      TX_DST_RDY     => pipe_in_dst_rdy,
      TX_SOP         => sig_rx_sop,
      TX_EOP         => sig_rx_eop,
      DEBUG_BLOCK    => DEBUG_BLOCK,
      DEBUG_DROP     => DEBUG_DROP,
      DEBUG_SRC_RDY  => DEBUG_SRC_RDY,
      DEBUG_DST_RDY  => DEBUG_DST_RDY,
      DEBUG_SOP      => DEBUG_SOP,
      DEBUG_EOP      => DEBUG_EOP
   );

end flu_pipe_arch;

