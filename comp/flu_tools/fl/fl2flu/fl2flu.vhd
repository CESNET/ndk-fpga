-- fl2flu.vhd: Top level entity for FL to FLU converter
-- Copyright (C) 2012 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl2flu is
   generic(
      -- data width of input FL and output FLU interfaces
      DATA_WIDTH : integer := 256;
      -- sop_pos width of input FLU
      SOP_POS_WIDTH  : integer := 2;
      -- use input pipe
      IN_PIPE_EN           : boolean := false;
      -- use output register of input pipe
      IN_PIPE_OUTREG       : boolean := false;
      -- use output pipe
      OUT_PIPE_EN          : boolean := false;
      -- use output register of input pipe
      OUT_PIPE_OUTREG      : boolean := false
   );
   port(
      -- common interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface (FL)
      RX_SOF_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0);

      -- output interface (FLU)
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
     );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl2flu is
   -- Input pipeline
   signal in_pipe_rx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_pipe_rx_drem     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_pipe_rx_src_rdy_n: std_logic;
   signal in_pipe_rx_dst_rdy_n: std_logic;
   signal in_pipe_rx_sof_n    : std_logic;
   signal in_pipe_rx_eof_n    : std_logic;
   signal in_pipe_rx_sop_n    : std_logic;
   signal in_pipe_rx_eop_n    : std_logic;

   -- Output pipeline
   signal out_pipe_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_pipe_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal out_pipe_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal out_pipe_sop        : std_logic;
   signal out_pipe_eop        : std_logic;
   signal out_pipe_src_rdy    : std_logic;
   signal out_pipe_dst_rdy    : std_logic;
begin
   -- connection and conversion
   out_pipe_data    <= in_pipe_rx_data;
   out_pipe_sop_pos <= (others => '0');
   out_pipe_eop_pos <= in_pipe_rx_drem;
   out_pipe_sop     <= not in_pipe_rx_sof_n;
   out_pipe_eop     <= not in_pipe_rx_eof_n;
   out_pipe_src_rdy <= not in_pipe_rx_src_rdy_n;
   in_pipe_rx_dst_rdy_n <= not out_pipe_dst_rdy;


   -- -------------------------------------------------------------------------------
   -- PIPES
   -- -------------------------------------------------------------------------------
   -- Input Pipe (FL)
   use_inpipe_gen : if IN_PIPE_EN generate
   in_pipe_i : entity work.FL_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      USE_OUTREG     => IN_PIPE_OUTREG
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- Input interf
      RX_SOF_N       => RX_SOF_N,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_EOF_N       => RX_EOF_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,
      RX_DATA        => RX_DATA,
      RX_REM         => RX_REM,
      -- Output inter
      TX_SOF_N       => in_pipe_rx_sof_n,
      TX_SOP_N       => in_pipe_rx_sop_n,
      TX_EOP_N       => in_pipe_rx_eop_n,
      TX_EOF_N       => in_pipe_rx_eof_n,
      TX_SRC_RDY_N   => in_pipe_rx_src_rdy_n,
      TX_DST_RDY_N   => in_pipe_rx_dst_rdy_n,
      TX_DATA        => in_pipe_rx_data,
      TX_REM         => in_pipe_rx_drem
   );
   end generate;
   no_use_inpipe_gen : if not IN_PIPE_EN generate
      in_pipe_rx_data      <= RX_DATA;
      in_pipe_rx_drem      <= RX_REM;
      in_pipe_rx_src_rdy_n <= RX_SRC_RDY_N;
      in_pipe_rx_sof_n     <= RX_SOF_N;
      in_pipe_rx_eof_n     <= RX_EOF_N;
      in_pipe_rx_sop_n     <= RX_SOP_N;
      in_pipe_rx_eop_n     <= RX_EOP_N;
      RX_DST_RDY_N         <= in_pipe_rx_dst_rdy_n;
   end generate;


   -- Output Pipe (FLU)
   out_pipe_i : entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_OUTREG     => OUT_PIPE_OUTREG,
      FAKE_PIPE      => not OUT_PIPE_EN
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- Input interf
      RX_DATA       => out_pipe_data,
      RX_SOP_POS    => out_pipe_sop_pos,
      RX_EOP_POS    => out_pipe_eop_pos,
      RX_SOP        => out_pipe_sop,
      RX_EOP        => out_pipe_eop,
      RX_SRC_RDY    => out_pipe_src_rdy,
      RX_DST_RDY    => out_pipe_dst_rdy,
      -- Output interf
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY
   );
end architecture;
