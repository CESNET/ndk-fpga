-- binder_stupid.vhd: FrameLink STUPID Binder architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Jiří Novotňák <xnovot87@liberouter.org>
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
entity FL_BINDER_STUPID is
   generic(
      INPUT_WIDTH    : integer;
      INPUT_COUNT    : integer;
      OUTPUT_WIDTH   : integer;
      FRAME_PARTS    : integer;
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := round_robin
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1
                                                          downto 0);
      RX_REM         : in  std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                          downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)
   );
end entity FL_BINDER_STUPID;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER_STUPID is

   -- ------------------ Constants declaration --------------------------------
   constant STATUS_WIDTH         : integer := 1;

   -- ------------------ Signals declaration ----------------------------------
   signal in_rx_sof_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_sop_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_eop_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_eof_n     : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_src_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_dst_rdy_n : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal in_rx_data      : std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1
                                                              downto 0);
   signal in_rx_rem       : std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                              downto 0);

   signal out_tx_sof_n      : std_logic;
   signal out_tx_sop_n      : std_logic;
   signal out_tx_eop_n      : std_logic;
   signal out_tx_eof_n      : std_logic;
   signal out_tx_src_rdy_n  : std_logic;
   signal out_tx_dst_rdy_n  : std_logic;
   signal out_tx_data       : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal out_tx_rem        : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

   signal status            : std_logic_vector(INPUT_COUNT*STATUS_WIDTH-1 downto 0);
   signal empty             : std_logic_vector(INPUT_COUNT-1 downto 0);


   signal mx_ifc_sof_n      : std_logic;
   signal mx_ifc_sop_n      : std_logic;
   signal mx_ifc_eop_n      : std_logic;
   signal mx_ifc_eof_n      : std_logic;
   signal mx_ifc_src_rdy_n  : std_logic;
   signal mx_ifc_dst_rdy_n  : std_logic;
   signal mx_ifc_data       : std_logic_vector(OUTPUT_WIDTH-1 downto 0);
   signal mx_ifc_rem        : std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

   signal mx_ifc_sel        : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);

   signal fc_frame_rdy      : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal fc_no_frame       : std_logic;


begin
-- ============================================================================
--                               Assertions
-- ============================================================================
   assert (INPUT_WIDTH = OUTPUT_WIDTH)
      report "INPUTs and OUTPUT have to have the same width"
      severity failure;

-- ============================================================================
--                              Mapped signals
-- ============================================================================
   in_rx_sof_n       <= RX_SOF_N;
   in_rx_sop_n       <= RX_SOP_N;
   in_rx_eop_n       <= RX_EOP_N;
   in_rx_eof_n       <= RX_EOF_N;
   in_rx_src_rdy_n   <= RX_SRC_RDY_N;
   RX_DST_RDY_N      <= in_rx_dst_rdy_n;
   in_rx_data        <= RX_DATA;
   in_rx_rem         <= RX_REM;

   TX_SOF_N          <= out_tx_sof_n;
   TX_SOP_N          <= out_tx_sop_n;
   TX_EOP_N          <= out_tx_eop_n;
   TX_EOF_N          <= out_tx_eof_n;
   TX_SRC_RDY_N      <= out_tx_src_rdy_n;
   out_tx_dst_rdy_n  <= TX_DST_RDY_N;
   TX_DATA           <= out_tx_data;
   TX_REM            <= out_tx_rem;

   -- control signals
   status            <= (others => '0');
   empty             <= in_rx_src_rdy_n;
   fc_frame_rdy      <= not in_rx_src_rdy_n;

   noframe_genand: process(fc_frame_rdy)
   begin
      fc_no_frame <= '1';
      for i in 0 to INPUT_COUNT-1 loop
         if (fc_frame_rdy(i) = '1') then
            fc_no_frame <= '0';
         end if;
      end loop;
   end process;

-- ============================================================================
--
-- ============================================================================
   OUTPUT_BLOCK : entity work.FLB_OUTPUT(round_robin)
      generic map(
         OUTPUT_WIDTH   => OUTPUT_WIDTH,
         STATUS_WIDTH   => STATUS_WIDTH,
         COUNT          => INPUT_COUNT,
         QUEUE_CHOOSING => QUEUE_CHOOSING,
         LOW_STATUS_LOW_SPACE => true
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Data transformation block interface
         RX_SOF_N       => mx_ifc_sof_n,
         RX_SOP_N       => mx_ifc_sop_n,
         RX_EOP_N       => mx_ifc_eop_n,
         RX_EOF_N       => mx_ifc_eof_n,
         RX_SRC_RDY_N   => mx_ifc_src_rdy_n,
         RX_DST_RDY_N   => mx_ifc_dst_rdy_n,
         RX_DATA        => mx_ifc_data,
         RX_REM         => mx_ifc_rem,
         STATUS         => status,
         EMPTY          => empty,
         IFC            => mx_ifc_sel,

         -- FrameLink Binder output
         TX_SOF_N       => out_tx_sof_n,
         TX_SOP_N       => out_tx_sop_n,
         TX_EOP_N       => out_tx_eop_n,
         TX_EOF_N       => out_tx_eof_n,
         TX_SRC_RDY_N   => out_tx_src_rdy_n,
         TX_DST_RDY_N   => out_tx_dst_rdy_n,
         TX_DATA        => out_tx_data,
         TX_REM         => out_tx_rem,

         -- Frame Counters' output
         FRAME_RDY      => fc_frame_rdy,
         NO_FRAME       => fc_no_frame
      );

-- ============================================================================
--                              Bind multiplexor
-- ============================================================================
   bind_mx: process(mx_ifc_sel, in_rx_sof_n, in_rx_sop_n, in_rx_eop_n,
         in_rx_eof_n, in_rx_src_rdy_n, mx_ifc_dst_rdy_n, in_rx_data, in_rx_rem)
   begin
      in_rx_dst_rdy_n   <= (others => '1');

      mx_ifc_sof_n       <= in_rx_sof_n(conv_integer(mx_ifc_sel));
      mx_ifc_sop_n       <= in_rx_sop_n(conv_integer(mx_ifc_sel));
      mx_ifc_eop_n       <= in_rx_eop_n(conv_integer(mx_ifc_sel));
      mx_ifc_eof_n       <= in_rx_eof_n(conv_integer(mx_ifc_sel));
      mx_ifc_src_rdy_n   <= in_rx_src_rdy_n(conv_integer(mx_ifc_sel));
      in_rx_dst_rdy_n(conv_integer(mx_ifc_sel)) <= mx_ifc_dst_rdy_n;
   end process;

   DATA_MUX : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => INPUT_WIDTH,
         MUX_WIDTH   => INPUT_COUNT
      )
      port map(
         DATA_IN     => in_rx_data,
         SEL         => mx_ifc_sel,
         DATA_OUT    => mx_ifc_data
      );

   REM_MUX : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => mx_ifc_rem'length,
         MUX_WIDTH   => INPUT_COUNT
      )
      port map(
         DATA_IN     => in_rx_rem,
         SEL         => mx_ifc_sel,
         DATA_OUT    => mx_ifc_rem
      );

end architecture full;
