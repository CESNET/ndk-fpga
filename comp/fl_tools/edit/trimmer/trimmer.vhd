-- trimmer.vhd: FrameLink Trimmer architecture
-- Copyright (C) 2007 CESNET
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


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_TRIMMER is

   -- ------------------ Constants declaration --------------------------------


   -- ------------------ Signals declaration ----------------------------------
   -- FL_DEC interface
   signal rx_dst_rdy       : std_logic;
   signal rx_dst_rdy_n_i   : std_logic;
   signal hdr_frame        : std_logic;
   signal sopld            : std_logic;
   signal pld_frame        : std_logic;
   signal eopld            : std_logic;
   signal softr            : std_logic;
   signal ftr_frame        : std_logic;

   -- registers
   signal reg_enable       : std_logic;
   signal reg_enable_we    : std_logic;

   -- multiplexers
   signal mx_rx_dst_rdy_n  : std_logic;
   signal mx_tx_sof_n      : std_logic;
   signal mx_tx_eof_n      : std_logic;
   signal mx_tx_src_rdy_n  : std_logic;

   -- others
   signal trimmer_rx_dst_rdy_n     : std_logic;

   signal trimmer_tx_sof_n         : std_logic;
   signal trimmer_tx_sop_n         : std_logic;
   signal trimmer_tx_eop_n         : std_logic;
   signal trimmer_tx_eof_n         : std_logic;
   signal trimmer_tx_src_rdy_n     : std_logic;
   signal trimmer_tx_dst_rdy_n     : std_logic;
   signal trimmer_tx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal trimmer_tx_rem           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

begin
   -- ------------------ Directly mapped signals ------------------------------
   rx_dst_rdy              <= not trimmer_rx_dst_rdy_n;

   -- FrameLink output ports
   RX_DST_RDY_N         <= mx_rx_dst_rdy_n;

   TX_SOF_N             <= mx_tx_sof_n;
   TX_SOP_N             <= RX_SOP_N;
   TX_EOP_N             <= RX_EOP_N;
   TX_EOF_N             <= mx_tx_eof_n;
   TX_SRC_RDY_N         <= mx_tx_src_rdy_n;
   TX_DATA              <= RX_DATA;
   TX_REM               <= RX_REM;

   -- asserts -----------------------------------------------------------------
   assert(not (TRIM_HEADER and not HEADER))
      report "FL_TRIMMER: You cannot trim header if it is not present in frame!"
      severity error;

   assert(not (TRIM_FOOTER and not FOOTER))
      report "FL_TRIMMER: You cannot trim footer if it is not present in frame!"
      severity error;

   -- trimming logic ----------------------------------------------------------
   GEN_SOF_HDR : if TRIM_HEADER generate
      trimmer_tx_sof_n     <= not sopld;
   end generate;

   GEN_SOF_NOHDR : if not TRIM_HEADER generate
      trimmer_tx_sof_n     <= RX_SOF_N;
   end generate;

   GEN_EOF_FTR : if TRIM_FOOTER generate
      trimmer_tx_eof_n     <= not eopld;
   end generate;

   GEN_EOF_NOFTR : if not TRIM_FOOTER generate
      trimmer_tx_eof_n     <= RX_EOF_N;
   end generate;

   GEN_FC_HDR_FTR : if TRIM_HEADER and TRIM_FOOTER generate
      trimmer_tx_src_rdy_n <= RX_SRC_RDY_N or (not pld_frame);
      trimmer_rx_dst_rdy_n <= TX_DST_RDY_N and pld_frame;
   end generate;

   GEN_FC_HDR : if TRIM_HEADER and not TRIM_FOOTER generate
      trimmer_tx_src_rdy_n <= RX_SRC_RDY_N or hdr_frame;
      trimmer_rx_dst_rdy_n <= TX_DST_RDY_N and (not hdr_frame);
   end generate;

   GEN_FC_FTR : if not TRIM_HEADER and TRIM_FOOTER generate
      trimmer_tx_src_rdy_n <= RX_SRC_RDY_N or ftr_frame;
      trimmer_rx_dst_rdy_n <= TX_DST_RDY_N and (not ftr_frame);
   end generate;

   GEN_FC_NOTRIM : if not TRIM_HEADER and not TRIM_FOOTER generate
      trimmer_tx_src_rdy_n <= RX_SRC_RDY_N;
      trimmer_rx_dst_rdy_n <= TX_DST_RDY_N;
   end generate;
   -- -------------------------------------------------------------------------

   -- AGREGATTOR BYPASS multiplexers ------------------------------------------

   -- multiplex RX_DST_RDY_N
   mx_rx_dst_rdy_np: process(reg_enable, TX_DST_RDY_N, trimmer_rx_dst_rdy_n)
   begin
      case reg_enable is
         when '0' => mx_rx_dst_rdy_n <= TX_DST_RDY_N;
         when '1' => mx_rx_dst_rdy_n <= trimmer_rx_dst_rdy_n;
         when others => mx_rx_dst_rdy_n <= '1';
      end case;
   end process;

   -- multiplex TX_SOF_N
   mx_tx_sof_np: process(reg_enable, RX_SOF_N, trimmer_tx_sof_n)
   begin
      case reg_enable is
         when '0' => mx_tx_sof_n <= RX_SOF_N;
         when '1' => mx_tx_sof_n <= trimmer_tx_sof_n;
         when others => mx_tx_sof_n <= '1';
      end case;
   end process;

   -- multiplex TX_EOF_N
   mx_tx_eof_np: process(reg_enable, RX_EOF_N, trimmer_tx_eof_n)
   begin
      case reg_enable is
         when '0' => mx_tx_eof_n <= RX_EOF_N;
         when '1' => mx_tx_eof_n <= trimmer_tx_eof_n;
         when others => mx_tx_eof_n <= '1';
      end case;
   end process;

   -- multiplex TX_SRC_RDY_N
   mx_tx_src_rdy_np: process(reg_enable, RX_SRC_RDY_N, trimmer_tx_src_rdy_n)
   begin
      case reg_enable is
         when '0' => mx_tx_src_rdy_n <= RX_SRC_RDY_N;
         when '1' => mx_tx_src_rdy_n <= trimmer_tx_src_rdy_n;
         when others => mx_tx_src_rdy_n <= '1';
      end case;
   end process;
   -- -------------------------------------------------------------------------

   -- register reg_enable - enable FL_TRIMMER
   reg_enablep:process (CLK)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            reg_enable <= '0';
         else
            reg_enable <= ENABLE;
         end if;
      end if;
   end process;

   -- decoder
   DECODER_I : entity work.FL_DEC
      generic map(
         -- Header data present
         HEADER      => HEADER,
         -- Footer data present
         FOOTER      => FOOTER
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         -- FrameLink interface
         SOF_N       => RX_SOF_N,
         SOP_N       => RX_SOP_N,
         EOP_N       => RX_EOP_N,
         EOF_N       => RX_EOF_N,
         SRC_RDY_N   => RX_SRC_RDY_N,
         DST_RDY_N   => open,
         -- decoder signals
         SOF         => open,
         SOHDR       => open,
         EOHDR       => open,
         HDR_FRAME   => hdr_frame,
         SOPLD       => sopld,
         EOPLD       => eopld,
         PLD_FRAME   => pld_frame,
         SOFTR       => softr,
         EOFTR       => open,
         FTR_FRAME   => ftr_frame,
         EOF         => open,
         SRC_RDY     => open,
         DST_RDY     => rx_dst_rdy
      );

end architecture full;
