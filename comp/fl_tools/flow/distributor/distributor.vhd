-- distributor.vhd: FrameLink distributor full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--       + Test behaviour after reset - especially when data comes
--         immediately
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_distributor is

   constant INUM_WIDTH : integer := log2(INTERFACES_COUNT);

   -- width of the RX_REM signal
   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);

   signal tx_if_sel        : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal tx_dst_ready_n     : std_logic;

   signal out_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_rem          : std_logic_vector(REM_WIDTH-1 downto 0);
   signal out_sop_n        : std_logic;
   signal out_eop_n        : std_logic;
   signal out_sof_n        : std_logic;
   signal out_eof_n        : std_logic;
   signal out_src_rdy_n    : std_logic;

begin

   -- assertions of generics
   -- interfaces count must be power of 2
   assert 2 ** log2(INTERFACES_COUNT) = INTERFACES_COUNT and INTERFACES_COUNT > 1
      report "Invalid INTERFACES_COUNT, must be power of 2" severity failure;

   assert DEFAULT_INTERFACE >= 0 and DEFAULT_INTERFACE < INTERFACES_COUNT
      report "Invalid DEFAULT_INTERFACE - out of range" severity failure;

   assert (INUM_OFFSET mod DATA_WIDTH) + INUM_WIDTH < DATA_WIDTH
      report "INTERFACE NUMBER must fit into one word (no split)" severity failure;


-- ----------------------------------------------------------------------------
--                      Generic output multiplexer
-- ----------------------------------------------------------------------------

   output_mux : entity work.fl_distributor_out
   generic map (
      INTERFACES_COUNT => INTERFACES_COUNT,
      DATA_WIDTH => DATA_WIDTH
   )
   port map (
      CLK => CLK,

      RX_DATA => out_data,
      RX_REM => out_rem,
      RX_SRC_RDY_N => out_src_rdy_n,
      RX_DST_RDY_N => tx_dst_ready_n,
      RX_SOP_N => out_sop_n,
      RX_EOP_N => out_eop_n,
      RX_SOF_N => out_sof_n,
      RX_EOF_N => out_eof_n,

      TX_DATA => TX_DATA,
      TX_REM  => TX_REM,
      TX_SRC_RDY_N => TX_SRC_RDY_N,
      TX_DST_RDY_N => TX_DST_RDY_N,
      TX_SOP_N => TX_SOP_N,
      TX_EOP_N => TX_EOP_N,
      TX_SOF_N => TX_SOF_N,
      TX_EOF_N => TX_EOF_N,

      TX_INTERFACE => tx_if_sel
   );


-- ----------------------------------------------------------------------------
--               Distributor for INUM in the first word
-- ----------------------------------------------------------------------------

   gen_when_inum_in_word0:
   if INUM_OFFSET < DATA_WIDTH generate

      inst_word0 : entity work.fl_distributor_ifsel(inum_in_word0)
      generic map (
         INTERFACES_COUNT => INTERFACES_COUNT,
         DATA_WIDTH => DATA_WIDTH,
         INUM_OFFSET => INUM_OFFSET,
         DEFAULT_INTERFACE => DEFAULT_INTERFACE,
         PARTS => PARTS,
         MASK  => MASK
      )
      port map (
         CLK => CLK,
         RESET => RESET,

         RX_DATA => RX_DATA,
         RX_REM => RX_REM,
         RX_SRC_RDY_N => RX_SRC_RDY_N,
         RX_DST_RDY_N => RX_DST_RDY_N,
         RX_SOP_N => RX_SOP_N,
         RX_EOP_N => RX_EOP_N,
         RX_SOF_N => RX_SOF_N,
         RX_EOF_N => RX_EOF_N,

         TX_DATA => out_data,
         TX_REM => out_rem,
         TX_SRC_RDY_N => out_src_rdy_n,
         TX_DST_RDY_N => tx_dst_ready_n,
         TX_SOP_N => out_sop_n,
         TX_EOP_N => out_eop_n,
         TX_SOF_N => out_sof_n,
         TX_EOF_N => out_eof_n,

         TX_INTERFACE => tx_if_sel
      );

   end generate;


-- ----------------------------------------------------------------------------
--               Distributor for INUM in word after the first
-- ----------------------------------------------------------------------------

   gen_when_inum_in_word_non0:
   if INUM_OFFSET >= DATA_WIDTH generate

      inst_word_non0 : entity work.fl_distributor_ifsel(inum_in_word_non0)
      generic map (
         INTERFACES_COUNT => INTERFACES_COUNT,
         DATA_WIDTH => DATA_WIDTH,
         INUM_OFFSET => INUM_OFFSET,
         DEFAULT_INTERFACE => DEFAULT_INTERFACE,
         PARTS => PARTS,
         MASK  => MASK
      )
      port map (
         CLK => CLK,
         RESET => RESET,

         RX_DATA => RX_DATA,
         RX_REM => RX_REM,
         RX_SRC_RDY_N => RX_SRC_RDY_N,
         RX_DST_RDY_N => RX_DST_RDY_N,
         RX_SOP_N => RX_SOP_N,
         RX_EOP_N => RX_EOP_N,
         RX_SOF_N => RX_SOF_N,
         RX_EOF_N => RX_EOF_N,

         TX_DATA => out_data,
         TX_REM => out_rem,
         TX_SRC_RDY_N => out_src_rdy_n,
         TX_DST_RDY_N => tx_dst_ready_n,
         TX_SOP_N => out_sop_n,
         TX_EOP_N => out_eop_n,
         TX_SOF_N => out_sof_n,
         TX_EOF_N => out_eof_n,

         TX_INTERFACE => tx_if_sel
      );

   end generate;

end architecture full;

