--
-- binder_stupid.vhd: Binder N-1 component for Frame Link Unaligned (basic easy implementation)
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_misc.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture STUPID of FLU_BINDER is
   constant EOP_POS_WIDTH : integer:=log2(DATA_WIDTH/8);
   constant INUM_WIDTH    : integer:=log2(INPUT_PORTS);

   signal rr_cnt_decoded  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rr_masked       : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal inum_rr_ready   : std_logic;
   signal inum            : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal inum_ready      : std_logic;
   signal inum_next       : std_logic;
   signal inum_base       : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal inum_rr         : std_logic_vector(INUM_WIDTH-1 downto 0);

begin
   -- basic packet MUX connection
   rx_mx_i : entity work.FLU_MULTIPLEXER_PACKET
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      INPUT_PORTS    => INPUT_PORTS
   ) port map (
      RESET   => RESET,
      CLK     => CLK,

      SEL       => inum,
      SEL_READY => inum_ready,
      SEL_NEXT  => inum_next,

      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,

      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY
   );

   rr_cnt_i : process(CLK)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            rr_cnt_decoded <= conv_std_logic_vector(1,INPUT_PORTS);
         elsif inum_ready='1' and inum_next='1' then
            rr_cnt_decoded <= rr_cnt_decoded(0) & rr_cnt_decoded(INPUT_PORTS-1 downto 1);
         end if;
      end if;
   end process;
   rr_masked <= RX_SRC_RDY and rr_cnt_decoded;
   inum_rr_ready <= or_reduce(rr_masked);

   inum <= inum_rr when inum_rr_ready='1' else inum_base;
   inum_ready <= or_reduce(RX_SRC_RDY);

   inum_base_enc : entity work.GEN_ENC
      generic map (INPUT_PORTS)
      port map (RX_SRC_RDY, inum_base);
   inum_rr_enc : entity work.GEN_ENC
      generic map (INPUT_PORTS)
      port map (rr_masked, inum_rr);

end architecture;
