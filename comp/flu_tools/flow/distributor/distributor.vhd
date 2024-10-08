-- distributor.vhd: Frame Link Unaligned distributor full architecture.
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
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
architecture full of flu_distributor is
   constant EOP_POS_WIDTH : integer:=log2(DATA_WIDTH/8);
   constant INUM_WIDTH    : integer:=OUTPUT_PORTS;

   -- distribution control interface
   signal inum_reg        : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal sig_inum_next   : std_logic;
   signal inum_sop        : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal inum_eop        : std_logic_vector(INUM_WIDTH-1 downto 0);

   -- FLU control
   signal sop_pos_augment : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal sop_after_eop   : std_logic;
   signal eop_detect      : std_logic;
   signal sop_detect      : std_logic;
   signal sop_valid       : std_logic;
   signal rx_valid        : std_logic;
   signal sig_rx_dst_rdy  : std_logic;

   -- output control
   signal out_rdy_all     : std_logic;
   signal out_rdy         : std_logic_vector(OUTPUT_PORTS-1 downto 0);
   signal out_sel         : std_logic_vector(OUTPUT_PORTS-1 downto 0);
   signal data_sent       : std_logic_vector(OUTPUT_PORTS-1 downto 0);
   signal sig_tx_src_rdy  : std_logic_vector(OUTPUT_PORTS-1 downto 0);

begin
   -- INUM -------------------------------------------------------------
   process(CLK,RESET)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            inum_reg <= (others => '0');
         elsif sig_inum_next='1' then
            inum_reg <= INUM_MASK;
         end if;
      end if;
   end process;
   sig_inum_next <= sop_valid and rx_valid;
   inum_sop      <= INUM_MASK;
   inum_eop      <= INUM_MASK when sop_after_eop='0' and sop_detect='1' else inum_reg;
   INUM_NEXT     <= sig_inum_next;


   -- FLU in control ----------------------------------------------------
   sop_pos_augment_gen : if EOP_POS_WIDTH > SOP_POS_WIDTH generate
      sop_pos_augment <= RX_SOP_POS & (EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0 => '0');
   end generate;
   sop_pos_augment_fake_gen : if EOP_POS_WIDTH = SOP_POS_WIDTH generate
      sop_pos_augment <= RX_SOP_POS;
   end generate;
   sop_after_eop  <= '1' when sop_pos_augment > RX_EOP_POS else '0';
   eop_detect     <= RX_EOP and RX_SRC_RDY;
   sop_detect     <= RX_SOP and RX_SRC_RDY;
   rx_valid       <= RX_SRC_RDY and sig_rx_dst_rdy;
   sop_valid      <= sop_detect and INUM_READY;
   sig_rx_dst_rdy <= (INUM_READY or not sop_detect) and out_rdy_all;


   -- FLU out control ---------------------------------------------------
   process(out_rdy)
   variable and_int : std_logic;
   begin
      and_int := '1';
      for i in 0 to OUTPUT_PORTS-1 loop
         and_int := and_int and out_rdy(i);
      end loop;
      out_rdy_all <= and_int;
   end process;
   out_rdy_gen : for i in 0 to OUTPUT_PORTS-1 generate
      out_sel(i) <= (inum_sop(i) and sop_detect) OR                   -- selected because of SOP *OR*
                    (inum_eop(i) and (eop_detect or not sop_detect)); -- selected because of EOP (or nothing)
      out_rdy(i) <= not out_sel(i) OR   -- not selected      *OR*
                    data_sent(i) OR     -- data already sent *OR*
                    TX_DST_RDY(i);      -- data ready to send
      sig_tx_src_rdy(i) <= RX_SRC_RDY AND                     -- data from SRC ready     *AND*
                           (INUM_READY or not sop_detect) AND -- SOP not blocked by INUM *AND*
                           out_sel(i) AND                     -- selected for output     *AND*
                           not data_sent(i);                  -- data hasn't been already sent
      process(CLK,RESET)
      begin
         if CLK'event and CLK='1' then
            if RESET='1' then
               data_sent(i) <= '0';
            elsif rx_valid='1' then
               data_sent(i) <= '0';
            elsif TX_DST_RDY(i)='1' and sig_tx_src_rdy(i)='1' then
               data_sent(i) <= '1';
            end if;
         end if;
      end process;
   end generate;


   -- RX & TX connection ------------------------------------------------
   RX_TX_connection_gen: for i in 1 to OUTPUT_PORTS generate
      TX_DATA(i*DATA_WIDTH-1 downto (i-1)*DATA_WIDTH)         <= RX_DATA;
      TX_SOP_POS(i*SOP_POS_WIDTH-1 downto (i-1)*SOP_POS_WIDTH)<= RX_SOP_POS;
      TX_EOP_POS(i*EOP_POS_WIDTH-1 downto (i-1)*EOP_POS_WIDTH)<= RX_EOP_POS;
      TX_SOP(i-1) <= inum_sop(i-1) and sop_detect;
      TX_EOP(i-1) <= inum_eop(i-1) and eop_detect;
   end generate;
   RX_DST_RDY <= sig_rx_dst_rdy;
   TX_SRC_RDY <= sig_tx_src_rdy;

end architecture full;

