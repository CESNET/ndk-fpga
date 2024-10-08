--
-- flu_multiplexer_packet.vhd: Multiplexer for Frame Link Unaligned (packet oriented!)
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

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_MULTIPLEXER_PACKET is
   generic(
       DATA_WIDTH     : integer := 256;
       SOP_POS_WIDTH  : integer := 2;
       INPUT_PORTS    : integer := 2;
       -- is multiplexer blocking or not
         -- when TRUE:  not selected ports are blocked
         -- when FALSE: not selected ports discard packets at the same rate as selected one forwarding
         --             something like exclusive packet selection
       BLOCKING       : boolean := true
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      SEL            : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
      SEL_READY      : in std_logic;
      SEL_NEXT       : out std_logic;

      -- Frame Link Unaligned input interfaces
      RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      -- Frame Link Unaligned concentrated interface
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
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH of FLU_MULTIPLEXER_PACKET is
   constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);

   signal mx_RX_DST_RDY  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal mx_RX_SRC_RDY  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_sop_detect  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_sop_detect_all : std_logic;

   signal mux_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_sop_pos    : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal mux_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal mux_sop        : std_logic;
   signal mux_eop        : std_logic;
   signal mux_src_rdy    : std_logic;
   signal mux_dst_rdy    : std_logic;

   signal sig_tx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sig_tx_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal sig_tx_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal sig_tx_sop        : std_logic;
   signal sig_tx_eop        : std_logic;
   signal sig_tx_src_rdy    : std_logic;
   signal sig_tx_dst_rdy    : std_logic;

   signal rx_sel         : std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
   signal sel_reg        : std_logic_vector(log2(INPUT_PORTS)-1 downto 0) := (others => '0');
   signal sig_sel_next   : std_logic;
   signal sel_nochange   : std_logic;

   signal sop_after_eop   : std_logic;
   signal eop_sent        : std_logic;
   signal sop_detect      : std_logic;
   signal sop_valid       : std_logic;
   signal tx_valid        : std_logic;
begin
   -- basic MUX connection
   rx_mx_i : entity work.FLU_MULTIPLEXER
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      INPUT_PORTS    => INPUT_PORTS,
      BLOCKING       => BLOCKING
   ) port map (
      RESET   => RESET,
      CLK     => CLK,
      SEL     => rx_sel,

      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => mx_RX_SRC_RDY,
      RX_DST_RDY    => mx_RX_DST_RDY,

      TX_DATA       => mux_data,
      TX_SOP_POS    => mux_sop_pos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH),
      TX_EOP_POS    => mux_eop_pos,
      TX_SOP        => mux_sop,
      TX_EOP        => mux_eop,
      TX_SRC_RDY    => mux_src_rdy,
      TX_DST_RDY    => mux_dst_rdy
   );
   SEL_NEXT <= sig_sel_next;
   mux_sop_pos_augment : if EOP_POS_WIDTH > SOP_POS_WIDTH generate
      mux_sop_pos(EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0) <= (others => '0');
   end generate;

   process(CLK)
   begin
      if CLK'event and CLK='1' then
         if sig_sel_next='1' then
            sel_reg <= SEL;
         end if;
      end if;
   end process;
   sig_sel_next <= sop_valid and tx_valid;
   rx_sel       <= SEL when eop_sent='1' and SEL_READY='1' else sel_reg;
   sel_nochange <= '1' when SEL=sel_reg and SEL_READY='1' else '0';

   sop_after_eop  <= '1' when mux_sop_pos > mux_eop_pos else '0';
   sop_detect     <= mux_sop and mux_src_rdy and (sel_nochange or eop_sent);
   tx_valid       <= sig_tx_dst_rdy and sig_tx_src_rdy;
   sop_valid      <= sop_detect and SEL_READY;

   process(CLK)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            eop_sent <= '1';
         elsif tx_valid='1' then
            eop_sent <= sig_tx_eop and not (sop_after_eop and sig_tx_sop);
         end if;
      end if;
   end process;

   sig_tx_data    <= mux_data;
   sig_tx_sop_pos <= mux_sop_pos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH);
   sig_tx_eop_pos <= mux_eop_pos;
   sig_tx_sop     <= sop_detect;
   sig_tx_eop     <= mux_eop when eop_sent='0' else (mux_eop and not(sop_after_eop and mux_sop));
   sig_tx_src_rdy <= mux_src_rdy and not(sop_detect and not SEL_READY);
   mux_dst_rdy    <= sig_tx_dst_rdy and not(sop_detect and not SEL_READY) and (eop_sent or sel_nochange or not mux_sop or not sop_after_eop);

   TX_DATA        <= sig_tx_data;
   TX_SOP_POS     <= sig_tx_sop_pos;
   TX_EOP_POS     <= sig_tx_eop_pos;
   TX_SOP         <= sig_tx_sop;
   TX_EOP         <= sig_tx_eop;
   TX_SRC_RDY     <= sig_tx_src_rdy;
   sig_tx_dst_rdy <= TX_DST_RDY;


   blocking_gen : if BLOCKING=true generate -- no special treatment of blocked ports needed
      RX_DST_RDY    <= mx_RX_DST_RDY;
      mx_RX_SRC_RDY <= RX_SRC_RDY;
   end generate;

   nonblocking_gen : if BLOCKING=false generate
      rx_dst_rdy_gen : for i in 0 to INPUT_PORTS-1 generate
         RX_DST_RDY(i)    <= mx_RX_DST_RDY(i) and not(rx_sop_detect(i) and not (rx_sop_detect_all and mux_dst_rdy));
         mx_RX_SRC_RDY(i) <= RX_SRC_RDY(i)    and not(rx_sop_detect(i) and not rx_sop_detect_all);
         rx_sop_detect(i) <= RX_SOP(i) and RX_SRC_RDY(i);
      end generate;

      rx_sop_detect_all_i : process(rx_sop_detect)
         variable and_sop : std_logic;
      begin
         and_sop := '1';
         for k in 0 to INPUT_PORTS-1 loop
            and_sop := and_sop and rx_sop_detect(k);
         end loop;
         rx_sop_detect_all <= and_sop;
      end process;
   end generate;

end architecture;
