-- hins_plus.vhd
--!
--! \file
--! \brief FLU plus header insert full architecture
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! \name  FLU plus header insert full architecture
architecture full of HINS_PLUS is
  signal channel_reg : std_logic_vector(max(1,log2(RX_CHANNELS))-1 downto 0);
  signal reg_vld     : std_logic;
  signal sig_rx_dst_rdy : std_logic;
  signal sig_tx_src_rdy : std_logic;
  signal sig_tx_sop     : std_logic;
  signal valid_rx_sop   : std_logic;
  signal valid_tx_sop   : std_logic;
begin
  main_hins : entity work.HINS
    generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      HDR_WIDTH      => HDR_WIDTH
    ) port map (
      CLK            => CLK,
      RESET          => RESET,
      RX_DATA        => RX_DATA,
      RX_SOP_POS     => RX_SOP_POS,
      RX_EOP_POS     => RX_EOP_POS,
      RX_SOP         => RX_SOP,
      RX_EOP         => RX_EOP,
      RX_SRC_RDY     => RX_SRC_RDY,
      RX_DST_RDY     => sig_RX_DST_RDY,
      HDR_DATA       => HDR_DATA,
      HDR_READY      => HDR_READY,
      HDR_NEXT       => HDR_NEXT,
      TX_DATA        => TX_DATA,
      TX_SOP_POS     => TX_SOP_POS,
      TX_EOP_POS     => TX_EOP_POS,
      TX_SOP         => sig_TX_SOP,
      TX_EOP         => TX_EOP,
      TX_SRC_RDY     => sig_TX_SRC_RDY,
      TX_DST_RDY     => TX_DST_RDY
    );
  RX_DST_RDY <= sig_rx_dst_rdy;
  TX_SRC_RDY <= sig_tx_src_rdy;
  TX_SOP     <= sig_tx_sop;

  TX_CHANNEL <= channel_reg when reg_vld='1' else RX_CHANNEL;
  channel_register : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RX_SRC_RDY='1' and sig_rx_dst_rdy='1' then
        channel_reg <= RX_CHANNEL;
      end if;
    end if;
  end process;
  valid_register : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (valid_tx_sop='1' and valid_rx_sop='0') then
        reg_vld <= '0';
      elsif valid_rx_sop='1' and valid_tx_sop='0' then
        reg_vld <= '1';
      end if;
    end if;
  end process;
  valid_rx_sop <= RX_SOP     and RX_SRC_RDY     and sig_rx_dst_rdy;
  valid_tx_sop <= sig_tx_sop and sig_tx_src_rdy and TX_DST_RDY;

end architecture;

