-- transformer.vhd: Implementation of FrameLinkUnaligned Transformer component.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- library containing log2 function
use work.math_pack.all;

architecture full of FLU_TRANSFORMER is
  signal rx_sop_pos_augment : std_logic_vector(TX_SOP_POS_WIDTH downto 0);
begin
  -- asserts over generics
  assert ((RX_DATA_WIDTH/(2**RX_SOP_POS_WIDTH))>=(TX_DATA_WIDTH/(2**TX_SOP_POS_WIDTH)))
    report "FLU_TRANSFORMER: Unsupported combination of RX and TX SOP_POS_WIDTH."
    severity error;
  assert (2**log2(RX_DATA_WIDTH)=RX_DATA_WIDTH and RX_DATA_WIDTH>4)
    report "FLU_TRANSFORMER: RX_DATA_WIDTH must be power of 2 and higher than 4."
    severity error;
  assert (2**log2(TX_DATA_WIDTH)=TX_DATA_WIDTH and TX_DATA_WIDTH>4)
    report "FLU_TRANSFORMER: TX_DATA_WIDTH must be power of 2 and higher than 4."
    severity error;
  assert (RX_SOP_POS_WIDTH<=log2(RX_DATA_WIDTH/8))
    report "FLU_TRANSFORMER: RX_SOP_POS_WIDTH cannot exceed log2(RX_DATA_WIDTH/8)."
    severity error;
  assert (TX_SOP_POS_WIDTH<=log2(TX_DATA_WIDTH/8))
    report "FLU_TRANSFORMER: TX_SOP_POS_WIDTH cannot exceed log2(TX_DATA_WIDTH/8)."
    severity error;

  -- data widths are equal
  GEN_ARCH_EQUAL: if (RX_DATA_WIDTH = TX_DATA_WIDTH) generate
    rx_sop_pos_augment <= RX_SOP_POS & (TX_SOP_POS_WIDTH-RX_SOP_POS_WIDTH downto 0 => '0');
    TX_DATA    <= RX_DATA;
    TX_SOP_POS <= rx_sop_pos_augment(TX_SOP_POS_WIDTH downto 1);
    TX_EOP_POS <= RX_EOP_POS;
    TX_SOP     <= RX_SOP;
    TX_EOP     <= RX_EOP;
    TX_SRC_RDY <= RX_SRC_RDY;
    RX_DST_RDY <= TX_DST_RDY;
  end generate;

  -- RX data width > TX data width
  GEN_ARCH_DOWN: if (RX_DATA_WIDTH > TX_DATA_WIDTH) generate
    FLU_TRANSFORMER_DOWN_U: entity work.FLU_TRANSFORMER_DOWN
      generic map (
        RX_DATA_WIDTH    => RX_DATA_WIDTH,
        RX_SOP_POS_WIDTH => RX_SOP_POS_WIDTH,
        TX_DATA_WIDTH    => TX_DATA_WIDTH,
        TX_SOP_POS_WIDTH => TX_SOP_POS_WIDTH
      ) port map (
        CLK           => CLK,
        RESET         => RESET,
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
  end generate;

  -- RX data width < TX data width
  GEN_ARCH_UP: if (RX_DATA_WIDTH < TX_DATA_WIDTH) generate
    FLU_TRANSFORMER_UP_U: entity work.FLU_TRANSFORMER_UP
      generic map (
        RX_DATA_WIDTH    => RX_DATA_WIDTH,
        RX_SOP_POS_WIDTH => RX_SOP_POS_WIDTH,
        TX_DATA_WIDTH    => TX_DATA_WIDTH,
        TX_SOP_POS_WIDTH => TX_SOP_POS_WIDTH
      ) port map (
        CLK           => CLK,
        RESET         => RESET,
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
  end generate;

end architecture;
