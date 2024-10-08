-- fifo_arch.vhd: Multi-Value Bus generic FIFO (full architecture)
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;



architecture full of MVB_FIFO is

  constant FIFO_WIDTH : integer := ITEMS * ITEM_WIDTH + ITEMS;

  signal rx_data_vec, tx_data_vec : std_logic_vector(FIFO_WIDTH-1 downto 0);
  signal we, fifo_full : std_logic;
  signal re, fifo_empty : std_logic;
  signal fifo_vld : std_logic;

begin

  real_fifo_gen : if USE_DST_RDY generate
    -- Main FIFO implementation
    bram_outreg_gen : if USE_BRAMS generate
      fifo_core : entity work.fifo_bram
      generic map(
        STATUS_ENABLED => STATUS_ENABLED,
        ITEMS       => FIFO_ITEMS,
        BLOCK_SIZE  => BLOCK_SIZE,
        DATA_WIDTH  => FIFO_WIDTH,
        DO_REG      => OUTPUT_REG,
        AUTO_PIPELINE => true
      ) port map(
        CLK         => CLK,
        RESET       => RESET,
        DI          => rx_data_vec,
        WR          => we,
        FULL        => fifo_full,
        LSTBLK      => LSTBLK,
        STATUS      => STATUS,
        DO          => tx_data_vec,
        RD          => re,
        EMPTY       => fifo_empty,
        DV          => fifo_vld
      );
    end generate;
    distmem_gen : if not USE_BRAMS generate
      fifo_core : entity work.fifo
      generic map(
        STATUS_ENABLED => STATUS_ENABLED,
        ITEMS          => FIFO_ITEMS,
        BLOCK_SIZE     => BLOCK_SIZE,
        DATA_WIDTH     => FIFO_WIDTH,
        DO_REG         => OUTPUT_REG
      ) port map(
        CLK            => CLK,
        RESET          => RESET,
        DATA_IN        => rx_data_vec,
        WRITE_REQ      => we,
        FULL           => fifo_full,
        LSTBLK         => LSTBLK,
        STATUS         => STATUS,
        DATA_OUT       => tx_data_vec,
        READ_REQ       => re,
        EMPTY          => fifo_empty
      );
      fifo_vld <= not fifo_empty;
    end generate;


    -- Connections with entity
    we <= RX_SRC_RDY and not fifo_full;
    re <= TX_DST_RDY or not fifo_vld;

    rx_data_vec <= RX_DATA & RX_VLD;
    RX_DST_RDY <= not fifo_full;

    TX_DATA <= tx_data_vec(FIFO_WIDTH-1 downto ITEMS);
    TX_VLD <= tx_data_vec(ITEMS-1 downto 0);
    TX_SRC_RDY <= fifo_vld;

    EMPTY <= fifo_empty;
    FULL <= fifo_full;
  end generate;

  fake_fifo_gen : if not USE_DST_RDY generate
    TX_DATA <= RX_DATA;
    TX_VLD <= RX_VLD;
    TX_SRC_RDY <= RX_SRC_RDY;
    RX_DST_RDY <= '1';
    STATUS <= (others => '0');
    LSTBLK <= '0';
    FULL <= '0';
    EMPTY <= not RX_SRC_RDY;
  end generate;

end architecture;
