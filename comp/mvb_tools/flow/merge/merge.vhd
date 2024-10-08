-- merge.vhd: Merge of multiple Single-Value Buses into one Multi-Value Bus
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;



entity MVB_MERGE is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    USE_DST_RDY    : boolean := true
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_SRC_RDY    : in std_logic_vector(ITEMS-1 downto 0);
    RX_DST_RDY    : out std_logic_vector(ITEMS-1 downto 0);

    TX_DATA       : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX_VLD        : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;



architecture arch of MVB_MERGE is


begin

  TX_DATA <= RX_DATA;
  TX_VLD <= RX_SRC_RDY;
  TX_SRC_RDY <= or_reduce(RX_SRC_RDY);
  use_dst_rdy_gen : if USE_DST_RDY generate
    RX_DST_RDY <= (ITEMS-1 downto 0 => TX_DST_RDY);
  end generate;
  no_dst_rdy_gen : if not USE_DST_RDY generate
    RX_DST_RDY <= (ITEMS-1 downto 0 => '1');
  end generate;

end architecture;
