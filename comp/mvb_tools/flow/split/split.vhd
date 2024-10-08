-- split.vhd: Split of Multi-Value Bus into multiple Single-Value Buses
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



entity MVB_SPLIT is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    USE_DST_RDY    : boolean := true
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX_DATA       : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX_SRC_RDY    : out std_logic_vector(ITEMS-1 downto 0);
    TX_DST_RDY    : in std_logic_vector(ITEMS-1 downto 0)
  );
end entity;



architecture arch of MVB_SPLIT is

  signal item_sent : std_logic_vector(ITEMS-1 downto 0);
  signal srdy : std_logic_vector(ITEMS-1 downto 0);
  signal drdy : std_logic;

begin

  no_dst_rdy_gen : if not USE_DST_RDY generate
    TX_DATA <= RX_DATA;
    TX_SRC_RDY <= RX_VLD and (ITEMS-1 downto 0 => RX_SRC_RDY);
    RX_DST_RDY <= '1';
  end generate;


  use_dst_rdy_gen : if USE_DST_RDY generate
    TX_DATA <= RX_DATA;
    TX_SRC_RDY <= srdy;
    RX_DST_RDY <= drdy;
    srdy <= RX_VLD and (ITEMS-1 downto 0 => RX_SRC_RDY) and not item_sent;
    drdy <= and_reduce(TX_DST_RDY or not RX_VLD or item_sent);

    item_sent_gen : for i in 0 to ITEMS-1 generate
      reg : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if RESET='1' or drdy='1' then
            item_sent(i) <= '0';
          elsif TX_DST_RDY(i)='1' and srdy(i)='1' then
            item_sent(i) <= '1';
          end if;
        end if;
      end process;
    end generate;
  end generate;

end architecture;
