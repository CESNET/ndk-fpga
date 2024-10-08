-- discard.vhd: Discard MVB items
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- The MVB_DISCARD component allows to discard selected items. The item marked
-- with the discard flag will be discarded (masked) in the internal logic.
-- There is a built-in optional output register.
entity MVB_DISCARD is
    generic(
        -- Number of items
        ITEMS      : natural := 4;
        -- Item width in bits
        ITEM_WIDTH : natural := 32;
        -- Optional output register
        OUTPUT_REG : boolean := True
    );
    port(
        -- Clock input
        CLK         : in  std_logic;
        -- Reset input synchronized with CLK
        RESET       : in  std_logic;

        -- RX MVB: data word with MVB items
        RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- RX MVB: discard flag of each MVB item
        RX_DISCARD : in  std_logic_vector(ITEMS-1 downto 0);
        -- RX MVB: valid of each MVB item
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        -- RX MVB: source ready
        RX_SRC_RDY : in  std_logic;
        -- RX MVB: destination ready
        RX_DST_RDY : out std_logic;

        -- TX MVB: Data word with MVB items
        TX_DATA     : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD      : out std_logic_vector(ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY  : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of MVB_DISCARD is

    signal out_data    : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal out_vld     : std_logic_vector(ITEMS-1 downto 0);
    signal out_src_rdy : std_logic;

begin

    RX_DST_RDY <= TX_DST_RDY;

    out_data    <= RX_DATA;
    out_vld     <= RX_VLD and not RX_DISCARD;
    out_src_rdy <= RX_SRC_RDY and (or out_vld);

    out_reg_on_g: if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_DST_RDY = '1') then
                    TX_DATA    <= out_data;
                    TX_VLD     <= out_vld;
                    TX_SRC_RDY <= out_src_rdy;
                end if;
                if (RESET = '1') then
                    TX_SRC_RDY <= '0';
                end if;
            end if;
        end process;
    end generate;

    out_reg_off_g: if not OUTPUT_REG generate
        TX_DATA    <= out_data;
        TX_VLD     <= out_vld;
        TX_SRC_RDY <= out_src_rdy;
    end generate;

end architecture;
