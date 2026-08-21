-- mvb_reordering.vhd: Reordering of MVB items within one MVB word
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- The MVB_REORDERING component moves MVB items to other positions within the
-- same MVB word. Each RX item has its own key (see REORDER_KEY) which says to
-- which TX position that item must be moved. It is a pure scatter network
-- (ITEMS multiplexers controlled by ITEMS*ITEMS comparators) without any
-- storage of items: an item is always transmitted in the same word in which it
-- was received, it is never moved to another word. The amount of logic grows
-- quadratically with ITEMS.
--
-- The requested reordering does not have to be a complete permutation, gaps
-- are allowed. A TX position which is not targeted by any valid RX item gets
-- TX_VLD='0' (data on that position are undefined). Compaction (all valid
-- items moved to the lowest positions) as well as scattering (valid items
-- moved to arbitrary positions) are therefore both valid use cases.
--
-- RX_DST_RDY is directly connected to TX_DST_RDY, the component never
-- generates backpressure of its own. Latency is one clock cycle when
-- OUT_REG_EN=True, otherwise the whole datapath is combinational.
--
-- .. WARNING::
--     The keys are not checked in any way and there is no output reporting a
--     discarded item. The user must guarantee these conditions for each valid
--     RX item (an item with RX_VLD(j)='1'):
--
--     * **Unique keys** - two valid RX items must not target the same TX
--       position. In case of such collision, the item on the higher RX
--       position (higher index j) wins and the other item is silently
--       discarded.
--     * **Key range** - the key value must be lower than ITEMS. When ITEMS is
--       not a power of two, the key is able to encode also higher values (for
--       ITEMS=5 the key is 3 bits wide and encodes values 0 to 7) and an item
--       with such key is silently discarded, because no TX position matches
--       it.
--
--     Keys of invalid RX items (RX_VLD(j)='0') are don't care.
--
entity MVB_REORDERING is
    generic (
        -- Number of MVB items in word, minimum value is 2.
        ITEMS         : natural := 5;
        -- Width of one MVB item in bits.
        ITEM_WIDTH    : natural := 64;
        -- Enable the output register on the TX MVB interface. It breaks the
        -- combinational path through the multiplexers at the cost of one clock
        -- cycle of latency.
        OUT_REG_EN    : boolean := True;
        -- Enable the reordering logic. When False, the RX MVB word is passed
        -- to the TX MVB interface unchanged and REORDER_KEY is ignored.
        REORDERING_EN : boolean := True
    );
    port (
        -- Clock input
        CLK         : in  std_logic;
        -- Reset input synchronized with CLK
        RESET       : in  std_logic;

        -- =====================================================================
        -- RX MVB INTERFACE (original item positions)
        -- =====================================================================

        RX_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD      : in  std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY  : in  std_logic;
        RX_DST_RDY  : out std_logic;

        -- =====================================================================
        -- TX MVB INTERFACE (new item positions)
        -- =====================================================================

        TX_DATA     : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD      : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY  : out std_logic;
        TX_DST_RDY  : in  std_logic;

        -- Target TX position of each RX item, log2(ITEMS) bits per item. The
        -- key of RX item j is REORDER_KEY((j+1)*log2(ITEMS)-1 downto
        -- j*log2(ITEMS)). Valid with RX_VLD and RX_SRC_RDY. The keys must meet
        -- the conditions described in the warning above.
        REORDER_KEY : in  std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0)
    );
end entity;

architecture FULL of MVB_REORDERING is

    constant KEY_SIZE : natural := log2(ITEMS);

    type data_array_t is array (ITEMS-1 downto 0) of std_logic_vector(ITEM_WIDTH-1 downto 0);
    type sel_array_t is array (ITEMS-1 downto 0) of std_logic_vector(KEY_SIZE-1 downto 0);

    signal data_arr         : data_array_t;
    signal reorder_data_arr : data_array_t;
    signal reorder_data     : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal reorder_vld      : std_logic_vector(ITEMS-1 downto 0);
    signal mux_sel          : std_logic_vector(ITEMS*KEY_SIZE-1 downto 0);
    signal mux_sel_arr      : sel_array_t;

begin

    reordering_on_g : if REORDERING_EN = True generate
        mvb_reordering_logic_i : entity work.MVB_REORDERING_LOGIC
        generic map (
            ITEMS => ITEMS
        )
        port map (
            -- INPUT CONTROL SIGNAL
            REORDER_KEY => REORDER_KEY,
            RX_VLD      => RX_VLD,
            -- OUTPUT CONTROL SIGNAL
            MUX_SEL     => mux_sel,
            TX_VLD      => reorder_vld
        );

        mux_sel_arr_g : for i in 0 to ITEMS-1 generate
            mux_sel_arr(i) <= mux_sel((i+1)*KEY_SIZE-1 downto i*KEY_SIZE);
        end generate;

        mux_g : for i in 0 to ITEMS-1 generate
            gen_mux_i : entity work.GEN_MUX
            generic map (
                DATA_WIDTH => ITEM_WIDTH,
                MUX_WIDTH  => ITEMS
            )
            port map (
                DATA_IN  => RX_DATA,
                SEL      => mux_sel_arr(i),
                DATA_OUT => reorder_data_arr(i)
            );
        end generate;

        tx_data_g : for i in 0 to ITEMS-1 generate
            reorder_data((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= reorder_data_arr(i);
        end generate;
    end generate;

    reordering_off_g : if REORDERING_EN = False generate
        reorder_data <= RX_DATA;
        reorder_vld  <= RX_VLD;
    end generate;

    RX_DST_RDY <= TX_DST_RDY;

    out_reg_on_g : if OUT_REG_EN = True generate
        tx_data_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_DST_RDY = '1') then
                    TX_DATA <= reorder_data;
                end if;
            end if;
        end process;

        tx_ctrl_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    TX_SRC_RDY <= '0';
                    TX_VLD     <= (others => '0');
                elsif (TX_DST_RDY = '1') then
                    TX_SRC_RDY <= RX_SRC_RDY;
                    TX_VLD     <= reorder_vld;
                end if;
            end if;
        end process;
    end generate;

    out_reg_off_g : if OUT_REG_EN = False generate
        TX_DATA    <= reorder_data;
        TX_SRC_RDY <= RX_SRC_RDY;
        TX_VLD     <= reorder_vld;
    end generate;

end architecture;
