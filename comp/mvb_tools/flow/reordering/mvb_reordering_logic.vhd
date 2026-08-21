-- mvb_reordering_logic.vhd: Control logic of the MVB items reordering
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- Control logic for the MVB_REORDERING component. It converts the scatter
-- mapping given by REORDER_KEY (RX item -> TX position) into the gather
-- mapping needed by the output multiplexers (TX position -> RX item) and it
-- computes the validity of each TX position. See the MVB_REORDERING entity for
-- the conditions which REORDER_KEY must meet.
--
entity MVB_REORDERING_LOGIC is
    generic (
        ITEMS : natural := 4
    );
    port (
        -- ====================
        -- INPUT CONTROL SIGNAL
        -- ====================

        -- Target TX position of each RX item, log2(ITEMS) bits per item.
        REORDER_KEY : in  std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0);
        -- Validity of each RX item, key of an invalid item is ignored.
        RX_VLD      : in  std_logic_vector(ITEMS-1 downto 0);
        -- =====================
        -- OUTPUT CONTROL SIGNAL
        -- =====================

        -- Index of the RX item selected for each TX position, log2(ITEMS)
        -- bits per position, valid only when the TX position is valid.
        MUX_SEL     : out std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0);
        -- Validity of each TX position, '0' when no valid RX item targets it.
        TX_VLD      : out std_logic_vector(ITEMS-1 downto 0)
    );
end entity;

architecture FULL of MVB_REORDERING_LOGIC is

    constant KEY_SIZE  : natural := log2(ITEMS);
    type     key_array_t is array (ITEMS-1 downto 0) of std_logic_vector(KEY_SIZE-1 downto 0);

    signal key_arr     : key_array_t;
    signal mux_sel_arr : key_array_t;

begin

    key_arr_g : for i in 0 to ITEMS-1 generate
        key_arr(i) <= REORDER_KEY((i+1)*KEY_SIZE-1 downto i*KEY_SIZE);
    end generate;

    sel_logic_g : for i in 0 to ITEMS-1 generate
        sel_logic_p : process (RX_VLD, key_arr)
            variable mux_sel_var : std_logic_vector(KEY_SIZE-1 downto 0);
            variable out_vld     : std_logic;
        begin
            mux_sel_var := std_logic_vector(to_unsigned(i,KEY_SIZE));
            out_vld     := '0';

            -- Search for the valid RX item which targets this TX position.
            -- When more of them do so (which is forbidden, see the entity
            -- doc), the last match wins, i.e. the item with the highest RX
            -- index, and the other items are lost without any notice.
            for j in 0 to ITEMS-1 loop
                if (RX_VLD(j) = '1' and key_arr(j) = std_logic_vector(to_unsigned(i,KEY_SIZE))) then
                    mux_sel_var := std_logic_vector(to_unsigned(j,KEY_SIZE));
                    out_vld     := '1';
                end if;
            end loop;

            mux_sel_arr(i) <= mux_sel_var;
            TX_VLD(i)      <= out_vld;
        end process;
    end generate;

    mux_sel_g : for i in 0 to ITEMS-1 generate
        MUX_SEL((i+1)*KEY_SIZE-1 downto i*KEY_SIZE) <= mux_sel_arr(i);
    end generate;

end architecture;
