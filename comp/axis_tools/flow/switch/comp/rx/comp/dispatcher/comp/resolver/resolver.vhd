-- resolver.vhd: RESOLVER component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity RESOLVER is
    generic (
        -- Action width in bits.
        DATA_WIDTH     : natural := 4;
        -- Number of input actions.
        SEL_WIDTH      : natural := 1;
        -- Default action.
        ACTION_DEFAULT : natural := 0;
        -- Target device.
        DEVICE         : string  := "AGILEX"
    );
    port (
        -- Input actions' validity indicator.
        ACTION_IN_VLD : in  std_logic_vector(SEL_WIDTH-1 downto 0);
        -- Input actions.
        ACTION_IN     : in  std_logic_vector(SEL_WIDTH*DATA_WIDTH-1 downto 0);
        -- Selected output action.
        ACTION_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of RESOLVER is

    signal s_priority_vld_onehot : std_logic_vector(SEL_WIDTH-1 downto 0);
    signal s_priority_action     : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

    priority_sel_g : for i in 0 to SEL_WIDTH-1 generate
        s_priority_vld_onehot(i) <= ACTION_IN_VLD(i) and (nor ACTION_IN_VLD(i-1 downto 0));
    end generate;

    priority_mux_i : entity work.GEN_MUX_ONEHOT
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        MUX_WIDTH  => SEL_WIDTH,
        DEVICE     => DEVICE
    )
    port map (
        DATA_IN    => ACTION_IN,
        SEL        => s_priority_vld_onehot,
        DATA_OUT   => s_priority_action
    );

    ACTION_OUT <= s_priority_action when (or s_priority_vld_onehot) = '1' else std_logic_vector(to_unsigned(ACTION_DEFAULT, DATA_WIDTH));

end architecture;
