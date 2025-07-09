-- priority_enc.vhd: PRIORITY_ENC component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity PRIORITY_ENC is
    generic (
        -- Data width in bits.
        DATA_WIDTH : natural := 8
    );
    port (
        -- Input data.
        DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Input priority.
        PRIORITY : in  std_logic_vector(log2(DATA_WIDTH)-1 downto 0);
        -- Output address.
        ADDR     : out std_logic_vector(log2(DATA_WIDTH)-1 downto 0)
    );
end entity;

architecture FULL of PRIORITY_ENC is

    signal s_di_r       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_priority_r : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_do         : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

    barrel_bit_rotator_right_i : entity work.BARREL_BIT_SHIFTER(barrel_bit_shifter_arch)
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        SHIFT_LEFT => false
    )
    port map (
        DATA_IN  => DI,
        SEL      => PRIORITY,
        DATA_OUT => s_di_r
    );

    first_one_i : entity work.FIRST_ONE
    generic map (
        DATA_WIDTH => DATA_WIDTH
    )
    port map (
        DI => s_di_r,
        DO => s_priority_r
    );

    barrel_bit_rotator_left_i : entity work.BARREL_BIT_SHIFTER(barrel_bit_shifter_arch)
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        SHIFT_LEFT => true
    )
    port map (
        DATA_IN  => s_priority_r,
        SEL      => PRIORITY,
        DATA_OUT => s_do
    );

    encoder_i : entity work.DEC1FN2B
    generic map (
        ITEMS => DATA_WIDTH
    )
    port map (
        ENABLE => '1',
        DI     => s_do,
        ADDR   => ADDR
    );

end architecture;
