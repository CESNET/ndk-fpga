-- arbiter.vhd: ARBITER component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity ARBITER is
    generic (
        -- Number of ports.
        NUM_PORTS : natural := 2
    );
    port (
        -- Clock and reset.
        CLK          : in  std_logic;
        RESET        : in  std_logic;

        -- Requests from ports.
        REQ_VECTOR   : in  std_logic_vector(NUM_PORTS-1 downto 0);
        -- Increment priority.
        PRIORITY_INC : in  std_logic;
        -- Response to ports.
        REQ_ACCEPT   : out std_logic_vector(NUM_PORTS-1 downto 0)
    );
end entity;

architecture FULL of ARBITER is

    signal s_priority_reg : std_logic_vector(log2(NUM_PORTS)-1 downto 0);
    signal s_port_addr    : std_logic_vector(log2(NUM_PORTS)-1 downto 0);

begin

    priority_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_priority_reg <= (others => '0');
            elsif (PRIORITY_INC = '1') then
                s_priority_reg <= std_logic_vector(unsigned(s_port_addr) + 1);
            end if;
        end if;
    end process;


    priority_enc_i : entity work.PRIORITY_ENC
    generic map (
        DATA_WIDTH => NUM_PORTS
    )
    port map (
        DI       => REQ_VECTOR,
        PRIORITY => s_priority_reg,
        ADDR     => s_port_addr
    );

    priority_onehot_i : entity work.DEC1FN_ENABLE
    generic map (
        ITEMS => NUM_PORTS
    )
    port map (
        ADDR   => s_port_addr,
        ENABLE => or REQ_VECTOR,
        DO     => REQ_ACCEPT
    );

end architecture;
