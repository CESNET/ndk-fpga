-- am_ins.vhd : Alignment marker inserter for 40GBASE-R PCS
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity AM_INS4 is
    generic (
        AM_INIT : std_logic_vector(13 downto 0) := (others => '0')
    );
    port (
        RESET : in std_logic;
        CLK   : in std_logic;
        EN    : in std_logic;                          -- Clock enable
        RD    : out std_logic;
        D     : in std_logic_vector(4*66-1 downto 0);  -- Input data
        Q     : out std_logic_vector(4*66-1 downto 0)  -- Generated marker
    );
end entity;

architecture BEHAVIORAL of AM_INS4 is

    constant NUM_LANES : natural := 4;

    attribute keep : string;
    attribute max_fanout : integer;

    signal q_i        : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal am_counter : unsigned(13 downto 0) := unsigned(AM_INIT);
    signal am         : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal am_insert  : std_logic := '0';
    signal ag_reset   : std_logic;
    attribute keep of am_insert       : signal is "true";
    attribute max_fanout of am_insert : signal is 200;

begin

    -- Generate alignment marker generators
    gen_am: for i in 0 to NUM_LANES-1 generate

        marker: entity work.AM_GEN_4
        generic map (
            LANE => i
        )
        port map (
            RESET => ag_reset,
            CLK   => CLK,
            EN    => EN,
            D     => q_i(66*(i+1)-1 downto 66*i),
            M     => am(66*(i+1)-1 downto 66*i)
        );
    end generate;

    ag_reset <= am_insert or RESET;

    am_cntr : process (CLK, RESET)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                am_counter <= unsigned(AM_INIT);
            elsif (EN = '1') then
                am_counter <= am_counter + 1;
            end if;
            if (am_counter = X"3FFF") then
                am_insert <= EN;
                if (EN = '1') then
                    am_counter <= unsigned(AM_INIT);
                end if;
            elsif (EN = '1') then
                am_insert <= '0';
            end if;
        end if;
    end process;

    q_i <= D when am_insert = '0' else am;

    Q  <= q_i;
    RD <= not am_insert;

end architecture;
