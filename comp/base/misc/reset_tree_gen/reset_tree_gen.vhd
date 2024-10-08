-- reset_tree_gen.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity RESET_TREE_GEN is
    generic(
        CLK_COUNT    : natural := 2;
        RST_REPLICAS : natural := 4
    );
    port(
        -- stable clock
        STABLE_CLK   : in  std_logic;
        -- input global reset synced with stable clock
        GLOBAL_RESET : in  std_logic;
        -- vector of clocks for reset synchronizating
        CLK_VECTOR   : in  std_logic_vector(CLK_COUNT-1 downto 0);
        -- resets synced with clocks in CLK_VECTOR
        RST_VECTOR   : out std_logic_vector(CLK_COUNT*RST_REPLICAS-1 downto 0)
    );
end entity;

architecture FULL of RESET_TREE_GEN is

    constant RST_CNT_WIDTH : natural := 8;

    signal s_global_rst_cnt      : unsigned(RST_CNT_WIDTH-1 downto 0);
    signal s_global_rst_extended : std_logic;

begin

    -- -------------------------------------------------------------------------
    --  RESET EXTENDER
    -- -------------------------------------------------------------------------

    process (STABLE_CLK, GLOBAL_RESET)
    begin
        if (GLOBAL_RESET = '1') then
            s_global_rst_cnt <= (others => '0');
        elsif (rising_edge(STABLE_CLK)) then
            if (s_global_rst_cnt(RST_CNT_WIDTH-1) = '0') then
                s_global_rst_cnt <= s_global_rst_cnt + 1;
            end if;
        end if;
    end process;

    process (STABLE_CLK)
    begin
        if (rising_edge(STABLE_CLK)) then
            s_global_rst_extended <= not s_global_rst_cnt(RST_CNT_WIDTH-1);
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  RESET SYNCHRONIZERS
    -- -------------------------------------------------------------------------

    rst_sync_g : for i in 0 to CLK_COUNT-1 generate
        rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RST_REPLICAS
        )
        port map (
            CLK       => CLK_VECTOR(i),
            ASYNC_RST => s_global_rst_extended,
            OUT_RST   => RST_VECTOR((i+1)*RST_REPLICAS-1 downto i*RST_REPLICAS)
        );
    end generate;

end architecture;
