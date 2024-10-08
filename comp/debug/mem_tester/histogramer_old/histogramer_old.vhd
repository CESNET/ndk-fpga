-- emif_refresh.vhd: Component for manual refresh of the EMIF IP
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.hist_types.all;

entity HISTOGRAMER_OLD is
generic (
    VARIANT                 : HIST_T := LINEAR;
    DATA_WIDTH              : integer;
    CNT_WIDTH               : integer;
    -- Do not set CNTER_CNT for LOG variant !
    -- Must be power of 2
    CNTER_CNT               : integer := DATA_WIDTH
);
port(
    -- Main --
    CLK                     : in  std_logic;
    RST                     : in  std_logic;

    INPUT_VLD               : in  std_logic;
    INPUT                   : in  std_logic_vector(DATA_WIDTH - 1 downto 0);

    SEL_CNTER               : in  std_logic_vector(log2(CNTER_CNT) - 1 downto 0);
    OUTPUT                  : out std_logic_vector(CNT_WIDTH - 1 downto 0);
    CNT_OVF                 : out std_logic
);
end entity;

-- =========================================================================

architecture FULL of HISTOGRAMER_OLD is

    constant CNTER_CNT_WIDTH: integer := log2(CNTER_CNT);
    constant CNT_LIMIT      : std_logic_vector(CNT_WIDTH - 1 downto 0) := (others => '1');

    signal any_full         : std_logic;
    signal cnters           : slv_array_t(CNTER_CNT - 1 downto 0)(CNT_WIDTH - 1 downto 0);
    signal cnters_en        : std_logic_vector(CNTER_CNT - 1 downto 0);
    signal cnters_full      : std_logic_vector(CNTER_CNT - 1 downto 0);

begin
    -------------------------
    -- Component instances --
    -------------------------

    log_variant_g : if VARIANT = LOG generate
        last_one_i : entity work.LAST_ONE
        generic map (
            DATA_WIDTH      => DATA_WIDTH
        )
        port map (
            DI              => INPUT,
            DO              => cnters_en
        );
    end generate;

    linear_variant_g : if VARIANT = LINEAR generate
        en_dec_i : entity work.dec1fn
        generic map (
            ITEMS       => CNTER_CNT
        )
        port map (
            ADDR        => INPUT(INPUT'length - 1 downto INPUT'length - CNTER_CNT_WIDTH),
            DO          => cnters_en
        );
    end generate;

    any_full_i : entity work.GEN_OR
    generic map (
        OR_WIDTH        => CNTER_CNT
    )
    port map (
        DI              => cnters_full,
        DO              => any_full
    );

    -------------------------
    -- Combinational logic --
    -------------------------

    cnters_full_g : for i in 0 to CNTER_CNT - 1 generate
        cnters_full(i) <= '1' when (cnters(i) = CNT_LIMIT) else
                          '0';
    end generate;

    OUTPUT <= cnters(to_integer(unsigned(SEL_CNTER)));

    ---------------
    -- Registers --
    ---------------

    cnters_g : for i in 0 to CNTER_CNT - 1 generate
        cnter_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1' or cnters_full(i) = '1') then
                    cnters(i) <= (others => '0');
                elsif (INPUT_VLD = '1' and cnters_en(i) = '1') then
                    cnters(i) <= std_logic_vector(unsigned(cnters(i)) + 1);
                end if;
            end if;
        end process;
    end generate;

    cnt_ovf_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                CNT_OVF <= '0';
            elsif (any_full = '1') then
                CNT_OVF <= '1';
            end if;
        end if;
    end process;

end architecture;
