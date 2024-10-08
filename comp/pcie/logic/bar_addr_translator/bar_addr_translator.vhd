-- bar_addr_translator.vhd: PCIE BAR addr translator
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PCIE_BAR_ADDR_TRANSLATOR is
    generic (
        -- =====================================================================
        -- BAR base address configuration
        -- =====================================================================
        BAR0_BASE_ADDR    : std_logic_vector(31 downto 0) := X"01000000";
        BAR1_BASE_ADDR    : std_logic_vector(31 downto 0) := X"02000000";
        BAR2_BASE_ADDR    : std_logic_vector(31 downto 0) := X"03000000";
        BAR3_BASE_ADDR    : std_logic_vector(31 downto 0) := X"04000000";
        BAR4_BASE_ADDR    : std_logic_vector(31 downto 0) := X"05000000";
        BAR5_BASE_ADDR    : std_logic_vector(31 downto 0) := X"06000000";
        EXP_ROM_BASE_ADDR : std_logic_vector(31 downto 0) := X"0A000000";

        -- =====================================================================
        -- Other configuration
        -- =====================================================================
        -- Optional output register
        OUTPUT_REG        : boolean := False
    );
    port (
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- Aperture of used BAR
        IN_BAR_APERTURE : in  std_logic_vector(6-1 downto 0);
        -- BAR ID of TLP header
        IN_BAR_ID       : in  std_logic_vector(3-1 downto 0);
        -- 64 bit address from TLP header
        IN_ADDR         : in  std_logic_vector(64-1 downto 0);

        -- Translated 64 bit address
        OUT_ADDR        : out std_logic_vector(64-1 downto 0)
    );
end entity;

architecture FULL of PCIE_BAR_ADDR_TRANSLATOR is

    signal tlp_addr_mask : unsigned(64-1 downto 0);
    signal bar_base_addr : std_logic_vector(32-1 downto 0);
    signal out_addr_sig  : std_logic_vector(64-1 downto 0);

begin

    -- computation of address mask
    process (all)
        variable mask_var : unsigned(63 downto 0);
    begin
        mask_var := (others => '0');
        for i in 0 to 63 loop
            if (i < unsigned(IN_BAR_APERTURE)) then
                mask_var(i) := '1';
            end if;
        end loop;
        tlp_addr_mask <= mask_var;
    end process;

    -- selection of correct BAR base address
    process (all)
    begin
        case IN_BAR_ID is
            when "000"  => bar_base_addr <= BAR0_BASE_ADDR;
            when "001"  => bar_base_addr <= BAR1_BASE_ADDR;
            when "010"  => bar_base_addr <= BAR2_BASE_ADDR;
            when "011"  => bar_base_addr <= BAR3_BASE_ADDR;
            when "100"  => bar_base_addr <= BAR4_BASE_ADDR;
            when "101"  => bar_base_addr <= BAR5_BASE_ADDR;
            when "110"  => bar_base_addr <= EXP_ROM_BASE_ADDR;
            when others => bar_base_addr <= (others => '0');
        end case;
    end process;

    -- address translation
    out_addr_sig <= std_logic_vector((unsigned(IN_ADDR) AND tlp_addr_mask) + unsigned(bar_base_addr));

    out_reg_g: if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                OUT_ADDR <= out_addr_sig;
            end if;
        end process;
    else generate
        OUT_ADDR <= out_addr_sig;
    end generate;

end architecture;
