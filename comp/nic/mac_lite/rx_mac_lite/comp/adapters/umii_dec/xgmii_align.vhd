-- xgmii_align.vhd: SOP aligner (to 8 bytes) for XGMII interface
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_XGMII_ALIGN is
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK           : in  std_logic;
        RESET         : in  std_logic;
        -- =====================================================================
        -- INPUT XGMII INTERFACE (valid each cycle, with SOP aligned to 4 bytes)
        -- =====================================================================
        -- MII signal with data bits
        IN_XGMII_RXD  : in  std_logic_vector(64-1 downto 0);
        -- MII signal with control flags
        IN_XGMII_RXC  : in  std_logic_vector(8-1 downto 0);
        -- =====================================================================
        -- OUPUT XGMII INTERFACE (with SOP aligned to 8 bytes)
        -- =====================================================================
        -- MII signal with data bits
        OUT_XGMII_RXD : out std_logic_vector(64-1 downto 0);
        -- MII signal with control flags
        OUT_XGMII_RXC : out std_logic_vector(8-1 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_XGMII_ALIGN is

    constant C_XGMII_IDLE : std_logic_vector := X"07";
    constant C_XGMII_SOP  : std_logic_vector := X"FB";

    signal start_detected     : std_logic_vector(2-1 downto 0);
    signal start_actived_vec  : std_logic_vector(2-1 downto 0);
    signal start_actived      : std_logic;
    signal start_aligned      : std_logic;
    signal start_aligned_reg  : std_logic;

    signal xgmii_rxd_reg      : std_logic_vector(64-1 downto 0);
    signal xgmii_rxc_reg      : std_logic_vector(8-1 downto 0);

    signal rxd_mux_in0        : std_logic_vector(64-1 downto 0);
    signal rxd_mux_in1        : std_logic_vector(64-1 downto 0);
    signal rxd_mux_out        : std_logic_vector(64-1 downto 0);

    signal rxc_mux_in0        : std_logic_vector(8-1 downto 0);
    signal rxc_mux_in1        : std_logic_vector(8-1 downto 0);
    signal rxc_mux_out        : std_logic_vector(8-1 downto 0);

    signal rxd_mux_out_masked : std_logic_vector(64-1 downto 0);
    signal rxc_mux_out_masked : std_logic_vector(8-1 downto 0);

begin

    start_detected(0) <= '1' when (IN_XGMII_RXD(7 downto 0)   = C_XGMII_SOP) else '0';
    start_detected(1) <= '1' when (IN_XGMII_RXD(39 downto 32) = C_XGMII_SOP) else '0';

    start_actived_vec <= start_detected and (IN_XGMII_RXC(4) & IN_XGMII_RXC(0));

    start_aligned <= '1' when (start_actived_vec = "01") else '0';
    start_actived <= or start_actived_vec;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                start_aligned_reg <= '0';
            elsif (start_actived = '1') then
                start_aligned_reg <= start_aligned;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            xgmii_rxd_reg <= IN_XGMII_RXD;
            xgmii_rxc_reg <= IN_XGMII_RXC;
        end if;
    end process;

    -- shift unaligned MII data
    rxd_mux_in0 <= IN_XGMII_RXD(31 downto 0) & xgmii_rxd_reg(63 downto 32);
    rxd_mux_in1 <= xgmii_rxd_reg;
    rxd_mux_out <= rxd_mux_in1 when (start_aligned_reg = '1') else rxd_mux_in0;

    -- shift unaligned MII CMD
    rxc_mux_in0 <= IN_XGMII_RXC(3 downto 0) & xgmii_rxc_reg(7 downto 4);
    rxc_mux_in1 <= xgmii_rxc_reg;
    rxc_mux_out <= rxc_mux_in1 when (start_aligned_reg = '1') else rxc_mux_in0;

    -- masking a possible duplicate start of the packet
    rxd_mux_out_masked <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & rxd_mux_out(31 downto 0);
    rxc_mux_out_masked <= "1111" & rxc_mux_out(3 downto 0);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (start_actived = '1') and (start_aligned = '1') then
                OUT_XGMII_RXD <= rxd_mux_out_masked;
                OUT_XGMII_RXC <= rxc_mux_out_masked;
            else
                OUT_XGMII_RXD <= rxd_mux_out;
                OUT_XGMII_RXC <= rxc_mux_out;
            end if;
        end if;
    end process;

end architecture;
