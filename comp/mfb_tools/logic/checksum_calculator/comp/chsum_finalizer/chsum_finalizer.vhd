-- chsum_regional.vhd: A component that completes the checksum calculation.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- ============================================================================
--  Description
-- ============================================================================

--
entity CHSUM_FINALIZER is
generic(
    -- Number of Regions within a data word, must be power of 2.
    REGIONS           : natural := 4;
    -- Width of an Item (in bits).
    CHECKSUM_WIDTH    : natural := 16
);
port(
    -- ========================================================================
    -- Clock and Reset
    -- ========================================================================

    CLK           : in  std_logic;
    RESET         : in  std_logic;

    -- ========================================================================
    -- RX INTERFACE
    --
    -- Checksums calculated per Region.
    -- ========================================================================

    RX_CHSUM_REGION : in  std_logic_vector(REGIONS*2*CHECKSUM_WIDTH-1 downto 0);
    RX_CHSUM_END    : in  std_logic_vector(REGIONS*2-1 downto 0);
    RX_CHSUM_VLD    : in  std_logic_vector(REGIONS*2-1 downto 0);
    RX_SRC_RDY      : in  std_logic;
    RX_DST_RDY      : out std_logic;

    -- ========================================================================
    -- TX INTERFACE
    --
    -- Final checksums (per packet).
    -- ========================================================================

    TX_CHECKSUM    : out std_logic_vector(REGIONS*2*CHECKSUM_WIDTH-1 downto 0);
    TX_VALID       : out std_logic_vector(REGIONS*2-1 downto 0);
    TX_SRC_RDY     : out std_logic;
    TX_DST_RDY     : in  std_logic
);
end entity;

architecture FULL of CHSUM_FINALIZER is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    constant CHSUM_WIDTH_EXT  : natural := CHECKSUM_WIDTH*2;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal chsum_region_16    : slv_array_2d_t(REGIONS-1 downto 0)(2-1 downto 0)(CHECKSUM_WIDTH-1 downto 0);
    signal chsum_region_end   : slv_array_t   (REGIONS-1 downto 0)(2-1 downto 0);
    signal chsum_region_vld   : slv_array_t   (REGIONS-1 downto 0)(2-1 downto 0);

    signal chsum_vld          : slv_array_t   (REGIONS-1 downto 0)(2-1 downto 0);

    signal add_port0          : std_logic_vector(REGIONS downto 1);
    signal add_port1          : std_logic_vector(REGIONS downto 1);

    signal chsum_32           : u_array_2d_t(REGIONS-1 downto 0)(2-1 downto 0)(CHSUM_WIDTH_EXT-1 downto 0);
    signal chsum_zeros_32     : unsigned                                      (CHSUM_WIDTH_EXT-1 downto 0) := (others => '0');
    signal chsum_32_prev      : unsigned                                      (CHSUM_WIDTH_EXT-1 downto 0);

    signal src_rdy            : std_logic_vector(REGIONS-1 downto 0);

    signal chsum_32_reg       : u_array_2d_t(REGIONS-1 downto 0)(2-1 downto 0)(CHSUM_WIDTH_EXT-1 downto 0);
    signal chsum_vld_reg      : slv_array_t (REGIONS-1 downto 0)(2-1 downto 0);
    signal src_rdy_reg        : std_logic;

    signal chsum_32_acc       : u_array_2d_t(REGIONS-1 downto 0)(2-1 downto 0)(CHSUM_WIDTH_EXT-1 downto 0);
    signal chsum_16           : u_array_2d_t(REGIONS-1 downto 0)(2-1 downto 0)(CHECKSUM_WIDTH-1 downto 0);

begin

    RX_DST_RDY <= TX_DST_RDY;

    chsum_region_16  <= slv_array_2d_deser(RX_CHSUM_REGION, REGIONS, 2);
    chsum_region_end <= slv_array_deser   (RX_CHSUM_END   , REGIONS   );
    chsum_region_vld <= slv_array_deser   (RX_CHSUM_VLD   , REGIONS   );

    -- ========================================================================
    -- Checksum validation
    -- ========================================================================

    chsum_vld_g : for r in 0 to REGIONS-1 generate
        chsum_vld(r)(0) <= chsum_region_end(r)(0) and chsum_region_vld(r)(0);
        chsum_vld(r)(1) <= chsum_region_end(r)(1) and chsum_region_vld(r)(1) and chsum_vld(r)(0);
    end generate;

    -- ========================================================================
    -- Checksum finalization
    -- ========================================================================

    -- add_port0(0) <= chsum_region_vld(0)(0);
    port_sel_g : for r in 1 to REGIONS generate
        add_port0(r) <= not chsum_region_end(r-1)(0) and chsum_region_vld(r-1)(0);
        add_port1(r) <= not chsum_region_end(r-1)(1) and chsum_region_vld(r-1)(1);
    end generate;

    chsum1_g : for r in 0 to REGIONS-1 generate
        chsum_32(r)(1) <= resize(unsigned(chsum_region_16(r)(1)), CHSUM_WIDTH_EXT);
    end generate;

    chsum_32(0)(0) <= unsigned(chsum_region_16(0)(0)) + chsum_32_prev;
    chsum0_g : for r in 1 to REGIONS-1 generate
        chsum_32(r)(0) <= unsigned(chsum_region_16(r)(0)) + chsum_32(r-1)(0) when (add_port0(r) = '1') else
                          unsigned(chsum_region_16(r)(0)) + chsum_32(r-1)(1) when (add_port1(r) = '1') else
                          unsigned(chsum_region_16(r)(0)) + chsum_zeros_32; -- add 32 zeros to resize_left by 16 bits
    end generate;

    -- ========================================================================
    -- Register with previous checksum
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RX_SRC_RDY = '1') and (TX_DST_RDY = '1') then
                if (add_port0(REGIONS) = '1') then
                    chsum_32_prev <= chsum_32(REGIONS-1)(0);
                elsif (add_port1(REGIONS) = '1') then
                    chsum_32_prev <= chsum_32(REGIONS-1)(1);
                else
                    chsum_32_prev <= (others => '0');
                end if;
            end if;
            if (RESET = '1') then
                chsum_32_prev <= (others => '0');
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Post-checksum register
    -- ========================================================================

    src_rdy_g : for r in 0 to REGIONS-1 generate
        src_rdy(r) <= or chsum_vld(r);
    end generate;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_DST_RDY = '1') then
                chsum_32_reg  <= chsum_32;
                chsum_vld_reg <= chsum_vld;
                src_rdy_reg   <= or src_rdy;
            end if;
            if (RESET = '1') then
                chsum_vld_reg <= (others => (others => '0'));
                src_rdy_reg   <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Overflow accumulation
    -- ========================================================================

    overflow_g : for r in 0 to REGIONS-1 generate
        chsum_32_acc(r)(0) <= resize(chsum_32_reg(r)(0)(chsum_32_reg(0)(0)'high downto 16), CHSUM_WIDTH_EXT) + chsum_32_reg(r)(0)(15 downto 0); -- 17 bits should be enough
        chsum_16    (r)(0) <=        chsum_32_acc(r)(0)(chsum_32_acc(0)(0)'high downto 16)                   + chsum_32_acc(r)(0)(15 downto 0);

        chsum_32_acc(r)(1) <= resize(chsum_32_reg(r)(1)(chsum_32_reg(0)(1)'high downto 16), CHSUM_WIDTH_EXT) + chsum_32_reg(r)(1)(15 downto 0); -- 17 bits should be enough
        chsum_16    (r)(1) <=        chsum_32_acc(r)(1)(chsum_32_acc(0)(1)'high downto 16)                   + chsum_32_acc(r)(1)(15 downto 0);
    end generate;

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    TX_CHECKSUM <= not slv_array_2d_ser(u_arr_to_slv_arr_2d(chsum_16));
    TX_VALID    <= slv_array_ser(chsum_vld_reg);
    TX_SRC_RDY  <= src_rdy_reg;

end architecture;
