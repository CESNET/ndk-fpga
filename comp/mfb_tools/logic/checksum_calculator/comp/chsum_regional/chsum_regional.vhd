-- chsum_regional.vhd: A component that calculates checksum per each MFB region.
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

-- This component calculates checksum per each MFB region.
-- Only a part of a packets checksum can be calculated here - in case the checksum data are also in the previous Region/word or continue to the following Region/word.
-- The partial checksums are used to make the final (per-packet) checksum in the chsum_regional.vhd component.
entity CHSUM_REGIONAL is
generic(
    -- Number of Items in a Region.
    ITEMS             : natural := 8*8;
    -- Width of an Item (in bits), must be 8.
    ITEM_WIDTH        : natural := 8;
    -- Width of the output checksum (in bits), must be 16.
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
    -- Data for the checksum calculation.
    -- ========================================================================

    RX_CHSUM_DATA : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    -- Checksum data start on an odd Item, always valid.
    RX_CHSUM_ODD  : in  std_logic_vector(ITEMS-1 downto 0);
    -- Checksum data end on this Item.
    RX_CHSUM_END  : in  std_logic_vector(ITEMS-1 downto 0);
    -- Valid for each Item, like the INFRAME signal (Mac Segmented bus).
    RX_VALID      : in  std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in  std_logic; -- to remove
    RX_DST_RDY    : out std_logic;

    -- ========================================================================
    -- TX INTERFACE
    --
    -- Calucated checksum(s) - there can be upto 2 in a Region.
    -- ========================================================================

    TX_CHSUM_REGION : out std_logic_vector(2*CHECKSUM_WIDTH-1 downto 0);
    TX_CHSUM_END    : out std_logic_vector(2-1 downto 0);
    TX_CHSUM_VLD    : out std_logic_vector(2-1 downto 0);
    TX_SRC_RDY      : out std_logic; -- to remove
    TX_DST_RDY      : in  std_logic
);
end entity;

architecture FULL of CHSUM_REGIONAL is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================
    constant ITEMS_16           : natural := ITEMS/2;
    constant ITEM_WIDTH_16      : natural := ITEM_WIDTH*2;
    constant ITEM_WIDTH_16_EXT  : natural := ITEM_WIDTH_16*2;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal chsum_data_8      : slv_array_t     (ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal chsum_data_8_fix  : slv_array_t     (ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal chsum_zeros_8     : std_logic_vector                  (ITEM_WIDTH-1 downto 0) := (others => '0');
    signal swap_bytes        : std_logic_vector(ITEMS_16-1 downto 0);
    signal chsum_data_16     : slv_array_t     (ITEMS_16-1 downto 0)(ITEM_WIDTH_16-1 downto 0);
    signal chsum_end_16      : std_logic_vector(ITEMS_16-1 downto 0);
    signal chsum_vld_16      : std_logic_vector(ITEMS_16-1 downto 0);

    signal chsum_data_16_reg : slv_array_t     (ITEMS_16-1 downto 0)(ITEM_WIDTH_16-1 downto 0);
    signal chsum_end_16_reg  : std_logic_vector(ITEMS_16-1 downto 0);
    signal chsum_vld_16_reg  : std_logic_vector(ITEMS_16-1 downto 0);
    signal rx_src_rdy_reg    : std_logic;

    signal chsum_data_16_arr : slv_array_2d_t(ITEMS_16-1 downto 0)(ITEMS_16-1 downto 0)(ITEM_WIDTH_16-1 downto 0);
    signal chsum_end_16_arr  : slv_array_t   (ITEMS_16-1 downto 0)(ITEMS_16-1 downto 0);
    signal chsum_vld_16_arr  : slv_array_t   (ITEMS_16-1 downto 0)(ITEMS_16-1 downto 0);

    signal chsum_32          : u_array_2d_t(ITEMS_16-1 downto 0)(ITEMS_16-1 downto 0)(ITEM_WIDTH_16_EXT-1 downto 0);
    signal chsum_zeros_32    : unsigned                                              (ITEM_WIDTH_16_EXT-1 downto 0) := (others => '0');

    signal chsum_32_reg2     : u_array_t       (ITEMS_16-1 downto 0)(ITEM_WIDTH_16_EXT-1 downto 0);
    signal chsum_end_16_reg2 : std_logic_vector(ITEMS_16-1 downto 0);
    signal chsum_vld_16_reg2 : std_logic_vector(ITEMS_16-1 downto 0);
    signal rx_src_rdy_reg2   : std_logic;

    signal chsum_32_acc      : u_array_t(ITEMS_16-1 downto 0)(ITEM_WIDTH_16_EXT-1 downto 0);
    signal chsum_16          : u_array_t(ITEMS_16-1 downto 0)(ITEM_WIDTH_16-1 downto 0);

    signal output0_ptr       : natural;
    signal output1_ptr       : natural;

    signal tx_checksum_arr   : slv_array_t     (2-1 downto 0)(ITEM_WIDTH_16-1 downto 0);
    signal tx_chsum_end_arr  : std_logic_vector(2-1 downto 0);
    signal tx_chsum_vld_arr  : std_logic_vector(2-1 downto 0);

begin

    RX_DST_RDY <= TX_DST_RDY;

    -- ========================================================================
    -- Splitting input data into 16-bit chunks
    -- ========================================================================

    chsum_data_8 <= slv_array_deser(RX_CHSUM_DATA, ITEMS);

    chsum_data_fix_g : for i in 0 to ITEMS-1 generate
        chsum_data_8_fix(i) <= chsum_data_8(i) when (RX_VALID(i) = '1') else (others => '0');
    end generate;

    chsum_data_16_g : for i in 0 to ITEMS_16-1 generate
        swap_bytes(i) <= '1' when (RX_CHSUM_ODD(2*(i+1)-1) = '0') and (RX_CHSUM_ODD(2*i) = '0') else '0'; -- when start is on an even Item

        chsum_data_16(i) <= chsum_data_8_fix(2*i)       & chsum_data_8_fix(2*(i+1)-1) when (swap_bytes(i) = '1') else
                            chsum_data_8_fix(2*(i+1)-1) & chsum_data_8_fix(2*i);

        chsum_end_16(i) <= '1' when (RX_CHSUM_END(2*(i+1)-1) = '1') or (RX_CHSUM_END(2*i) = '1') else '0';

        chsum_vld_16(i) <= '1' when (RX_VALID    (2*(i+1)-1) = '1') or (RX_VALID    (2*i) = '1') else '0';

    end generate;

    -- ========================================================================
    -- Pre-checksum register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_DST_RDY = '1') then
                chsum_data_16_reg <= chsum_data_16;
                chsum_end_16_reg  <= chsum_end_16;
                chsum_vld_16_reg  <= chsum_vld_16;
                rx_src_rdy_reg    <= RX_SRC_RDY;
            end if;
            if (RESET = '1') then
                rx_src_rdy_reg <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Checksum calculation
    -- ========================================================================

    chsum_32(0)(0) <= resize_left(unsigned(chsum_data_16_reg(0)), ITEM_WIDTH_16_EXT);
    chsum_data_16_arr(0) <= chsum_data_16_reg;
    chsum_end_16_arr(0) <= chsum_end_16_reg;
    chsum_vld_16_arr(0) <= chsum_vld_16_reg;

    chsum_g : for i in 1 to ITEMS_16-1 generate

        chsum_p : process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_DST_RDY = '1') then
                    chsum_32(i) <= chsum_32(i-1);
                    if (chsum_end_16_arr(i-1)(i-1) = '0') then
                        chsum_32(i)(i) <= chsum_32(i-1)(i-1) + unsigned(chsum_data_16_arr(i-1)(i));
                    else
                        chsum_32(i)(i) <= chsum_zeros_32 + unsigned(chsum_data_16_arr(i-1)(i));
                    end if;
                end if;
            end if;
        end process;

        chsum_data_propg_p : process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_DST_RDY = '1') then
                    chsum_data_16_arr(i) <= chsum_data_16_arr(i-1);
                    chsum_end_16_arr(i) <= chsum_end_16_arr(i-1);
                    chsum_vld_16_arr(i) <= chsum_vld_16_arr(i-1);
                end if;
                if (RESET = '1') then
                    chsum_vld_16_arr(i) <= (others => '0');
                end if;
            end if;
        end process;

    end generate;

    -- ========================================================================
    -- Post-checksum register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_DST_RDY = '1') then
                chsum_32_reg2     <= chsum_32(ITEMS_16-1);
                chsum_end_16_reg2 <= chsum_end_16_arr(ITEMS_16-1);
                chsum_vld_16_reg2 <= chsum_vld_16_arr(ITEMS_16-1);
                rx_src_rdy_reg2   <= or chsum_vld_16_arr(ITEMS_16-1);
            end if;
            if (RESET = '1') then
                rx_src_rdy_reg2 <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Overflow accumulation
    -- ========================================================================

    overflow_g : for i in 0 to ITEMS_16-1 generate
        chsum_32_acc(i) <= resize_left(chsum_32_reg2(i)(chsum_32_reg2(0)'high downto 16), ITEM_WIDTH_16_EXT) + chsum_32_reg2(i)(15 downto 0); -- 17 bits should be enough
        chsum_16    (i) <=             chsum_32_acc (i)(chsum_32_acc (0)'high downto 16)                     + chsum_32_acc (i)(15 downto 0);
    end generate;

    -- ========================================================================
    -- Output selection logic
    -- ========================================================================

    process(all)
        variable prev_end : std_logic := '0';
    begin
        prev_end := '0';
        output0_ptr <= ITEMS_16-1;
        output1_ptr <= ITEMS_16-1;

        for i in 0 to ITEMS_16-1 loop
            if (chsum_end_16_reg2(i) = '1') then
                if (prev_end = '0') then
                    output0_ptr <= i;
                end if;
                if (prev_end = '1') then
                    output1_ptr <= i;
                end if;
                prev_end := '1';
            end if;
        end loop;
    end process;

    tx_checksum_arr (0) <= std_logic_vector(chsum_16(output0_ptr));
    tx_checksum_arr (1) <= std_logic_vector(chsum_16(output1_ptr));

    tx_chsum_end_arr(0) <=                                                                  chsum_end_16_reg2(output0_ptr);
    tx_chsum_end_arr(1) <= '0' when (chsum_end_16_reg2(0) = '1') and (output1_ptr = 0) else chsum_end_16_reg2(output1_ptr);

    tx_chsum_vld_arr(0) <= rx_src_rdy_reg2;
    tx_chsum_vld_arr(1) <= '0' when (output0_ptr = ITEMS_16-1) else (or chsum_vld_16_reg2(ITEMS_16-1 downto output0_ptr+1));

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    TX_CHSUM_REGION <= slv_array_ser(tx_checksum_arr);
    TX_CHSUM_END    <= tx_chsum_end_arr;
    TX_CHSUM_VLD    <= tx_chsum_vld_arr;
    TX_SRC_RDY      <= rx_src_rdy_reg2;

end architecture;
