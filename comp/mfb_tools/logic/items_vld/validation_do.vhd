-- validation_do.vhd: A component that performs the validation based on the input Offsets.
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;


-- ============================================================================
--  Description
-- ============================================================================

-- This unit inserts '1's from the first Offset to the second Offset (applies for both input interfaces).
-- Then the final output is the OR of both these results.
-- The two input interfaces (and the ORing of results) are necessary because there can be a part of valid data from the previous packet as well as from the new packet in each Region.
entity VALIDATION_DO is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS     : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE  : natural := 8
);
port(
    -- ========================================================================
    -- First input inf
    --
    -- The new data (arriving with SOF).
    -- ========================================================================

    OFFSET1_LOW  : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    OFFSET1_HIGH : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    VALID1       : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    -- ========================================================================
    -- Second input inf
    --
    -- The older data (with SOF in some of the previous Regions/Words)
    -- ========================================================================

    OFFSET2_LOW  : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    OFFSET2_HIGH : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    VALID2       : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    -- ========================================================================
    -- Output inf
    -- ========================================================================

    VALID_VECTOR : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0)
);
end entity;

architecture FULL of VALIDATION_DO is

    constant REGION_ITEMS   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;

    signal ones_vec1      : slv_array_t     (MFB_REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
    signal ones_vec2      : slv_array_t     (MFB_REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);

begin

    ones_vector_g : for r in 0 to MFB_REGIONS-1 generate

        -- ----------------------------------------
        --  Ones Insertor for the first input
        -- ----------------------------------------
        ones_insertor1_i : entity work.ONES_INSERTOR
        generic map(
            OFFSET_WIDTH => log2(REGION_ITEMS)
        )
        port map(
            OFFSET_LOW  => OFFSET1_LOW (r),
            OFFSET_HIGH => OFFSET1_HIGH(r),
            VALID       => VALID1      (r),

            ONES_VECTOR => ones_vec1   (r)
        );

        -- -----------------------------------------
        --  Ones Insertor for the second input
        -- -----------------------------------------
        ones_insertor2_i : entity work.ONES_INSERTOR
        generic map(
            OFFSET_WIDTH => log2(REGION_ITEMS)
        )
        port map(
            OFFSET_LOW  => OFFSET2_LOW (r),
            OFFSET_HIGH => OFFSET2_HIGH(r),
            VALID       => VALID2      (r),

            ONES_VECTOR => ones_vec2   (r)
        );

    end generate;

    -- Finalization
    VALID_VECTOR <= slv_array_ser(ones_vec1) or slv_array_ser(ones_vec2);

end architecture;
