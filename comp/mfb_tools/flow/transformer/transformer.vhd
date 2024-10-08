-- transformer.vhd: Implementation of MFB transformer component
-- Copyright (C) 2020 CESNET
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

-- This component performs changing MFB word size by increasing or decreasing the number of Regions on RX to TX.
--
-- There are two possible solutions:
--   - RX_REGIONS > TX_REGIONS - **Multiple Regions** in **one word** on the RX side are sent in **multiple words** with **fewer Regions** from the TX side.
--   - RX_REGIONS < TX_REGIONS - **Multiple words** on the RX side are put together to form **one word** with **multiple Regions** on the TX side.
entity MFB_TRANSFORMER is
    generic (
        -- =============================
        -- MFB Configuration
        -- =============================

        RX_REGIONS  : integer := 2;
        TX_REGIONS  : integer := 1;
        REGION_SIZE : integer := 1;
        BLOCK_SIZE  : integer := 8;
        ITEM_WIDTH  : integer := 32;
        META_WIDTH  : integer := 0
    );
    port (
        -- =============================
        -- Clock and Reset
        -- =============================

        CLK   : in std_logic;
        RESET : in std_logic;

        -- =============================
        -- MFB input interface
        -- =============================

        RX_DATA    : in  std_logic_vector(RX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META    : in  std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_EOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_SOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        RX_EOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =============================
        -- MFB output interface
        -- =============================

        TX_DATA    : out std_logic_vector(TX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META    : out std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
        TX_SOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_EOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_SOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        TX_EOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of MFB_TRANSFORMER is
begin
    -- asserts over generics
    assert (2**log2(RX_REGIONS) = RX_REGIONS and RX_REGIONS > 0)
        report "MFB_TRANSFORMER: RX_REGIONS must be power of 2 and higher than 0."
        severity error;
    assert (2**log2(TX_REGIONS) = TX_REGIONS and TX_REGIONS > 0)
        report "MFB_TRANSFORMER: TX_REGIONS must be power of 2 and higher than 0."
        severity error;
    assert (2**log2(REGION_SIZE) = REGION_SIZE and REGION_SIZE > 0)
        report "MFB_TRANSFORMER: REGION_SIZE must be power of 2 and higher than 0."
        severity error;

    -- RX regions = TX regions
    gen_arch_equal_g: if (RX_REGIONS = TX_REGIONS) generate
        TX_DATA    <= RX_DATA;
        TX_META    <= RX_META;
        TX_SOP     <= RX_SOP;
        TX_EOP     <= RX_EOP;
        TX_SOP_POS <= RX_SOP_POS;
        TX_EOP_POS <= RX_EOP_POS;
        TX_SRC_RDY <= RX_SRC_RDY;
        RX_DST_RDY <= TX_DST_RDY;
    end generate;

    -- RX regions > TX regions
    gen_arch_down_g: if (RX_REGIONS > TX_REGIONS) generate
        mfb_transformer_down_i: entity work.MFB_TRANSFORMER_DOWN
            generic map (
                RX_REGIONS  => RX_REGIONS,
                TX_REGIONS  => TX_REGIONS,
                REGION_SIZE => REGION_SIZE,
                BLOCK_SIZE  => BLOCK_SIZE,
                ITEM_WIDTH  => ITEM_WIDTH,
                META_WIDTH  => META_WIDTH)
            port map (
                CLK         => CLK,
                RESET       => RESET,
                RX_DATA     => RX_DATA,
                RX_META     => RX_META,
                RX_SOP      => RX_SOP,
                RX_EOP      => RX_EOP,
                RX_SOP_POS  => RX_SOP_POS,
                RX_EOP_POS  => RX_EOP_POS,
                RX_SRC_RDY  => RX_SRC_RDY,
                RX_DST_RDY  => RX_DST_RDY,
                TX_DATA     => TX_DATA,
                TX_META     => TX_META,
                TX_SOP      => TX_SOP,
                TX_EOP      => TX_EOP,
                TX_SOP_POS  => TX_SOP_POS,
                TX_EOP_POS  => TX_EOP_POS,
                TX_SRC_RDY  => TX_SRC_RDY,
                TX_DST_RDY  => TX_DST_RDY
            );
    end generate;

    -- RX regions < TX regions
    gen_arch_up_g: if (RX_REGIONS < TX_REGIONS) generate
        mfb_transformer_up_i: entity work.MFB_TRANSFORMER_UP
            generic map (
                RX_REGIONS  => RX_REGIONS,
                TX_REGIONS  => TX_REGIONS,
                REGION_SIZE => REGION_SIZE,
                BLOCK_SIZE  => BLOCK_SIZE,
                ITEM_WIDTH  => ITEM_WIDTH,
                META_WIDTH  => META_WIDTH)
            port map (
                CLK         => CLK,
                RESET       => RESET,
                RX_DATA     => RX_DATA,
                RX_META     => RX_META,
                RX_SOP      => RX_SOP,
                RX_EOP      => RX_EOP,
                RX_SOP_POS  => RX_SOP_POS,
                RX_EOP_POS  => RX_EOP_POS,
                RX_SRC_RDY  => RX_SRC_RDY,
                RX_DST_RDY  => RX_DST_RDY,
                TX_DATA     => TX_DATA,
                TX_META     => TX_META,
                TX_SOP      => TX_SOP,
                TX_EOP      => TX_EOP,
                TX_SOP_POS  => TX_SOP_POS,
                TX_EOP_POS  => TX_EOP_POS,
                TX_SRC_RDY  => TX_SRC_RDY,
                TX_DST_RDY  => TX_DST_RDY
            );
    end generate;

end architecture;
