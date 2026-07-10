-- mfb_get_last_items.vhd: Get last items from MFB frame
-- Copyright (C) 2026 CESNET z.s.p.o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This MFB_GET_LAST_ITEMS component extracts the last EXTRACTED_ITEMS from each
-- incoming MFB frame and outputs them on a separate MVB interface. The MFB frame
-- is forwarded unchanged to the TX MFB interface. The EX MVB interface provides
-- the extracted last items together with a per-region valid flag (EX_VLD) and
-- a source ready signal (EX_SRC_RDY).
entity MFB_GET_LAST_ITEMS is
    generic (
        REGIONS          : natural := 4;
        REGION_SIZE      : natural := 8;
        BLOCK_SIZE       : natural := 8;
        ITEM_WIDTH       : natural := 8;
        META_WIDTH       : natural := 2;
        -- Set maximum supported frame length in bytes, is used to correctly set
        -- the data width of the word counter.
        MAX_FRAME_LENGHT : natural := 16383;
        -- Count of extracted last items.
        -- Minimum value is 1, maximum value is REGION_SIZE*BLOCK_SIZE.
        EXTRACTED_ITEMS  : natural := 4
    );
    port (
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;
        -- =======================================================================
        -- INPUT MFB INTERFACE
        -- =======================================================================
        RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;
        -- =======================================================================
        -- OUTPUT MFB INTERFACE
        -- =======================================================================
        TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic;
        -- =======================================================================
        -- OUTPUT MVB INTERFACE WITH EXTRACTED LAST ITEMS
        -- =======================================================================
        EX_DATA    : out std_logic_vector(REGIONS*EXTRACTED_ITEMS*ITEM_WIDTH-1 downto 0);
        EX_VLD     : out std_logic_vector(REGIONS-1 downto 0);
        EX_SRC_RDY : out std_logic;
        EX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_GET_LAST_ITEMS is

    constant DATA_WIDTH          : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant REGION_WIDTH        : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant REGION_ITEMS        : natural := REGION_SIZE*BLOCK_SIZE;
    constant EOF_POS_WIDTH       : natural := max(1,log2(REGION_ITEMS));
    constant EXTRACTED_WIDTH     : natural := EXTRACTED_ITEMS*ITEM_WIDTH;

    signal s_dst_rdy             : std_logic;
    signal s_valid_word          : std_logic;

    -- registered previous word (delay line)
    signal s_word0_reg           : std_logic_vector(DATA_WIDTH-1 downto 0);

    -- region arrays from previous and current words
    signal s_word0_regions       : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_rx_regions          : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);

    -- double region buffer for each possible EOF region
    signal s_double_region       : slv_array_t(REGIONS-1 downto 0)(2*REGION_WIDTH-1 downto 0);
    signal s_ex_sel              : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    -- mux inputs and outputs
    signal s_mux_din_2d_arr      : slv_array_2d_t(REGIONS-1 downto 0)(EXTRACTED_ITEMS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_ex_items_arr        : slv_array_t(REGIONS-1 downto 0)(EXTRACTED_WIDTH-1 downto 0);
    signal s_ex_items_vld        : std_logic_vector(REGIONS-1 downto 0);
    signal s_ex_items            : std_logic_vector(REGIONS*EXTRACTED_WIDTH-1 downto 0);

begin

    assert (EXTRACTED_ITEMS > 0 and EXTRACTED_ITEMS <= REGION_ITEMS)
        report "MFB_GET_LAST_ITEMS: Wrong EXTRACTED_ITEMS value! Minimum value is 1, maximum value is REGION_SIZE*BLOCK_SIZE."
        severity failure;

    s_dst_rdy    <= TX_DST_RDY and EX_DST_RDY;
    s_valid_word <= RX_SRC_RDY and s_dst_rdy;

    ---------------------------------------------------------------------------
    -- INPUT WORD DELAY LINE (one previous word to cover wrap around word boundary)
    ---------------------------------------------------------------------------

    word_delay_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_word0_reg <= (others => '0');
            elsif (s_valid_word = '1') then
                s_word0_reg <= RX_DATA;
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- REGION ARRAYS FROM PREVIOUS AND CURRENT WORDS
    ---------------------------------------------------------------------------

    s_word0_regions <= slv_array_downto_deser(s_word0_reg, REGIONS, REGION_WIDTH);
    s_rx_regions    <= slv_array_downto_deser(RX_DATA,    REGIONS, REGION_WIDTH);

    ---------------------------------------------------------------------------
    -- DOUBLE REGION BUFFER AND MULTIPLEXOR SELECT
    -- (combinational extraction based on current RX_EOF / RX_EOF_POS)
    ---------------------------------------------------------------------------

    double_region_g : for r in 0 to REGIONS-1 generate
        -- lower region is the previous region in the data stream:
        -- region r-1 of current word, or last region of previous word for r=0
        lower_region_g : if (r = 0) generate
            s_double_region(r)(REGION_WIDTH-1 downto 0) <= s_word0_regions(REGIONS-1);
        end generate;
        lower_region_nz_g : if (r > 0) generate
            s_double_region(r)(REGION_WIDTH-1 downto 0) <= s_rx_regions(r-1);
        end generate;

        -- upper region is the region where EOF is detected
        s_double_region(r)(2*REGION_WIDTH-1 downto REGION_WIDTH) <= s_rx_regions(r);

        -- mux select corresponds to EOF position within region (in items)
        s_ex_sel(r) <= RX_EOF_POS((r+1)*EOF_POS_WIDTH-1 downto r*EOF_POS_WIDTH);
    end generate;

    ---------------------------------------------------------------------------
    -- ITEMS MULTIPLEXORS
    ---------------------------------------------------------------------------

    items_mux_g : for r in 0 to REGIONS-1 generate
        item_mux_g : for i in 0 to EXTRACTED_ITEMS-1 generate
            -- sliding window of REGION_ITEMS items from the double region buffer
            s_mux_din_2d_arr(r)(i) <= s_double_region(r)((REGION_ITEMS-EXTRACTED_ITEMS+1+i)*ITEM_WIDTH+REGION_WIDTH-1 downto (REGION_ITEMS-EXTRACTED_ITEMS+1+i)*ITEM_WIDTH);

            item_mux_i : entity work.GEN_MUX
            generic map (
                DATA_WIDTH => ITEM_WIDTH,
                MUX_WIDTH  => REGION_ITEMS
            )
            port map (
                DATA_IN  => s_mux_din_2d_arr(r)(i),
                SEL      => s_ex_sel(r),
                DATA_OUT => s_ex_items_arr(r)((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH)
            );
        end generate;

        -- valid signal of extracted items, valid in the cycle when EOF is on input
        s_ex_items_vld(r) <= RX_EOF(r) and RX_SRC_RDY and TX_DST_RDY;
    end generate;

    s_ex_items <= slv_array_ser(s_ex_items_arr, REGIONS, EXTRACTED_WIDTH);

    ---------------------------------------------------------------------------
    -- OUTPUT MFB SIGNAL ASSIGNMENTS
    ---------------------------------------------------------------------------

    TX_DATA    <= RX_DATA;
    TX_META    <= RX_META;
    TX_SOF_POS <= RX_SOF_POS;
    TX_EOF_POS <= RX_EOF_POS;
    TX_SOF     <= RX_SOF;
    TX_EOF     <= RX_EOF;
    TX_SRC_RDY <= RX_SRC_RDY and EX_DST_RDY;
    RX_DST_RDY <= s_dst_rdy;

    ---------------------------------------------------------------------------
    -- OUTPUT REGISTERS WITH EXTRACTED LAST ITEMS
    ---------------------------------------------------------------------------

    ex_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (EX_DST_RDY = '1') then
                EX_DATA <= s_ex_items;
                EX_VLD  <= s_ex_items_vld;
            end if;
        end if;
    end process;

    ex_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                EX_SRC_RDY <= '0';
            elsif (EX_DST_RDY = '1') then
                EX_SRC_RDY <= or s_ex_items_vld;
            end if;
        end if;
    end process;

end architecture;
