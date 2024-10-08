-- mfb_items_vld.vhd: A component that validates Items from the given Offset for the given Length.
-- Copyright (C) 2023 CESNET z.s.p.o.
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

-- This component validates Items from the received offset until the Length is reached.
entity MFB_ITEMS_VLD is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS          : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE      : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE       : natural := 8;
    -- Item width (in bits).
    MFB_ITEM_WIDTH       : natural := 8;
    -- Metadata width (in bits).
    MFB_META_WIDTH       : natural := 0;

    -- Maximum size of a packet (in Items).
    PKT_MTU              : natural := 2**14;

    -- Width of each Offset signal in the in the RX_OFFSET vector.
    OFFSET_WIDTH         : integer := log2(PKT_MTU);
    -- Width of each Length signal in the in the RX_LENGTH vector.
    LENGTH_WIDTH         : integer := log2(PKT_MTU)
);
port(
    -- ========================================================================
    -- Clock and Reset
    -- ========================================================================

    CLK              : in  std_logic;
    RESET            : in  std_logic;

    -- ========================================================================
    -- RX STREAM
    --
    -- #. Input packets (MFB),
    -- #. Meta information.
    -- ========================================================================

    RX_MFB_DATA      : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_META      : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX_MFB_SOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY   : in  std_logic;
    RX_MFB_DST_RDY   : out std_logic;

    -- A vector of Offsets (each in Items), valid with SOF.
    RX_OFFSET        : in  std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);
    -- A vector of Lengths (each in Items), valid with SOF.
    RX_LENGTH        : in  std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
    -- Enable data validation, valid with SOF.
    RX_ENABLE        : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    -- ========================================================================
    -- TX STREAM
    --
    -- Validated data.
    -- ========================================================================

    -- Extracted data for the checksum calculation.
    TX_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_META       : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    -- Valid per each Item.
    TX_END        : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);
    TX_VLD        : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in  std_logic
);
end entity;

architecture FULL of MFB_ITEMS_VLD is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    -- MFB data width.
    constant MFB_DATA_W       : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    -- Maximum amount of Words a single packet can stretch over. (multiplied by 2 for one extra bit)
    constant PKT_MAX_WORDS    : natural := div_roundup(PKT_MTU, MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE) *2;

    -- Number of Items in a Region.
    constant SOFPOS_WORD_W  : natural := log2(MFB_REGIONS) + max(1, log2(MFB_REGION_SIZE)) + log2(MFB_BLOCK_SIZE);
    constant REGION_ITEMS   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant REGION_ITEMS_W : natural := log2(REGION_ITEMS);
    -- MAX_REGIONS = maximum amount of Regions (possibly across multiple words) a single packet can strech over.
    constant MAX_REGIONS_W  : natural := max(0, OFFSET_WIDTH - REGION_ITEMS_W);
    constant WORD_ITEMS_W : natural := log2(MFB_REGIONS) + REGION_ITEMS_W;

    -- Extended
    constant OFFSET_WIDTH_EXT : natural := minimum(max(WORD_ITEMS_W, log2(PKT_MTU)), max(WORD_ITEMS_W, OFFSET_WIDTH+LENGTH_WIDTH)) + 1;
    -- Diminished
    constant OFFSET_WIDTH_DIM : natural := tsel(LENGTH_WIDTH >= REGION_ITEMS_W, LENGTH_WIDTH, REGION_ITEMS_W);

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal rx_length_arr         : u_array_t       (MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal length_not_0          : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal word_cnt              : u_array_t(MFB_REGIONS downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);

    signal rx_offset_arr         : u_array_t(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal rx_mfb_sof_pos_arr    : u_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal rx_sof_pos_word       : u_array_t(MFB_REGIONS-1 downto 0)(SOFPOS_WORD_W-1 downto 0);
    signal global_offset_start   : u_array_t(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_EXT-1 downto 0);
    signal global_offset_end     : u_array_t(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_EXT-1 downto 0);

    signal rx_data_reg0          : std_logic_vector(MFB_DATA_W-1 downto 0);
    signal rx_meta_reg0          : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_word_reg0          : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal rx_word_prev_reg0     : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal rx_offset_start_reg0  : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_EXT-1 downto 0);
    signal rx_offset_end_reg0    : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_EXT-1 downto 0);
    signal rx_valid_reg0         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_src_rdy_reg0       : std_logic;
    signal rx_dst_rdy_reg0       : std_logic;

    signal vp_offset1_start_reg0 : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_offset1_end_reg0   : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_valid1_reg0        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vp_end1_pointer_reg0  : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_end1_reg0          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vp_offset2_start_reg0 : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_offset2_end_reg0   : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_valid2_reg0        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vp_end2_pointer_reg0  : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vp_end2_reg0          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vp_src_rdy_reg0       : std_logic;
    signal vp_dst_rdy_reg0       : std_logic;

    signal rx_data_reg1          : std_logic_vector(MFB_DATA_W-1 downto 0);
    signal rx_data_items_reg1    : slv_array_t     (MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0); -- debug
    signal rx_meta_reg1          : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal vd_offset1_low_reg1   : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_offset1_high_reg1  : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_valid1_reg1        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vd_end1_pointer_reg1  : slv_array_t     (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_end1_reg1          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vd_offset2_low_reg1   : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_offset2_high_reg1  : u_array_t       (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_valid2_reg1        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vd_end2_pointer_reg1  : slv_array_t     (MFB_REGIONS-1 downto 0)(REGION_ITEMS_W-1 downto 0);
    signal vd_end2_reg1          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vd_src_rdy_reg1       : std_logic;
    signal vd_dst_rdy_reg1       : std_logic;

    signal vd_valid_vec_reg1     : std_logic_vector(MFB_REGIONS*            MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);
    signal end1_onehot_reg1      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);
    signal end2_onehot_reg1      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);
    signal end_multihot_reg1     : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE-1 downto 0);

begin

    assert (OFFSET_WIDTH <= log2(PKT_MTU))
        report "MFB_ITEMS_VLD: the value of the OFFSET_WIDTH generic can't be greater than log2(PKT_MTU)!"-- &
            -- " offset width: " & integer'image(OFFSET_WIDTH) &
            -- "log2(MTU): " & integer'image(log2(PKT_MTU))
        severity failure;

    assert (LENGTH_WIDTH <= log2(PKT_MTU))
        report "MFB_ITEMS_VLD: the value of the LENGTH_WIDTH generic can't be greater than the log2(PKT_MTU)!"-- &
            -- " length width: " & integer'image(LENGTH_WIDTH) &
            -- "log2(MTU): " & integer'image(log2(PKT_MTU))
        severity failure;

    -- TODO: Add more asserts ?
    -- for current offset+length?

    RX_MFB_DST_RDY <= rx_dst_rdy_reg0;

    -- -----------------------
    --  Validate input length
    -- -----------------------
    rx_length_arr <= slv_arr_to_u_arr(slv_array_deser(RX_LENGTH, MFB_REGIONS));
    length_check_g : for r in 0 to MFB_REGIONS-1 generate
        length_not_0(r) <= '1' when (rx_length_arr(r) > 0) else '0';
    end generate;

    -- --------------
    --  Word counter
    -- --------------
    word_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RX_MFB_SRC_RDY = '1') and (rx_dst_rdy_reg0 = '1') then
                word_cnt(0) <= word_cnt(MFB_REGIONS) + 1;
            end if;
            if (RESET = '1') then
                word_cnt(0) <= (others => '0');
            end if;
        end if;
    end process;

    -- Current (Valid) counts are at word_cnt(MFB_REGIONS downto 1) and
    -- word_cnt(0) carries the value from the previous clock cycle
    word_cnt_g: for r in 0 to MFB_REGIONS-1 generate
        word_cnt(r+1) <= (others => '0') when (RX_MFB_SOF(r) = '1') and (length_not_0(r) = '1') else word_cnt(r);
    end generate;

    -- -----------------------
    --  Offset precalculation
    -- -----------------------
    rx_offset_arr      <= slv_arr_to_u_arr(slv_array_deser(RX_OFFSET     , MFB_REGIONS));
    rx_mfb_sof_pos_arr <= slv_arr_to_u_arr(slv_array_deser(RX_MFB_SOF_POS, MFB_REGIONS));
    act_offset_g : for r in 0  to MFB_REGIONS-1 generate
        rx_sof_pos_word(r) <= to_unsigned(r, log2(MFB_REGIONS)) &   -- add the Regional prefix
                              rx_mfb_sof_pos_arr(r)             &   -- to the SOF POS
                              to_unsigned(0, log2(MFB_BLOCK_SIZE)); -- and conver it to Items
        -- Global Offset begins from the start of the word rather than the SOF POS.
        -- Start Offset points to the first Item of the Section-to-be-validated
        global_offset_start(r) <= resize_left(rx_offset_arr(r), OFFSET_WIDTH_EXT) + resize_left(rx_sof_pos_word(r), WORD_ITEMS_W);
        -- End Offset points to the last Item of the Section-to-be-validated
        global_offset_end  (r) <= global_offset_start(r) + rx_length_arr(r)-1;
    end generate;

    -- ========================================================================
    -- Input register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (rx_dst_rdy_reg0 = '1') then
                rx_data_reg0          <= RX_MFB_DATA;
                rx_meta_reg0          <= RX_MFB_META;

                rx_word_reg0          <= word_cnt(MFB_REGIONS   downto 1);
                rx_word_prev_reg0     <= word_cnt(MFB_REGIONS-1 downto 0);

                rx_offset_start_reg0  <= global_offset_start;
                rx_offset_end_reg0    <= global_offset_end;
                rx_valid_reg0         <= RX_MFB_SOF and RX_MFB_SRC_RDY and length_not_0 and RX_ENABLE;

                rx_src_rdy_reg0       <= RX_MFB_SRC_RDY;
            end if;

            if (RESET = '1') then
                rx_src_rdy_reg0 <= '0';
            end if;
        end if;
    end process;

    -- ------------------------
    --  Prepare for validation
    -- ------------------------
    validation_prepare_i : entity work.VALIDATION_PREPARE
    generic map(
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        MAX_WORDS       => PKT_MAX_WORDS  ,
        OFFSET_WIDTH    => OFFSET_WIDTH_EXT
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_WORD          => rx_word_reg0         ,
        RX_WORD_PREV     => rx_word_prev_reg0    ,
        RX_OFFSET_START  => rx_offset_start_reg0 ,
        RX_OFFSET_END    => rx_offset_end_reg0   ,
        RX_VALID         => rx_valid_reg0        ,
        RX_SRC_RDY       => rx_src_rdy_reg0      ,
        RX_DST_RDY       => rx_dst_rdy_reg0      ,

        TX_OFFSET1_START => vp_offset1_start_reg0,
        TX_OFFSET1_END   => vp_offset1_end_reg0  ,
        TX_END1_POINTER  => vp_end1_pointer_reg0 ,
        TX_END1          => vp_end1_reg0         ,
        TX_VALID1        => vp_valid1_reg0       ,

        TX_OFFSET2_START => vp_offset2_start_reg0,
        TX_OFFSET2_END   => vp_offset2_end_reg0  ,
        TX_END2_POINTER  => vp_end2_pointer_reg0 ,
        TX_END2          => vp_end2_reg0         ,
        TX_VALID2        => vp_valid2_reg0       ,

        TX_SRC_RDY       => vp_src_rdy_reg0      ,
        TX_DST_RDY       => vp_dst_rdy_reg0
    );

    -- ----------------------------------------
    --  Secong stage (Mid-validation) register
    -- ----------------------------------------
    vp_dst_rdy_reg0 <= vd_dst_rdy_reg1;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (vd_dst_rdy_reg1 = '1') then
                rx_data_reg1         <= rx_data_reg0;
                rx_data_items_reg1   <= slv_array_deser(rx_data_reg0, MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE); -- Debug data signal
                rx_meta_reg1         <= rx_meta_reg0;

                vd_offset1_low_reg1  <= vp_offset1_start_reg0;
                vd_offset1_high_reg1 <= vp_offset1_end_reg0;
                vd_valid1_reg1       <= vp_valid1_reg0;
                vd_end1_pointer_reg1 <= u_arr_to_slv_arr(vp_end1_pointer_reg0);
                vd_end1_reg1         <= vp_end1_reg0;

                vd_offset2_low_reg1  <= vp_offset2_start_reg0;
                vd_offset2_high_reg1 <= vp_offset2_end_reg0;
                vd_valid2_reg1       <= vp_valid2_reg0;
                vd_end2_pointer_reg1 <= u_arr_to_slv_arr(vp_end2_pointer_reg0);
                vd_end2_reg1         <= vp_end2_reg0;

                vd_src_rdy_reg1      <= vp_src_rdy_reg0;
            end if;

            if (RESET = '1') then
                vd_valid1_reg1  <= (others => '0');
                vd_valid2_reg1  <= (others => '0');
                vd_src_rdy_reg1 <= '0';
            end if;
        end if;
    end process;

    -- -----------------------------
    --  Do (perform) the validation
    -- -----------------------------
    validation_do_i : entity work.VALIDATION_DO
    generic map(
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE
    )
    port map(
        OFFSET1_LOW  => vd_offset1_low_reg1 ,
        OFFSET1_HIGH => vd_offset1_high_reg1,
        VALID1       => vd_valid1_reg1      ,

        OFFSET2_LOW  => vd_offset2_low_reg1 ,
        OFFSET2_HIGH => vd_offset2_high_reg1,
        VALID2       => vd_valid2_reg1      ,

        VALID_VECTOR => vd_valid_vec_reg1
    );

    -- -----------------------
    --  Create the End vector
    -- -----------------------
    end_g : for r in 0 to MFB_REGIONS-1 generate

        bin2hot_1_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => REGION_ITEMS_W
        )
        port map(
            EN     => vd_end1_reg1        (r),
            INPUT  => vd_end1_pointer_reg1(r),
            OUTPUT => end1_onehot_reg1    (r)
        );

        bin2hot_2_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => REGION_ITEMS_W
        )
        port map(
            EN     => vd_end2_reg1        (r),
            INPUT  => vd_end2_pointer_reg1(r),
            OUTPUT => end2_onehot_reg1    (r)
        );

        end_multihot_reg1(r) <= end1_onehot_reg1(r) or end2_onehot_reg1(r);

    end generate;

    -- ========================================================================
    -- Output register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_DST_RDY = '1') then
                TX_DATA    <= rx_data_reg1;
                TX_META    <= rx_meta_reg1;
                TX_END     <= slv_array_ser(end_multihot_reg1);
                TX_VLD     <= vd_src_rdy_reg1 and vd_valid_vec_reg1;
                TX_SRC_RDY <= vd_src_rdy_reg1 and (or vd_valid_vec_reg1); -- TODO
            end if;

            if (RESET = '1') then
                TX_VLD     <= (others => '0');
                TX_END     <= (others => '0');
                TX_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    vd_dst_rdy_reg1 <= TX_DST_RDY;

end architecture;
