-- mfb_frame_extender_dm_ctrl.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_FRAME_EXTENDER_DM_CTRL is
    generic(
        REGIONS        : natural := 4;
        REGION_SIZE    : natural := 8;
        BLOCK_SIZE     : natural := 8;
        ITEM_WIDTH     : natural := 8;
        USERMETA_WIDTH : natural := 8;
        LEN_WIDTH      : natural := 14;
        DEVICE         : string  := "AGILEX"
    );
    port(
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        RX_INSERT      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_OFFSET      : in  std_logic_vector(REGIONS*LEN_WIDTH-1 downto 0);
        RX_USERMETA    : in  std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
        RX_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY     : in  std_logic;
        RX_DST_RDY     : out std_logic;

        TX_INSERT_MOVE : out slv_array_t(REGIONS*REGION_SIZE-1 downto 0)(log2(REGIONS*REGION_SIZE)-1 downto 0);
        TX_INSERT_MASK : out std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);
        TX_INSERT_VLD  : out std_logic;
        TX_USERMETA    : out std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
        TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY     : out std_logic;
        TX_DST_RDY     : in  std_logic
    );
end entity;

architecture FULL of MFB_FRAME_EXTENDER_DM_CTRL is

    constant REGION_ITEMS   : natural := REGION_SIZE*BLOCK_SIZE;
    constant SOF_POS_WIDTH  : natural := log2(REGION_SIZE);
    constant EOF_POS_WIDTH  : natural := log2(REGION_ITEMS);
    constant WORD_BLOCKS    : natural := REGIONS*REGION_SIZE;
    constant WORD_ITEMS     : natural := REGIONS*REGION_ITEMS;
    constant WORD_CNT_WIDTH : natural := LEN_WIDTH - log2(WORD_ITEMS);

    signal s_rx_word_cnt             : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_word_cnt_prev        : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_word_cnt_reg         : unsigned(WORD_CNT_WIDTH-1 downto 0);

    signal s_rx_sof_pos              : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos              : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_pl_offset            : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);

    signal s_rx_sof_pos_ext          : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_sof_after_eof        : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_after_eof_vld    : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_before_eof_vld   : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_offset_ext_curr   : u_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_rx_pl_offset_ext        : u_array_t(REGIONS+1-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_insert_lvld             : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_insert_fpir             : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_word_off          : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_pl_region_off        : u_array_t(REGIONS-1 downto 0)(log2(REGIONS)-1 downto 0);
    signal s_rx_pl_block_off         : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE)-1 downto 0);
    signal s_rx_pl_word_off_prev     : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_pl_region_off_prev   : u_array_t(REGIONS-1 downto 0)(log2(REGIONS)-1 downto 0);
    signal s_rx_pl_block_off_prev    : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE)-1 downto 0);
    signal s_rx_pl_word_ok           : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_region_ok         : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_word_prev_ok      : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_region_prev_ok    : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_ok                : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_prev_ok           : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_eof_pos_blk          : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_masked           : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_pl_block_en          : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_rx_pl_block_prev_en     : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_pof_per_wb              : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_eof_per_wb              : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal s_usermeta_reg0           : std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
    signal s_sof_pos_reg0            : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_eof_pos_reg0            : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_sof_reg0                : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg0                : std_logic_vector(REGIONS-1 downto 0);
    signal s_pof_per_wb_reg0         : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_eof_per_wb_reg0         : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_src_rdy_reg0            : std_logic;

    signal s_pl_continues            : std_logic_vector(WORD_BLOCKS+1-1 downto 0);
    signal s_pl_valid                : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal s_usermeta_reg1           : std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
    signal s_sof_pos_reg1            : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_eof_pos_reg1            : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_sof_reg1                : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg1                : std_logic_vector(REGIONS-1 downto 0);
    signal s_pl_valid_reg1           : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_src_rdy_reg1            : std_logic;

    signal s_insert_mask             : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_insert_move             : slv_array_t(WORD_BLOCKS-1 downto 0)(log2(WORD_BLOCKS)-1 downto 0);
    signal s_insert                  : std_logic;

    signal s_usermeta_reg2           : std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
    signal s_sof_pos_reg2            : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_eof_pos_reg2            : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_sof_reg2                : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg2                : std_logic_vector(REGIONS-1 downto 0);
    signal s_insert_mask_reg2        : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_insert_move_reg2        : slv_array_t(WORD_BLOCKS-1 downto 0)(log2(WORD_BLOCKS)-1 downto 0);
    signal s_insert_reg2             : std_logic;
    signal s_src_rdy_reg2            : std_logic;

begin

    RX_DST_RDY <= TX_DST_RDY;

    -- ==========================================================================
    --  0. LOGIC STAGE
    -- ==========================================================================

    -- --------------------------------------------------------------------------
    --  RX WORD COUNTER
    -- --------------------------------------------------------------------------

    rx_word_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_rx_word_cnt_reg <= (others => '0');
            elsif (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_rx_word_cnt_reg <= s_rx_word_cnt(REGIONS-1) + 1;
            end if;
        end if;
    end process;

    s_rx_word_cnt(0) <= (others => '0') when ((RX_SOF(0) = '1')) else s_rx_word_cnt_reg;
    rx_word_cnt_g : for r in 1 to REGIONS-1 generate
        s_rx_word_cnt(r) <= (others => '0') when (RX_SOF(r) = '1') else s_rx_word_cnt(r-1);
    end generate;

    s_rx_word_cnt_prev(0) <= s_rx_word_cnt_reg;
    rx_word_cnt_prev_g : for r in 1 to REGIONS-1 generate
        s_rx_word_cnt_prev(r) <= (others => '0') when (RX_SOF(r-1) = '1') else s_rx_word_cnt(r-1);
    end generate;

    -- --------------------------------------------------------------------------
    --  PACKET PREPARE
    -- --------------------------------------------------------------------------

    s_rx_sof_pos   <= slv_array_deser(RX_SOF_POS, REGIONS, SOF_POS_WIDTH);
    s_rx_eof_pos   <= slv_array_deser(RX_EOF_POS, REGIONS, EOF_POS_WIDTH);
    s_rx_pl_offset <= slv_array_deser(RX_OFFSET, REGIONS, LEN_WIDTH);

    rx_pl_offset_ext_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_rx_pl_offset_ext(0) <= s_rx_pl_offset_ext(REGIONS);
            end if;
        end if;
    end process;

    payload_lvld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_insert_lvld(0) <= '0';
            elsif (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_insert_lvld(0) <= s_insert_lvld(REGIONS);
            end if;
        end if;
    end process;

    pl_offset_g : for r in 0 to REGIONS-1 generate
        s_rx_sof_pos_ext(r) <= unsigned(s_rx_sof_pos(r)) & to_unsigned(0,log2(BLOCK_SIZE));
        s_rx_eof_pos_blk(r) <= s_rx_eof_pos(r)(EOF_POS_WIDTH-1 downto log2(BLOCK_SIZE));
        s_rx_sof_after_eof(r) <= '1' when (unsigned(s_rx_sof_pos(r)) > unsigned(s_rx_eof_pos_blk(r))) else '0';
        s_rx_sof_after_eof_vld(r)  <= s_rx_sof_after_eof(r) and RX_SOF(r) and RX_EOF(r);
        s_rx_sof_before_eof_vld(r) <= not s_rx_sof_after_eof(r) and RX_SOF(r) and RX_EOF(r);

        s_rx_pl_offset_ext_curr(r) <= unsigned(s_rx_pl_offset(r)) + (r*REGION_SIZE*BLOCK_SIZE) + s_rx_sof_pos_ext(r);
        s_rx_pl_offset_ext(r+1) <= s_rx_pl_offset_ext_curr(r) when (RX_SOF(r) = '1') else s_rx_pl_offset_ext(r);

        -- last valid of payload valid
        s_insert_lvld(r+1) <= RX_INSERT(r) when (RX_SOF(r) = '1') else s_insert_lvld(r);
        -- payload valid of first packet in region
        s_insert_fpir(r) <= RX_INSERT(r) when (s_rx_sof_before_eof_vld(r) = '1') else s_insert_lvld(r);

        s_rx_pl_word_off(r)        <= s_rx_pl_offset_ext(r+1)(LEN_WIDTH-1 downto log2(REGIONS*REGION_ITEMS));
        s_rx_pl_region_off(r)      <= s_rx_pl_offset_ext(r+1)(log2(REGIONS*REGION_ITEMS)-1 downto log2(REGION_ITEMS));
        s_rx_pl_block_off(r)       <= s_rx_pl_offset_ext(r+1)(log2(REGION_ITEMS)-1 downto log2(BLOCK_SIZE));
        s_rx_pl_word_off_prev(r)   <= s_rx_pl_offset_ext(r)(LEN_WIDTH-1 downto log2(REGIONS*REGION_ITEMS));
        s_rx_pl_region_off_prev(r) <= s_rx_pl_offset_ext(r)(log2(REGIONS*REGION_ITEMS)-1 downto log2(REGION_ITEMS));
        s_rx_pl_block_off_prev(r)  <= s_rx_pl_offset_ext(r)(log2(REGION_ITEMS)-1 downto log2(BLOCK_SIZE));

        s_rx_pl_word_ok(r)        <= '1' when (s_rx_pl_word_off(r) = s_rx_word_cnt(r)) else '0';
        s_rx_pl_region_ok(r)      <= '1' when (REGIONS = 1) or (s_rx_pl_region_off(r) = r) else '0';
        s_rx_pl_word_prev_ok(r)   <= '1' when (s_rx_pl_word_off_prev(r) = s_rx_word_cnt_prev(r)) else '0';
        s_rx_pl_region_prev_ok(r) <= '1' when (REGIONS = 1) or (s_rx_pl_region_off_prev(r) = r) else '0';

        s_rx_pl_ok(r)      <= s_rx_pl_word_ok(r) and s_rx_pl_region_ok(r) and s_insert_lvld(r+1);
        s_rx_pl_prev_ok(r) <= s_rx_pl_word_prev_ok(r) and s_rx_pl_region_prev_ok(r) and s_insert_lvld(r) and s_rx_sof_after_eof_vld(r);
    end generate;

    -- --------------------------------------------------------------------------
    --  START OF PAYLOAD PER WORD BLOCK
    -- --------------------------------------------------------------------------

    pl_onehot_g : for r in 0 to REGIONS-1 generate
        pl_onehot_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => log2(REGION_SIZE)
        )
        port map(
            EN     => s_rx_pl_ok(r),
            INPUT  => std_logic_vector(s_rx_pl_block_off(r)),
            OUTPUT => s_rx_pl_block_en((r+1)*REGION_SIZE-1 downto r*REGION_SIZE)
        );

        pl_prev_onehot_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => log2(REGION_SIZE)
        )
        port map(
            EN     => s_rx_pl_prev_ok(r),
            INPUT  => std_logic_vector(s_rx_pl_block_off_prev(r)),
            OUTPUT => s_rx_pl_block_prev_en((r+1)*REGION_SIZE-1 downto r*REGION_SIZE)
        );
    end generate;

    s_pof_per_wb <= s_rx_pl_block_en or s_rx_pl_block_prev_en;

    -- --------------------------------------------------------------------------
    --  END OF PACKET PER WORD BLOCK
    -- --------------------------------------------------------------------------

    eof_per_wb_g : for r in 0 to REGIONS-1 generate
        s_rx_eof_masked(r) <= RX_EOF(r) and s_insert_fpir(r);

        sof_pos_onehot_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => log2(REGION_SIZE)
        )
        port map(
            EN     => s_rx_eof_masked(r),
            INPUT  => s_rx_eof_pos_blk(r),
            OUTPUT => s_eof_per_wb((r+1)*REGION_SIZE-1 downto r*REGION_SIZE)
        );
    end generate;

    -- ==========================================================================
    --  0. REGISTERS STAGE
    -- ==========================================================================

    reg0_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                s_usermeta_reg0   <= RX_USERMETA;
                s_sof_pos_reg0    <= RX_SOF_POS;
                s_eof_pos_reg0    <= RX_EOF_POS;
                s_sof_reg0        <= RX_SOF;
                s_eof_reg0        <= RX_EOF;
                s_pof_per_wb_reg0 <= s_pof_per_wb;
                s_eof_per_wb_reg0 <= s_eof_per_wb;
            end if;
        end if;
    end process;

    vld_reg0_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg0 <= '0';
            elsif (TX_DST_RDY = '1') then
                s_src_rdy_reg0 <= RX_SRC_RDY;
            end if;
        end if;
    end process;

    -- ==========================================================================
    --  1. LOGIC STAGE
    -- ==========================================================================

    -- --------------------------------------------------------------------------
    --  PAYLOAD BLOCK VALID
    -- --------------------------------------------------------------------------

    pl_continues_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_pl_continues(0) <= '0';
            elsif (s_src_rdy_reg0 = '1' and TX_DST_RDY = '1') then
                s_pl_continues(0) <= s_pl_continues(WORD_BLOCKS);
            end if;
        end if;
    end process;

    pl_continues_paraller_g : for i in 0 to WORD_BLOCKS-1 generate
        pl_continues_paraller_p : process (s_pl_continues,s_pof_per_wb_reg0,s_eof_per_wb_reg0)
            variable v_continues : std_logic;
        begin
            v_continues := s_pl_continues(0);
            pl_continues_l : for j in 0 to i loop
                v_continues := (s_pof_per_wb_reg0(j) or v_continues) and not s_eof_per_wb_reg0(j);
            end loop;
            s_pl_continues(i+1) <= v_continues;
        end process;
    end generate;

    pl_valid_g : for i in 0 to WORD_BLOCKS-1 generate
        s_pl_valid(i) <= s_pof_per_wb_reg0(i) or (s_pl_continues(i));
    end generate;

    -- ==========================================================================
    --  1. REGISTERS STAGE
    -- ==========================================================================

    reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                s_usermeta_reg1 <= s_usermeta_reg0;
                s_sof_pos_reg1  <= s_sof_pos_reg0;
                s_eof_pos_reg1  <= s_eof_pos_reg0;
                s_sof_reg1      <= s_sof_reg0;
                s_eof_reg1      <= s_eof_reg0;
                s_pl_valid_reg1 <= s_pl_valid;
            end if;
        end if;
    end process;

    vld_reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg1 <= '0';
            elsif (TX_DST_RDY = '1') then
                s_src_rdy_reg1 <= s_src_rdy_reg0;
            end if;
        end if;
    end process;

    -- ==========================================================================
    --  2. LOGIC STAGE
    -- ==========================================================================

    -- --------------------------------------------------------------------------
    --  COMPUTING INSERT_MASK VECTOR
    -- --------------------------------------------------------------------------

    insert_mask_i : entity work.SHAKEDOWN
    generic map(
        INPUTS     => REGIONS*REGION_SIZE,
        OUTPUTS    => REGIONS*REGION_SIZE,
        DATA_WIDTH => 1
    )
    port map(
        CLK      => CLK,
        RESET    => RESET,
        DIN      => (others => '0'),
        DIN_VLD  => s_pl_valid_reg1,
        DOUT     => open,
        DOUT_VLD => s_insert_mask
    );

    -- --------------------------------------------------------------------------
    --  SELECT OF MULTIPLEXORS
    -- --------------------------------------------------------------------------

    insert_move_g : for i in 0 to REGIONS*REGION_SIZE-1 generate
        insert_move_p : process (s_pl_valid_reg1)
            variable v_count : natural range 0 to i+1;
            variable v_addr  : natural range 0 to i;
        begin
            v_count := 0;
            block_l : for j in 0 to i loop
                if (s_pl_valid_reg1(j) = '1') then
                v_count := v_count + 1;
                end if;
            end loop;

            if (v_count = 0) then
                v_addr := 0;
            else
                v_addr := v_count - 1;
            end if;

            s_insert_move(i) <= std_logic_vector(to_unsigned(v_addr,log2(REGIONS*REGION_SIZE)));
        end process;
    end generate;

    -- --------------------------------------------------------------------------
    --  COMPUTING NEED PAYLOAD BIT
    -- --------------------------------------------------------------------------

    s_insert <= (or s_pl_valid_reg1) and s_src_rdy_reg1;

    -- ==========================================================================
    --  2. REGISTERS STAGE
    -- ==========================================================================

    reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                s_usermeta_reg2    <= s_usermeta_reg1;
                s_sof_pos_reg2     <= s_sof_pos_reg1;
                s_eof_pos_reg2     <= s_eof_pos_reg1;
                s_sof_reg2         <= s_sof_reg1;
                s_eof_reg2         <= s_eof_reg1;
                s_insert_mask_reg2 <= s_insert_mask;
                s_insert_move_reg2 <= s_insert_move;
            end if;
        end if;
    end process;

    vld_reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg2 <= '0';
                s_insert_reg2  <= '0';
            elsif (TX_DST_RDY = '1') then
                s_src_rdy_reg2 <= s_src_rdy_reg1;
                s_insert_reg2  <= s_insert;
            end if;
        end if;
    end process;

    -- ==========================================================================
    --  TX SIGNALS
    -- ==========================================================================

    TX_USERMETA    <= s_usermeta_reg2;
    TX_SOF_POS     <= s_sof_pos_reg2;
    TX_EOF_POS     <= s_eof_pos_reg2;
    TX_SOF         <= s_sof_reg2;
    TX_EOF         <= s_eof_reg2;
    TX_SRC_RDY     <= s_src_rdy_reg2;
    TX_INSERT_MASK <= s_insert_mask_reg2;
    TX_INSERT_MOVE <= s_insert_move_reg2;
    TX_INSERT_VLD  <= s_insert_reg2;

end architecture;
