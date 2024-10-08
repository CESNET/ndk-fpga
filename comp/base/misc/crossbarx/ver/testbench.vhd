-- testbench.vhd: Verification unit for CrossbarX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.basics_test_pkg.all;
use work.test_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

    -- Synchronization
    signal clk                                : std_logic;
    signal clk2                               : std_logic;
    signal reset                              : std_logic := '1';

    signal clk_arb                            : std_logic;
    signal reset_arb                          : std_logic := '1';

    -- uut I/O

    signal trans_record         : trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    signal trans_a_col          : slv_array_t     (TRANS_STREAMS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal trans_a_item         : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_A_STREAM_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_b_col          : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal trans_b_item         : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_len            : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal trans_meta           : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(TRANS_WIDTH-TRANS_LENGTH_MAX*ITEM_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal trans_vld            : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    signal trans_src_rdy        : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trans_dst_rdy        : std_logic_vector(TRANS_STREAMS-1 downto 0);

    signal trans_true_src_rdy   : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    signal src_buf_rd_addr      : slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS))-1 downto 0);
    signal src_buf_rd_data      : slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);

    signal dst_buf_wr_addr      : slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS))-1 downto 0);
    signal dst_buf_wr_data      : slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);
    signal dst_buf_wr_ie        : slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(ROW_ITEMS-1 downto 0); -- Item enable
    signal dst_buf_wr_en        : std_logic_vector(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0);

    signal trans_comp_meta      : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(TRANS_WIDTH-TRANS_LENGTH_MAX*ITEM_WIDTH-1 downto 0);
    signal trans_comp_src_rdy   : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    signal trans_comp_dst_rdy   : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    signal trans_comp_record    : trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    signal trans_filled_record  : trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    signal trans_filled_src_rdy : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    signal trans_filled_dst_rdy : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

begin

    -- -------------------------------------------------------------------------
    -- UUT
    -- -------------------------------------------------------------------------

    uut : entity work.CROSSBARX
    generic map(
        DATA_DIR            => DATA_DIR           ,
        USE_CLK2            => USE_CLK2           ,
        USE_CLK_ARB         => USE_CLK_ARB        ,
        TRANS_STREAMS       => TRANS_STREAMS      ,
        BUF_A_COLS          => BUF_A_COLS         ,
        BUF_A_STREAM_ROWS   => BUF_A_STREAM_ROWS  ,
        BUF_A_ROWS          => BUF_A_ROWS         ,
        BUF_B_COLS          => BUF_B_COLS         ,
        BUF_B_ROWS          => BUF_B_ROWS         ,
        BUF_A_SECTIONS      => BUF_A_SECTIONS     ,
        BUF_B_SECTIONS      => BUF_B_SECTIONS     ,
        ROW_ITEMS           => ROW_ITEMS          ,
        ITEM_WIDTH          => ITEM_WIDTH         ,
        TRANSS              => TRANSS             ,
        TRANS_MTU           => TRANS_MTU          ,
        METADATA_WIDTH      => TRANS_WIDTH-TRANS_LENGTH_MAX*ITEM_WIDTH,
        TRANS_FIFO_ITEMS    => TRANS_FIFO_ITEMS   ,
        COLOR_TIMEOUT_WIDTH => COLOR_TIMEOUT_WIDTH,
        COLOR_CONF_DELAY    => COLOR_CONF_DELAY   ,
        RD_LATENCY          => RD_LATENCY         ,
        DATA_MUX_LAT        => DATA_MUX_LAT       ,
        DATA_MUX_OUTREG_EN  => DATA_MUX_OUTREG_EN ,
        DATA_ROT_LAT        => DATA_ROT_LAT       ,
        DATA_ROT_OUTREG_EN  => DATA_ROT_OUTREG_EN ,
        DEVICE              => DEVICE
    )
    port map(
        CLK                => clk  ,
        CLK2               => clk2 ,
        RESET              => reset,

        CLK_ARB            => clk_arb  ,
        RESET_ARB          => reset_arb,

        TRANS_A_COL        => trans_a_col       ,
        TRANS_A_ITEM       => trans_a_item      ,
        TRANS_B_COL        => trans_b_col       ,
        TRANS_B_ITEM       => trans_b_item      ,
        TRANS_LEN          => trans_len         ,
        TRANS_META         => trans_meta        ,
        TRANS_VLD          => trans_vld         ,
        TRANS_SRC_RDY      => trans_src_rdy     ,
        TRANS_DST_RDY      => trans_dst_rdy     ,

        SRC_BUF_RD_ADDR    => src_buf_rd_addr   ,
        SRC_BUF_RD_DATA    => src_buf_rd_data   ,

        DST_BUF_WR_ADDR    => dst_buf_wr_addr   ,
        DST_BUF_WR_DATA    => dst_buf_wr_data   ,
        DST_BUF_WR_IE      => dst_buf_wr_ie     ,
        DST_BUF_WR_EN      => dst_buf_wr_en     ,

        TRANS_COMP_META    => trans_comp_meta   ,
        TRANS_COMP_SRC_RDY => trans_comp_src_rdy,
        TRANS_COMP_DST_RDY => trans_comp_dst_rdy
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Comp Transaction FIFO
    -- -------------------------------------------------------------------------

    comp_trans_fifo_gen : for i in 0 to TRANS_STREAMS-1 generate

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Tester unit
    -- -------------------------------------------------------------------------

    tester_i : entity work.CROSSBARX_TESTER
    port map(
        CLK                => clk  ,
        RESET              => reset,

        TX_TRANS_RECORD    => trans_record ,
        TX_TRANS_VLD       => trans_vld    ,
        TX_TRANS_SRC_RDY   => trans_src_rdy,
        TX_TRANS_DST_RDY   => trans_dst_rdy,

        RX_TRANS_RECORD    => trans_filled_record ,
        RX_TRANS_SRC_RDY   => trans_filled_src_rdy,
        RX_TRANS_DST_RDY   => trans_filled_dst_rdy
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- SRC Buffer
    -- -------------------------------------------------------------------------

    src_buf_i : entity work.CROSSBARX_VER_RX_BUF
    port map(
        CLK                => clk  ,
        CLK2               => clk2 ,
        RESET              => reset,

        RX_TRANS_RECORD    => trans_record      ,
        RX_TRANS_SRC_RDY   => trans_true_src_rdy,

        SRC_BUF_RD_ADDR    => src_buf_rd_addr,
        SRC_BUF_RD_DATA    => src_buf_rd_data
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- DST Buffer
    -- -------------------------------------------------------------------------

    dst_buf_i : entity work.CROSSBARX_VER_TX_BUF
    port map(
        CLK                => clk  ,
        CLK2               => clk2 ,
        RESET              => reset,

        RX_TRANS_RECORD    => trans_comp_record ,
        RX_TRANS_SRC_RDY   => trans_comp_src_rdy,
        RX_TRANS_DST_RDY   => trans_comp_dst_rdy,

        TX_TRANS_RECORD    => trans_filled_record ,
        TX_TRANS_SRC_RDY   => trans_filled_src_rdy,
        TX_TRANS_DST_RDY   => trans_filled_dst_rdy,

        DST_BUF_WR_ADDR    => dst_buf_wr_addr,
        DST_BUF_WR_DATA    => dst_buf_wr_data,
        DST_BUF_WR_IE      => dst_buf_wr_ie  ,
        DST_BUF_WR_EN      => dst_buf_wr_en
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- CLK and RESET generation
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen: process
    begin
        clk <= '1';
        wait for C_CLK_PER / 2;
        clk <= '0';
        wait for C_CLK_PER / 2;
    end process;

    clk_other_gen : if (USE_CLK_ARB) generate
        -- generating clk_arb
        clk_arb_gen: process
        begin
            clk_arb <= '1';
            clk2    <= '1';
            wait for C_CLK_ARB_PER / 2;
            clk_arb <= '0';
            clk2    <= '0';
            wait for C_CLK_ARB_PER / 2;
        end process;
    else generate
        clk_arb   <= '0';
        -- generating clk2
        clk2_gen: process
        begin
            clk2 <= '1';
            wait for C_CLK_PER / 4;
            clk2 <= '0';
            wait for C_CLK_PER / 4;
        end process;
    end generate;

    -- generating reset
    rst_gen: process
    begin
        reset <= '1';
        wait for C_CLK_PER * 16;
        reset <= '0';
        wait;
    end process;

    -- generating reset_arb
    rst_arb_gen: process
    begin
        reset_arb <= '1';
        wait for C_CLK_PER * 16;
        reset_arb <= '0';
        wait;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Metadata/Record conversions
    -- -------------------------------------------------------------------------

    meta_record_conv_pr : process (all)
    begin
        for i in 0 to TRANS_STREAMS-1 loop
            trans_true_src_rdy(i) <= trans_vld(i) and trans_src_rdy(i) and trans_dst_rdy(i);
            for e in 0 to TRANSS-1 loop
                trans_meta       (i)(e) <= std_logic_vector(enlarge_right(unsigned(trans_ser(trans_record(i)(e))),-TRANS_LENGTH_MAX*ITEM_WIDTH));
                trans_a_item(i)(e) <= std_logic_vector(enlarge_left(to_unsigned(trans_record(i)(e).a_ptr,log2(BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS)),-log2(BUF_A_SECTION_COLS)));
                trans_b_col (i)(e) <= std_logic_vector(unsigned'(to_unsigned(trans_record(i)(e).b_section,log2(BUF_B_SECTIONS)) & resize_right(to_unsigned(trans_record(i)(e).b_ptr,log2(BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS)),log2(BUF_B_SECTION_COLS))));
                trans_b_item(i)(e) <= std_logic_vector(enlarge_left(to_unsigned(trans_record(i)(e).b_ptr,log2(BUF_B_SECTION_COLS*BUF_B_ROWS*ROW_ITEMS)),-log2(BUF_B_SECTION_COLS)));
                trans_len   (i)(e) <= std_logic_vector(to_unsigned(trans_record(i)(e).length,log2(TRANS_MTU+1)));
                if (trans_vld(i)(e)='1') then
                    trans_a_col(i) <= std_logic_vector(unsigned'(to_unsigned(trans_record(i)(e).a_section,log2(BUF_A_SECTIONS)) & resize_right(to_unsigned(trans_record(i)(e).a_ptr,log2(BUF_A_SECTION_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS)),log2(BUF_A_SECTION_COLS))));
                end if;
            end loop;
            for e in 0 to TRANSS-1 loop
                trans_comp_record(i)(e) <= trans_deser(std_logic_vector(enlarge_right(unsigned(trans_comp_meta(i)(e)),TRANS_LENGTH_MAX*ITEM_WIDTH)));
            end loop;

        end loop;
    end process;

    -- -------------------------------------------------------------------------

end architecture;
