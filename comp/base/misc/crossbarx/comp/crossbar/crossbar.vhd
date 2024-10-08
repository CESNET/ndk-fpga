-- crossbar.vhd: Crossbar data transfer crossbar
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_CROSSBAR is
generic (
    -- Transfer data on double frequency Clock
    USE_CLK2        : boolean := true;

    -- Source buffer size
    SRC_BUF_COLS    : integer := 512;
    SRC_BUF_ROWS    : integer := 8;
    -- Destination buffer size
    DST_BUF_COLS    : integer := 512;
    DST_BUF_ROWS    : integer := 4;

    -- Number of items in one bufer row
    ROW_ITEMS       : integer := 8;
    -- Width of one item
    ITEM_WIDTH      : integer := 8;

    -- Source buffer read latency
    RD_LATENCY      : integer := 1;

    -- Data multiplexer's latency (increase for better timing)
    DATA_MUX_LATENCY            : integer := 0;
    -- Data multiplexer's output register enable (set to TRUE for better timing)
    DATA_MUX_OUTPUT_REG_EN      : boolean := true;

    -- Data blocks rotation latency (increase for better timing)
    DATA_ROTATION_LATENCY       : integer := 0;
    -- Data blocks rotation output register enable (set to TRUE for better timing)
    DATA_ROTATION_OUTPUT_REG_EN : boolean := true;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE          : string := "STRATIX10"
);
port (
    -- =================================
    -- Clock and reset
    -- =================================

    CLK             : in  std_logic;
    CLK2            : in  std_logic;
    RESET           : in  std_logic;

    -- =================================
    -- Input uInstructions
    -- =================================

    -- per src row
    RX_UINSTR_SRC_COL : in  slv_array_2d_t(2-1 downto 0)(SRC_BUF_ROWS-1 downto 0)(log2(SRC_BUF_COLS)-1 downto 0);
    -- per dst row
    RX_UINSTR_SRC_ROW : in  slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    RX_UINSTR_DST_COL : in  slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    -- row rotation
    RX_UINSTR_ROW_ROT : in  slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    -- item enable
    RX_UINSTR_IE      : in  slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    RX_UINSTR_SRC_RDY : in  slv_array_t   (2-1 downto 0)(DST_BUF_ROWS-1 downto 0);

    -- =================================
    -- Source buffer read interface
    -- =================================

    SRC_BUF_RD_ADDR : out slv_array_t(SRC_BUF_ROWS-1 downto 0)(log2(SRC_BUF_COLS)-1 downto 0);
    SRC_BUF_RD_DATA : in  slv_array_t(SRC_BUF_ROWS-1 downto 0)(ROW_ITEMS*ITEM_WIDTH-1 downto 0);

    -- =================================
    -- Destination buffer read interface
    -- =================================

    DST_BUF_WR_ADDR : out slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    DST_BUF_WR_DATA : out slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS*ITEM_WIDTH-1 downto 0);
    -- item enable
    DST_BUF_WR_IE   : out slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    DST_BUF_WR_EN   : out std_logic_vector(DST_BUF_ROWS-1 downto 0)
);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of CROSSBARX_CROSSBAR is

    constant ROW_WIDTH : integer := ROW_ITEMS*ITEM_WIDTH;

    constant UINSTR_WORD_WIDTH : integer := SRC_BUF_ROWS*log2(ROW_ITEMS)
                                           +DST_BUF_ROWS*log2(SRC_BUF_ROWS)
                                           +DST_BUF_ROWS*ROW_ITEMS
                                           +DST_BUF_ROWS*log2(DST_BUF_COLS)
                                           +DST_BUF_ROWS;

    -- ----------------------------------------------------------------------------
    -- Signals
    -- ----------------------------------------------------------------------------

    -- data transfer clock
    signal d_clk : std_logic;

    -- control asynch register
    signal uinstr_src_word_reg  : slv_array_2d_t(2-1 downto 0)(SRC_BUF_ROWS-1 downto 0)(log2(SRC_BUF_COLS)-1 downto 0);
    signal uinstr_rot_sel_reg   : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal uinstr_src_block_reg : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    signal uinstr_dst_be_reg    : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal uinstr_dst_word_reg  : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal uinstr_vld_reg       : slv_array_t   (2-1 downto 0)(DST_BUF_ROWS-1 downto 0);

    signal delayed_uinstr_src_word_reg  : slv_array_2d_t(2-1 downto 0)(SRC_BUF_ROWS-1 downto 0)(log2(SRC_BUF_COLS)-1 downto 0);
    signal delayed_uinstr_rot_sel_reg   : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal delayed_uinstr_src_block_reg : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    signal delayed_uinstr_dst_be_reg    : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal delayed_uinstr_dst_word_reg  : slv_array_2d_t(2-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal delayed_uinstr_vld_reg       : slv_array_t   (2-1 downto 0)(DST_BUF_ROWS-1 downto 0);

    -- control plan select register
    signal plan_sel_reg  : std_logic_vector(0 downto 0);
    signal plan_sel_regI : integer := 0;

    --------
    -- data transmission path
    --------

    -- step -1 - plan select, Source buffer read addr insert
    signal s_1_rot_sel_reg   : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal s_1_src_block_reg : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    signal s_1_dst_be_reg    : slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal s_1_dst_word_reg  : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal s_1_vld_reg       : std_logic_vector(DST_BUF_ROWS-1 downto 0);

    -- step 0 - wait for Source buffer read response
    -- The last (+1) item is only used for asynch connection when RD_LATENCY==0.
    signal s0_rot_sel_reg   : slv_array_2d_t(RD_LATENCY+1-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal s0_src_block_reg : slv_array_2d_t(RD_LATENCY+1-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    signal s0_dst_be_reg    : slv_array_2d_t(RD_LATENCY+1-1 downto 0)(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal s0_dst_word_reg  : slv_array_2d_t(RD_LATENCY+1-1 downto 0)(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal s0_vld_reg       : slv_array_t   (RD_LATENCY+1-1 downto 0)(DST_BUF_ROWS-1 downto 0);

    -- step 1 - Source buffer read data save
    signal s1_rot_sel_reg   : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal s1_src_block_reg : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(SRC_BUF_ROWS)-1 downto 0);
    signal s1_dst_be_reg    : slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal s1_dst_word_reg  : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal s1_vld_reg       : std_logic_vector(DST_BUF_ROWS-1 downto 0);
    signal s1_data_reg      : slv_array_t(SRC_BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    -- step 2 - Source buffer blocks rotation
    signal s2_rot_sel_dst_be_dst_word_reg : slv_array_t(DST_BUF_ROWS-1 downto 0)( log2(ROW_ITEMS)
                                                                                 +ROW_ITEMS
                                                                                 +log2(DST_BUF_COLS)-1 downto 0);

    signal s2_rot_sel_reg   : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal s2_dst_be_reg    : slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal s2_dst_word_reg  : slv_array_t(DST_BUF_ROWS-1 downto 0)(log2(DST_BUF_COLS)-1 downto 0);
    signal s2_vld_reg       : std_logic_vector(DST_BUF_ROWS-1 downto 0);
    signal s2_data_reg      : slv_array_t(DST_BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    -- step 3 - data multiplex, Destination buffer write addr and data insert
    signal dst_buf_wr_addr_ie : slv_array_t(DST_BUF_ROWS-1 downto 0)( log2(DST_BUF_COLS)
                                                                     +ROW_ITEMS-1 downto 0);

    --------

    -- ----------------------------------------------------------------------------

    -- Setting maximum fanout for select signal register of data multiplexers for better routing
    -- Quartus
    attribute maxfan : integer;
    attribute maxfan of s1_src_block_reg : signal is 32;
    -- Vivado
    attribute max_fanout : integer;
    attribute max_fanout of s1_src_block_reg : signal is 32;

begin

    -- data transfer clock select
    use_clk2_gen : if (USE_CLK2) generate
        d_clk <= CLK2;
    else generate
        d_clk <= CLK;
    end generate;

    -- signals read on d_clk must be reassigned to compensate the 'delta' delay from d_clk in ModelSim simulation
    delayed_uinstr_rot_sel_reg   <= uinstr_rot_sel_reg;
    delayed_uinstr_src_block_reg <= uinstr_src_block_reg;
    delayed_uinstr_dst_be_reg    <= uinstr_dst_be_reg;
    delayed_uinstr_dst_word_reg  <= uinstr_dst_word_reg;
    delayed_uinstr_vld_reg       <= uinstr_vld_reg;
    delayed_uinstr_src_word_reg  <= uinstr_src_word_reg;

    -- control asynch register
    control_reg_ptr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            uinstr_src_word_reg  <= RX_UINSTR_SRC_COL;
            uinstr_rot_sel_reg   <= RX_UINSTR_ROW_ROT;
            uinstr_src_block_reg <= RX_UINSTR_SRC_ROW;
            uinstr_vld_reg       <= RX_UINSTR_SRC_RDY;
            uinstr_dst_be_reg    <= RX_UINSTR_IE;
            uinstr_dst_word_reg  <= RX_UINSTR_DST_COL;

            if (RESET='1') then
                uinstr_vld_reg <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- control plan select register
    plan_sel_reg_pr : process (d_clk)
    begin
        if (rising_edge(d_clk)) then
            -- when USE_CLK2==false only plan0 is used
            if (USE_CLK2) then
                plan_sel_reg(0) <= not plan_sel_reg(0);
            end if;

            if (RESET='1') then
                plan_sel_reg(0) <= '0';
            end if;
        end if;
    end process;

    plan_sel_regI <= to_integer(unsigned(plan_sel_reg));

    --------
    -- data transmission path
    --------

    -- step -1 - plan select, Source buffer read addr insert

    s_1_reg_pr : process (d_clk)
    begin
        if (rising_edge(d_clk)) then
            s_1_rot_sel_reg   <= delayed_uinstr_rot_sel_reg  (plan_sel_regI);
            s_1_src_block_reg <= delayed_uinstr_src_block_reg(plan_sel_regI);
            s_1_dst_be_reg    <= delayed_uinstr_dst_be_reg   (plan_sel_regI);
            s_1_dst_word_reg  <= delayed_uinstr_dst_word_reg (plan_sel_regI);
            s_1_vld_reg       <= delayed_uinstr_vld_reg      (plan_sel_regI);
            for i in 0 to SRC_BUF_ROWS-1 loop
                SRC_BUF_RD_ADDR(i) <= delayed_uinstr_src_word_reg(plan_sel_regI)(i);
            end loop;

            if (RESET='1') then
                s_1_vld_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- step 0 - wait for Source buffer read response

    rd_latency_wait_gen : if (RD_LATENCY>0) generate

        -- generate RD_LATENCY number of shift registers
        s0_reg_pr : process (d_clk)
        begin
            if (rising_edge(d_clk)) then
                s0_rot_sel_reg  (RD_LATENCY-1) <= s_1_rot_sel_reg;
                s0_src_block_reg(RD_LATENCY-1) <= s_1_src_block_reg;
                s0_dst_be_reg   (RD_LATENCY-1) <= s_1_dst_be_reg;
                s0_dst_word_reg (RD_LATENCY-1) <= s_1_dst_word_reg;
                s0_vld_reg      (RD_LATENCY-1) <= s_1_vld_reg;

                for i in 0 to RD_LATENCY-1-1 loop
                    s0_rot_sel_reg  (i) <= s0_rot_sel_reg  (i+1);
                    s0_src_block_reg(i) <= s0_src_block_reg(i+1);
                    s0_dst_be_reg   (i) <= s0_dst_be_reg   (i+1);
                    s0_dst_word_reg (i) <= s0_dst_word_reg (i+1);
                    s0_vld_reg      (i) <= s0_vld_reg      (i+1);
                end loop;

                if (RESET='1') then
                    s0_vld_reg <= (others => (others => '0'));
                end if;
            end if;
        end process;

    else generate

        -- direct asynch connection
        s0_rot_sel_reg  (0) <= s_1_rot_sel_reg;
        s0_src_block_reg(0) <= s_1_src_block_reg;
        s0_dst_be_reg   (0) <= s_1_dst_be_reg;
        s0_dst_word_reg (0) <= s_1_dst_word_reg;
        s0_vld_reg      (0) <= s_1_vld_reg;

    end generate;

    -- step 1 - Source buffer read data save

    s1_reg_pr : process (d_clk)
    begin
        if (rising_edge(d_clk)) then
            s1_rot_sel_reg   <= s0_rot_sel_reg  (0);
            s1_src_block_reg <= s0_src_block_reg(0);
            s1_dst_word_reg  <= s0_dst_word_reg (0);
            s1_dst_be_reg    <= s0_dst_be_reg   (0);
            s1_vld_reg       <= s0_vld_reg      (0);
            for i in 0 to SRC_BUF_ROWS-1 loop -- to -> downto
                s1_data_reg(i) <= SRC_BUF_RD_DATA(i);
            end loop;

            if (RESET='1') then
                s1_vld_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- step 2 - data multiplex, Destination buffer write addr and data insert

    data_muxes_gen : for i in 0 to DST_BUF_ROWS-1 generate
        signal s2_rot_sel_tmp  : std_logic_vector(log2(ROW_ITEMS)-1 downto 0);
        signal s2_dst_be_tmp   : std_logic_vector(ROW_ITEMS-1 downto 0);
        signal s2_dst_word_tmp : std_logic_vector(log2(DST_BUF_COLS)-1 downto 0);
    begin
        data_mux_i : entity work.GEN_MUX_PIPED
        generic map (
            DATA_WIDTH     => ROW_WIDTH             ,
            MUX_WIDTH      => SRC_BUF_ROWS          ,
            MUX_LATENCY    => DATA_MUX_LATENCY      ,
            OUTPUT_REG     => DATA_MUX_OUTPUT_REG_EN,
            METADATA_WIDTH => log2(ROW_ITEMS)
                             +ROW_ITEMS
                             +log2(DST_BUF_COLS)
        )
        port map (
            CLK   => d_clk,
            RESET => RESET,

            RX_DATA     => slv_array_ser(s1_data_reg,SRC_BUF_ROWS,ROW_WIDTH)        ,
            RX_SEL      => s1_src_block_reg(i)                                      ,
            RX_METADATA => s1_rot_sel_reg(i) & s1_dst_be_reg(i) & s1_dst_word_reg(i),
            RX_SRC_RDY  => s1_vld_reg(i)                                            ,
            RX_DST_RDY  => open                                                     ,

            TX_DATA     => s2_data_reg(i)                   ,
            TX_METADATA => s2_rot_sel_dst_be_dst_word_reg(i),
            TX_SRC_RDY  => s2_vld_reg(i)                    ,
            TX_DST_RDY  => '1'
        );

        (s2_rot_sel_tmp, s2_dst_be_tmp, s2_dst_word_tmp) <= s2_rot_sel_dst_be_dst_word_reg(i);

        s2_rot_sel_reg (i) <= s2_rot_sel_tmp;
        s2_dst_be_reg  (i) <= s2_dst_be_tmp;
        s2_dst_word_reg(i) <= s2_dst_word_tmp;

    end generate;

    --------

    -- step 2 - Source buffer blocks rotation

    block_bar_shift_gen : for i in 0 to DST_BUF_ROWS-1 generate
        signal DST_BUF_WR_ADDR_tmp : std_logic_vector(log2(DST_BUF_COLS)-1 downto 0);
        signal DST_BUF_WR_IE_tmp   : std_logic_vector(ROW_ITEMS-1 downto 0);
    begin
        block_bar_shift_i : entity work.BARREL_SHIFTER_GEN_PIPED
        generic map (
            BLOCKS            => ROW_ITEMS                  ,
            BLOCK_WIDTH       => ITEM_WIDTH                 ,
            BAR_SHIFT_LATENCY => DATA_ROTATION_LATENCY      ,
            OUTPUT_REG        => DATA_ROTATION_OUTPUT_REG_EN,
            SHIFT_LEFT        => true                       ,
            METADATA_WIDTH    => ROW_ITEMS
                                +log2(DST_BUF_COLS)
        )
        port map (
            CLK         => d_clk,
            RESET       => RESET,

            RX_DATA     => s2_data_reg(i)                       ,
            RX_SEL      => s2_rot_sel_reg(i)                    ,
            RX_METADATA => s2_dst_be_reg(i) & s2_dst_word_reg(i),
            RX_SRC_RDY  => s2_vld_reg(i)                        ,
            RX_DST_RDY  => open                                 ,

            TX_DATA     => DST_BUF_WR_DATA(i)   ,
            TX_METADATA => dst_buf_wr_addr_ie(i),
            TX_SRC_RDY  => DST_BUF_WR_EN(i),
            TX_DST_RDY  => '1'
        );

        (DST_BUF_WR_IE_tmp, DST_BUF_WR_ADDR_tmp) <= dst_buf_wr_addr_ie(i);

        DST_BUF_WR_IE  (i) <= DST_BUF_WR_IE_tmp;
        DST_BUF_WR_ADDR(i) <= DST_BUF_WR_ADDR_tmp;

    end generate;


end architecture;
