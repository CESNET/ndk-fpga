-- crossbarx.vhd: Universal memory data transfering unit
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
--                                Description
-- ----------------------------------------------------------------------------
-- This unit performs data transfer between two buffers connected on SRC_BUF
-- and DST_BUF interfaces based on Transactions passed on the TRANS interface.
-- Transactions can be passed on multiple independent Streams. Different
-- Streams must have different Buffer A but common Buffer B. Transactions passed
-- in one CLK tick on one Stream must not overlap in its Buffer A. CrossbarX
-- unit solves collisions in Buffer B between all Transactions by planning
-- the data transfers out-of-order. To enable tracking of the data transfer
-- actual progress. The unit propagates Completed signal for each done Transaction
-- together with its Metadata. These Completed signals have the same order as
-- the input Transactions (within each Stream).

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX is
generic(
    -- Data transfer direction
    -- true  -> from A to B
    -- false -> from B to A
    DATA_DIR            : boolean := true;

    -- Transfer data on double frequency Clock
    USE_CLK2            : boolean := true;
    -- Transfer data on arbitrary frequency Clock
    -- (Overrides USE_CLK2 when set to True.)
    -- In this setting the Planner and Crossbar both run on the CLK_ARB
    -- and only process one transfer plan per cycle.
    -- This way the Planner can read more than 100% of Instructions from
    -- its input in each cycle of CLK and can thus achieve higher burst
    -- throughput.
    USE_CLK_ARB         : boolean := false;

    -- Number of independent Transaction Streams
    TRANS_STREAMS       : integer := 1;

    -- Buffer A size
    BUF_A_COLS          : integer := 512;
    BUF_A_STREAM_ROWS   : integer := 4;
    -- constant alias, DO NOT CHANGE!
    BUF_A_ROWS          : integer := BUF_A_STREAM_ROWS*TRANS_STREAMS;

    -- Buffer B size
    BUF_B_COLS          : integer := 512;
    BUF_B_ROWS          : integer := 4;

    -- Number of non-overlapping Sections of Buffer A
    -- (All Instructions must overflow inside space
    --  of one Buffer A Section.)
    BUF_A_SECTIONS      : integer := 1;

    -- Number of non-overlapping Sections of Buffer B
    -- (All Instructions must overflow inside space
    --  of one Buffer B Section.)
    BUF_B_SECTIONS      : integer := 1;

    -- Number of Items in one buffer row
    ROW_ITEMS           : integer := 8;
    -- Width of one Item
    ITEM_WIDTH          : integer := 8;

    -- Number of input Transactions per Transaction Stream
    TRANSS              : integer := 2;

    -- Maximum length of one Transaction (in number of Items)
    TRANS_MTU           : integer := 64;

    -- Width of Transaction user Metadata
    METADATA_WIDTH      : integer := 0;

    -- Size of FIFO for Transaction awaiting completion (for TRANS_COMP interface)
    -- Defines the maximum number of Transactions inside at any moment! (on each Transaction Stream)
    -- You should set this, so that the FIFO never fills up.
    TRANS_FIFO_ITEMS    : integer := TRANSS*16;

    -- Width of Color confirmation Timeout counter in Planner
    -- The resulting timeout takes 2**COLOR_TIMEOUT_WIDTH cycles to expire.
    -- This affects the maximum latency of TRANS_CONF_ interface.
    -- WARNING:
    --     When set too low, the Timeout might expire between the arrival
    --     of NEW_RX_TRANS signal and the arrival of the corresponding RX_UINSTR_SRC_RDY.
    --     This could break the entire Color confirmation mechanism!
    COLOR_TIMEOUT_WIDTH : integer := 6;

    -- Delay of Color confirmation signal from Planner
    -- Setting this value too low will cause frequent changes of Color and thus a slightly
    -- lower throughput in Planner.
    -- Setting it too high will cause greater filling of Transaction FIFO
    -- (see TRANS_FIFO_ITEMS) and increase the average TRANS_CONF_ interface latency.
    COLOR_CONF_DELAY    : integer := 16;

    -- Source Buffer read latency
    RD_LATENCY          : integer := 1;

    -- Data multiplexer's latency (increase for better timing)
    DATA_MUX_LAT        : integer := 0;
    -- Data multiplexer's output register enable (set to TRUE for better timing)
    DATA_MUX_OUTREG_EN  : boolean := true;

    -- Data blocks rotation latency (increase for better timing)
    DATA_ROT_LAT        : integer := 0;
    -- Data blocks rotation output register enable (set to TRUE for better timing)
    DATA_ROT_OUTREG_EN  : boolean := true;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", "STRATIX10" ...
    DEVICE              : string := "ULTRASCALE"
);
port(
    -- ===================================
    -- Clock and reset
    -- ===================================

    CLK                : in  std_logic;
    -- Only used when USE_CLK2==True and USE_CLK_ARB==False
    CLK2               : in  std_logic := '0';
    RESET              : in  std_logic;

    -- Only used when USE_CLK_ARB==True
    CLK_ARB            : in  std_logic := '0';
    RESET_ARB          : in  std_logic := '0';

    -- ===================================
    -- Input Transactions
    -- ===================================

    TRANS_A_COL        : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    TRANS_A_ITEM       : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_A_STREAM_ROWS*ROW_ITEMS)-1 downto 0);
    TRANS_B_COL        : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    TRANS_B_ITEM       : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    TRANS_LEN          : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    TRANS_META         : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    TRANS_VLD          : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    TRANS_SRC_RDY      : in  std_logic_vector(TRANS_STREAMS-1 downto 0);
    TRANS_DST_RDY      : out std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ===================================
    -- Source Buffer read interface
    -- ===================================

    SRC_BUF_RD_ADDR    : out slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS))-1 downto 0);
    SRC_BUF_RD_DATA    : in  slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);

    -- ===================================
    -- Destination Buffer write interface
    -- ===================================

    DST_BUF_WR_ADDR    : out slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS))-1 downto 0);
    DST_BUF_WR_DATA    : out slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);
    -- Item enable
    DST_BUF_WR_IE      : out slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(ROW_ITEMS-1 downto 0);
    DST_BUF_WR_EN      : out std_logic_vector(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0);

    -- ===================================
    -- Transactions Completed confirmation
    -- ===================================

    -- Each index only contains confirmations from the respective Transaction Stream, but there is more of them
    -- to allow burst confirmations
    TRANS_COMP_META    : out slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    TRANS_COMP_SRC_RDY : out slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    -- Read for FIFOX Multi!
    TRANS_COMP_DST_RDY : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)
);
end entity;

-- ----------------------------------------------------------------------------
--                           Architecture
-- ----------------------------------------------------------------------------

architecture FULL of CROSSBARX is

    -- ------------------------------------------------------------------------
    -- CLK & RESET signals
    -- ------------------------------------------------------------------------

    -- For components before Planner
    signal clk_0 : std_logic;
    signal rst_0 : std_logic;
    -- For Planner and Crossbar
    signal clk_1 : std_logic;
    signal rst_1 : std_logic;
    -- For Crossbar
    signal clk_2 : std_logic;
    signal rst_2 : std_logic;


    signal trcg_new_rx_trans  : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ------------------------------------------------------------------------
    -- Transaction Sorter
    -- ------------------------------------------------------------------------

    signal trsr_trans_dst_rdy      : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trsr_trans_comp_id      : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(1-1 downto 0);
    signal trsr_trans_comp_meta    : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal trsr_trans_comp_src_rdy : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    signal trsr_trans_comp_dst_rdy : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Transaction Shakedown
    -- ------------------------------------------------------------------------

    signal trsh_do            : slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS*METADATA_WIDTH-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Transaction Breaker
    -- ------------------------------------------------------------------------

    constant INSTRS : integer := TRANSS+1;

    signal trbr_instr_a_col   : slv_array_t     (TRANS_STREAMS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal trbr_instr_a_item  : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0)(log2(BUF_A_STREAM_ROWS*ROW_ITEMS)-1 downto 0);
    signal trbr_instr_b_col   : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal trbr_instr_b_item  : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trbr_instr_len     : slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0)(log2(BUF_A_STREAM_ROWS*ROW_ITEMS+1)-1 downto 0);
    signal trbr_instr_color   : slv_array_t     (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0);
    signal trbr_instr_vld     : slv_array_t     (TRANS_STREAMS-1 downto 0)(INSTRS-1 downto 0);
    signal trbr_instr_src_rdy : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trbr_instr_dst_rdy : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- uInstruction Generator
    -- ------------------------------------------------------------------------

    signal ugen_instr_src_rdy : std_logic_vector(TRANS_STREAMS-1 downto 0);

    signal ugen_uinstr_a_col  : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal ugen_uinstr_a_item : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal ugen_uinstr_b_col  : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal ugen_uinstr_b_item : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal ugen_uinstr_len    : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(ROW_ITEMS+1)-1 downto 0);
    signal ugen_uinstr_color  : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_uinstr_vld    : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ---------------------------
    -- uInstruction Generator FIFO(s)
    -- ---------------------------

    constant UGEN_UINSTR_WIDTH   : integer := log2(BUF_A_COLS)
                                             +log2(ROW_ITEMS)
                                             +log2(BUF_B_COLS)
                                             +log2(BUF_B_ROWS*ROW_ITEMS)
                                             +log2(ROW_ITEMS+1)
                                             +1;
    constant UGEN_F_ITEMS        : integer := 32;
    constant UGEN_F_AFULL_OFFSET : integer := 4; -- must be greater then the latency of uInstruction Generator

    signal ugen_f_di    : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(UGEN_UINSTR_WIDTH-1 downto 0);
    signal ugen_f_wr    : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_full  : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_afull : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_do    : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(UGEN_UINSTR_WIDTH-1 downto 0);
    signal ugen_f_rd    : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_empty : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);

    signal ugen_f_uinstr_a_col   : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal ugen_f_uinstr_a_item  : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal ugen_f_uinstr_b_col   : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal ugen_f_uinstr_b_item  : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal ugen_f_uinstr_len     : slv_array_2d_t(TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0)(log2(ROW_ITEMS+1)-1 downto 0);
    signal ugen_f_uinstr_color   : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_uinstr_src_rdy : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal ugen_f_uinstr_dst_rdy : slv_array_t   (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);

    -- ---------------------------

    -- ------------------------------------------------------------------------
    -- uInstruction Splitter(s)
    -- ------------------------------------------------------------------------

    signal uspl_uinstr_a_col   : slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal uspl_uinstr_b_col   : slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal uspl_uinstr_b_row   : slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS)-1 downto 0);
    signal uspl_uinstr_row_rot : slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal uspl_uinstr_ie      : slv_array_t     (BUF_A_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal uspl_uinstr_color   : std_logic_vector(BUF_A_ROWS-1 downto 0);
    signal uspl_uinstr_src_rdy : std_logic_vector(BUF_A_ROWS-1 downto 0);
    signal uspl_uinstr_dst_rdy : std_logic_vector(BUF_A_ROWS-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Planner
    -- ------------------------------------------------------------------------

    signal plan_uinstr_src_col   : slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_A_COLS),log2(BUF_B_COLS))-1 downto 0);
    signal plan_uinstr_src_row   : slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_A_ROWS),log2(BUF_B_ROWS))-1 downto 0);
    signal plan_uinstr_dst_col   : slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_B_COLS),log2(BUF_A_COLS))-1 downto 0);
    signal plan_uinstr_row_rot   : slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal plan_uinstr_ie        : slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal plan_uinstr_src_rdy   : slv_array_t   (2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0);

    signal plan_new_rx_trans    : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal plan_conf_color      : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal plan_conf_vld        : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal plan_conf_propagated : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Actual Color Confirmation latency must be increased
    -- to prevent TRANS_COMP_ propagation before the actual data transfer.
    -- Total latency = user defined latency + Planner latency + Crossbar latency
    constant ACT_COLOR_CONF_DELAY    : integer := COLOR_CONF_DELAY+3+(1+(1+RD_LATENCY+1+DATA_MUX_LAT+tsel(DATA_MUX_OUTREG_EN,1,0)+DATA_ROT_LAT+tsel(DATA_ROT_OUTREG_EN,1,0)+1)/tsel(USE_CLK2 and (not USE_CLK_ARB),2,1));
    signal plan_conf_color_delayed   : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal plan_conf_vld_delayed     : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trcg_color_conf_color_reg : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trcg_color_conf_vld_reg0  : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trcg_color_conf_vld_reg1  : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trcg_color_conf_vld_reg2  : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal trcg_color_conf           : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Crossbar
    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------

begin

    assert (BUF_A_STREAM_ROWS*TRANS_STREAMS=BUF_A_ROWS)
        report "ERROR: CrossbarX: The number of BUF_A_ROWS(" & to_string(BUF_A_ROWS) & ")" &
               " is not divisible by the number of TRANS_STREAMS(" & to_string(TRANS_STREAMS) & ")!"
        severity failure;

    -- ------------------------------------------------------------------------
    -- CLK signals
    -- ------------------------------------------------------------------------
    -- Clock and Reset signals are chosen based on USE_CLK_ARB and USE_CLK2 generics.

    clk_gen : if (USE_CLK_ARB) generate
        clk_0 <= CLK;
        rst_0 <= RESET;
        clk_1 <= CLK_ARB;
        rst_1 <= RESET_ARB;
        clk_2 <= CLK;
        rst_2 <= RESET;
    elsif (USE_CLK2) generate
        clk_0 <= CLK;
        rst_0 <= RESET;
        clk_1 <= CLK;
        rst_1 <= RESET;
        clk_2 <= CLK2;
        rst_2 <= RESET;
    else generate
        clk_0 <= CLK;
        rst_0 <= RESET;
        clk_1 <= CLK;
        rst_1 <= RESET;
        clk_2 <= CLK;
        rst_2 <= RESET;
    end generate;

    -- ------------------------------------------------------------------------

    instr_stream_gen : for s in 0 to TRANS_STREAMS-1 generate
        signal trcg_trans_a_col   : std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
        signal trcg_trans_a_item  : slv_array_t(TRANSS-1 downto 0)(log2(BUF_A_STREAM_ROWS*ROW_ITEMS)-1 downto 0);
        signal trcg_trans_b_col   : slv_array_t(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
        signal trcg_trans_b_item  : slv_array_t(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
        signal trcg_trans_len     : slv_array_t(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
        signal trcg_trans_meta    : slv_array_t(TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
        signal trcg_trans_vld     : std_logic_vector(TRANSS-1 downto 0);
        signal trcg_trans_color   : std_logic;
        signal trcg_trans_src_rdy : std_logic;
        signal trcg_trans_dst_rdy : std_logic;
    begin
        -- ------------------------------------------------------------------------
        -- Transaction Color Generator(s)
        -- ------------------------------------------------------------------------

        trcg_i : entity work.CROSSBARX_TRANS_COLOR_GEN
        generic map(
            TRANSS         => TRANSS           ,
            BUF_A_COLS     => BUF_A_COLS       ,
            BUF_A_ROWS     => BUF_A_STREAM_ROWS,
            BUF_B_COLS     => BUF_B_COLS       ,
            BUF_B_ROWS     => BUF_B_ROWS       ,
            ROW_ITEMS      => ROW_ITEMS        ,
            ITEM_WIDTH     => ITEM_WIDTH       ,
            TRANS_MTU      => TRANS_MTU        ,
            METADATA_WIDTH => METADATA_WIDTH   ,
            SHREG_LATENCY  => 1                ,
            DEVICE         => DEVICE
        )
        port map(
            CLK   => clk_0,
            RESET => rst_0,

            RX_TRANS_A_COL   => TRANS_A_COL  (s),
            RX_TRANS_A_ITEM  => TRANS_A_ITEM (s),
            RX_TRANS_B_COL   => TRANS_B_COL  (s),
            RX_TRANS_B_ITEM  => TRANS_B_ITEM (s),
            RX_TRANS_LEN     => TRANS_LEN    (s),
            RX_TRANS_META    => TRANS_META   (s),
            RX_TRANS_VLD     => TRANS_VLD    (s),
            RX_TRANS_SRC_RDY => TRANS_SRC_RDY(s),
            RX_TRANS_DST_RDY => TRANS_DST_RDY(s),

            TX_TRANS_A_COL   => trcg_trans_a_col,
            TX_TRANS_A_ITEM  => trcg_trans_a_item,
            TX_TRANS_B_COL   => trcg_trans_b_col,
            TX_TRANS_B_ITEM  => trcg_trans_b_item,
            TX_TRANS_LEN     => trcg_trans_len,
            TX_TRANS_META    => trcg_trans_meta,
            TX_TRANS_VLD     => trcg_trans_vld,
            TX_TRANS_COLOR   => trcg_trans_color,
            TX_TRANS_SRC_RDY => trcg_trans_src_rdy,
            TX_TRANS_DST_RDY => trcg_trans_dst_rdy and trsr_trans_dst_rdy(s),

            NEW_RX_TRANS     => trcg_new_rx_trans(s),
            COLOR_CONF       => trcg_color_conf  (s)
        );

        -- Color change must wait until all confirmed Transactions have been
        -- removed from Transaction Sorter to prevent adding Transactions to Sorter
        -- with Color, which is just being Confirmed.
        trcg_color_conf_pr : process (clk_0)
        begin
            if (rising_edge(clk_0)) then

                -- Don't propagate anything by default
                trcg_color_conf(s) <= '0';

                -- When no more Transactions with the Confirmed Color are on Transaction Sorter output
                if (trsr_trans_comp_id(s)(0)(0)/=trcg_color_conf_color_reg(s) or trsr_trans_comp_src_rdy(s)(0)='0') then
                    -- Propagate Confirmation to Transaction Color Generator and reset waiting register
                    trcg_color_conf(s) <= trcg_color_conf_vld_reg2(s);
                    trcg_color_conf_vld_reg2(s) <= '0';
                end if;

                -- Delay waiting register for 2 cycles to give Transaction Sorter time to start generating valid output
                trcg_color_conf_vld_reg1(s) <= trcg_color_conf_vld_reg0(s);
                if (trcg_color_conf_vld_reg1(s)='1') then
                    trcg_color_conf_vld_reg2(s) <= trcg_color_conf_vld_reg1(s);
                end if;

                -- When new Color Confirmation is generated
                if (plan_conf_vld_delayed(s)='1') then
                    -- Set register for waiting to propagate Confirmation
                    trcg_color_conf_color_reg(s) <= plan_conf_color_delayed(s);
                    trcg_color_conf_vld_reg0 (s) <= '1';
                else
                    trcg_color_conf_vld_reg0(s) <= '0';
                end if;

                if (rst_0='1') then
                    trcg_color_conf_vld_reg0(s) <= '0';
                    trcg_color_conf_vld_reg1(s) <= '0';
                    trcg_color_conf_vld_reg2(s) <= '0';
                end if;
            end if;
        end process;

        -- ------------------------------------------------------------------------

        -- ------------------------------------------------------------------------
        -- Transaction Sorter(s)
        -- ------------------------------------------------------------------------

        trsr_i : entity work.TRANS_SORTER
        generic map(
            RX_TRANSS        => TRANSS          ,
            TX_TRANSS        => TRANSS          ,
            ID_CONFS         => 1               ,
            ID_WIDTH         => 1               ,
            TRANS_FIFO_ITEMS => TRANS_FIFO_ITEMS,
            METADATA_WIDTH   => METADATA_WIDTH  ,
            MSIDT_BEHAV      => 0               ,
            DEVICE           => DEVICE
        )
        port map(
            CLK              => clk_0,
            RESET            => rst_0,

            RX_TRANS_ID      => (others => (0 => trcg_trans_color)),
            RX_TRANS_META    => trcg_trans_meta,
            RX_TRANS_SRC_RDY => trcg_trans_vld and trcg_trans_src_rdy and trcg_trans_dst_rdy,
            RX_TRANS_DST_RDY => trsr_trans_dst_rdy(s),

            RX_CONF_ID       => (others => (0 => plan_conf_color_delayed(s))),
            RX_CONF_VLD      => (others => plan_conf_vld_delayed(s)),

            TX_TRANS_ID      => trsr_trans_comp_id     (s),
            TX_TRANS_META    => trsr_trans_comp_meta   (s),
            TX_TRANS_SRC_RDY => trsr_trans_comp_src_rdy(s),
            TX_TRANS_DST_RDY => trsr_trans_comp_dst_rdy(s)
        );

        assert (((or trcg_trans_vld)='1' and trcg_trans_src_rdy='1' and trcg_trans_dst_rdy='1' and trsr_trans_dst_rdy(s)='0')=false)
            report "WARNING: CROSSBARX: Internal Transaction FIFO is FULL causing a decrease in throughput! Consider increasing value of generic TRANS_FIFO_ITEMS (currently "&to_string(TRANS_FIFO_ITEMS)&")."
            severity warning;

        -- ------------------------------------------------------------------------

        -- ------------------------------------------------------------------------
        -- Transaction Shakedown
        -- ------------------------------------------------------------------------

        trsh_i : entity work.MVB_SHAKEDOWN
        generic map(
            RX_ITEMS    => TRANSS        ,
            TX_ITEMS    => TRANSS        ,
            ITEM_WIDTH  => METADATA_WIDTH,
            SHAKE_PORTS => 2
        )
        port map(
            CLK        => clk_0,
            RESET      => rst_0,

            RX_DATA    => slv_array_ser(trsr_trans_comp_meta(s)),
            RX_VLD     => trsr_trans_comp_src_rdy(s)            ,
            RX_SRC_RDY => (or trsr_trans_comp_src_rdy(s))       ,
            RX_DST_RDY => trsr_trans_comp_dst_rdy(s)            ,

            TX_DATA    => trsh_do(s)           ,
            TX_VLD     => TRANS_COMP_SRC_RDY(s),
            TX_NEXT    => TRANS_COMP_DST_RDY(s)
        );

        TRANS_COMP_META(s) <= slv_array_deser(trsh_do(s),TRANSS);

        -- ------------------------------------------------------------------------

        -- ------------------------------------------------------------------------
        -- Transaction Breaker(s)
        -- ------------------------------------------------------------------------

        trbr_i : entity work.CROSSBARX_TRANS_BREAKER
        generic map(
            TRANSS         => TRANSS           ,
            BUF_A_COLS     => BUF_A_COLS       ,
            BUF_A_ROWS     => BUF_A_STREAM_ROWS,
            BUF_B_COLS     => BUF_B_COLS       ,
            BUF_B_ROWS     => BUF_B_ROWS       ,
            BUF_A_SECTIONS => BUF_A_SECTIONS   ,
            BUF_B_SECTIONS => BUF_B_SECTIONS   ,
            ROW_ITEMS      => ROW_ITEMS        ,
            ITEM_WIDTH     => ITEM_WIDTH       ,
            TRANS_MTU      => TRANS_MTU        ,
            DEVICE         => DEVICE
        )
        port map(
            CLK   => clk_0,
            RESET => rst_0,

            TRANS_A_COL   => trcg_trans_a_col,
            TRANS_A_ITEM  => trcg_trans_a_item,
            TRANS_B_COL   => trcg_trans_b_col,
            TRANS_B_ITEM  => trcg_trans_b_item,
            TRANS_LEN     => trcg_trans_len,
            TRANS_VLD     => trcg_trans_vld,
            TRANS_COLOR   => trcg_trans_color,
            TRANS_SRC_RDY => trcg_trans_src_rdy and trsr_trans_dst_rdy(s),
            TRANS_DST_RDY => trcg_trans_dst_rdy,

            INSTR_A_COL   => trbr_instr_a_col  (s),
            INSTR_A_ITEM  => trbr_instr_a_item (s),
            INSTR_B_COL   => trbr_instr_b_col  (s),
            INSTR_B_ITEM  => trbr_instr_b_item (s),
            INSTR_LEN     => trbr_instr_len    (s),
            INSTR_COLOR   => trbr_instr_color  (s),
            INSTR_VLD     => trbr_instr_vld    (s),
            INSTR_SRC_RDY => trbr_instr_src_rdy(s),
            INSTR_DST_RDY => trbr_instr_dst_rdy(s)
        );

        -- ------------------------------------------------------------------------

        -- ------------------------------------------------------------------------
        -- uInstruction Generator(s)
        -- ------------------------------------------------------------------------

        -- Instructions input must be stop once one of uInstruction Generator FIFOs
        -- reaches almost full.
        trbr_instr_dst_rdy(s) <= '1' when (or ugen_f_afull(s))='0' else '0';
        ugen_instr_src_rdy(s) <= '1' when (or ugen_f_afull(s))='0' and trbr_instr_src_rdy(s)='1' else '0';

        ugen_i : entity work.CROSSBARX_UINSTR_GEN
        generic map(
            INSTRS         => INSTRS           ,
            BUF_A_COLS     => BUF_A_COLS       ,
            BUF_A_ROWS     => BUF_A_STREAM_ROWS,
            BUF_B_COLS     => BUF_B_COLS       ,
            BUF_B_ROWS     => BUF_B_ROWS       ,
            BUF_B_SECTIONS => BUF_B_SECTIONS   ,
            ROW_ITEMS      => ROW_ITEMS        ,
            ITEM_WIDTH     => ITEM_WIDTH       ,
            DEVICE         => DEVICE
        )
        port map(
            CLK   => clk_0,
            RESET => rst_0,

            INSTR_A_COL   => trbr_instr_a_col  (s),
            INSTR_A_ITEM  => trbr_instr_a_item (s),
            INSTR_B_COL   => trbr_instr_b_col  (s),
            INSTR_B_ITEM  => trbr_instr_b_item (s),
            INSTR_LEN     => trbr_instr_len    (s),
            INSTR_COLOR   => trbr_instr_color  (s),
            INSTR_VLD     => trbr_instr_vld    (s),
            INSTR_SRC_RDY => ugen_instr_src_rdy(s),

            UINSTR_A_COL  => ugen_uinstr_a_col (s),
            UINSTR_A_ITEM => ugen_uinstr_a_item(s),
            UINSTR_B_COL  => ugen_uinstr_b_col (s),
            UINSTR_B_ITEM => ugen_uinstr_b_item(s),
            UINSTR_LEN    => ugen_uinstr_len   (s),
            UINSTR_COLOR  => ugen_uinstr_color (s),
            UINSTR_VLD    => ugen_uinstr_vld   (s)
        );

        -- ------------------------------------------------------------------------

        uspl_gen : for i in 0 to BUF_A_STREAM_ROWS-1 generate
            signal tmp_ugen_f_uinstr_a_col  : std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
            signal tmp_ugen_f_uinstr_a_item : std_logic_vector(log2(ROW_ITEMS)-1 downto 0);
            signal tmp_ugen_f_uinstr_b_col  : std_logic_vector(log2(BUF_B_COLS)-1 downto 0);
            signal tmp_ugen_f_uinstr_b_item : std_logic_vector(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
            signal tmp_ugen_f_uinstr_len    : std_logic_vector(log2(ROW_ITEMS+1)-1 downto 0);
            signal tmp_ugen_f_uinstr_color  : std_logic;
        begin

            -- ---------------------------
            -- uInstruction Generator FIFO(s)
            -- ---------------------------
            -- These FIFOs buffer uInstructions while they are being
            -- unevenly consumed by the Planner.
            -- Their almost full controls uInstruction Generator input.
            -- (They must NEVER OVERFLOW!)

            ugen_f_di(s)(i) <= ugen_uinstr_a_col (s)(i)
                              &ugen_uinstr_a_item(s)(i)
                              &ugen_uinstr_b_col (s)(i)
                              &ugen_uinstr_b_item(s)(i)
                              &ugen_uinstr_len   (s)(i)
                              &ugen_uinstr_color (s)(i);

            ugen_f_wr(s)(i) <= ugen_uinstr_vld(s)(i);

            ugen_f_gen : if (USE_CLK_ARB) generate

                ugen_f_i : entity work.ASFIFOX
                generic map(
                    DATA_WIDTH          => UGEN_UINSTR_WIDTH  ,
                    ITEMS               => UGEN_F_ITEMS       ,
                    RAM_TYPE            => "LUT"              ,
                    FWFT_MODE           => true               ,
                    OUTPUT_REG          => true               ,
                    DEVICE              => DEVICE             ,
                    ALMOST_FULL_OFFSET  => UGEN_F_AFULL_OFFSET,
                    ALMOST_EMPTY_OFFSET => 0
                )
                port map(
                    WR_CLK    => clk_0,
                    WR_RST    => rst_0,
                    WR_DATA   => ugen_f_di   (s)(i),
                    WR_EN     => ugen_f_wr   (s)(i),
                    WR_FULL   => ugen_f_full (s)(i),
                    WR_AFULL  => ugen_f_afull(s)(i),
                    WR_STATUS => open              ,

                    RD_CLK    => clk_1,
                    RD_RST    => rst_1,
                    RD_DATA   => ugen_f_do   (s)(i),
                    RD_EN     => ugen_f_rd   (s)(i),
                    RD_EMPTY  => ugen_f_empty(s)(i),
                    RD_AEMPTY => open              ,
                    RD_STATUS => open
                );

            else generate

                ugen_f_i : entity work.FIFOX
                generic map(
                    DATA_WIDTH          => UGEN_UINSTR_WIDTH  ,
                    ITEMS               => UGEN_F_ITEMS       ,
                    RAM_TYPE            => "AUTO"             ,
                    DEVICE              => DEVICE             ,
                    ALMOST_FULL_OFFSET  => UGEN_F_AFULL_OFFSET,
                    ALMOST_EMPTY_OFFSET => 0                  ,
                    FAKE_FIFO           => false
                )
                port map(
                    CLK    => clk_0,
                    RESET  => rst_0,

                    DI     => ugen_f_di   (s)(i),
                    WR     => ugen_f_wr   (s)(i),
                    FULL   => ugen_f_full (s)(i),
                    AFULL  => ugen_f_afull(s)(i),
                    STATUS => open              ,

                    DO     => ugen_f_do   (s)(i),
                    RD     => ugen_f_rd   (s)(i),
                    EMPTY  => ugen_f_empty(s)(i),
                    AEMPTY => open
                );

            end generate;

            -- overflow checking
            assert (ugen_f_wr(s)(i)/='1' or ugen_f_full(s)(i)/='1')
                report "ERROR: CrossbarX: uInstruction Generator FIFOX_" & to_string(s) & "_" & to_string(i) &
                       " overflow detected! Consider increasing UGEN_F_AFULL_OFFSET."
                severity failure;

            (tmp_ugen_f_uinstr_a_col ,
             tmp_ugen_f_uinstr_a_item,
             tmp_ugen_f_uinstr_b_col ,
             tmp_ugen_f_uinstr_b_item,
             tmp_ugen_f_uinstr_len   ,
             tmp_ugen_f_uinstr_color  ) <= ugen_f_do(s)(i);

            ugen_f_uinstr_a_col  (s)(i) <= tmp_ugen_f_uinstr_a_col;
            ugen_f_uinstr_a_item (s)(i) <= tmp_ugen_f_uinstr_a_item;
            ugen_f_uinstr_b_col  (s)(i) <= tmp_ugen_f_uinstr_b_col;
            ugen_f_uinstr_b_item (s)(i) <= tmp_ugen_f_uinstr_b_item;
            ugen_f_uinstr_len    (s)(i) <= tmp_ugen_f_uinstr_len;
            ugen_f_uinstr_color  (s)(i) <= tmp_ugen_f_uinstr_color;

            ugen_f_uinstr_src_rdy(s)(i) <= not ugen_f_empty(s)(i);
            ugen_f_rd            (s)(i) <= ugen_f_uinstr_dst_rdy(s)(i);

            -- ---------------------------

            -- ------------------------------------------------------------------------
            -- uInstruction Splitter(s)
            -- ------------------------------------------------------------------------

            uspl_i : entity work.CROSSBARX_UINSTR_SPLITTER
            generic map(
                DATA_DIR       => DATA_DIR      ,
                INSTRS         => INSTRS+1      ,
                BUF_A_COLS     => BUF_A_COLS    ,
                BUF_B_COLS     => BUF_B_COLS    ,
                BUF_B_SECTIONS => BUF_B_SECTIONS,
                BUF_B_ROWS     => BUF_B_ROWS    ,
                ROW_ITEMS      => ROW_ITEMS     ,
                ITEM_WIDTH     => ITEM_WIDTH    ,
                DEVICE         => DEVICE
            )
            port map(
                CLK   => clk_1,
                RESET => rst_1,

                RX_UINSTR_A_COL   => ugen_f_uinstr_a_col  (s)(i),
                RX_UINSTR_A_ITEM  => ugen_f_uinstr_a_item (s)(i),
                RX_UINSTR_B_COL   => ugen_f_uinstr_b_col  (s)(i),
                RX_UINSTR_B_ITEM  => ugen_f_uinstr_b_item (s)(i),
                RX_UINSTR_LEN     => ugen_f_uinstr_len    (s)(i),
                RX_UINSTR_COLOR   => ugen_f_uinstr_color  (s)(i),
                RX_UINSTR_SRC_RDY => ugen_f_uinstr_src_rdy(s)(i),
                RX_UINSTR_DST_RDY => ugen_f_uinstr_dst_rdy(s)(i),

                TX_UINSTR_A_COL   => uspl_uinstr_a_col    (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_B_COL   => uspl_uinstr_b_col    (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_B_ROW   => uspl_uinstr_b_row    (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_ROW_ROT => uspl_uinstr_row_rot  (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_IE      => uspl_uinstr_ie       (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_COLOR   => uspl_uinstr_color    (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_SRC_RDY => uspl_uinstr_src_rdy  (s*BUF_A_STREAM_ROWS+i),
                TX_UINSTR_DST_RDY => uspl_uinstr_dst_rdy  (s*BUF_A_STREAM_ROWS+i)
            );

            -- ------------------------------------------------------------------------

        end generate;

    end generate;

    -- ------------------------------------------------------------------------
    -- Planner
    -- ------------------------------------------------------------------------

    plan_i : entity work.CROSSBARX_PLANNER
    generic map(
        DATA_DIR            => DATA_DIR           ,
        USE_CLK2            => USE_CLK2 and (not USE_CLK_ARB),
        TRANS_STREAMS       => TRANS_STREAMS      ,
        BUF_A_COLS          => BUF_A_COLS         ,
        BUF_A_ROWS          => BUF_A_ROWS         ,
        BUF_B_COLS          => BUF_B_COLS         ,
        BUF_B_ROWS          => BUF_B_ROWS         ,
        ROW_ITEMS           => ROW_ITEMS          ,
        ITEM_WIDTH          => ITEM_WIDTH         ,
        COLOR_TIMEOUT_WIDTH => COLOR_TIMEOUT_WIDTH,
        DEVICE              => DEVICE
    )
    port map(
        CLK   => clk_1,
        RESET => rst_1,

        RX_UINSTR_A_COL   => uspl_uinstr_a_col  ,
        RX_UINSTR_B_COL   => uspl_uinstr_b_col  ,
        RX_UINSTR_B_ROW   => uspl_uinstr_b_row  ,
        RX_UINSTR_ROW_ROT => uspl_uinstr_row_rot,
        RX_UINSTR_IE      => uspl_uinstr_ie     ,
        RX_UINSTR_COLOR   => uspl_uinstr_color  ,
        RX_UINSTR_SRC_RDY => uspl_uinstr_src_rdy,
        RX_UINSTR_DST_RDY => uspl_uinstr_dst_rdy,

        TX_UINSTR_SRC_COL => plan_uinstr_src_col,
        TX_UINSTR_SRC_ROW => plan_uinstr_src_row,
        TX_UINSTR_DST_COL => plan_uinstr_dst_col,
        TX_UINSTR_ROW_ROT => plan_uinstr_row_rot,
        TX_UINSTR_IE      => plan_uinstr_ie     ,
        TX_UINSTR_SRC_RDY => plan_uinstr_src_rdy,

        NEW_RX_TRANS     => plan_new_rx_trans   ,
        CONF_COLOR       => plan_conf_color     ,
        CONF_VLD         => plan_conf_vld       ,
        CONF_PROPAGATED  => plan_conf_propagated
    );

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Planner Synchronisator
    -- ------------------------------------------------------------------------

    plan_synch_i : entity work.CROSSBARX_PLANNER_SYNCHRONISATOR
    generic map(
        ASYNC_EN         => USE_CLK_ARB         ,
        TRANS_STREAMS    => TRANS_STREAMS       ,
        COLOR_CONF_DELAY => ACT_COLOR_CONF_DELAY,
        DEVICE           => DEVICE
    )
    port map(
        CLK_PLAN          => clk_1,
        RESET_PLAN        => rst_1,
        CLK_OTHER         => clk_0,
        RESET_OTHER       => rst_0,

        P_NEW_RX_TRANS    => plan_new_rx_trans   ,
        P_CONF_COLOR      => plan_conf_color     ,
        P_CONF_VLD        => plan_conf_vld       ,
        P_CONF_PROPAGATED => plan_conf_propagated,

        O_NEW_RX_TRANS    => trcg_new_rx_trans      ,
        O_CONF_COLOR      => plan_conf_color_delayed,
        O_CONF_VLD        => plan_conf_vld_delayed  ,
        O_CONF_PROPAGATED => trcg_color_conf
    );

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Crossbar
    -- ------------------------------------------------------------------------

    cros_i : entity work.CROSSBARX_CROSSBAR
    generic map(
        USE_CLK2                    => USE_CLK2 and (not USE_CLK_ARB)      ,
        SRC_BUF_COLS                => tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS),
        SRC_BUF_ROWS                => tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS),
        DST_BUF_COLS                => tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS),
        DST_BUF_ROWS                => tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS),
        ROW_ITEMS                   => ROW_ITEMS                           ,
        ITEM_WIDTH                  => ITEM_WIDTH                          ,
        RD_LATENCY                  => RD_LATENCY                          ,
        DATA_MUX_LATENCY            => DATA_MUX_LAT                        ,
        DATA_MUX_OUTPUT_REG_EN      => DATA_MUX_OUTREG_EN                  ,
        DATA_ROTATION_LATENCY       => DATA_ROT_LAT                        ,
        DATA_ROTATION_OUTPUT_REG_EN => DATA_ROT_OUTREG_EN                  ,
        DEVICE                      => DEVICE
    )
    port map(
        CLK   => clk_1,
        CLK2  => clk_2,
        RESET => rst_1,

        RX_UINSTR_SRC_COL => plan_uinstr_src_col,
        RX_UINSTR_SRC_ROW => plan_uinstr_src_row,
        RX_UINSTR_DST_COL => plan_uinstr_dst_col,
        RX_UINSTR_ROW_ROT => plan_uinstr_row_rot,
        RX_UINSTR_IE      => plan_uinstr_ie     ,
        RX_UINSTR_SRC_RDY => plan_uinstr_src_rdy,

        SRC_BUF_RD_ADDR   => SRC_BUF_RD_ADDR    ,
        SRC_BUF_RD_DATA   => SRC_BUF_RD_DATA    ,

        DST_BUF_WR_ADDR   => DST_BUF_WR_ADDR    ,
        DST_BUF_WR_DATA   => DST_BUF_WR_DATA    ,
        DST_BUF_WR_IE     => DST_BUF_WR_IE      ,
        DST_BUF_WR_EN     => DST_BUF_WR_EN
    );

    -- ------------------------------------------------------------------------

end architecture;
