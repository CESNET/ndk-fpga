-- trans_breaker.vhd: Transaction Breaker for CrossbarX
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
-- Breakes input Transaction (which all start in the same column in Buffer A)
-- to Instructions, which only describe data in one column of Buffer A.
-- (thus there are no collisions in Buffer A rows)

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_TRANS_BREAKER is
generic(
    -- Number of Transaction
    TRANSS          : integer := 4;
    -- Buffer A size
    BUF_A_COLS      : integer := 512;
    -- max(BUF_A_TRUE_ROWS)
    BUF_A_ROWS      : integer := 4;
    -- Buffer B size
    BUF_B_COLS      : integer := 512;
    -- max(BUF_B_TRUE_ROWS)
    BUF_B_ROWS      : integer := 4;

    -- Number of non-overlapping Sections of Buffer A
    -- (All Instructions must overflow inside space
    --  of one Buffer A Section.)
    BUF_A_SECTIONS  : integer := 1;

    -- Number of non-overlapping Sections of Buffer B
    -- (All Instructions must overflow inside space
    --  of one Buffer B Section.)
    BUF_B_SECTIONS  : integer := 1;

    -- Number of items in one bufer row
    ROW_ITEMS       : integer := 8;
    -- Width of one item
    ITEM_WIDTH      : integer := 8;

    -- Maximum length of one Transaction (in number of items)
    TRANS_MTU       : integer := 512;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE          : string := "STRATIX10"
);
port(
    -- ====================
    -- Clock and Reset
    -- ====================

    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- ====================
    -- Input Transactions
    -- ====================

    TRANS_A_COL     : in  std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    TRANS_A_ITEM    : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    TRANS_B_COL     : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    TRANS_B_ITEM    : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    TRANS_LEN       : in  slv_array_t     (TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    TRANS_VLD       : in  std_logic_vector(TRANSS-1 downto 0);
    -- Color is the same for all Transactions in one word
    TRANS_COLOR     : in  std_logic;
    TRANS_SRC_RDY   : in  std_logic;
    TRANS_DST_RDY   : out std_logic;

    -- ====================
    -- Output Instructions
    -- ====================

    INSTR_A_COL     : out std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    INSTR_A_ITEM    : out slv_array_t     (TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    INSTR_B_COL     : out slv_array_t     (TRANSS+1-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    INSTR_B_ITEM    : out slv_array_t     (TRANSS+1-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    INSTR_LEN       : out slv_array_t     (TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS+1)-1 downto 0);
    -- Color might be different for index 0
    INSTR_COLOR     : out std_logic_vector(TRANSS+1-1 downto 0);
    INSTR_VLD       : out std_logic_vector(TRANSS+1-1 downto 0);
    INSTR_SRC_RDY   : out std_logic;
    INSTR_DST_RDY   : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_TRANS_BREAKER is

    -------------------------------------------------------------
    -- Input Transaction Shakedown and register 0
    -------------------------------------------------------------

    constant TRANS_WIDTH : integer := log2(BUF_A_COLS)
                                     +log2(BUF_A_ROWS*ROW_ITEMS)
                                     +log2(BUF_B_COLS)
                                     +log2(BUF_B_ROWS*ROW_ITEMS)
                                     +log2(TRANS_MTU+1)
                                     +1;

    signal shake_din      : std_logic_vector(TRANSS*TRANS_WIDTH-1 downto 0);
    signal shake_din_vld  : std_logic_vector(TRANSS-1 downto 0);
    signal shake_dout     : std_logic_vector(TRANSS*TRANS_WIDTH-1 downto 0);
    signal shake_dout_vld : std_logic_vector(TRANSS-1 downto 0);
    signal shake_src_rdy  : std_logic;
    signal shake_dst_rdy  : std_logic;

    signal reg0_trans_a_col  : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal reg0_trans_a_item : u_array_t(TRANSS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg0_trans_b_col  : u_array_t(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg0_trans_b_item : u_array_t(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg0_trans_len    : u_array_t(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal reg0_trans_vld    : std_logic_vector(TRANSS-1 downto 0);
    signal reg0_trans_color  : std_logic;
    signal reg0_trans_en     : std_logic;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Register 1
    -------------------------------------------------------------

    signal reg1_trans_a_col     : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal reg1_trans_a_item    : u_array_t(TRANSS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg1_trans_a_eot_ptr : u_array_t(TRANSS-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg1_trans_b_col     : u_array_t(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg1_trans_b_item    : u_array_t(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg1_trans_len       : u_array_t(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal reg1_trans_vld       : std_logic_vector(TRANSS-1 downto 0);
    signal reg1_trans_color     : std_logic;
    signal reg1_trans_en        : std_logic;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Register 2
    -------------------------------------------------------------

    signal reg2_trans_a_col     : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal reg2_trans_a_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg2_trans_a_eot_ptr : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg2_trans_b_col     : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg2_trans_b_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg2_trans_len       : u_array_t(TRANSS+1-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal reg2_trans_vld       : std_logic_vector(TRANSS+1-1 downto 0);
    signal reg2_trans_color     : std_logic_vector(TRANSS+1-1 downto 0);
    signal reg2_trans_cont      : std_logic_vector(TRANSS+1-1 downto 0);
    signal reg2_trans_en        : std_logic;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Split Transactions
    -------------------------------------------------------------

    signal trans_part0_a_col     : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal trans_part0_a_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
  --signal trans_part0_a_eot_ptr : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part0_b_col     : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal trans_part0_b_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part0_len       : u_array_t(TRANSS+1-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal trans_part0_vld       : std_logic_vector(TRANSS+1-1 downto 0);
    signal trans_part0_color     : std_logic_vector(TRANSS+1-1 downto 0);

  --signal trans_part1_a_col     : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal trans_part1_a_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
  --signal trans_part1_a_eot_ptr : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part1_b_col     : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal trans_part1_b_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part1_len       : u_array_t(TRANSS+1-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal trans_part1_vld       : std_logic_vector(TRANSS+1-1 downto 0);
  --signal trans_part1_color     : std_logic_vector(TRANSS+1-1 downto 0);

    signal trans_part2_a_col     : unsigned(log2(BUF_A_COLS)-1 downto 0);
    signal trans_part2_a_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part2_a_eot_ptr : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part2_b_col     : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal trans_part2_b_item    : u_array_t(TRANSS+1-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_part2_len       : u_array_t(TRANSS+1-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    signal trans_part2_vld       : std_logic_vector(TRANSS+1-1 downto 0);
    signal trans_part2_color     : std_logic_vector(TRANSS+1-1 downto 0);

    -------------------------------------------------------------

begin

    -------------------------------------------------------------
    -- Input Transaction Shakedown and register 0
    -------------------------------------------------------------

    -- input serialization
    shake_din_gen : for i in 0 to TRANSS-1 generate
        shake_din((i+1)*TRANS_WIDTH-1 downto i*TRANS_WIDTH) <= TRANS_A_COL -- Buffer A column is propagated to all inputs
                                                              &TRANS_A_ITEM(i)
                                                              &TRANS_B_COL (i)
                                                              &TRANS_B_ITEM(i)
                                                              &TRANS_LEN   (i)
                                                              &TRANS_COLOR;
    end generate;
    shake_din_vld <= TRANS_VLD;

    input_shakedown_i : entity work.SHAKEDOWN
    generic map(
        INPUTS     => TRANSS     ,
        OUTPUTS    => TRANSS     ,
        DATA_WIDTH => TRANS_WIDTH,
        OUTPUT_REG => true
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        DIN          => shake_din     ,
        DIN_VLD      => shake_din_vld ,
        DIN_SRC_RDY  => TRANS_SRC_RDY ,
        DIN_DST_RDY  => TRANS_DST_RDY ,

        DOUT         => shake_dout    ,
        DOUT_VLD     => shake_dout_vld,
        DOUT_SRC_RDY => shake_src_rdy ,
        DOUT_DST_RDY => shake_dst_rdy
    );

    -- register 0 (register hidden in Shakedown output)
    reg0_trans_gen : for i in 0 to TRANSS-1 generate
        signal tmp_shake_dout        : unsigned(TRANS_WIDTH-1 downto 0);
        signal tmp_reg0_trans_a_item : unsigned(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
        signal tmp_reg0_trans_b_col  : unsigned(log2(BUF_B_COLS)-1 downto 0);
        signal tmp_reg0_trans_b_item : unsigned(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
        signal tmp_reg0_trans_len    : unsigned(log2(TRANS_MTU+1)-1 downto 0);
    begin

        tmp_shake_dout <= unsigned(shake_dout((i+1)*TRANS_WIDTH-1 downto i*TRANS_WIDTH));

        (tmp_reg0_trans_a_item,
         tmp_reg0_trans_b_col ,
         tmp_reg0_trans_b_item,
         tmp_reg0_trans_len    ) <= enlarge_left(enlarge_right(tmp_shake_dout,-1),-log2(BUF_A_COLS));

        reg0_trans_a_item(i) <= tmp_reg0_trans_a_item;
        reg0_trans_b_col (i) <= tmp_reg0_trans_b_col;
        reg0_trans_b_item(i) <= tmp_reg0_trans_b_item;
        reg0_trans_len   (i) <= tmp_reg0_trans_len;

    end generate;

    -- Buffer A column and Color is only taken from the zero output (they are all the same)
    reg0_trans_a_col <= resize_right(resize_left(unsigned(shake_dout),TRANS_WIDTH),log2(BUF_A_COLS));
    reg0_trans_color <= shake_dout(0);

    reg0_trans_vld <= shake_dout_vld and shake_src_rdy;
    shake_dst_rdy  <= reg0_trans_en;

    -- Register 0 is updated when Register 1 is being updated
    reg0_trans_en <= reg1_trans_en;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Register 1
    -------------------------------------------------------------
    -- Count ending address in Buffer A of every Transaction

    reg1_trans_pr : process (CLK)
        variable sot_ptr : unsigned(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            if (reg1_trans_en='1') then
                reg1_trans_a_col  <= reg0_trans_a_col;
                reg1_trans_a_item <= reg0_trans_a_item;
                reg1_trans_b_col  <= reg0_trans_b_col;
                reg1_trans_b_item <= reg0_trans_b_item;
                reg1_trans_len    <= reg0_trans_len;
                reg1_trans_vld    <= reg0_trans_vld;
                reg1_trans_color  <= reg0_trans_color;

                for i in 0 to TRANSS-1 loop
                    sot_ptr := (reg0_trans_a_col & reg0_trans_a_item(i));
                    -- End of Transaction pointer
                    reg1_trans_a_eot_ptr(i) <= sot_ptr + resize_left(reg0_trans_len(i),sot_ptr'length) - 1;
                    -- Address must overflow within space of one Buffer B Section
                    if (log2(BUF_A_SECTIONS) > 0) then
                        reg1_trans_a_eot_ptr(i)(sot_ptr'high downto sot_ptr'high-log2(BUF_A_SECTIONS)+1) <= resize_right(sot_ptr,log2(BUF_A_SECTIONS));
                    end if;
                end loop;
            end if;

            if (RESET='1') then
                reg1_trans_vld <= (others => '0');
            end if;
        end if;
    end process;

    -- Register 1 is updated when the next possible Buffer A column is the one in Register 1
    --               '1' when (Register 2 is being updated) and ((the next step is the column in Register 1) or (all Transactions from Register 2 consumed)) else '0';
    reg1_trans_en <= '1' when (     reg2_trans_en='1'     ) and ((    trans_part2_a_col=reg1_trans_a_col   ) or (         (or trans_part2_vld)='0'        )) else '0';

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Register 2
    -------------------------------------------------------------
    -- Save Transaction while they are being processed including
    -- Transaction, which continued from the previous word.

    reg2_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (reg2_trans_en='1') then
                -- consume Transactions; save overflowing Transaction to position 0

                -- load first valid Transaction Part 2 to position 0
                for i in 0 to TRANSS+1-1 loop
                    reg2_trans_a_item   (0) <= trans_part2_a_item   (i);
                    reg2_trans_a_eot_ptr(0) <= trans_part2_a_eot_ptr(i);
                    reg2_trans_b_col    (0) <= trans_part2_b_col    (i);
                    reg2_trans_b_item   (0) <= trans_part2_b_item   (i);
                    reg2_trans_len      (0) <= trans_part2_len      (i);
                    reg2_trans_vld      (0) <= trans_part2_vld      (i);
                    reg2_trans_color    (0) <= trans_part2_color    (i);

                    exit when (trans_part2_vld(i)='1');
                end loop;

                -- invalidate all other Transactions
                reg2_trans_vld(TRANSS+1-1 downto 1) <= (others => '0');

                -- load new Transactions
                reg2_trans_a_item   (TRANSS+1-1 downto 1) <= reg1_trans_a_item;
                reg2_trans_a_eot_ptr(TRANSS+1-1 downto 1) <= reg1_trans_a_eot_ptr;
                reg2_trans_b_col    (TRANSS+1-1 downto 1) <= reg1_trans_b_col;
                reg2_trans_b_item   (TRANSS+1-1 downto 1) <= reg1_trans_b_item;
                reg2_trans_len      (TRANSS+1-1 downto 1) <= reg1_trans_len;
                reg2_trans_color    (TRANSS+1-1 downto 1) <= (others => reg1_trans_color);

                -- step to the next Buffer A column
                reg2_trans_a_col <= trans_part2_a_col;

                if (reg1_trans_en='1') then
                    -- validate newly loaded Transactions
                    reg2_trans_vld(TRANSS+1-1 downto 1) <= reg1_trans_vld;
                    -- jump to the Buffer A column described by Register 1
                    reg2_trans_a_col <= reg1_trans_a_col;
                end if;

            end if;

            if (RESET='1') then
                reg2_trans_vld <= (others => '0');
            end if;
        end if;
    end process;

    -- detect when a Transaction continues to the next Buffer A column
    reg2_trans_cont_gen : for i in 0 to TRANSS+1-1 generate
        reg2_trans_cont(i) <= '1' when resize_right(reg2_trans_a_eot_ptr(i),log2(BUF_A_COLS))/=reg2_trans_a_col else '0';
    end generate;

    -- Register 2 is updated when output register is updated
    reg2_trans_en <= '1' when INSTR_DST_RDY='1' or INSTR_SRC_RDY='0' else '0';

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Split Transactions
    -------------------------------------------------------------
    -- Split every Transaction from Register 2 to 3 parts. where
    -- Part 0 is the original Transaction
    -- Part 1 is part from start of the Transaction to the end
    -- of this Buffer A Column and
    -- Part 2 is part, that continues after this Column.

    trans_split_pr : process (all)
        variable part1_len       : unsigned(log2(TRANS_MTU+1)-1 downto 0);
        variable part2_b_sot_ptr : unsigned(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    begin
        -- Parts 0 and 1 stay in the same Buffer A column
        trans_part0_a_col <= reg2_trans_a_col;
      --trans_part1_a_col <= reg2_trans_a_col; -- not needed
        -- Part 2 continues to the next Buffer A column
        -- It must overflow inside the Buffer A Section, where it begins
        trans_part2_a_col <= reg2_trans_a_col;
        trans_part2_a_col(trans_part2_a_col'high-log2(BUF_A_SECTIONS) downto 0) <= enlarge_left(reg2_trans_a_col+1,-log2(BUF_A_SECTIONS));

        -- Colors do not change
        trans_part0_color <= reg2_trans_color;
      --trans_part1_color <= reg2_trans_color; -- not needed
        trans_part2_color <= reg2_trans_color;

        for i in 0 to TRANSS+1-1 loop

            -- Part 0 ----
            trans_part0_a_item   (i) <= reg2_trans_a_item   (i);
          --trans_part0_a_eot_ptr(i) <= reg2_trans_a_eot_ptr(i); -- not needed
            trans_part0_b_col    (i) <= reg2_trans_b_col    (i);
            trans_part0_b_item   (i) <= reg2_trans_b_item   (i);
            trans_part0_len      (i) <= reg2_trans_len      (i);
            trans_part0_vld      (i) <= reg2_trans_vld      (i);
            --------------

            -- Part 1 ----
            trans_part1_a_item   (i) <= reg2_trans_a_item   (i);
          --trans_part1_a_eot_ptr(i) <= reg2_trans_a_eot_ptr(i); -- not needed
            trans_part1_b_col    (i) <= reg2_trans_b_col    (i);
            trans_part1_b_item   (i) <= reg2_trans_b_item   (i);
            trans_part1_vld      (i) <= reg2_trans_vld(i) and reg2_trans_cont(i);
            -- counting new length
            part1_len := resize_left( to_unsigned(BUF_A_ROWS*ROW_ITEMS,log2(BUF_A_ROWS*ROW_ITEMS+1))
                                     -resize_left(reg2_trans_a_item(i),log2(BUF_A_ROWS*ROW_ITEMS+1))
                                     ,log2(TRANS_MTU+1));
            trans_part1_len(i) <= part1_len;
            --------------

            -- Part 2 ----
            trans_part2_a_item   (i) <= (others => '0');
            trans_part2_a_eot_ptr(i) <= reg2_trans_a_eot_ptr(i);
            trans_part2_len      (i) <= reg2_trans_len(i)-part1_len;
            trans_part2_vld      (i) <= reg2_trans_vld(i) and reg2_trans_cont(i);
            -- counting new Buffer B pointer
            part2_b_sot_ptr := reg2_trans_b_col(i) & reg2_trans_b_item(i);
            part2_b_sot_ptr := part2_b_sot_ptr + resize_left(part1_len,part2_b_sot_ptr'length);
            -- Buffer B Column must overflow inside the Buffer B Section, where it begins
            part2_b_sot_ptr(part2_b_sot_ptr'high downto part2_b_sot_ptr'high-log2(BUF_B_SECTIONS)+1) := resize_right(reg2_trans_b_col(i),log2(BUF_B_SECTIONS));

            trans_part2_b_col (i) <= resize_right(part2_b_sot_ptr,log2(BUF_B_COLS));
            trans_part2_b_item(i) <= resize_left (part2_b_sot_ptr,log2(BUF_B_ROWS*ROW_ITEMS));
            --------------

        end loop;

    end process;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Output register
    -------------------------------------------------------------
    -- Select the correct Part of every Transaction to output

    tx_instr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (INSTR_DST_RDY='1' or INSTR_SRC_RDY='0') then

                INSTR_A_COL <= std_logic_vector(trans_part0_a_col);
                INSTR_COLOR <= std_logic_vector(trans_part0_color);

                for i in 0 to TRANSS+1-1 loop
                    -- Part 0 / Part 1 MUX
                    INSTR_A_ITEM(i) <= std_logic_vector(trans_part0_a_item(i));
                    INSTR_B_COL (i) <= std_logic_vector(trans_part0_b_col (i));
                    INSTR_B_ITEM(i) <= std_logic_vector(trans_part0_b_item(i));
                    INSTR_LEN   (i) <= std_logic_vector(resize_left(trans_part0_len(i),log2(BUF_A_ROWS*ROW_ITEMS+1)));
                    if (trans_part1_vld(i)='1') then
                        INSTR_A_ITEM(i) <= std_logic_vector(trans_part1_a_item(i));
                        INSTR_B_COL (i) <= std_logic_vector(trans_part1_b_col (i));
                        INSTR_B_ITEM(i) <= std_logic_vector(trans_part1_b_item(i));
                        INSTR_LEN   (i) <= std_logic_vector(resize_left(trans_part1_len(i),log2(BUF_A_ROWS*ROW_ITEMS+1)));
                    end if;

                    INSTR_VLD(i) <= trans_part0_vld(i) or trans_part1_vld(i);
                end loop;

                INSTR_SRC_RDY <= (or trans_part0_vld);

            end if;

            if (RESET='1') then
                INSTR_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -------------------------------------------------------------

end architecture;
