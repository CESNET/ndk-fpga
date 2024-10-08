-- trans_color_gen.vhd: Transaction Color Generator for CrossbarX
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
-- Assigns Color ('0' or '1') to Transactions to create barriers between them
-- to control their processing in Planner. Changes Color after recieving Color
-- Confirmation signal from Planner.

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_TRANS_COLOR_GEN is
generic(
    -- Number of Transaction
    TRANSS          : integer := 4;
    -- Buffer A size
    BUF_A_COLS      : integer := 512;
    BUF_A_ROWS      : integer := 4;
    -- Buffer B size
    BUF_B_COLS      : integer := 512;
    BUF_B_ROWS      : integer := 4;
    -- Number of items in one bufer row
    ROW_ITEMS       : integer := 8;
    -- Width of one item
    ITEM_WIDTH      : integer := 8;

    -- Maximum length of one Transaction (in number of Items)
    TRANS_MTU       : integer := 512;

    -- Width of Transaction user Metadata
    METADATA_WIDTH  : integer := 0;

    -- Internal Transaction Shift Register latency
    -- WARNING:
    --     Might cause errors in Color-Barrier
    --     mechanism when set too low!
    --     Depends on the latency of NEW_RX_TRANS
    --     and COLOR_CONF propagation.
    SHREG_LATENCY   : integer := 16;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE          : string := "STRATIX10"
);
port(
    -- ====================
    -- Clock and Reset
    -- ====================

    CLK              : in  std_logic;
    RESET            : in  std_logic;

    -- ====================
    -- Input Transactions
    -- ====================

    RX_TRANS_A_COL   : in  std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    RX_TRANS_A_ITEM  : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    RX_TRANS_B_COL   : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    RX_TRANS_B_ITEM  : in  slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    RX_TRANS_LEN     : in  slv_array_t     (TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    RX_TRANS_META    : in  slv_array_t     (TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0) := (others => (others => '0'));
    RX_TRANS_VLD     : in  std_logic_vector(TRANSS-1 downto 0);
    RX_TRANS_SRC_RDY : in  std_logic;
    RX_TRANS_DST_RDY : out std_logic;

    -- ====================
    -- Output Transactions
    -- ====================

    TX_TRANS_A_COL   : out std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    TX_TRANS_A_ITEM  : out slv_array_t     (TRANSS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    TX_TRANS_B_COL   : out slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    TX_TRANS_B_ITEM  : out slv_array_t     (TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    TX_TRANS_LEN     : out slv_array_t     (TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    TX_TRANS_META    : out slv_array_t     (TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    TX_TRANS_VLD     : out std_logic_vector(TRANSS-1 downto 0);
    -- Color is the same for all Transactions in one word
    TX_TRANS_COLOR   : out std_logic;
    TX_TRANS_SRC_RDY : out std_logic;
    -- Serves as this unit's 'Enable'
    TX_TRANS_DST_RDY : in  std_logic;

    -- Color Confirmation Timeout cancel signal
    NEW_RX_TRANS     : out std_logic;

    -- Color Confirmation signal
    COLOR_CONF       : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_TRANS_COLOR_GEN is

    -------------------------------------------------------------
    -- Transaction delay Shreg
    -------------------------------------------------------------

    constant TRANS_WIDTH : integer := log2(BUF_A_ROWS*ROW_ITEMS)
                                     +log2(BUF_B_COLS)
                                     +log2(BUF_B_ROWS*ROW_ITEMS)
                                     +log2(TRANS_MTU+1)
                                     +METADATA_WIDTH
                                     +1;

    signal trans_shreg_din_arr : slv_array_t(TRANSS-1 downto 0)(TRANS_WIDTH-1 downto 0);
    signal trans_shreg_din     : std_logic_vector(log2(BUF_A_COLS)+TRANSS*TRANS_WIDTH+1-1 downto 0);
    signal trans_shreg_dout    : std_logic_vector(log2(BUF_A_COLS)+TRANSS*TRANS_WIDTH+1-1 downto 0);

    signal tx_trans_ser        : std_logic_vector(TRANSS*TRANS_WIDTH-1 downto 0);
    signal tx_trans_arr        : slv_array_t(TRANSS-1 downto 0)(TRANS_WIDTH-1 downto 0);

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Current Color register
    -------------------------------------------------------------

    signal curr_color_reg : std_logic;

    -------------------------------------------------------------

begin

    -- This unit is wholly enabled by TX_TRANS_DST_RDY
    RX_TRANS_DST_RDY <= TX_TRANS_DST_RDY;

    -------------------------------------------------------------
    -- Color Confirmation Timeout cancelation
    -------------------------------------------------------------
    -- Color Confirmation Timeout counting must be cancelled when new
    -- Transactions are incomming.
    -- This signal must include DST_RDY to enable Timeout expiration
    -- when pipeline is stopped by DST_RDY. (This only happens when
    -- FIFO in Transaction Sorter is too small!)

    NEW_RX_TRANS <= RX_TRANS_SRC_RDY and (or RX_TRANS_VLD) and RX_TRANS_DST_RDY;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction delay Shreg
    -------------------------------------------------------------
    -- This might not actually be needed. Going to make verification
    -- to be sure.
    -- --
    -- -- If the NEW_RX_TRANS arrives to Planner right after
    -- -- the Color Confirmation Timeout has already expired, we must ensure,
    -- -- that the corresponding COLOR_CONF signal is applied
    -- -- (and curr_color_reg is switched) BEFORE assigning the Color
    -- -- to these Transactions. For this reason the Transactions
    -- -- must be delayed for a few cycles.

    trans_shreg_din_gen : for i in 0 to TRANSS-1 generate
        trans_shreg_din_arr(i) <= RX_TRANS_A_ITEM(i)
                                 &RX_TRANS_B_COL (i)
                                 &RX_TRANS_B_ITEM(i)
                                 &RX_TRANS_LEN   (i)
                                 &RX_TRANS_META  (i)
                                 &RX_TRANS_VLD   (i);
    end generate;

    trans_shreg_din <= RX_TRANS_A_COL & slv_array_ser(trans_shreg_din_arr) & RX_TRANS_SRC_RDY;

    trans_shreg_i : entity work.SH_REG_BASE_STATIC
    generic map(
        DATA_WIDTH      => log2(BUF_A_COLS)+TRANSS*TRANS_WIDTH+1,
        NUM_BITS        => SHREG_LATENCY,
        INIT_TYPE       => 0            ,
        IS_CLK_INVERTED => '0'          ,
        DEVICE          => DEVICE
    )
    port map(
        CLK  => CLK,

        DIN  => trans_shreg_din ,
        DOUT => trans_shreg_dout,
        CE   => TX_TRANS_DST_RDY
    );

    (TX_TRANS_A_COL  ,
     tx_trans_ser    ,
     TX_TRANS_SRC_RDY ) <= trans_shreg_dout;

    tx_trans_arr <= slv_array_deser(tx_trans_ser,TRANSS);

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- TX Trans generation
    -------------------------------------------------------------

    tx_trans_gen : for i in 0 to TRANSS-1 generate
        signal tmp_a_item : std_logic_vector(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
        signal tmp_b_col  : std_logic_vector(log2(BUF_B_COLS)-1 downto 0);
        signal tmp_b_item : std_logic_vector(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
        signal tmp_len    : std_logic_vector(log2(TRANS_MTU+1)-1 downto 0);
        signal tmp_meta   : std_logic_vector(METADATA_WIDTH-1 downto 0);
        signal tmp_vld    : std_logic;
    begin
        (tmp_a_item,
         tmp_b_col ,
         tmp_b_item,
         tmp_len   ,
         tmp_meta  ,
         tmp_vld    ) <= tx_trans_arr(i);

        TX_TRANS_A_ITEM(i) <= tmp_a_item;
        TX_TRANS_B_COL (i) <= tmp_b_col;
        TX_TRANS_B_ITEM(i) <= tmp_b_item;
        TX_TRANS_LEN   (i) <= tmp_len;
        TX_TRANS_META  (i) <= tmp_meta;
        TX_TRANS_VLD   (i) <= tmp_vld;
    end generate;

    TX_TRANS_COLOR <= curr_color_reg;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Current Color register
    -------------------------------------------------------------

    curr_color_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (COLOR_CONF='1') then
                curr_color_reg <= not curr_color_reg;
            end if;

            if (RESET='1') then
                curr_color_reg <= '0';
            end if;
        end if;
    end process;

    -------------------------------------------------------------

end architecture;
