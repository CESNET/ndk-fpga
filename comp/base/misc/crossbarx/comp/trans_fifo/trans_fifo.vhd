-- trans_fifo.vhd: Trans FIFO for CrossbarX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                                Description
-- ----------------------------------------------------------------------------
-- This FIFO holds Transactions and only releases them when they have been
-- sent from the SRC Buffer to the DST Buffer.

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_TRANS_FIFO is
generic(
    -- Data transfer direction
    -- true  -> from A to B
    -- false -> from B to A
    DATA_DIR           : boolean := true;

    -- Number of independent Instruction Streams
    TRANS_STREAMS      : integer := 1;

    -- Number of input instructions per Transaction Stream
    TRANSS             : integer := 2;

    -- Maximum number of Items described by one Transaction
    TRANS_MTU          : integer := 64;

    -- Buffer A size
    BUF_A_COLS         : integer := 512;
    -- max(BUF_A_TRUE_ROWS)
    BUF_A_ROWS         : integer := 4;

    -- Buffer B size
    BUF_B_COLS         : integer := 512;
    BUF_B_ROWS         : integer := 4;

    -- Number of Items in one buffer row
    ROW_ITEMS          : integer := 8;

    -- Maximum number of Transaction words in the FIFO
    FIFO_SIZE          : integer := 512;

    -- Width of signal expressing maximum total length of one Transaction
    -- word in Buffer A and Buffer B
    A_LEN_SUM_WIDTH    : integer := 4;
    B_LEN_SUM_WIDTH    : integer := 8;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", "STRATIX10" ...
    DEVICE             : string := "ULTRASCALE"
);
port(
    -- ====================
    -- Clock and Reset
    -- ====================

    CLK                : in  std_logic;
    RESET              : in  std_logic;

    -- ====================
    -- Input Transactions
    -- ====================

    RX_TRANS_B_COL     : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    RX_TRANS_B_ITEM    : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    RX_TRANS_LEN       : in  slv_array_2d_t  (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    -- Total number of items from the start of the first valid Transaction
    -- to the end of the last valid Transaction (with no other Transactions being present).
    -- (These values include possible gaps between Transaction data and might
    --  be different for Buffer A and Buffer B.)
    -- The reason why the values aren't computed in this unit is, that it is the user,
    -- who generates the Transactions and he knows best, what is the maximum value
    -- of these signals and can correctly set the _LEN_SUM_WIDTH generics.
    RX_TRANS_A_LEN_SUM : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(A_LEN_SUM_WIDTH-1 downto 0);
    RX_TRANS_B_LEN_SUM : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(B_LEN_SUM_WIDTH-1 downto 0);
    ----
    RX_TRANS_VLD       : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_SRC_RDY   : in  std_logic_vector(TRANS_STREAMS-1 downto 0);
    RX_TRANS_DST_RDY   : out std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Buffer A pointer
    BUF_A_PTR          : in  slv_array_t(TRANS_STREAMS-1 downto 0)(log2(BUF_A_COLS*BUF_A_ROWS*ROW_ITEMS)-1 downto 0);

    -- ====================
    -- Input Transactions
    -- ====================

    TX_TRANS_B_COL     : out slv_array_t     (TRANS_STREAMS*TRANSS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    TX_TRANS_B_ITEM    : out slv_array_t     (TRANS_STREAMS*TRANSS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    TX_TRANS_LEN       : out slv_array_t     (TRANS_STREAMS*TRANSS-1 downto 0)(log2(TRANS_MTU+1)-1 downto 0);
    TX_TRANS_VLD       : out std_logic_vector(TRANS_STREAMS*TRANSS-1 downto 0);
    TX_TRANS_SRC_RDY   : out std_logic;
    TX_TRANS_DST_RDY   : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_TRANS_FIFO is

    constant TOTAL_TRANSS          : natural := TRANS_STREAMS*TRANSS;
    constant TOTAL_B_LEN_SUM_WIDTH : natural := log2(TRANS_STREAMS)+B_LEN_SUM_WIDTH;

    -- ---------------------------------------------------------------------
    -- FIFOX for waiting Transactions
    -- ---------------------------------------------------------------------

    constant TRANS_WIDTH : integer := log2(BUF_B_COLS)
                                     +log2(BUF_B_ROWS*ROW_ITEMS)
                                     +log2(TRANS_MTU+1)
                                     +1;
    constant TRANS_WORD_WIDTH : integer := TOTAL_TRANSS*TRANS_WIDTH
                                          +TRANS_STREAMS*A_LEN_SUM_WIDTH
                                          +TOTAL_B_LEN_SUM_WIDTH;

    signal RX_TRANS_TOTAL_B_LEN_SUM : std_logic_vector(TOTAL_B_LEN_SUM_WIDTH-1 downto 0);

    signal trans_fifox_di    : std_logic_vector(TRANS_WORD_WIDTH-1 downto 0);
    signal trans_fifox_wr    : std_logic;
    signal trans_fifox_full  : std_logic;
    signal trans_fifox_do    : std_logic_vector(TRANS_WORD_WIDTH-1 downto 0);
    signal trans_fifox_rd    : std_logic;
    signal trans_fifox_empty : std_logic;

    signal trans_fifox_do_b_col_ser     : std_logic_vector(TOTAL_TRANSS*log2(BUF_B_COLS)-1 downto 0);
    signal trans_fifox_do_b_item_ser    : std_logic_vector(TOTAL_TRANSS*log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal trans_fifox_do_len_ser       : std_logic_vector(TOTAL_TRANSS*log2(TRANS_MTU+1)-1 downto 0);
    signal trans_fifox_do_a_len_sum_ser : std_logic_vector(TRANS_STREAMS*A_LEN_SUM_WIDTH-1 downto 0);
    signal trans_fifox_do_a_len_sum     : slv_array_t(TRANS_STREAMS-1 downto 0)(A_LEN_SUM_WIDTH-1 downto 0);
    signal trans_fifox_do_b_len_sum     : std_logic_vector(TOTAL_B_LEN_SUM_WIDTH-1 downto 0);
    signal trans_fifox_do_vld           : std_logic_vector(TOTAL_TRANSS-1 downto 0);

    -- ---------------------------------------------------------------------

    -- ---------------------------------------------------------------------
    -- SRC Buffer data transferreded counter
    -- ---------------------------------------------------------------------

    constant SRC_BUF_COLS : natural := tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS);
    constant SRC_BUF_ROWS : natural := tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS);

    signal src_buf_ptr_reg                 : slv_array_t     (TRANS_STREAMS-1 downto 0)(log2(SRC_BUF_COLS*SRC_BUF_ROWS*ROW_ITEMS)-1 downto 0);
    signal src_buf_data_transed_reg        : u_array_t       (TRANS_STREAMS-1 downto 0)(log2(SRC_BUF_COLS*SRC_BUF_ROWS*ROW_ITEMS+1)-1 downto 0);
    signal src_buf_data_transed_enough     : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal src_buf_data_transed_enough_all : std_logic;

    -- ---------------------------------------------------------------------

    -- ---------------------------------------------------------------------
    -- DST Buffer free space counter
    -- ---------------------------------------------------------------------

    constant DST_BUF_COLS : natural := tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS);
    constant DST_BUF_ROWS : natural := tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS);

    signal dst_buf_free_space_reg    : unsigned(log2(DST_BUF_COLS*DST_BUF_ROWS*ROW_ITEMS+1)-1 downto 0);
    signal dst_buf_free_space_enough : std_logic;

    -- ---------------------------------------------------------------------

begin

    RX_TRANS_DST_RDY <= (others => ((not trans_fifox_full) and dst_buf_free_space_enough));

    -- ---------------------------------------------------------------------
    -- FIFOX for waiting Transactions
    -- ---------------------------------------------------------------------

    RX_TRANS_TOTAL_B_LEN_SUM <= sum(RX_TRANS_B_LEN_SUM);

    trans_fifox_di <= slv_array_2d_ser(RX_TRANS_B_COL)
                     &slv_array_2d_ser(RX_TRANS_B_ITEM)
                     &slv_array_2d_ser(RX_TRANS_LEN)
                     &slv_array_ser(RX_TRANS_A_LEN_SUM)
                     &RX_TRANS_TOTAL_B_LEN_SUM
                     &slv_array_ser(RX_TRANS_VLD);
    -- only accept new Transactions when there is enough space in DST Buffer
    trans_fifox_wr <= (or RX_TRANS_SRC_RDY) and dst_buf_free_space_enough;

    trans_fifox_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => TRANS_WORD_WIDTH,
        ITEMS               => FIFO_SIZE       ,
        RAM_TYPE            => "AUTO"          ,
        DEVICE              => DEVICE          ,
        ALMOST_FULL_OFFSET  => 0               ,
        ALMOST_EMPTY_OFFSET => 0               ,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => trans_fifox_di    ,
        WR     => trans_fifox_wr    ,
        FULL   => trans_fifox_full  ,
        AFULL  => open              ,
        STATUS => open              ,

        DO     => trans_fifox_do    ,
        RD     => trans_fifox_rd    ,
        EMPTY  => trans_fifox_empty ,
        AEMPTY => open
    );

    (trans_fifox_do_b_col_ser    ,
     trans_fifox_do_b_item_ser   ,
     trans_fifox_do_len_ser      ,
     trans_fifox_do_a_len_sum_ser,
     trans_fifox_do_b_len_sum    ,
     trans_fifox_do_vld           ) <= trans_fifox_do;

    trans_fifox_do_a_len_sum <= slv_array_deser(trans_fifox_do_a_len_sum_ser,TRANS_STREAMS);

    TX_TRANS_B_COL   <= slv_array_deser(trans_fifox_do_b_col_ser ,TOTAL_TRANSS);
    TX_TRANS_B_ITEM  <= slv_array_deser(trans_fifox_do_b_item_ser,TOTAL_TRANSS);
    TX_TRANS_LEN     <= slv_array_deser(trans_fifox_do_len_ser   ,TOTAL_TRANSS);
    TX_TRANS_VLD     <= trans_fifox_do_vld;
    -- only send data when Transactions are ready and they have been transfered from SRC Buffer
    TX_TRANS_SRC_RDY <= (not trans_fifox_empty) and src_buf_data_transed_enough_all;

    -- only read from FIFO when TX is ready and Transactions have been transfered from SRC Buffer
    trans_fifox_rd   <= TX_TRANS_DST_RDY and src_buf_data_transed_enough_all;

    -- ---------------------------------------------------------------------

    -- ---------------------------------------------------------------------
    -- DST Buffer space counter
    -- ---------------------------------------------------------------------

    dst_buf_free_space_pr : process (CLK)
        variable tmp_data_size : unsigned(log2(DST_BUF_COLS*DST_BUF_ROWS*ROW_ITEMS+1)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            tmp_data_size := dst_buf_free_space_reg;

            -- increment when releasing a word of Transactions
            if (TX_TRANS_DST_RDY='1' and trans_fifox_empty='0' and src_buf_data_transed_enough_all='1') then
                tmp_data_size := tmp_data_size+unsigned(trans_fifox_do_b_len_sum);
            end if;

            -- decrement when accepting a word of Transactions
            if ((or RX_TRANS_SRC_RDY)='1' and trans_fifox_full='0' and dst_buf_free_space_enough='1') then
                tmp_data_size := tmp_data_size-unsigned(RX_TRANS_TOTAL_B_LEN_SUM);
            end if;

            dst_buf_free_space_reg <= tmp_data_size;

            if (RESET='1') then
                dst_buf_free_space_reg <= (others => '0');
                dst_buf_free_space_reg(dst_buf_free_space_reg'high) <= '1';
            end if;
        end if;
    end process;

    -- There is enough free space in DST Buffer for the current RX Transactions word
    dst_buf_free_space_enough <= '1' when dst_buf_free_space_reg>=unsigned(RX_TRANS_TOTAL_B_LEN_SUM) else '0';

    -- ---------------------------------------------------------------------

    -- ---------------------------------------------------------------------
    -- SRC Buffer data transferred counter
    -- ---------------------------------------------------------------------

    src_buf_data_transed_pr : process (CLK)
        variable tmp_data_size : unsigned(log2(SRC_BUF_COLS*SRC_BUF_ROWS*ROW_ITEMS+1)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            for i in 0 to TRANS_STREAMS-1 loop

                tmp_data_size := src_buf_data_transed_reg(i);

                -- increment when SRC Buffer read pointer moved
                if (src_buf_ptr_reg(i)/=BUF_A_PTR(i)) then
                    tmp_data_size := tmp_data_size+(unsigned(BUF_A_PTR(i))-unsigned(src_buf_ptr_reg(i)));
                end if;

                -- decrement when releasing a word of Transactions
                if (TX_TRANS_DST_RDY='1' and trans_fifox_empty='0' and src_buf_data_transed_enough_all='1') then
                    tmp_data_size := tmp_data_size-unsigned(trans_fifox_do_a_len_sum(i));
                end if;

                src_buf_data_transed_reg(i) <= tmp_data_size;

            end loop;

            src_buf_ptr_reg <= BUF_A_PTR;

            if (RESET='1') then
                src_buf_ptr_reg          <= (others => (others => '0'));
                src_buf_data_transed_reg <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- Enough data has been transed from SRC Buffer for the current Transactions word waiting on FIFO output
    data_transed_enough_gen : for i in 0 to TRANS_STREAMS-1 generate
        src_buf_data_transed_enough(i) <= '1' when src_buf_data_transed_reg(i)>=unsigned(trans_fifox_do_a_len_sum(i)) else '0';
    end generate;
    src_buf_data_transed_enough_all <= (and src_buf_data_transed_enough);

    -- ---------------------------------------------------------------------

end architecture;
