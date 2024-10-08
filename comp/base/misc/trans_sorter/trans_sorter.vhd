-- trans_sorter.vhd: Transaction Confirmation Sorter
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
-- This component recieves Transactions on RX_TRANS interface with assigned IDs.
-- These IDs are then confirmed in random order on the RX_CONF interface.
-- The component then sends already cofirmed Transactions on the TX_TRANS
-- interface in the same order as they were on the RX_TRANS interface.
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity TRANS_SORTER is
generic(
    -- Maximum number of RX Transactions
    RX_TRANSS               : integer := 2;
    -- Maximum number of TX Transactions
    TX_TRANSS               : integer := 2;
    -- Maximum number of ID confirmations
    ID_CONFS                : integer := 2;

    -- Transaction ID width
    ID_WIDTH                : integer := 8;

    -- Size of internal Transaction storage FIFO
    -- Default is one Transaction per ID.
    -- Warning:
    --     The inner Transaction FIFO may actually
    --     accept more items than this!
    --     Use Almost Full to check filling precisely.
    TRANS_FIFO_ITEMS        : integer := 2**ID_WIDTH;

    -- Transaction Metadata width
    METADATA_WIDTH          : integer := 0;

    -- Multiple same ID Transactions behaviour configuration
    -- Options:
    --     0 - Each RX_CONF confirmation confirms ALL Transactions
    --         currently present in the unit which have
    --         the corresponding ID.
    --     1 - Each RX_CONF only confirms ONE Transaction.
    --         In this case the value MAX_SAME_ID_TRANS defines
    --         the maximum number of Transactions with the same ID
    --         present in the unit at any moment.
    --         This leads to worse timing and resources consumption!
    MSIDT_BEHAV             : integer := 0;

    -- Maximum number of unconfirmed Transactions present in the unit
    -- at any moment. (And the maximum number of confirmations
    -- received with one ID before any Transaction with this
    -- ID arrives.)
    -- Waning:
    --     This generic only sets the Transactions' counter width
    --     No overflow checking is implemented!
    -- Only applies when MSIDT_BEHAV==1.
    MAX_SAME_ID_TRANS       : natural := 1;

    -- Switches inner FIFO (FIFOX Multi) architecture from Full
    -- to Shakedown for possible better timing
    USE_SHAKEDOWN_FIFOX     : boolean := false;

    -- Almost Full offset
    -- Allows for better control of inner FIFO filling
    ALMOST_FULL_OFFSET      : natural := 0;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE                  : string := "STRATIX10"
);
port(
    -- ===================
    -- Clock and Reset
    -- ===================

    CLK              : in  std_logic;
    RESET            : in  std_logic;

    -- ===================
    -- Input Transactions
    -- ===================

    -- WARNING:
    --     When inserting an RX Transaction, any Transaction with the same ID which
    --     is currently present in the component will become unconfirmed with the next
    --     CLK rising edge!
    -- WARNING:
    --     When inserting an RX Transaction in the same cycle as an RX Confirmation
    --     with the same ID, the Transaction will be considered confirmed immediately!
    RX_TRANS_ID      : in  slv_array_t     (RX_TRANSS-1 downto 0)(ID_WIDTH-1 downto 0);
    RX_TRANS_META    : in  slv_array_t     (RX_TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    RX_TRANS_SRC_RDY : in  std_logic_vector(RX_TRANSS-1 downto 0);
    -- Only falls when internal FIFO is full.
    RX_TRANS_DST_RDY : out std_logic;

    -- Inner Transaction FIFO Almost Full
    TRANS_FIFO_AFULL : out std_logic;

    -- ======================
    -- Input ID Confirmations
    -- ======================

    RX_CONF_ID       : in  slv_array_t     (ID_CONFS-1 downto 0)(ID_WIDTH-1 downto 0);
    RX_CONF_VLD      : in  std_logic_vector(ID_CONFS-1 downto 0);

    -- ===================
    -- Output Transactions
    -- ===================

    TX_TRANS_ID      : out slv_array_t     (TX_TRANSS-1 downto 0)(ID_WIDTH-1 downto 0);
    TX_TRANS_META    : out slv_array_t     (TX_TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    TX_TRANS_SRC_RDY : out std_logic_vector(TX_TRANSS-1 downto 0);
    -- All Transactions must be read all at once
    TX_TRANS_DST_RDY : in  std_logic
);
end entity;

architecture FULL of TRANS_SORTER is

    -- When ID only has 1 bit, the output register should never
    -- contain valid Transactions with both ID values at the same time.
    -- Otherwise the confirmation of BOTH ID values at the same time
    -- will be required, which is probably not possible.
    constant ALLOW_MULTI_ID_OUTPUT : boolean := (ID_WIDTH>1);

    -------------------------------------------------------------
    -- Confirmation memory registers
    -------------------------------------------------------------

    signal conf_mem_reg   : std_logic_vector(2**ID_WIDTH-1 downto 0);
    signal conf_mem_s_reg : s_array_t(2**ID_WIDTH-1 downto 0)(1+log2(MAX_SAME_ID_TRANS)-1 downto 0);

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction FIFO
    -------------------------------------------------------------

    signal trans_fifo_di_arr  : slv_array_t     (RX_TRANSS-1 downto 0)(METADATA_WIDTH+ID_WIDTH-1 downto 0);
    signal trans_fifo_di      : std_logic_vector(RX_TRANSS*(METADATA_WIDTH+ID_WIDTH)-1 downto 0);
    signal trans_fifo_wr      : std_logic_vector(RX_TRANSS-1 downto 0);
    signal trans_fifo_full    : std_logic;
    signal trans_fifo_do      : std_logic_vector(TX_TRANSS*(METADATA_WIDTH+ID_WIDTH)-1 downto 0);
    signal trans_fifo_rd      : std_logic_vector(TX_TRANSS-1 downto 0);
    signal trans_fifo_empty   : std_logic_vector(TX_TRANSS-1 downto 0);
    signal trans_fifo_do_arr  : slv_array_t     (TX_TRANSS-1 downto 0)(METADATA_WIDTH+ID_WIDTH-1 downto 0);
    signal trans_fifo_do_id   : slv_array_t     (TX_TRANSS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal trans_fifo_do_meta : slv_array_t     (TX_TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);

    signal trans_fifo_do_id_match : std_logic_vector(TX_TRANSS-1 downto 0);

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction confirmation
    -------------------------------------------------------------

    signal conf_sel        : u_array_t       (TX_TRANSS-1 downto 0)(ID_WIDTH-1 downto 0);

    signal reg0_conf       : std_logic_vector(TX_TRANSS-1 downto 0);
    signal reg0_conf_s     : s_array_t       (TX_TRANSS-1 downto 0)(1+log2(MAX_SAME_ID_TRANS)-1 downto 0);

    signal reg0_trans_id   : slv_array_t     (TX_TRANSS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal reg0_trans_meta : slv_array_t     (TX_TRANSS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg0_trans_vld  : std_logic_vector(TX_TRANSS-1 downto 0);

    signal reg0_trans_confirmed     : std_logic_vector(TX_TRANSS-1 downto 0);
    signal reg0_trans_confirmed_act : std_logic_vector(TX_TRANSS-1 downto 0);

    signal conf_successful : std_logic;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- TX generation
    -------------------------------------------------------------

    signal out_reg_load : std_logic;

    -------------------------------------------------------------

begin

    -------------------------------------------------------------
    -- Asserts
    -------------------------------------------------------------

    assert (MSIDT_BEHAV/=1 or MAX_SAME_ID_TRANS>0)
        report "Trans Sorter: MAX_SAME_ID_TRANS (" & to_string(MAX_SAME_ID_TRANS) & ")" &
               " must be a positive value!"
        severity failure;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Confirmation memory registers
    -------------------------------------------------------------

    conf_mem_0_gen : if (MSIDT_BEHAV=0) generate
        conf_mem_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then

                for i in 0 to RX_TRANSS-1 loop
                    if (RX_TRANS_SRC_RDY(i)='1' and RX_TRANS_DST_RDY='1') then
                        -- Register newly arrived Transaction as waiting for comfirmation.
                        conf_mem_reg(to_integer(unsigned(RX_TRANS_ID(i)))) <= '0';
                    end if;
                end loop;

                for i in 0 to ID_CONFS-1 loop
                    if (RX_CONF_VLD(i)='1') then
                        -- Confirm all previous Transactions with this ID.
                        conf_mem_reg(to_integer(unsigned(RX_CONF_ID(i)))) <= '1';
                    end if;
                end loop;

                if (RESET='1') then
                    conf_mem_reg <= (others => '0');
                end if;
            end if;
        end process;
    end generate;
    conf_mem_1_gen : if (MSIDT_BEHAV=1) generate
        conf_mem_s_reg_pr : process (CLK)
            variable conf_mem_s_reg_v : s_array_t(2**ID_WIDTH-1 downto 0)(1+log2(MAX_SAME_ID_TRANS)-1 downto 0);
        begin
            if (rising_edge(CLK)) then

                conf_mem_s_reg_v := conf_mem_s_reg;

                for i in 0 to TX_TRANSS-1 loop
                    if (conf_successful='1') then
                        -- Increment on successfuly confirmed Transaction
                        conf_mem_s_reg_v(to_integer(unsigned(reg0_trans_id(i)))) := conf_mem_s_reg_v(to_integer(unsigned(reg0_trans_id(i))))+1;
                    end if;
                end loop;

                for i in 0 to ID_CONFS-1 loop
                    if (RX_CONF_VLD(i)='1') then
                        -- Decrement on newly arrived confirmation
                        conf_mem_s_reg_v(to_integer(unsigned(RX_CONF_ID(i)))) := conf_mem_s_reg_v(to_integer(unsigned(RX_CONF_ID(i))))-1;
                    end if;
                end loop;

                conf_mem_s_reg <= conf_mem_s_reg_v;

                if (RESET='1') then
                    conf_mem_s_reg <= (others => (others => '0'));
                end if;
            end if;
        end process;
    end generate;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction FIFO
    -------------------------------------------------------------
    -- FIFO for Transactions, which are waiting for confirmation.

    RX_TRANS_DST_RDY <= (not trans_fifo_full);

    trans_fifo_di_gen : for i in 0 to RX_TRANSS-1 generate
        trans_fifo_di_arr(i) <= RX_TRANS_META(i) & RX_TRANS_ID(i);
    end generate;
    trans_fifo_di <= slv_array_ser(trans_fifo_di_arr);

    trans_fifo_wr <= RX_TRANS_SRC_RDY;

    trans_fifo_full_gen : if (USE_SHAKEDOWN_FIFOX=false) generate

        trans_fifo_i : entity work.FIFOX_MULTI(FULL)
        generic map(
            DATA_WIDTH          => METADATA_WIDTH+ID_WIDTH,
            ITEMS               => TRANS_FIFO_ITEMS       ,
            WRITE_PORTS         => RX_TRANSS              ,
            READ_PORTS          => TX_TRANSS              ,
            RAM_TYPE            => "AUTO"                 ,
            DEVICE              => DEVICE                 ,
            ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET     ,
            ALMOST_EMPTY_OFFSET => 0                      ,
            SAFE_READ_MODE      => true
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => trans_fifo_di   ,
            WR     => trans_fifo_wr   ,
            FULL   => trans_fifo_full ,
            AFULL  => TRANS_FIFO_AFULL,

            DO     => trans_fifo_do   ,
            RD     => trans_fifo_rd   ,
            EMPTY  => trans_fifo_empty,
            AEMPTY => open
        );

    else generate

        trans_fifo_i : entity work.FIFOX_MULTI(SHAKEDOWN)
        generic map(
            DATA_WIDTH          => METADATA_WIDTH+ID_WIDTH,
            ITEMS               => TRANS_FIFO_ITEMS       ,
            WRITE_PORTS         => RX_TRANSS              ,
            READ_PORTS          => TX_TRANSS              ,
            RAM_TYPE            => "AUTO"                 ,
            DEVICE              => DEVICE                 ,
            ALMOST_FULL_OFFSET  => minimum(TRANS_FIFO_ITEMS-1,ALMOST_FULL_OFFSET+2*RX_TRANSS), -- compensate for output Shakedown registers
            ALMOST_EMPTY_OFFSET => 0                      ,
            SAFE_READ_MODE      => true
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => trans_fifo_di   ,
            WR     => trans_fifo_wr   ,
            FULL   => trans_fifo_full ,
            AFULL  => TRANS_FIFO_AFULL,

            DO     => trans_fifo_do   ,
            RD     => trans_fifo_rd   ,
            EMPTY  => trans_fifo_empty,
            AEMPTY => open
        );

    end generate;

    trans_fifo_do_arr <= slv_array_deser(trans_fifo_do,TX_TRANSS);
    trans_fifo_do_gen : for i in 0 to TX_TRANSS-1 generate
        signal tmp_meta : std_logic_vector(METADATA_WIDTH-1 downto 0);
        signal tmp_id   : std_logic_vector(ID_WIDTH-1 downto 0);
    begin
        (tmp_meta, tmp_id) <= trans_fifo_do_arr(i);

        trans_fifo_do_id  (i) <= tmp_id;
        trans_fifo_do_meta(i) <= tmp_meta;
    end generate;

    -- Check if all values of 'trans_fifo_do_id' up to index 'i' are the same as on index 0
    trans_fifo_do_id_match_pr : process (trans_fifo_do_id)
    begin
        trans_fifo_do_id_match <= (others => '0');
        for i in 0 to TX_TRANSS-1 loop
            if (trans_fifo_do_id(i)=trans_fifo_do_id(0)) then
                trans_fifo_do_id_match(i) <= '1';
            else
                exit;
            end if;
        end loop;
    end process;

    trans_fifo_rd_gen : for i in 0 to TX_TRANSS-1 generate
        -- Read when confirmation was successful
        -- Only read Transactions with matching ID when ALLOW_MULTI_ID_OUTPUT==False
        trans_fifo_rd(i) <= '1' when conf_successful='1' and (ALLOW_MULTI_ID_OUTPUT or trans_fifo_do_id_match(i)='1') else '0';
    end generate;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Transaction confirmation
    -------------------------------------------------------------

    -- Confirmation info selection
    conf_sel_gen : for i in 0 to TX_TRANSS-1 generate
        conf_sel(i) <= unsigned(trans_fifo_do_id(i)) when conf_successful='1' else unsigned(reg0_trans_id(i));
    end generate;

    reg0_conf_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Load new info
            for i in 0 to TX_TRANSS-1 loop
                reg0_conf  (i) <= conf_mem_reg  (to_integer(conf_sel(i)));
                reg0_conf_s(i) <= conf_mem_s_reg(to_integer(conf_sel(i)));
            end loop;

            if (RESET='1') then
                reg0_conf   <= (others => '0');
                reg0_conf_s <= (others => (others => '0'));
            end if;
        end if;
    end process;

    reg0_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Load new transactions when confirmation successful
            if (conf_successful='1') then
                reg0_trans_id   <= trans_fifo_do_id;
                reg0_trans_meta <= trans_fifo_do_meta;
                -- Only Transactions which are actually read are valid
                reg0_trans_vld  <= (not trans_fifo_empty) and trans_fifo_rd;
            end if;

            if (RESET='1') then
                reg0_trans_vld <= (others => '0');
            end if;
        end if;
    end process;

    -- Evaluate confirmation of transactions in reg0
    reg0_trans_conf_gen : for i in 0 to TX_TRANSS-1 generate
        reg0_trans_conf_0_gen : if (MSIDT_BEHAV=0) generate
            reg0_trans_confirmed(i) <= '1' when reg0_conf(i)='1' else '0';
        end generate;
        reg0_trans_conf_1_gen : if (MSIDT_BEHAV=1) generate
            reg0_trans_confirmed(i) <= '1' when reg0_conf_s(i)<=0 else '0';
        end generate;
        -- Confirmation is taken as true when the transaction is not valid
        reg0_trans_confirmed_act(i) <= '1' when reg0_trans_confirmed(i)='1' or reg0_trans_vld(i)='0' else '0';
    end generate;

    conf_successful <= '1' when (and reg0_trans_confirmed_act)='1' and out_reg_load='1' else '0';

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- TX generation
    -------------------------------------------------------------

    tx_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            for i in 0 to TX_TRANSS-1 loop
                -- TX reg read
                if (TX_TRANS_DST_RDY='1') then
                    TX_TRANS_SRC_RDY(i) <= '0';
                end if;

                -- TX reg write
                if (out_reg_load='1') then
                    TX_TRANS_ID     (i) <= reg0_trans_id  (i);
                    TX_TRANS_META   (i) <= reg0_trans_meta(i);
                    TX_TRANS_SRC_RDY(i) <= reg0_trans_vld (i) and conf_successful;
                end if;
            end loop;

            if (RESET='1') then
                TX_TRANS_SRC_RDY <= (others => '0');
            end if;
        end if;
    end process;

    out_reg_load <= '1' when TX_TRANS_DST_RDY='1' or TX_TRANS_SRC_RDY(0)='0' else '0';

    -------------------------------------------------------------

end architecture;
