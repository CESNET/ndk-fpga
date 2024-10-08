-- gap_counter.vhd: TX MAC Lite Spacer Gap Counter
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--  Description
-- =========================================================================
-- This unit adds space after each passed packet. The unit makes sure, that
-- there is at least GAP MFB items after every TX packet.

entity TX_MAC_LITE_SPACER_GAP_COUNTER is
generic(
    -- Number of regions within a data word, must be power of 2.
    MFB_REGIONS        : natural := 4;
    -- Region size (in blocks).
    MFB_REGION_SIZE    : natural := 8;
    -- Block size (in items).
    MFB_BLOCK_SIZE     : natural := 8;

    -- Number of words in Source Buffer
    RX_BUF_WORDS       : natural := 512;
    -- Number of words in Destination Buffer
    TX_BUF_WORDS       : natural := 512;

    -- Maximum packet size in MFB ITEMS.
    PKT_MTU            : natural := 1024;
    -- Required minimum gap after every packet in MFB ITEMS.
    -- 4B CRC + 12B Idle + 8B Preamble
    GAP                : natural := 24;

    -- FPGA device name.
    DEVICE             : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK                  : in  std_logic;
    RESET                : in  std_logic;

    -- =====================================================================
    --  RX Transactions
    -- =====================================================================

    RX_TRANS_A_COL       : in  std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    RX_TRANS_A_ITEM      : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    RX_TRANS_LEN         : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    RX_TRANS_VLD         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_TRANS_SRC_RDY     : in  std_logic;
    RX_TRANS_DST_RDY     : out std_logic;

    -- =====================================================================
    --  TX Transactions
    -- =====================================================================

    TX_TRANS_A_COL       : out std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    TX_TRANS_A_ITEM      : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_TRANS_B_COL       : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    TX_TRANS_B_ITEM      : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_TRANS_LEN         : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    TX_TRANS_A_LEN_SUM   : out std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU                +1)-1 downto 0); -- total number of items taken in RX Buffer
    TX_TRANS_B_LEN_SUM   : out std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU+MFB_REGIONS*GAP+1)-1 downto 0); -- total number of items taken in TX Buffer
    TX_TRANS_VLD         : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_TRANS_SRC_RDY     : out std_logic;
    TX_TRANS_DST_RDY     : in  std_logic
);
end entity;

architecture FULL of TX_MAC_LITE_SPACER_GAP_COUNTER is

    -- =====================================================================
    --  Deficit idle count tables
    -- =====================================================================

    signal RX_TRANS_LEN_block : slv_array_t(0 to MFB_REGIONS-1)(log2(MFB_BLOCK_SIZE)-1 downto 0);
    signal dic_gap_block      : slv_array_t(0 to MFB_REGIONS-1)(log2(((GAP+MFB_BLOCK_SIZE-1)/MFB_BLOCK_SIZE)+1)-1 downto 0);
    signal dic_gap            : u_array_t(MFB_REGIONS-1 downto 0)(log2(GAP+1)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Register 0
    -- =====================================================================

    signal reg0_trans_a_col     : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal reg0_trans_a_item    : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal reg0_trans_b_col     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal reg0_trans_b_item    : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal reg0_trans_len       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal reg0_trans_gap       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(GAP+1)-1 downto 0);
    signal reg0_trans_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal reg0_trans_src_rdy   : std_logic;
    signal reg0_trans_en        : std_logic;
    signal reg0_first_nonvld_i  : integer;

    -- =====================================================================

    -- =====================================================================
    --  Register 1
    -- =====================================================================

    signal rx_buf_ptr_reg         : unsigned(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal tx_buf_ptr_reg         : unsigned(log2(TX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);

    signal reg1_trans_a_col       : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal reg1_trans_a_item      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal reg1_trans_b_col       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal reg1_trans_b_item      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal reg1_trans_len         : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal reg1_trans_a_len_sum   : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU                +1)-1 downto 0);
    signal reg1_trans_b_len_sum   : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU+MFB_REGIONS*GAP+1)-1 downto 0);
    signal reg1_trans_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal reg1_trans_src_rdy     : std_logic;
    signal reg1_trans_en          : std_logic;

    -- =====================================================================

begin

    -- =====================================================================
    --  Deficit idle count tables
    -- =====================================================================
    -- Calculate gap for each RX Transaction.

    rx_trans_len_item_to_block_gen : for i in 0 to MFB_REGIONS-1 generate
        RX_TRANS_LEN_block(i) <= std_logic_vector(resize_left(unsigned(RX_TRANS_LEN(i)),log2(MFB_BLOCK_SIZE)));
    end generate;

    dic_i: entity work.CDG_SCHEDULER_TX_SCHEDULER_CTRL_MERGER_DIC
    generic map(
        ETH_MFB_REGIONS    => MFB_REGIONS   ,
        ETH_MFB_BLOCK_SIZE => MFB_BLOCK_SIZE,
        GAP                => GAP
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_PACKET_LENGTH         => RX_TRANS_LEN_block,
        RX_PACKET_LENGTH_EOP     => (others => '1')   ,
        RX_PACKET_LENGTH_VLD     => RX_TRANS_VLD      ,
        RX_PACKET_LENGTH_SRC_RDY => RX_TRANS_SRC_RDY  ,
        RX_PACKET_LENGTH_DST_RDY => RX_TRANS_DST_RDY  ,

        TX_PACKET_GAP            => dic_gap_block     ,
        TX_PACKET_GAP_VLD        => open              ,
        TX_PACKET_GAP_SRC_RDY    => open              ,
        TX_PACKET_GAP_DST_RDY    => reg0_trans_en
    );

    dic_gap_block_to_item_gen : for i in 0 to MFB_REGIONS-1 generate
        dic_gap(i) <= resize_right(unsigned(dic_gap_block(i)),log2(GAP+1));
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Register 0
    -- =====================================================================
    -- Save RX Transaction with counted gaps.

    reg0_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (reg0_trans_en='1') then
                reg0_trans_a_col   <= RX_TRANS_A_COL;
                reg0_trans_a_item  <= RX_TRANS_A_ITEM;
                reg0_trans_len     <= RX_TRANS_LEN;
                for i in 0 to MFB_REGIONS-1 loop
                    reg0_trans_gap(i) <= std_logic_vector(dic_gap(i)+enlarge_left(to_unsigned(MFB_BLOCK_SIZE,log2(MFB_BLOCK_SIZE+1))-unsigned(RX_TRANS_LEN_block(i)),-1));
                end loop;
                reg0_trans_vld     <= RX_TRANS_VLD;
                reg0_trans_src_rdy <= RX_TRANS_SRC_RDY;
            end if;

            if (RESET='1') then
                reg0_trans_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- enabled when being read
    reg0_trans_en <= reg1_trans_en;

    -- find index of the first non-valid Transaction in Register 0
    reg0_first_nonvld_i_pr : process (reg0_trans_vld)
    begin
        reg0_first_nonvld_i <= 0;
        for i in 0 to MFB_REGIONS-1 loop
            exit when (reg0_trans_vld(i)='0');
            reg0_first_nonvld_i <= i+1;
        end loop;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  Register 1
    -- =====================================================================
    -- Set TX Buffer address for all Transactions.
    -- Count TX Buffer write pointer.

    reg1_trans_pr : process (CLK)
        variable tmp_a_ptr  : unsigned(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        variable tmp_b_ptr  : unsigned(log2(TX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        variable tmp_b_col  : std_logic_vector(log2(TX_BUF_WORDS)-1 downto 0);
        variable tmp_b_item : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            if (reg1_trans_en='1') then
                reg1_trans_a_col   <= reg0_trans_a_col;
                reg1_trans_a_item  <= reg0_trans_a_item;
                reg1_trans_len     <= reg0_trans_len;
                reg1_trans_vld     <= reg0_trans_vld;
                reg1_trans_src_rdy <= reg0_trans_src_rdy;

                -- count sum of length of all valid Transactions in TX Buffer
                tmp_b_ptr := (others => '0');
                for i in 0 to MFB_REGIONS-1 loop
                    if (i<reg0_first_nonvld_i) then
                        tmp_b_ptr := tmp_b_ptr
                                    +resize_left(unsigned(reg0_trans_len(i)),tmp_b_ptr'length)
                                    +resize_left(unsigned(reg0_trans_gap(i)),tmp_b_ptr'length);
                    end if;
                end loop;
                reg1_trans_b_len_sum <= std_logic_vector(resize_left(tmp_b_ptr,reg1_trans_b_len_sum'length));

                -- calcutate TX Buffer addresses for Transactions
                tmp_b_ptr := tx_buf_ptr_reg;
                for i in 0 to MFB_REGIONS-1 loop

                    -- set address of this Transaction
                    (tmp_b_col, tmp_b_item) := std_logic_vector(tmp_b_ptr);
                    reg1_trans_b_col(i)     <= tmp_b_col;
                    reg1_trans_b_item(i)    <= tmp_b_item;

                    -- move the pointer to the start of the next Transaction
                    tmp_b_ptr := tmp_b_ptr
                                +resize_left(unsigned(reg0_trans_len(i)),tmp_b_ptr'length)
                                +resize_left(unsigned(reg0_trans_gap(i)),tmp_b_ptr'length);

                    -- save new TX Buffer pointer for next Transactions
                    -- (only take the last valid value)
                    if (reg0_trans_src_rdy='1' and i+1=reg0_first_nonvld_i) then
                        tx_buf_ptr_reg <= tmp_b_ptr;
                    end if;

                end loop;

                -- calcutate new RX Buffer pointer for next Transactions
                tmp_a_ptr := rx_buf_ptr_reg;
                for i in 0 to MFB_REGIONS-1 loop
                    if (i<reg0_first_nonvld_i) then
                        tmp_a_ptr := unsigned(reg0_trans_a_col) & unsigned(reg0_trans_a_item(i));
                        tmp_a_ptr := resize(tmp_a_ptr + unsigned(reg0_trans_len(i)),tmp_a_ptr'length);
                    end if;
                end loop;
                reg1_trans_a_len_sum <= std_logic_vector(resize_left(tmp_a_ptr-rx_buf_ptr_reg,reg1_trans_a_len_sum'length));

                -- save the next pointer
                if (reg0_trans_src_rdy='1') then
                    rx_buf_ptr_reg <= tmp_a_ptr;
                end if;

            end if;

            if (RESET='1') then
                reg1_trans_src_rdy <= '0';
                rx_buf_ptr_reg     <= (others => '0');
                tx_buf_ptr_reg     <= (others => '0');
            end if;
        end if;
    end process;

    -- enabled when empty or being read
    reg1_trans_en <= '1' when TX_TRANS_DST_RDY='1' or reg1_trans_src_rdy='0' else '0';

    -- =====================================================================

    -- =====================================================================
    --  TX generation
    -- =====================================================================

    TX_TRANS_A_COL       <= reg1_trans_a_col;
    TX_TRANS_A_ITEM      <= reg1_trans_a_item;
    TX_TRANS_B_COL       <= reg1_trans_b_col;
    TX_TRANS_B_ITEM      <= reg1_trans_b_item;
    TX_TRANS_LEN         <= reg1_trans_len;
    TX_TRANS_A_LEN_SUM   <= reg1_trans_a_len_sum;
    TX_TRANS_B_LEN_SUM   <= reg1_trans_b_len_sum;
    TX_TRANS_VLD         <= reg1_trans_vld;
    TX_TRANS_SRC_RDY     <= reg1_trans_src_rdy;

    -- =====================================================================

end architecture;
