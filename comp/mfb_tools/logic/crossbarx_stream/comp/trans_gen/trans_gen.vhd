-- trans_gen.vhd: Crossbarx stream Trans Gen
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek   <xkubal11@fit.vutbr.cz>
--            Daniel Kondys <xkondy00@vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--  Description
-- =========================================================================
-- This unit joins MFB Transaction's start address (recieved on SOF) with its
-- length (recieved on EOF) into one Transaction.

entity CROSSBARX_STREAM_TRANS_GEN is
generic(
    -- Number of regions within a data word, must be power of 2.
    MFB_REGIONS        : natural := 4;
    -- Region size (in blocks).
    MFB_REGION_SIZE    : natural := 8;
    -- Block size (in items).
    MFB_BLOCK_SIZE     : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH     : natural := 8;

    -- Number of words in Source Buffer
    RX_BUF_WORDS       : natural := 512;

    -- Maximum packet size in MFB ITEMS.
    PKT_MTU            : natural := 1024;

    -- Width of user metadata
    META_WIDTH         : natural := 0;

    -- FPGA device name.
    DEVICE             : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK                : in  std_logic;
    RESET              : in  std_logic;

    -- =====================================================================
    --  RX MFB info
    -- =====================================================================

    RX_MFB_SOF_ADDR    : in  std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    RX_MFB_SOF_POS     : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    RX_MFB_SOF_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    RX_MFB_EOF_META    : in  slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    RX_MFB_EOF_LEN     : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    RX_MFB_EOF_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    RX_MFB_SRC_RDY     : in  std_logic;
    RX_MFB_DST_RDY     : out std_logic;

    -- =====================================================================
    --  TX Transactions
    -- =====================================================================

    TX_TRANS_A_COL     : out std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    TX_TRANS_A_ITEM    : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_TRANS_META      : out slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    TX_TRANS_LEN       : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    TX_TRANS_VLD       : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_TRANS_SRC_RDY   : out std_logic;
    TX_TRANS_DST_RDY   : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_STREAM_TRANS_GEN is

    -- =====================================================================
    --  SOF Shakedown
    -- =====================================================================

    signal rx_mfb_last_vld_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal sof_shake_rx_data         : std_logic_vector(MFB_REGIONS*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1)-1 downto 0);
    signal sof_shake_rx_dst_rdy      : std_logic;
    signal sof_shake_tx_data         : std_logic_vector(MFB_REGIONS*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1)-1 downto 0);
    signal sof_shake_tx_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal sof_shake_tx_next         : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal sof_shake_tx_a_col        : slv_array_t(MFB_REGIONS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal sof_shake_tx_a_item       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal sof_shake_tx_last_vld_sof : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal sof_shake_tx_eow_before   : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  EOF Shakedown
    -- =====================================================================

    signal eof_shake_rx_data    : std_logic_vector(MFB_REGIONS*(log2(PKT_MTU+1)+META_WIDTH)-1 downto 0);
    signal eof_shake_tx_data    : std_logic_vector(MFB_REGIONS*(log2(PKT_MTU+1)+META_WIDTH)-1 downto 0);
    signal eof_shake_rx_dst_rdy : std_logic;
    signal eof_shake_tx_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_shake_tx_next    : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal eof_shake_tx_meta    : slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal eof_shake_tx_len     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);

    -- =====================================================================

begin

    RX_MFB_DST_RDY <= sof_shake_rx_dst_rdy and eof_shake_rx_dst_rdy;

    -- =====================================================================
    --  SOF Shakedown
    -- =====================================================================

    -- last valid SOF detection
    rx_mfb_last_vld_sof_pr : process (RX_MFB_SOF_VLD)
    begin
        rx_mfb_last_vld_sof <= (others => '0');
        for i in MFB_REGIONS-1 downto 0 loop
            if (RX_MFB_SOF_VLD(i)='1') then
                rx_mfb_last_vld_sof(i) <= '1';
                exit;
            end if;
        end loop;
    end process;

    -- SOF Shakedown input generation
    sof_shake_rx_gen : for i in 0 to MFB_REGIONS-1 generate
        sof_shake_rx_data((i+1)*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1)-1
                       downto i*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1))
            <= RX_MFB_SOF_ADDR & std_logic_vector(to_unsigned(i,log2(MFB_REGIONS))) & RX_MFB_SOF_POS(i) & rx_mfb_last_vld_sof(i);
    end generate;

    sof_shake_i : entity work.MVB_SHAKEDOWN
    generic map(
        RX_ITEMS    => MFB_REGIONS,
        TX_ITEMS    => MFB_REGIONS,
        ITEM_WIDTH  => log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1,
        SHAKE_PORTS => 3
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => sof_shake_rx_data,
        RX_VLD     => RX_MFB_SOF_VLD   ,
        RX_SRC_RDY => RX_MFB_SRC_RDY and eof_shake_rx_dst_rdy,
        RX_DST_RDY => sof_shake_rx_dst_rdy,

        TX_DATA    => sof_shake_tx_data,
        TX_VLD     => sof_shake_tx_vld ,
        TX_NEXT    => sof_shake_tx_next
    );

    sof_shake_tx_next <= TX_TRANS_DST_RDY and (eof_shake_tx_vld and (not sof_shake_tx_eow_before));

    -- SOF Shakedown output parsing
    sof_shake_tx_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_a_col  : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
        signal tmp_a_item : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0);
        signal tmp_last   : std_logic_vector(1-1 downto 0);
    begin
        (tmp_a_col, tmp_a_item, tmp_last) <= sof_shake_tx_data((i+1)*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1)-1
                                                            downto i*(log2(RX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)+1));

        sof_shake_tx_a_col       (i) <= tmp_a_col;
        sof_shake_tx_a_item      (i) <= tmp_a_item & (log2(MFB_BLOCK_SIZE)-1 downto 0 => '0');
        sof_shake_tx_last_vld_sof(i) <= tmp_last(0);
    end generate;

    -- spread End of Word information
    sof_shake_eow_pr : process (sof_shake_tx_last_vld_sof)
    begin
        for i in 0 to MFB_REGIONS-1 loop
            sof_shake_tx_eow_before(i) <= (or sof_shake_tx_last_vld_sof(i-1 downto 0));
        end loop;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  EOF Shakedown
    -- =====================================================================

    -- EOF Shakedown input generation
    eof_shake_rx_gen : for i in 0 to MFB_REGIONS-1 generate
        eof_shake_rx_data((i+1)*(META_WIDTH+log2(PKT_MTU+1))-1
                       downto i*(META_WIDTH+log2(PKT_MTU+1)))
            <= RX_MFB_EOF_META(i) & RX_MFB_EOF_LEN(i);
    end generate;

    eof_shake_i : entity work.MVB_SHAKEDOWN
    generic map(
        RX_ITEMS    => MFB_REGIONS,
        TX_ITEMS    => MFB_REGIONS,
        ITEM_WIDTH  => META_WIDTH+log2(PKT_MTU+1),
        SHAKE_PORTS => 2
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => eof_shake_rx_data   ,
        RX_VLD     => RX_MFB_EOF_VLD      ,
        RX_SRC_RDY => RX_MFB_SRC_RDY and sof_shake_rx_dst_rdy,
        RX_DST_RDY => eof_shake_rx_dst_rdy,

        TX_DATA    => eof_shake_tx_data,
        TX_VLD     => eof_shake_tx_vld ,
        TX_NEXT    => eof_shake_tx_next
    );

    eof_shake_tx_next <= TX_TRANS_DST_RDY and (not sof_shake_tx_eow_before);

    -- EOF Shakedown output parsing
    eof_shake_tx_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_meta    : std_logic_vector(META_WIDTH-1 downto 0);
        signal tmp_len     : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
    begin
        (tmp_meta, tmp_len) <= eof_shake_tx_data((i+1)*(META_WIDTH+log2(PKT_MTU+1))-1
                                              downto i*(META_WIDTH+log2(PKT_MTU+1)));


        eof_shake_tx_meta   (i) <= tmp_meta;
        eof_shake_tx_len    (i) <= tmp_len;
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Transaction generaration logic
    -- =====================================================================

    tx_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_TRANS_DST_RDY='1') then

                -- set Transaction values
                TX_TRANS_A_COL  <= sof_shake_tx_a_col(0);
                TX_TRANS_A_ITEM <= sof_shake_tx_a_item;
                TX_TRANS_META   <= eof_shake_tx_meta;
                TX_TRANS_LEN    <= eof_shake_tx_len;

                -- set valid
                -- Transaction is valid when EOF is valid and there is not an End of Word in any previous Transaction
                TX_TRANS_VLD <= eof_shake_tx_vld and (not sof_shake_tx_eow_before);

                TX_TRANS_SRC_RDY <= (or eof_shake_tx_vld);
            end if;

            if (RESET='1') then
                TX_TRANS_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- =====================================================================

end architecture;
