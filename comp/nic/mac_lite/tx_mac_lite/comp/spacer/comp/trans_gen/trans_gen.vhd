-- trans_gen.vhd: TX MAC Lite Spacer Trans Gen
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
-- This unit joins MFB Transaction's start address (recieved on SOF) with its
-- length (recieved on EOF) into one Transaction.

entity TX_MAC_LITE_SPACER_TRANS_GEN is
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

    RX_MFB_EOF_LEN     : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    RX_MFB_EOF_DISCARD : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    RX_MFB_SRC_RDY     : in  std_logic;
    RX_MFB_DST_RDY     : out std_logic;

    -- =====================================================================
    --  TX Transactions
    -- =====================================================================

    TX_TRANS_A_COL     : out std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    TX_TRANS_A_ITEM    : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_TRANS_LEN       : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    TX_TRANS_VLD       : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_TRANS_SRC_RDY   : out std_logic;
    TX_TRANS_DST_RDY   : in  std_logic
);
end entity;

architecture FULL of TX_MAC_LITE_SPACER_TRANS_GEN is

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

    signal eof_shake_rx_data    : std_logic_vector(MFB_REGIONS*(log2(PKT_MTU+1)+1)-1 downto 0);
    signal eof_shake_tx_data    : std_logic_vector(MFB_REGIONS*(log2(PKT_MTU+1)+1)-1 downto 0);
    signal eof_shake_rx_dst_rdy : std_logic;
    signal eof_shake_tx_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_shake_tx_next    : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal eof_shake_tx_len     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal eof_shake_tx_discard : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Transaction generaration logic
    -- =====================================================================

    signal trans_a_col   : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal trans_a_item  : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal trans_len     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal trans_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trans_src_rdy : std_logic;
    signal trans_dst_rdy : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  TX shakedown
    -- =====================================================================

    constant TRANS_SHAKE_DATA_WIDTH : integer := log2(PKT_MTU+1)+log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)+log2(RX_BUF_WORDS);
    signal trans_shake_din     : std_logic_vector(MFB_REGIONS*TRANS_SHAKE_DATA_WIDTH-1 downto 0);
    signal trans_shake_dout    : std_logic_vector(MFB_REGIONS*TRANS_SHAKE_DATA_WIDTH-1 downto 0);

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

    sof_shake_tx_next <= trans_dst_rdy and (eof_shake_tx_vld and (not sof_shake_tx_eow_before));

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
        eof_shake_rx_data((i+1)*(log2(PKT_MTU+1)+1)-1
                       downto i*(log2(PKT_MTU+1)+1))
            <= RX_MFB_EOF_LEN(i) & RX_MFB_EOF_DISCARD(i);
    end generate;

    eof_shake_i : entity work.MVB_SHAKEDOWN
    generic map(
        RX_ITEMS    => MFB_REGIONS,
        TX_ITEMS    => MFB_REGIONS,
        ITEM_WIDTH  => log2(PKT_MTU+1)+1,
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

    eof_shake_tx_next <= trans_dst_rdy and (not sof_shake_tx_eow_before);

    -- EOF Shakedown output parsing
    eof_shake_tx_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_len     : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        signal tmp_discard : std_logic_vector(1-1 downto 0);
    begin
        (tmp_len, tmp_discard) <= eof_shake_tx_data((i+1)*(log2(PKT_MTU+1)+1)-1
                                                 downto i*(log2(PKT_MTU+1)+1));

        eof_shake_tx_len    (i) <= tmp_len;
        eof_shake_tx_discard(i) <= tmp_discard(0);
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Transaction generaration logic
    -- =====================================================================

    tx_trans_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (trans_dst_rdy='1') then

                -- set Transaction values
                trans_a_col  <= sof_shake_tx_a_col(0);
                trans_a_item <= sof_shake_tx_a_item;
                trans_len    <= eof_shake_tx_len;

                -- set valid
                -- Transaction is valid when EOF is valid and is not being discarded
                -- and there is not an End of Word in any previous Transaction
                trans_vld <= eof_shake_tx_vld and (not eof_shake_tx_discard) and (not sof_shake_tx_eow_before);

                trans_src_rdy <= (or eof_shake_tx_vld);
            end if;

            if (RESET='1') then
                trans_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  TX shakedown
    -- =====================================================================
    -- The Transactions need to be shook down again becouse some of the became
    -- invalid after their discrading (eof_shake_tx_discard).

    trans_shake_din_gen : for i in 0 to MFB_REGIONS-1 generate
        trans_shake_din((i+1)*TRANS_SHAKE_DATA_WIDTH-1
                     downto i*TRANS_SHAKE_DATA_WIDTH)
            <= trans_len(i) & trans_a_item(i) & trans_a_col;
    end generate;

    trans_shake_i : entity work.SHAKEDOWN
    generic map(
        INPUTS     => MFB_REGIONS,
        OUTPUTS    => MFB_REGIONS,
        DATA_WIDTH => TRANS_SHAKE_DATA_WIDTH,
        OUTPUT_REG => true
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        DIN          => trans_shake_din ,
        DIN_VLD      => trans_vld       ,
        DIN_SRC_RDY  => trans_src_rdy   ,
        DIN_DST_RDY  => trans_dst_rdy   ,

        DOUT         => trans_shake_dout,
        DOUT_VLD     => TX_TRANS_VLD    ,
        DOUT_SRC_RDY => TX_TRANS_SRC_RDY,
        DOUT_DST_RDY => TX_TRANS_DST_RDY
    );

    trans_shake_dout_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_trans_len    : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        signal tmp_trans_a_item : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        signal tmp_trans_a_col  : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    begin
        (tmp_trans_len   ,
         tmp_trans_a_item,
         tmp_trans_a_col  ) <= trans_shake_dout((i+1)*TRANS_SHAKE_DATA_WIDTH-1
                                             downto i*TRANS_SHAKE_DATA_WIDTH);

         TX_TRANS_A_ITEM(i) <= tmp_trans_a_item;
         TX_TRANS_LEN   (i) <= tmp_trans_len;
    end generate;

    TX_TRANS_A_COL <= trans_shake_dout(log2(RX_BUF_WORDS)-1 downto 0);

    -- =====================================================================

end architecture;
