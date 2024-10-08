-- pcie_mfb2avst.vhd: This component transfers MFB to AVST bus.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity PCIE_MFB2AVST is
    Generic(
        REGIONS            : natural := 2;
        REGION_SIZE        : natural := 1; -- not to be changed
        BLOCK_SIZE         : natural := 8; -- not to be changed
        ITEM_WIDTH         : natural := 32; -- not to be changed
        META_WIDTH         : natural := 8
    );
    Port(
        CLK            : in  std_logic;
        RST            : in  std_logic;
        -- rx interface
        RX_MFB_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;
        -- tx interface
        TX_AVST_DATA   : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_AVST_META   : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_AVST_SOP    : out std_logic_vector(REGIONS-1 downto 0);
        TX_AVST_EOP    : out std_logic_vector(REGIONS-1 downto 0);
        TX_AVST_EMPTY  : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_AVST_VALID  : out std_logic_vector(REGIONS-1 downto 0);
        TX_AVST_READY  : in  std_logic
    );
end entity;

architecture behav of PCIE_MFB2AVST is

    constant META_SIGNAL_WIDTH : natural := REGIONS*META_WIDTH;
    constant DATA_WIDTH        : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant AVST_EMPTY_WIDTH  : natural := REGIONS*log2(REGION_SIZE*BLOCK_SIZE);

    signal avst_empty_arr   : slv_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal mfb_eof_pos_arr  : slv_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal ready_delay_reg1 : std_logic;
    signal mfb_dst_rdy      : std_logic;
    signal avst_empty       : std_logic_vector(AVST_EMPTY_WIDTH-1 downto 0);
    signal mfb_src_rdy      : std_logic;
    signal avst_sop         : std_logic_vector(REGIONS-1 downto 0);
    signal avst_eop         : std_logic_vector(REGIONS-1 downto 0);
    signal pkt_cont         : std_logic_vector(REGIONS-1 downto 0); -- signals that the packet has not ended in the previous region (continues into this region)
    signal next_pkt         : std_logic_vector(REGIONS-1 downto 0); -- signals that the packet continues to the next region

begin

    mfb_eof_pos_arr <= slv_array_downto_deser(RX_MFB_EOF_POS, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

    eof_pos_array_g : for i in 0 to REGIONS - 1 generate
        avst_empty_arr(i) <= std_logic_vector((REGION_SIZE*BLOCK_SIZE-1) - unsigned(mfb_eof_pos_arr(i)));
    end generate;

    avst_empty <= slv_array_ser(avst_empty_arr, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

    -- ===================================================================
    -- once delayed data and twice delayed src_rdy makes ready_latency = 3
    -- ===================================================================
    data_delay_reg_p :process (CLK)
    begin
        if (rising_edge(CLK)) then
            TX_AVST_DATA  <= RX_MFB_DATA;
            TX_AVST_META  <= RX_MFB_META;
            avst_sop      <= RX_MFB_SOF;
            avst_eop      <= RX_MFB_EOF;
            TX_AVST_EMPTY <= avst_empty;
        end if;
    end process;

    ready_delay1_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                ready_delay_reg1 <= '0';
            else
                ready_delay_reg1 <= TX_AVST_READY;
            end if;
        end if;
    end process;

    ready_delay2_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                mfb_dst_rdy <= '0';
            else
                mfb_dst_rdy <= ready_delay_reg1;
            end if;
        end if;
    end process;

    -- ======================
    --  logic for avst valid
    -- ======================
    src_rdy_delay_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                mfb_src_rdy <= '0';
            else
                mfb_src_rdy <= RX_MFB_SRC_RDY and mfb_dst_rdy;
            end if;
        end if;
    end process;

    packet_cont : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                pkt_cont(0) <= '0';
            elsif mfb_src_rdy = '1' then
                pkt_cont(0) <= next_pkt(REGIONS-1);
            end if;
        end if;
    end process;

    rename_gen : for i in 1 to REGIONS-1 generate
        pkt_cont(i) <= next_pkt(i-1);
    end generate;

    valid_gen : for i in 0 to REGIONS-1 generate
        next_pkt(i)      <= (not pkt_cont(i) and     avst_sop(i) and not avst_eop(i)) or
                            (    pkt_cont(i) and not avst_sop(i) and not avst_eop(i)) or
                            (    pkt_cont(i) and     avst_sop(i) and     avst_eop(i));
        TX_AVST_VALID(i) <= mfb_src_rdy and (
                            (not pkt_cont(i) and     avst_sop(i) and not avst_eop(i)) or
                            (not pkt_cont(i) and     avst_sop(i) and     avst_eop(i)) or
                            (    pkt_cont(i) and not avst_sop(i) and not avst_eop(i)) or
                            (    pkt_cont(i) and not avst_sop(i) and     avst_eop(i)) or
                            (    pkt_cont(i) and     avst_sop(i) and     avst_eop(i)));
    end generate;

    -- ===============================================
    -- ouput interface assignment to according signals
    -- ===============================================
    RX_MFB_DST_RDY <= mfb_dst_rdy;
    TX_AVST_SOP    <= avst_sop;
    TX_AVST_EOP    <= avst_eop;

end behav;
