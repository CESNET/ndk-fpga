-- pcie_axicc2mfb.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- INPUT - AXI CC: DATA=512, CC=80 for Gen3x16 PCIe (Ultrascale+), no straddling!
-- OUTPUT - MFB for Gen3x16 PCIe (Stratix10)

entity PCIE_AXICC2MFB is
    generic(
        DEVICE : string  := "STRATIX10"
    );
    port(
        CLK             : in  std_logic;
        RESET           : in  std_logic;
        -- =====================================================================
        -- AXI Completer Completion Interface (CC)
        -- =====================================================================
        -- Data bus
        RX_AXI_CC_DATA  : in  std_logic_vector(512-1 downto 0);
        -- Set of signals with sideband information about trasferred transaction
        RX_AXI_CC_USER  : in  std_logic_vector(81-1 downto 0);
        -- Indication of the last word of a transaction
        RX_AXI_CC_LAST  : in  std_logic;
        -- Indication of valid data
        -- each bit determines validity of different Dword (1 Dword = 4 Bytes)
        RX_AXI_CC_KEEP  : in  std_logic_vector(512/32-1 downto 0);
        -- Indication of valid data
        -- i.e. user application is ready to send a transaction
        RX_AXI_CC_VALID : in  std_logic;
        -- Completer is ready to receive a transaction
        RX_AXI_CC_READY : out std_logic;
        -- =====================================================================
        -- MFB UP stream
        -- =====================================================================
        TX_MFB_DATA     : out std_logic_vector(512-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(2-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(2-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of PCIE_AXICC2MFB is

    constant MFB_REGIONS     : natural := 2;  -- don't change it!
    constant MFB_REGION_SIZE : natural := 1;  -- don't change it!
    constant MFB_BLOCK_SIZE  : natural := 8;  -- don't change it!
    constant MFB_ITEM_WIDTH  : natural := 32; -- don't change it!

    signal s_reg_axi_cc_data : std_logic_vector(512-1 downto 0);
    signal s_reg_axi_cc_user : std_logic_vector(81-1 downto 0);
    signal s_reg_axi_cc_last : std_logic;
    signal s_reg_axi_cc_keep : std_logic_vector(512/32-1 downto 0);
    signal s_reg_axi_cc_vld  : std_logic;
    signal s_axi_cc_ready    : std_logic;

    signal s_word_cnt : unsigned(8-1 downto 0);

    signal s_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal s_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_mfb_src_rdy : std_logic;
    signal s_mfb_dst_rdy : std_logic;

begin

    RX_AXI_CC_READY <= s_axi_cc_ready;

    -- =========================================================================
    -- Input AXI CC registers
    -- =========================================================================

    reg_axicc_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_axi_cc_ready = '1') then
                s_reg_axi_cc_data <= RX_AXI_CC_DATA;
                s_reg_axi_cc_user <= RX_AXI_CC_USER;
                s_reg_axi_cc_last <= RX_AXI_CC_LAST;
                s_reg_axi_cc_keep <= RX_AXI_CC_KEEP;
            end if;
        end if;
    end process;

    reg_axicc_vld_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_axi_cc_vld <= '0';
            elsif (s_axi_cc_ready = '1') then
                s_reg_axi_cc_vld <= RX_AXI_CC_VALID;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Convert AXI CC stream to MFB stream
    -- =========================================================================

    word_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_word_cnt <= (others => '0');
            elsif (s_reg_axi_cc_vld = '1' and s_axi_cc_ready = '1') then
                if (s_reg_axi_cc_last = '1') then
                    s_word_cnt <= (others => '0');
                else
                    s_word_cnt <= s_word_cnt + 1;
                end if;
            end if;
        end if;
    end process;

    s_mfb_sof <= "01" when (s_word_cnt = 0) else "00";
    s_mfb_eof(0) <= s_reg_axi_cc_last and s_reg_axi_cc_keep(0) and not s_reg_axi_cc_keep(8);
    s_mfb_eof(1) <= s_reg_axi_cc_last and s_reg_axi_cc_keep(8);
    s_mfb_src_rdy <= s_reg_axi_cc_vld;

    s_avst_data_p : process (s_reg_axi_cc_data, s_mfb_sof)
    begin
        if (s_mfb_sof(0) = '1') then -- header and data
            -- copy Intel header and data
            s_mfb_data <= s_reg_axi_cc_data;
            -- header modifications (Xilinx to Intel)
            s_mfb_data(95 downto 80) <= s_reg_axi_cc_data(63 downto 48); -- Requester ID
            s_mfb_data(79 downto 72) <= s_reg_axi_cc_data(71 downto 64); -- Tag
            s_mfb_data(71) <= '0'; -- reserved bit
            s_mfb_data(70 downto 64) <= s_reg_axi_cc_data(6 downto 0); -- Lower Address
            s_mfb_data(63 downto 48) <= s_reg_axi_cc_data(87 downto 72); -- completer ID
            s_mfb_data(47 downto 45) <= s_reg_axi_cc_data(45 downto 43); -- status
            s_mfb_data(44) <= '0'; -- BCM (force GND, this is only for PCI-X)
            s_mfb_data(43 downto 32) <= s_reg_axi_cc_data(27 downto 16); -- byte count
            s_mfb_data(31 downto 24) <= "01001010"; -- fmt & type (only Completion with Data is supported)
            s_mfb_data(23) <= '0'; -- reserved bit
            s_mfb_data(22 downto 20) <= s_reg_axi_cc_data(91 downto 89); -- TC
            s_mfb_data(19) <= '0'; -- reserved bit
            s_mfb_data(18) <= s_reg_axi_cc_data(94); -- attr[2]
            s_mfb_data(17) <= '0'; -- reserved bit
            s_mfb_data(16) <= '0'; -- TH (reserved bit for completions)
            s_mfb_data(15) <= s_reg_axi_cc_data(95); -- TD
            s_mfb_data(14) <= s_reg_axi_cc_data(46); -- EP
            s_mfb_data(13 downto 12) <= s_reg_axi_cc_data(93 downto 92); -- attr[1:0]
            s_mfb_data(11 downto 10) <= s_reg_axi_cc_data(9 downto 8); -- AT
            s_mfb_data(9 downto 0) <= s_reg_axi_cc_data(41 downto 32); -- dword count
        else -- only data
            s_mfb_data <= s_reg_axi_cc_data;
        end if;
    end process;

    s_axi_cc_ready <= s_mfb_dst_rdy;

    -- =========================================================================
    -- MFB OUTPUT PIPE
    -- =========================================================================

    mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => s_mfb_data,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => (others => '0'),
        RX_SOF     => s_mfb_sof,
        RX_EOF     => s_mfb_eof,
        RX_SRC_RDY => s_mfb_src_rdy,
        RX_DST_RDY => s_mfb_dst_rdy,

        TX_DATA    => TX_MFB_DATA,
        TX_SOF_POS => open,
        TX_EOF_POS => open,
        TX_SOF     => TX_MFB_SOF,
        TX_EOF     => TX_MFB_EOF,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
