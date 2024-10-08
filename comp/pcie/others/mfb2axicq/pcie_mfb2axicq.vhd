-- pcie_mfb2axicq.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- INPUT  - MFB for Gen3x16 PCIe (Stratix10), straddling!
-- OUTPUT - AXI CQ: DATA=512, CQ=183 for Gen3x16 PCIe (Ultrascale+), no straddling!

entity PCIE_MFB2AXICQ is
    generic(
        BAR_APERTURE      : natural := 63;
        FIFO_DEPTH        : natural := 512;
        FIFO_RAM_TYPE     : string  := "BRAM";
        FIFO_AFULL_OFFSET : natural := 20;
        DEVICE            : string  := "STRATIX10"
    );
    port(
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- =====================================================================
        -- MFB Down Stream
        -- =====================================================================
        RX_MFB_DATA      : in  std_logic_vector(512-1 downto 0);
        RX_MFB_BAR_RANGE : in  std_logic_vector(6-1 downto 0);
        RX_MFB_SOF       : in  std_logic_vector(2-1 downto 0);
        RX_MFB_EOF       : in  std_logic_vector(2-1 downto 0);
        RX_MFB_EOF_POS   : in  std_logic_vector(6-1 downto 0);
        RX_MFB_SRC_RDY   : in  std_logic;
        RX_MFB_DST_RDY   : out std_logic;
        RX_FIFO_AFULL    : out std_logic;
        -- =====================================================================
        -- AXI Completer Request Interface (CQ)
        -- =====================================================================
        -- Data bus
        TX_AXI_CQ_DATA   : out std_logic_vector(511 downto 0);
        -- Set of signals with sideband information about trasferred transaction
        TX_AXI_CQ_USER   : out std_logic_vector(183-1 downto 0);
        -- Indication of the last word of a transaction
        TX_AXI_CQ_LAST   : out std_logic;
        -- Indication of valid data
        -- each bit determines validity of different Dword (1 Dword = 4 Bytes)
        TX_AXI_CQ_KEEP   : out std_logic_vector(512/32-1 downto 0);
        -- Indication of valid data
        -- i.e. completer is ready to send a transaction
        TX_AXI_CQ_VALID  : out std_logic;
        -- User application is ready to receive a transaction
        TX_AXI_CQ_READY  : in  std_logic
    );
end entity;

architecture FULL of PCIE_MFB2AXICQ is

    signal s_rx_mfb_dst_rdy       : std_logic;
    signal s_rx_mfb_data_arr      : slv_array_t(2-1 downto 0)(256-1 downto 0);
    signal s_rx_mfb_eof_pos_arr   : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal s_rx_mfb_bar_range_arr : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal s_rx_mfb_region_vld    : std_logic_vector(1 downto 0);
    signal s_inc_pkt              : std_logic_vector(2 downto 0);

    signal s_fifoxm_din_arr  : slv_array_t(2-1 downto 0)(256+3+3+1+1-1 downto 0);
    signal s_fifoxm_din      : std_logic_vector(2*(256+3+3+1+1)-1 downto 0);
    signal s_fifoxm_full     : std_logic;
    signal s_fifoxm_afull    : std_logic;
    signal s_fifoxm_wr       : std_logic_vector(1 downto 0);
    signal s_fifoxm_dout     : std_logic_vector(2*(256+3+3+1+1)-1 downto 0);
    signal s_fifoxm_rd       : std_logic_vector(1 downto 0);
    signal s_fifoxm_empty    : std_logic_vector(1 downto 0);
    signal s_fifoxm_dout_arr : slv_array_t(2-1 downto 0)(256+3+3+1+1-1 downto 0);

    signal s_fifoxm_mfb_region_vld : std_logic_vector(1 downto 0);
    signal s_fifoxm_mfb_data       : slv_array_t(2-1 downto 0)(256-1 downto 0);
    signal s_fifoxm_mfb_sof        : std_logic_vector(1 downto 0);
    signal s_fifoxm_mfb_eof        : std_logic_vector(1 downto 0);
    signal s_fifoxm_mfb_eof_pos    : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal s_fifoxm_mfb_bar_range  : slv_array_t(2-1 downto 0)(3-1 downto 0);

    signal s_flag_two_packets   : std_logic;
    signal s_flag_word_no_ready : std_logic;

    signal s_destr_mfb_data      : std_logic_vector(511 downto 0);
    signal s_destr_mfb_eof_pos   : std_logic_vector(4-1 downto 0);
    signal s_destr_mfb_bar_range : std_logic_vector(3-1 downto 0);
    signal s_destr_mfb_sof       : std_logic;
    signal s_destr_mfb_eof       : std_logic;
    signal s_destr_mfb_src_rdy   : std_logic;

    signal s_reg_mfb_data      : std_logic_vector(511 downto 0);
    signal s_reg_mfb_eof_pos   : std_logic_vector(4-1 downto 0);
    signal s_reg_mfb_bar_range : std_logic_vector(3-1 downto 0);
    signal s_reg_mfb_sof       : std_logic;
    signal s_reg_mfb_eof       : std_logic;
    signal s_reg_mfb_src_rdy   : std_logic;

    signal s_mfb_data_parr  : slv_array_t(512/32 downto 0)(32-1 downto 0);
    signal s_is_3dw_header  : std_logic;
    signal s_last_dw_is_eof : std_logic;
    signal s_shift_en       : std_logic_vector(512/32-1 downto 0);

    type t_fsm_state is (idle,shifted_pkt,new_word);
    signal s_fsm_pst : t_fsm_state;
    signal s_fsm_nst : t_fsm_state;

    signal s_sh_mfb_data      : std_logic_vector(511 downto 0);
    signal s_sh_mfb_eof_pos   : std_logic_vector(4-1 downto 0);
    signal s_sh_mfb_bar_range : std_logic_vector(3-1 downto 0);
    signal s_sh_mfb_sof       : std_logic;
    signal s_sh_mfb_eof       : std_logic;
    signal s_sh_mfb_src_rdy   : std_logic;
    signal s_sh_mfb_dst_rdy   : std_logic;

    signal s_reg1_mfb_data      : std_logic_vector(511 downto 0);
    signal s_reg1_mfb_eof_pos   : std_logic_vector(4-1 downto 0);
    signal s_reg1_mfb_bar_range : std_logic_vector(3-1 downto 0);
    signal s_reg1_mfb_sof       : std_logic;
    signal s_reg1_mfb_eof       : std_logic;
    signal s_reg1_mfb_src_rdy   : std_logic;

    signal s_mfb_dst_rdy    : std_logic;
    signal s_tpl_mem_wr_req : std_logic;

    signal s_axi_cq_addr32 : std_logic_vector(61 downto 0);
    signal s_axi_cq_addr64 : std_logic_vector(61 downto 0);
    signal s_axi_cq_addr   : std_logic_vector(61 downto 0);
    signal s_axi_cq_type   : std_logic_vector(3 downto 0);
    signal s_axi_cq_data   : std_logic_vector(512-1 downto 0);
    signal s_axi_cq_user   : std_logic_vector(183-1 downto 0);
    signal s_axi_cq_keep   : std_logic_vector(512/32-1 downto 0);
    signal s_axi_cq_last   : std_logic;
    signal s_axi_cq_valid  : std_logic;
    signal s_axi_cq_ready  : std_logic;

begin

    -- =========================================================================
    -- Input MFB buffer and de-straddling
    -- =========================================================================

    RX_MFB_DST_RDY <= s_rx_mfb_dst_rdy;

    rx_fifo_afull_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                RX_FIFO_AFULL <= '0';
            else
                RX_FIFO_AFULL <= s_fifoxm_afull;
            end if;
        end if;
    end process;

    inc_pkt_g : for i in 0 to 1 generate
        s_inc_pkt(i+1) <= (RX_MFB_SOF(i) and not RX_MFB_EOF(i) and not s_inc_pkt(i)) or
            (RX_MFB_SOF(i) and RX_MFB_EOF(i) and s_inc_pkt(i)) or
            (not RX_MFB_SOF(i) and not RX_MFB_EOF(i) and s_inc_pkt(i));
    end generate;

    inc_pkt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_pkt(0) <= '0';
            elsif (RX_MFB_SRC_RDY = '1' and s_rx_mfb_dst_rdy = '1') then
                s_inc_pkt(0) <= s_inc_pkt(2);
            end if;
        end if;
    end process;

    s_rx_mfb_data_arr      <= slv_array_downto_deser(RX_MFB_DATA,2,256);
    s_rx_mfb_eof_pos_arr   <= slv_array_downto_deser(RX_MFB_BAR_RANGE,2,3);
    s_rx_mfb_bar_range_arr <= slv_array_downto_deser(RX_MFB_EOF_POS,2,3);
    s_rx_mfb_region_vld    <= (RX_MFB_SOF or s_inc_pkt(1 downto 0)) and RX_MFB_SRC_RDY;

    fifoxm_din_arr_g : for i in 0 to 1 generate
        s_fifoxm_din_arr(i) <= s_rx_mfb_data_arr(i) & RX_MFB_SOF(i) & RX_MFB_EOF(i) & s_rx_mfb_eof_pos_arr(i) & s_rx_mfb_bar_range_arr(i);
    end generate;

    s_fifoxm_din     <= slv_array_ser(s_fifoxm_din_arr,2,(256+3+3+1+1));
    s_fifoxm_wr      <= s_rx_mfb_region_vld;
    s_rx_mfb_dst_rdy <= not s_fifoxm_full;

    mfb_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH         => 256+3+3+1+1,
        ITEMS              => FIFO_DEPTH,
        RAM_TYPE           => FIFO_RAM_TYPE,
        ALMOST_FULL_OFFSET => FIFO_AFULL_OFFSET+1, -- +1 due to afull register
        DEVICE             => DEVICE,
        WRITE_PORTS        => 2,
        READ_PORTS         => 2,
        SAFE_READ_MODE     => true
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,
        DI     => s_fifoxm_din,
        WR     => s_fifoxm_wr,
        FULL   => s_fifoxm_full,
        AFULL  => s_fifoxm_afull,
        DO     => s_fifoxm_dout,
        RD     => s_fifoxm_rd,
        EMPTY  => s_fifoxm_empty,
        AEMPTY => open
    );

    s_fifoxm_dout_arr <= slv_array_downto_deser(s_fifoxm_dout,2,(256+3+3+1+1));
    s_fifoxm_mfb_region_vld <= not s_fifoxm_empty;

    fifoxm_dout_arr_unpack_g : for i in 0 to 1 generate
        s_fifoxm_mfb_data(i)      <= s_fifoxm_dout_arr(i)(256+8-1 downto 8);
        s_fifoxm_mfb_sof(i)       <= s_fifoxm_dout_arr(i)(7);
        s_fifoxm_mfb_eof(i)       <= s_fifoxm_dout_arr(i)(6);
        s_fifoxm_mfb_eof_pos(i)   <= s_fifoxm_dout_arr(i)(5 downto 3);
        s_fifoxm_mfb_bar_range(i) <= s_fifoxm_dout_arr(i)(2 downto 0);
    end generate;

    -- flag of two packets on FIFOX output
    s_flag_two_packets <= s_fifoxm_mfb_eof(0) and s_fifoxm_mfb_region_vld(0) and s_fifoxm_mfb_sof(1) and s_fifoxm_mfb_region_vld(1);

    -- first SOF in the word is not in first region
    s_flag_word_no_ready <= not s_fifoxm_mfb_region_vld(0) and s_fifoxm_mfb_sof(1) and s_fifoxm_mfb_region_vld(1);

    -- FIFOX read signals
    s_fifoxm_rd(0) <= s_sh_mfb_dst_rdy and not s_flag_word_no_ready;
    s_fifoxm_rd(1) <= s_sh_mfb_dst_rdy and not s_flag_two_packets and not s_flag_word_no_ready;

    -- de-straddled MFB word (only one packet per word)
    s_destr_mfb_data      <= s_fifoxm_mfb_data(1) & s_fifoxm_mfb_data(0);
    s_destr_mfb_eof_pos   <= ('0' & s_fifoxm_mfb_eof_pos(0)) when (s_fifoxm_mfb_eof(0) = '1') else ('1' & s_fifoxm_mfb_eof_pos(1));
    s_destr_mfb_bar_range <= s_fifoxm_mfb_bar_range(0);
    s_destr_mfb_sof       <= or s_fifoxm_mfb_sof;
    s_destr_mfb_eof       <= or s_fifoxm_mfb_eof;
    s_destr_mfb_src_rdy   <= (or s_fifoxm_mfb_region_vld) and not s_flag_word_no_ready;

    -- registers of de-straddled MFB word
    reg_mfb_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_sh_mfb_dst_rdy = '1') then
                s_reg_mfb_data      <= s_destr_mfb_data;
                s_reg_mfb_eof_pos   <= s_destr_mfb_eof_pos;
                s_reg_mfb_bar_range <= s_destr_mfb_bar_range;
                s_reg_mfb_sof       <= s_destr_mfb_sof;
                s_reg_mfb_eof       <= s_destr_mfb_eof;
            end if;
        end if;
    end process;

    reg_mfb_src_rdy_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_mfb_src_rdy <= '0';
            elsif (s_sh_mfb_dst_rdy = '1') then
                s_reg_mfb_src_rdy <= s_destr_mfb_src_rdy;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- RESIZE 3DW HEADERS TO 4DW
    -- =========================================================================

    s_sh_mfb_bar_range <= s_reg_mfb_bar_range;

    data_shifted_g: for i in 0 to (512/32)-1 generate
        s_mfb_data_parr(i+1) <= s_reg_mfb_data((i+1)*32-1 downto i*32);
        s_sh_mfb_data((i+1)*32-1 downto i*32) <= s_mfb_data_parr(i) when (s_shift_en(i) = '1') else s_mfb_data_parr(i+1);
    end generate;

    mfb_data_parr0_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_mfb_dst_rdy = '1' and s_reg_mfb_src_rdy = '1') then
                s_mfb_data_parr(0) <= s_mfb_data_parr(512/32);
            end if;
        end if;
    end process;

    s_is_3dw_header  <= not s_reg_mfb_data(29) and s_reg_mfb_sof and s_reg_mfb_src_rdy;
    s_last_dw_is_eof <= and s_reg_mfb_eof_pos;

    fsm_reg_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_fsm_pst <= idle;
            elsif (s_mfb_dst_rdy = '1') then
                s_fsm_pst <= s_fsm_nst;
            end if;
        end if;
    end process;

    fsm_logic_p: process (all)
    begin
        case s_fsm_pst is
            when idle =>
                s_shift_en       <= (others => '0');
                s_sh_mfb_sof     <= s_reg_mfb_sof;
                s_sh_mfb_eof     <= s_reg_mfb_eof;
                s_sh_mfb_eof_pos <= s_reg_mfb_eof_pos;
                s_sh_mfb_src_rdy <= s_reg_mfb_src_rdy;
                s_sh_mfb_dst_rdy <= s_mfb_dst_rdy;

                if (s_is_3dw_header = '1') then
                    s_shift_en <= "1111111111111000";
                end if;

                if (s_is_3dw_header = '1' and s_reg_mfb_eof = '0') then
                    s_fsm_nst <= shifted_pkt;
                elsif (s_is_3dw_header = '1' and s_reg_mfb_eof = '1') then
                    if (s_last_dw_is_eof = '1') then
                        s_sh_mfb_eof <= '0';
                        s_fsm_nst <= new_word;
                    else
                        s_sh_mfb_eof_pos <= std_logic_vector(unsigned(s_reg_mfb_eof_pos) + 1);
                        s_fsm_nst <= idle;
                    end if;
                else
                    s_fsm_nst <= idle;
                end if;

            when shifted_pkt =>
                s_shift_en       <= (others => '1');
                s_sh_mfb_sof     <= '0';
                s_sh_mfb_eof     <= s_reg_mfb_eof;
                s_sh_mfb_eof_pos <= std_logic_vector(unsigned(s_reg_mfb_eof_pos) + 1);
                s_sh_mfb_src_rdy <= s_reg_mfb_src_rdy;
                s_sh_mfb_dst_rdy <= s_mfb_dst_rdy;

                if (s_reg_mfb_eof = '1' and s_reg_mfb_src_rdy = '1') then
                    if (s_last_dw_is_eof = '1') then
                        s_sh_mfb_eof <= '0';
                        s_fsm_nst <= new_word;
                    else
                        s_fsm_nst <= idle;
                    end if;
                else
                    s_fsm_nst <= shifted_pkt;
                end if;

            when new_word =>
                s_shift_en       <= (others => '0');
                s_sh_mfb_sof     <= '0';
                s_sh_mfb_eof     <= '1';
                s_sh_mfb_eof_pos <= (others => '1');
                s_sh_mfb_src_rdy <= '1';
                s_sh_mfb_dst_rdy <= '0';

                s_fsm_nst <= idle;

            when others => null;
        end case;
    end process;

    -- registers of shifted MFB word
    reg1_avst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_mfb_dst_rdy = '1') then
                s_reg1_mfb_data      <= s_sh_mfb_data;
                s_reg1_mfb_eof_pos   <= s_sh_mfb_eof_pos;
                s_reg1_mfb_bar_range <= s_sh_mfb_bar_range;
                s_reg1_mfb_sof       <= s_sh_mfb_sof;
                s_reg1_mfb_eof       <= s_sh_mfb_eof;
            end if;
        end if;
    end process;

    reg1_avst_vld_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg1_mfb_src_rdy <= '0';
            elsif (s_mfb_dst_rdy = '1') then
                s_reg1_mfb_src_rdy <= s_sh_mfb_src_rdy;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Convert MFB stream to AXI CQ output stream
    -- =========================================================================

    s_axi_cq_addr32 <= std_logic_vector(to_unsigned(0,32)) & s_reg1_mfb_data(95 downto 66);
    s_axi_cq_addr64 <= s_reg1_mfb_data(95 downto 64) & s_reg1_mfb_data(127 downto 98);
    -- 64bit or 32bit address
    s_axi_cq_addr <= s_axi_cq_addr64 when (s_reg1_mfb_data(29) = '1') else s_axi_cq_addr32;

    -- decode AXI PCIe packet type (support only memory R/W now)
    with s_reg1_mfb_data(31 downto 24) select
    s_axi_cq_type <= "0000" when "00000000", -- 32b mem rd
                     "0000" when "00100000", -- 64b mem rd
                     "0001" when "01000000", -- 32b mem wr
                     "0001" when "01100000", -- 64b mem wr
                     "1111" when others;

    with s_reg1_mfb_data(31 downto 24) select
    s_tpl_mem_wr_req <= '1' when "01000000", -- 32b mem wr
                        '1' when "01100000", -- 64b mem wr
                        '0' when others;

    s_cq_data_p : process (all)
    begin
        if (s_reg1_mfb_sof = '1') then -- header and data
            -- copy Intel header and data
            s_axi_cq_data <= s_reg1_mfb_data;
            -- header modifications (Intel to Xilinx)
            s_axi_cq_data(127) <= '0'; -- reserved bit
            s_axi_cq_data(126 downto 124) <= s_reg1_mfb_data(18) & s_reg1_mfb_data(13 downto 12); -- Attr
            s_axi_cq_data(123 downto 121) <= s_reg1_mfb_data(22 downto 20); -- TC
            s_axi_cq_data(120 downto 115) <= std_logic_vector(to_unsigned(BAR_APERTURE,6)); -- BAR Aperture
            s_axi_cq_data(114 downto 112) <= s_reg1_mfb_bar_range; -- BAR ID
            s_axi_cq_data(111 downto 104) <= (others => '0'); -- target fce/function ID (don't support yet)
            s_axi_cq_data(103 downto 96)  <= s_reg1_mfb_data(47 downto 40); -- tag
            s_axi_cq_data(95 downto 80)   <= s_reg1_mfb_data(63 downto 48); -- req id
            s_axi_cq_data(79) <= '0'; -- reserved bit
            s_axi_cq_data(78 downto 75) <= s_axi_cq_type; -- req type
            s_axi_cq_data(74 downto 64) <= '0' & s_reg1_mfb_data(9 downto 0); -- dword count
            s_axi_cq_data(63 downto 2)  <= s_axi_cq_addr; -- address (every time is 62bits)
            s_axi_cq_data(1 downto 0)   <= s_reg1_mfb_data(11 downto 10); -- AT
        else -- only data
            s_axi_cq_data <= s_reg1_mfb_data;
        end if;
    end process;

    s_cq_user_p : process (s_reg1_mfb_data, s_reg1_mfb_sof, s_tpl_mem_wr_req)
    begin
        -- initial value
        s_axi_cq_user <= (others => '0');
        -- set user values
        s_axi_cq_user(3 downto 0)  <= s_reg1_mfb_data(35 downto 32); -- first BE
        s_axi_cq_user(11 downto 8) <= s_reg1_mfb_data(39 downto 36); -- last BE
        s_axi_cq_user(80)          <= s_reg1_mfb_sof;

        -- TPH values
        s_axi_cq_user(97) <= s_reg1_mfb_data(16); -- cq_user_tph_present (TH)

        if (s_reg1_mfb_data(29) = '1') then -- is 4DW header
            s_axi_cq_user(100 downto 99) <= s_reg1_mfb_data(97 downto 96); -- cq_user_tph_type (PH)
        else
            s_axi_cq_user(100 downto 99) <= s_reg1_mfb_data(65 downto 64); -- cq_user_tph_type (PH)
        end if;

        if (s_tpl_mem_wr_req = '1') then -- is memory write request
            s_axi_cq_user(110 downto 103) <= s_reg1_mfb_data(47 downto 40); -- cq_user_tph_st_tag (ST)
        else
            s_axi_cq_user(110 downto 103) <= s_reg1_mfb_data(39 downto 32); -- cq_user_tph_st_tag (ST)
        end if;
    end process;

    -- keep signal serves as valid for each DWORD of CQ_DATA signal
    s_cq_keep_p : process (s_reg1_mfb_src_rdy, s_reg1_mfb_eof, s_reg1_mfb_eof_pos)
    begin
        if (s_reg1_mfb_src_rdy = '0') then -- no data
            s_axi_cq_keep <= (others => '0');
        elsif (s_reg1_mfb_eof = '1') then -- end of data
            s_axi_cq_keep <= (others => '0');
            for i in 0 to 512/32-1 loop
                s_axi_cq_keep(i) <= '1';
                exit when (i = to_integer(unsigned(s_reg1_mfb_eof_pos)));
            end loop;
        else -- start or middle of data
            s_axi_cq_keep <= (others => '1');
        end if;
    end process;

    s_axi_cq_last  <= s_reg1_mfb_eof;
    s_axi_cq_valid <= s_reg1_mfb_src_rdy;
    s_mfb_dst_rdy  <= TX_AXI_CQ_READY;

    -- =========================================================================
    -- AXI CQ output registers
    -- =========================================================================

    tx_reg_axicq_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_AXI_CQ_READY = '1') then
                TX_AXI_CQ_DATA <= s_axi_cq_data;
                TX_AXI_CQ_USER <= s_axi_cq_user;
                TX_AXI_CQ_LAST <= s_axi_cq_last;
                TX_AXI_CQ_KEEP <= s_axi_cq_keep;
            end if;
        end if;
    end process;

    tx_reg_axicq_vld_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TX_AXI_CQ_VALID <= '0';
            elsif (TX_AXI_CQ_READY = '1') then
                TX_AXI_CQ_VALID <= s_axi_cq_valid;
            end if;
        end if;
    end process;

end architecture;
