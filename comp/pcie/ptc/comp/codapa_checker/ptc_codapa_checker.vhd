-- ptc_codapa_checker.vhd: PTC header data merge - header plan and insert
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PTC_CODAPA_CHECKER is
    generic(
        -- =====================================================================
        -- MVB HEADER BUS CONFIGURATION:
        -- =====================================================================
        -- Supported configuration is only MVB(2,128)
        MVB_ITEMS          : natural := 2;
        MVB_ITEM_WIDTH     : natural := 128;
        -- =====================================================================
        -- OTHER CONFIGURATION:
        -- =====================================================================
        -- Width of PCIe transaction size signal. Set Log2 of maximum supported
        -- PCIe transaction size (HDR + payload) in dwords
        TRANS_SIZE_WIDTH   : natural := 8;
        CODAPA_INC_WIDTH   : integer := 2;
        CODAPA_CNT_WIDTH   : natural := 8;
        DEVICE             : string  := "ULTRASCALE"
    );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK                 : in  std_logic;
        RESET               : in  std_logic;
        -- =======================================================================
        -- INPUT MVB HEADER INTERFACE
        -- =======================================================================
        -- header of PCIe transaction
        RX_MVB_DATA         : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
        RX_MVB_BE           : in  std_logic_vector(MVB_ITEMS*8-1 downto 0);
        -- is PCIe transaction with payload
        RX_MVB_PAYLOAD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- size of transaction payload, valid with RX_MVB_PAYLOAD
        RX_MVB_PAYLOAD_SIZE : in  std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
        -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
        RX_MVB_TYPE         : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- valid of each header of PCIe transaction in MVB word
        RX_MVB_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- MVB word is valid
        RX_MVB_SRC_RDY      : in  std_logic;
        -- MVB destination is ready
        RX_MVB_DST_RDY      : out std_logic;
        -- =======================================================================
        -- INPUT COMPLET DATA PACKET INCREMENT
        -- =======================================================================
        -- increment of complete data packets (are stored in FIFO), valid in each cycle
        RX_CODAPA_INC       : in  std_logic_vector(CODAPA_INC_WIDTH-1 downto 0);
        -- =======================================================================
        -- OUTPUT MVB HEADER INTERFACE
        -- =======================================================================
        -- header of PCIe transaction
        TX_MVB_DATA         : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
        TX_MVB_BE           : out std_logic_vector(MVB_ITEMS*8-1 downto 0);
        -- is PCIe transaction with payload
        TX_MVB_PAYLOAD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- size of transaction payload, valid with RX_MVB_PAYLOAD
        TX_MVB_PAYLOAD_SIZE : out std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
        -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
        TX_MVB_TYPE         : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- valid of each header of PCIe transaction in MVB word
        TX_MVB_VLD          : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- MVB word is valid
        TX_MVB_SRC_RDY      : out std_logic;
        -- MVB destination is ready
        TX_MVB_DST_RDY      : in  std_logic
    );
end entity;

architecture FULL of PTC_CODAPA_CHECKER is

    constant MVB_FIFO_ITEMS    : natural := 32;
    constant CODAPA_INC_DELAY  : natural := 10;
    constant PIPE_W : natural := MVB_ITEMS*(MVB_ITEM_WIDTH+TRANS_SIZE_WIDTH+8+1+1+1);

    signal s_pipe_din                : std_logic_vector(PIPE_W-1 downto 0);
    signal RX_MVB_n_DST_RDY          : std_logic;
    signal s_pipe_dout               : std_logic_vector(PIPE_W-1 downto 0);

    signal s_po_mvb_data             : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_po_mvb_be               : std_logic_vector(MVB_ITEMS*8-1 downto 0);
    signal s_po_mvb_payload          : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_po_mvb_payload_size     : std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
    signal s_po_mvb_type             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_po_mvb_vld              : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_po_mvb_src_rdy          : std_logic;
    signal s_po_mvb_n_src_rdy        : std_logic;
    signal s_po_mvb_dst_rdy          : std_logic;

    signal s_codapa_cnt              : unsigned(CODAPA_CNT_WIDTH-1 downto 0);
    signal s_codapa_inc_reg          : u_array_t(CODAPA_INC_DELAY-1 downto 0)(CODAPA_INC_WIDTH-1 downto 0);
    signal s_codapa_dec_slv          : std_logic_vector(log2(MVB_ITEMS+1)-1 downto 0);
    signal s_codapa_dec              : unsigned(log2(MVB_ITEMS+1)-1 downto 0);
    signal s_codapa_dec_vld          : std_logic;

    signal s_rx_payload_packets_cnt  : unsigned(log2(MVB_ITEMS+1)-1 downto 0);

    signal s_codapa_check_ok         : std_logic;

begin

    s_pipe_din <= RX_MVB_DATA & RX_MVB_BE & RX_MVB_PAYLOAD & RX_MVB_PAYLOAD_SIZE & RX_MVB_TYPE & RX_MVB_VLD;
    RX_MVB_DST_RDY <= not RX_MVB_n_DST_RDY;

    fifox_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => PIPE_W,
        ITEMS               => MVB_FIFO_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0     ,
        ALMOST_EMPTY_OFFSET => 0     ,
        FAKE_FIFO           => false
    ) port map(
        CLK         => CLK,
        RESET       => RESET,
        DI          => s_pipe_din,
        WR          => RX_MVB_SRC_RDY,
        FULL        => RX_MVB_n_DST_RDY,
        DO          => s_pipe_dout,
        EMPTY       => s_po_mvb_n_src_rdy,
        RD          => s_po_mvb_dst_rdy
    );

    s_po_mvb_src_rdy <= not s_po_mvb_n_src_rdy;

    s_po_mvb_data         <= s_pipe_dout(PIPE_W-1 downto MVB_ITEMS*8+MVB_ITEMS*TRANS_SIZE_WIDTH+3*MVB_ITEMS);
    s_po_mvb_be           <= s_pipe_dout(MVB_ITEMS*8+MVB_ITEMS*TRANS_SIZE_WIDTH+3*MVB_ITEMS-1 downto MVB_ITEMS*TRANS_SIZE_WIDTH+3*MVB_ITEMS);
    s_po_mvb_payload      <= s_pipe_dout(MVB_ITEMS*TRANS_SIZE_WIDTH+3*MVB_ITEMS-1 downto MVB_ITEMS*TRANS_SIZE_WIDTH+2*MVB_ITEMS);
    s_po_mvb_payload_size <= s_pipe_dout(MVB_ITEMS*TRANS_SIZE_WIDTH+2*MVB_ITEMS-1 downto 2*MVB_ITEMS);
    s_po_mvb_type         <= s_pipe_dout(2*MVB_ITEMS-1 downto MVB_ITEMS);
    s_po_mvb_vld          <= s_pipe_dout(MVB_ITEMS-1 downto 0);

    ----------------------------------------------------------------------------
    -- COMPLETE DATA PACKET COUNTER
    ----------------------------------------------------------------------------

    rx_codapa_inc_inreg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_codapa_inc_reg <= (others => (others => '0'));
            else
                s_codapa_inc_reg(0) <= unsigned(RX_CODAPA_INC);
                for i in 1 to s_codapa_inc_reg'high loop
                    s_codapa_inc_reg(i) <= s_codapa_inc_reg(i-1);
                end loop;
            end if;
        end if;
    end process;

    codapa_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_codapa_cnt <= (others => '0');
            else
                s_codapa_cnt <= s_codapa_cnt + s_codapa_inc_reg(s_codapa_inc_reg'high) - s_codapa_dec;
            end if;
        end if;
    end process;

    -- count number of valid MVB headers with payload on RX
    rx_mvb_payload_packets_cnt_p : process (s_po_mvb_payload,s_po_mvb_vld)
        variable v_rx_payload_packets_cnt  : unsigned(log2(MVB_ITEMS+1)-1 downto 0);
    begin
        v_rx_payload_packets_cnt := (others => '0');
        for i in 0 to MVB_ITEMS-1 loop
            if (s_po_mvb_vld(i)='1' and s_po_mvb_payload(i)='1') then
                v_rx_payload_packets_cnt := v_rx_payload_packets_cnt+1;
            end if;
        end loop;

        s_rx_payload_packets_cnt <= v_rx_payload_packets_cnt;
    end process;

    s_codapa_dec_vld  <= s_codapa_check_ok and s_po_mvb_src_rdy and s_po_mvb_dst_rdy; -- only actually update if ready for data transfer
    s_codapa_dec      <= s_rx_payload_packets_cnt when (s_codapa_dec_vld='1') else (others => '0');

    s_codapa_check_ok <= '1' when s_codapa_cnt>=s_rx_payload_packets_cnt else '0';

    ----------------------------------------------------------------------------
    -- TX generation
    ----------------------------------------------------------------------------

    s_po_mvb_dst_rdy <= TX_MVB_DST_RDY and s_codapa_check_ok;

    TX_MVB_DATA         <= s_po_mvb_data;
    TX_MVB_BE           <= s_po_mvb_be;
    TX_MVB_PAYLOAD      <= s_po_mvb_payload;
    TX_MVB_PAYLOAD_SIZE <= s_po_mvb_payload_size;
    TX_MVB_TYPE         <= s_po_mvb_type;
    TX_MVB_VLD          <= s_po_mvb_vld;
    TX_MVB_SRC_RDY      <= s_po_mvb_src_rdy and s_codapa_check_ok;

end architecture;
