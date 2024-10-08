-- merge_streams_ordered.vhd: Merge multiple MVB streams to single MVB stream with defined order of items
-- Copyright (C) 2024 CESNET
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Merges multiple MVB streams to one big streams in defined order.
-- Order is defined by RX_SEL interface. Each word on this interface
-- tells from which interface next word should be transmitted.
-- Words are transmitted exacly as defined on RX_SEL interface, i.e.
-- when RX_SEL word at position 1 is 2, at position 2 is 3,
-- TX interface will contain word from RX interface 2 at position 1
-- and word from RX interface 3 at position 2.
-- There are no constraints on RX_SEL interface - all selects can
-- be from same RX interface.
entity MVB_MERGE_STREAMS_ORDERED is
    generic(
        -- Number of MVB items
        MVB_ITEMS       : natural := 1;
        -- MVB item width in bits
        MVB_ITEM_WIDTH  : natural := 32;
        -- Number of input MVB streams, must be power of two
        RX_STREAMS      : natural := 4;
        -- Use FIFOX multi instead of shakedown to improve
        -- on efficiency and buffering. Costs more resources.
        USE_FIFOX_MULTI : boolean := true;
        -- Fifox multi items multiplier, should be power of 2.
        -- Defines total capacity of FIFOX MULTI by expression:
        -- `MVB_ITEMS * RX_STREAMS * FIFOX_ITEMS_MULT`.
        -- Ignored when USE_FIFOX_MULTI is false.
        FIFOX_ITEMS_MULT    : natural := 4;
        -- Enable shakedown on RX SEL MVB interface.
        -- Can improve throughput by accumulating sparse selects
        -- to dense ones. More effective with FIFOX MULTI enabled.
        SEL_SHAKEDOWN_EN    : boolean := true;
        -- FPGA device string
        DEVICE          : string := "AGILEX"
    );
    port(
        -- Clock input
        CLK        : in  std_logic;
        -- Reset input synchronized with CLK
        RESET      : in  std_logic;

        -- RX MVB: data word with MVB items
        RX_DATA    : in  slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- RX MVB: valid of each MVB item
        RX_VLD     : in  slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS-1 downto 0);
        -- RX MVB: source ready
        RX_SRC_RDY : in  std_logic_vector(RX_STREAMS-1 downto 0);
        -- RX MVB: destination ready
        RX_DST_RDY : out std_logic_vector(RX_STREAMS-1 downto 0);

        -- RX SEL MVB: defines from which interface a word should be taken
        RX_SEL_IF       : in  std_logic_vector(RX_STREAMS*MVB_ITEMS*log2(RX_STREAMS)-1 downto 0);
        -- RX SEL MVB: valid of each MVB item
        RX_SEL_VLD      : in  std_logic_vector(RX_STREAMS*MVB_ITEMS-1 downto 0);
        -- RX SEL MVB: source ready
        RX_SEL_SRC_RDY  : in  std_logic;
        -- RX SEL MVB: destination ready
        RX_SEL_DST_RDY  : out std_logic;

        -- TX MVB: data word with MVB items
        TX_DATA    : out std_logic_vector(RX_STREAMS*MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD     : out std_logic_vector(RX_STREAMS*MVB_ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB_MERGE_STREAMS_ORDERED is

    constant TX_ITEMS   : natural := RX_STREAMS*MVB_ITEMS;
    constant SEL_WIDTH  : natural := log2(RX_STREAMS);
    constant POS_WIDTH  : natural := log2(TX_ITEMS);

    constant FIFOX_MULTI_ITEMS  : natural := TX_ITEMS * FIFOX_ITEMS_MULT;

    signal rx_sel_arr           : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*SEL_WIDTH-1 downto 0);
    signal rx_sel_strm_vld      : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);
    signal rx_sel_pos           : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*POS_WIDTH-1 downto 0);

    signal rx_sel_strm_pos      : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*POS_WIDTH-1 downto 0);
    signal rx_sel_strm_pos_vld  : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);
    signal rx_sel_strm_src_rdy  : std_logic_vector(RX_STREAMS - 1 downto 0);
    signal rx_sel_strm_dst_rdy  : std_logic_vector(RX_STREAMS - 1 downto 0);

    signal rx_strm_rdy          : std_logic_vector(RX_STREAMS-1 downto 0);

    signal strm_rd_data         : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal strm_rd_pos          : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*POS_WIDTH-1 downto 0);
    signal strm_rd_vld          : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);
    signal strm_src_rdy         : std_logic;

    signal strm_rd_data_repos   : slv_array_2d_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal strm_rd_vld_repos    : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);

    signal fifox_multi_full     : std_logic_vector(RX_STREAMS - 1 downto 0);
    signal fifox_multi_do       : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal fifox_multi_rd       : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);
    signal fifox_multi_empty    : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);
    signal fifox_multi_src_rdy  : slv_array_t(RX_STREAMS-1 downto 0)(TX_ITEMS-1 downto 0);

    signal sel_shake_tx_data    : std_logic_vector(TX_ITEMS*SEL_WIDTH-1 downto 0);
    signal sel_shake_tx_vld     : std_logic_vector(TX_ITEMS-1 downto 0);
    signal sel_shake_tx_src_rdy : std_logic;
    signal sel_shake_tx_dst_rdy : std_logic;

begin

    sel_shakedown_g : if SEL_SHAKEDOWN_EN generate
        sel_shakedown_i : entity work.MVB_SHAKEDOWN
        generic map (
            RX_ITEMS        => TX_ITEMS,
            TX_ITEMS        => TX_ITEMS,
            ITEM_WIDTH      => SEL_WIDTH,
            SHAKE_PORTS     => 2,
            USE_MUX_IMPL    => false,
            DEVICE          => DEVICE
        ) port map (
            CLK             => CLK,
            RESET           => RESET,

            RX_DATA         => RX_SEL_IF,
            RX_VLD          => RX_SEL_VLD,
            RX_SRC_RDY      => RX_SEL_SRC_RDY,
            RX_DST_RDY      => RX_SEL_DST_RDY,

            TX_DATA         => sel_shake_tx_data,
            TX_VLD          => sel_shake_tx_vld,
            TX_NEXT         => (others => sel_shake_tx_dst_rdy)
        );
        sel_shake_tx_src_rdy <= or (sel_shake_tx_vld);
    else generate
        sel_shake_tx_data       <= RX_SEL_IF;
        sel_shake_tx_vld        <= RX_SEL_VLD;
        sel_shake_tx_src_rdy    <= RX_SEL_SRC_RDY;
        RX_SEL_DST_RDY          <= sel_shake_tx_dst_rdy;
    end generate;


    sel_shake_tx_dst_rdy <= (and rx_strm_rdy) and TX_DST_RDY;

    rx_g : for i in 0 to RX_STREAMS - 1 generate
        signal rx_strm_word_rdy : std_logic_vector(TX_ITEMS-1 downto 0);
    begin

        rx_sel_arr(i) <= sel_shake_tx_data;

        vld_g : for x in 0 to TX_ITEMS - 1 generate
            rx_sel_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH) <= std_logic_vector(to_unsigned(x, POS_WIDTH));
            rx_sel_strm_vld(i)(x) <= '1' when rx_sel_arr(i)((x+1)*SEL_WIDTH-1 downto x*SEL_WIDTH) = std_logic_vector(to_unsigned(i, SEL_WIDTH)) and sel_shake_tx_vld(x) = '1' and sel_shake_tx_src_rdy = '1' else '0';
        end generate;

        sel_shakedown_i : entity work.SHAKEDOWN
        generic map (
            INPUTS      => TX_ITEMS,
            OUTPUTS     => TX_ITEMS,
            DATA_WIDTH  => POS_WIDTH,
            OUTPUT_REG  => false
        ) port map (
            CLK         => CLK,
            RESET       => RESET,

            DIN         => rx_sel_pos(i),
            DIN_VLD     => rx_sel_strm_vld(i),

            DOUT        => rx_sel_strm_pos(i),
            DOUT_VLD    => rx_sel_strm_pos_vld(i)
        );

        -- Word requested => word ready
        rx_strm_word_rdy <= not rx_sel_strm_pos_vld(i) or fifox_multi_src_rdy(i);
        -- All words ready
        rx_strm_rdy(i) <= and (rx_strm_word_rdy);

        fifox_multi_rd(i) <= rx_sel_strm_pos_vld(i) when (and rx_strm_rdy) = '1' and TX_DST_RDY = '1' else (others => '0');

        process (CLK)
        begin
            if rising_edge(CLK) then
                if RESET = '1' then
                    strm_rd_vld(i) <= (others => '0');
                elsif TX_DST_RDY = '1' then
                    strm_rd_vld(i)  <= rx_sel_strm_pos_vld(i) and (and rx_strm_rdy);
                    strm_rd_data(i) <= fifox_multi_do(i);
                    strm_rd_pos(i)  <= rx_sel_strm_pos(i);
                end if;
            end if;
        end process;

        process (all)
        begin
            strm_rd_data_repos(i) <= slv_array_deser(strm_rd_data(i), TX_ITEMS);
            strm_rd_vld_repos(i) <= (others => '0');
            for x in 0 to TX_ITEMS-1 loop
                if strm_rd_vld(i)(x) = '1' then
                    strm_rd_data_repos(i)(to_integer(unsigned(strm_rd_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH)))) <= strm_rd_data(i)((x+1)*MVB_ITEM_WIDTH-1 downto x*MVB_ITEM_WIDTH);
                    strm_rd_vld_repos(i)(to_integer(unsigned(strm_rd_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH)))) <= strm_rd_vld(i)(x);
                end if;
            end loop;
        end process;

        fifox_multi_g : if USE_FIFOX_MULTI generate
            RX_DST_RDY <= not fifox_multi_full;
            fifox_multi_i : entity work.FIFOX_MULTI(FULL)
            generic map (
                DATA_WIDTH      => MVB_ITEM_WIDTH,
                ITEMS           => FIFOX_MULTI_ITEMS,
                WRITE_PORTS     => MVB_ITEMS,
                READ_PORTS      => TX_ITEMS,
                DEVICE          => DEVICE,
                SAFE_READ_MODE  => true
            ) port map (
                CLK             => CLK,
                RESET           => RESET,

                DI              => RX_DATA(i),
                WR              => RX_VLD(i) and RX_SRC_RDY(i),
                FULL            => fifox_multi_full(i),
                AFULL           => open,

                DO              => fifox_multi_do(i),
                RD              => fifox_multi_rd(i),
                EMPTY           => fifox_multi_empty(i),
                AEMPTY          => open
            );
            fifox_multi_src_rdy(i) <= not fifox_multi_empty(i);
        else generate
            mvb_shakedown_i : entity work.MVB_SHAKEDOWN
            generic map (
                RX_ITEMS        => MVB_ITEMS,
                TX_ITEMS        => TX_ITEMS,
                ITEM_WIDTH      => MVB_ITEM_WIDTH,
                SHAKE_PORTS     => 2,
                USE_MUX_IMPL    => false,
                DEVICE          => DEVICE
            ) port map (
                CLK             => CLK,
                RESET           => RESET,

                RX_DATA         => RX_DATA(i),
                RX_VLD          => RX_VLD(i),
                RX_SRC_RDY      => RX_SRC_RDY(i),
                RX_DST_RDY      => RX_DST_RDY(i),

                TX_DATA         => fifox_multi_do(i),
                TX_VLD          => fifox_multi_src_rdy(i),
                TX_NEXT         => fifox_multi_rd(i)
            );
        end generate;
    end generate;

    mvbs_merge_p : process (all)
    begin
        TX_VLD  <= (others => '0');
        TX_DATA <= slv_array_ser(strm_rd_data_repos(0));
        for it in 0 to TX_ITEMS-1 loop
            for strm_i in 0 to RX_STREAMS-1 loop
                if strm_rd_vld_repos(strm_i)(it) = '1' then
                    TX_DATA((it+1)*MVB_ITEM_WIDTH-1 downto it*MVB_ITEM_WIDTH) <= strm_rd_data_repos(strm_i)(it);
                    TX_VLD(it) <= '1';
                end if;
            end loop;
        end loop;
    end process;

    TX_SRC_RDY <= or TX_VLD;
end architecture;
