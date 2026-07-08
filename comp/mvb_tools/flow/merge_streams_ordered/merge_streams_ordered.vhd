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
--
-- .. vhdl:enum:: ARCH
--
--    There are multiple implementations of this component, each has its
--    pros and cons:
--
--    .. vhdl:enumval:: FIFOX
--
--        Under the hood, it uses FIFOX_MULTI as word storage and supports
--        full throughput even from one RX interface. Resource usage is high,
--        but some resources are transferred to BRAMs.
--
--    .. vhdl:enumval:: SHAKEDOWN
--
--       Instead of FIFOX_MULTI, this implementation uses MVB_SHAKEDOWN.
--       It may have little less throughput than FIFOX implementation, but
--       it does not use any BRAMs.
--
--    .. vhdl:enumval:: SIMPLE
--
--       This implementation does NOT support reading multiple items from
--       one RX port in a clock cycle. However, it is useful, when traffic
--       is evenly distributed between RX ports and simillarly, selects are
--       distrbuted evenly too. The biggest advantage is massive resource
--       savings compared to FIFOX and SHAKEDOWN implementation. You can expect
--       5x to 6x resource savings.
entity MVB_MERGE_STREAMS_ORDERED is
    generic (
        -- Number of MVB items
        MVB_ITEMS           : natural := 1;
        -- MVB item width in bits
        MVB_ITEM_WIDTH      : natural := 32;
        -- Number of input MVB streams, must be power of two
        RX_STREAMS          : natural := 4;
        -- Use FIFOX multi instead of shakedown to improve
        -- on efficiency and buffering. Costs more resources.
        -- Deprecated option, use ARCH parameter!
        USE_FIFOX_MULTI     : boolean := true;
        -- Fifox multi items multiplier, should be power of 2.
        -- Defines total capacity of FIFOX MULTI by expression:
        -- `MVB_ITEMS * RX_STREAMS * FIFOX_ITEMS_MULT`.
        -- Ignored when USE_FIFOX_MULTI is false. This value
        -- is also used for fifo depths in SIMPLE implementation.
        FIFOX_ITEMS_MULT    : natural := 4;
        -- Enable shakedown on RX SEL MVB interface.
        -- Can improve throughput by accumulating sparse selects
        -- to dense ones. More effective with FIFOX MULTI enabled.
        SEL_SHAKEDOWN_EN    : boolean := true;
        -- Available options are: "SIMPLE", "FIFOX" and "SHAKEDOWN"
        ARCH                : string := "FIFOX";
        -- FPGA device string
        DEVICE              : string := "AGILEX"
    );
    port (
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

    signal sel_shake_tx_data     : std_logic_vector(TX_ITEMS*SEL_WIDTH-1 downto 0);
    signal sel_shake_tx_data_arr : slv_array_t(TX_ITEMS-1 downto 0)(SEL_WIDTH-1 downto 0);
    signal sel_shake_tx_vld      : std_logic_vector(TX_ITEMS-1 downto 0);
    signal sel_shake_tx_src_rdy  : std_logic;
    signal sel_shake_tx_dst_rdy  : std_logic;

    signal s_collision_mtx      : slv_array_t(RX_STREAMS-1 downto 0)(RX_STREAMS-1 downto 0);
    signal s_item_read          : std_logic_vector(RX_STREAMS-1 downto 0);
    signal s_item_done          : std_logic_vector(RX_STREAMS-1 downto 0);
    signal s_grant              : std_logic_vector(RX_STREAMS-1 downto 0);

    signal s_tx_data            : slv_array_t(TX_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal s_item_buf           : slv_array_t(TX_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal s_tx_vld             : std_logic_vector(TX_ITEMS-1 downto 0);

    signal mvb_fifox_tx_data    : slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal mvb_fifox_tx_src_rdy : std_logic_vector(RX_STREAMS-1 downto 0);
    signal mvb_fifox_tx_dst_rdy : std_logic_vector(RX_STREAMS-1 downto 0);

    signal selected_data        : slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal selected_src_rdy     : std_logic_vector(RX_STREAMS-1 downto 0);
    signal selected_dst_rdy     : slv_array_t(RX_STREAMS-1 downto 0)(RX_STREAMS-1 downto 0);

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
        sel_shake_tx_src_rdy    <= or (sel_shake_tx_vld);
    else generate
        sel_shake_tx_data       <= RX_SEL_IF;
        sel_shake_tx_vld        <= RX_SEL_VLD;
        sel_shake_tx_src_rdy    <= RX_SEL_SRC_RDY;
        RX_SEL_DST_RDY          <= sel_shake_tx_dst_rdy;
    end generate;
    sel_shake_tx_data_arr <= slv_array_deser(sel_shake_tx_data, TX_ITEMS);

    arch_g : if ARCH = "FIFOX" or ARCH = "SHAKEDOWN" generate
        sel_shake_tx_dst_rdy <= (and rx_strm_rdy) and TX_DST_RDY;

        rx_g : for i in 0 to RX_STREAMS - 1 generate
            signal rx_strm_word_rdy : std_logic_vector(TX_ITEMS-1 downto 0);
        begin

            rx_sel_arr(i) <= sel_shake_tx_data;

            vld_g : for x in 0 to TX_ITEMS - 1 generate
                rx_sel_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH) <= std_logic_vector(to_unsigned(x, POS_WIDTH));
                rx_sel_strm_vld(i)(x)                               <= '1' when rx_sel_arr(i)((x+1)*SEL_WIDTH-1 downto x*SEL_WIDTH) = std_logic_vector(to_unsigned(i, SEL_WIDTH)) and sel_shake_tx_vld(x) = '1' and sel_shake_tx_src_rdy = '1' else '0';
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
            rx_strm_rdy(i)   <= and (rx_strm_word_rdy);

            fifox_multi_rd(i) <= rx_sel_strm_pos_vld(i) when (and rx_strm_rdy) = '1' and TX_DST_RDY = '1' else (others => '0');

            process (CLK)
            begin
                if rising_edge(CLK) then
                    if (TX_DST_RDY = '1') then
                        strm_rd_vld(i)  <= rx_sel_strm_pos_vld(i) and (and rx_strm_rdy);
                        strm_rd_data(i) <= fifox_multi_do(i);
                        strm_rd_pos(i)  <= rx_sel_strm_pos(i);
                    end if;

                    if (RESET = '1') then
                        strm_rd_vld(i) <= (others => '0');
                    end if;
                end if;
            end process;

            process (all)
            begin
                strm_rd_data_repos(i) <= slv_array_deser(strm_rd_data(i), TX_ITEMS);
                strm_rd_vld_repos(i)  <= (others => '0');
                for x in 0 to TX_ITEMS-1 loop
                    if (strm_rd_vld(i)(x) = '1') then
                        strm_rd_data_repos(i)(to_integer(unsigned(strm_rd_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH)))) <= strm_rd_data(i)((x+1)*MVB_ITEM_WIDTH-1 downto x*MVB_ITEM_WIDTH);
                        strm_rd_vld_repos(i)(to_integer(unsigned(strm_rd_pos(i)((x+1)*POS_WIDTH-1 downto x*POS_WIDTH))))  <= strm_rd_vld(i)(x);
                    end if;
                end loop;
            end process;

            fifox_multi_g : if USE_FIFOX_MULTI or ARCH = "FIFOX" generate
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
            elsif ARCH = "SHAKEDOWN" generate
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
                    if (strm_rd_vld_repos(strm_i)(it) = '1') then
                        TX_DATA((it+1)*MVB_ITEM_WIDTH-1 downto it*MVB_ITEM_WIDTH) <= strm_rd_data_repos(strm_i)(it);
                        TX_VLD(it)                                                <= '1';
                    end if;
                end loop;
            end loop;
        end process;

        TX_SRC_RDY <= or TX_VLD;
    elsif ARCH = "SIMPLE" generate
    begin
        rx_g : for i in 0 to RX_STREAMS-1 generate
            mvb_fifox_i : entity work.MVB_FIFOX
            generic map (
                ITEMS      => MVB_ITEMS,
                ITEM_WIDTH => MVB_ITEM_WIDTH,
                FIFO_DEPTH => FIFOX_ITEMS_MULT,
                DEVICE     => DEVICE
            ) port map (
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => RX_DATA(i),
                RX_VLD     => "1",
                RX_SRC_RDY => RX_SRC_RDY(i),
                RX_DST_RDY => RX_DST_RDY(i),

                TX_DATA    => mvb_fifox_tx_data(i),
                TX_VLD     => open,
                TX_SRC_RDY => mvb_fifox_tx_src_rdy(i),
                TX_DST_RDY => mvb_fifox_tx_dst_rdy(i)
            );

        end generate;

        -- Collision matrix - whether multiple selects want to read from same fifo
        coll_mtx_row_g : for i in 0 to RX_STREAMS-1 generate
        begin
            coll_mtx_col_g : for j in 0 to RX_STREAMS-1 generate
            begin
                s_collision_mtx(i)(j) <= '1' when sel_shake_tx_data_arr(i) = sel_shake_tx_data_arr(j) and sel_shake_tx_vld(i) = '1' and sel_shake_tx_vld(j) = '1' and s_item_done(j) = '0' and s_item_done(i) = '0' else '0';
            end generate;
        end generate;

        -- When any select on lower position in MVB word wants to read from the same fifo, dont give grant
        s_grant(0) <= '1' when sel_shake_tx_vld(0) = '1' and s_item_done(0) = '0' and sel_shake_tx_src_rdy = '1'  else '0';
        grant_g : for i in 1 to RX_STREAMS-1 generate
        begin
            s_grant(i) <= '0' when or (s_collision_mtx(i)(i-1 downto 0)) = '1' or sel_shake_tx_vld(i) = '0' or sel_shake_tx_src_rdy = '0' or s_item_done(i) = '1' else '1';
        end generate;

        muxes_g : for i in 0 to RX_STREAMS-1 generate
            signal sel : integer := 0;

        begin
            sel                 <= to_integer(unsigned(sel_shake_tx_data_arr(i)));
            selected_data(i)    <= mvb_fifox_tx_data(sel);
            selected_src_rdy(i) <= mvb_fifox_tx_src_rdy(sel);

            -- Read from fifos which have grant
            process (all)
            begin
                selected_dst_rdy(i)      <= (others => '0');
                selected_dst_rdy(i)(sel) <= s_grant(i);
            end process;

            process (all)
                variable dst_rdy : std_logic;
            begin
                dst_rdy := '0';
                for j in 0 to RX_STREAMS-1 loop
                    dst_rdy := dst_rdy or selected_dst_rdy(j)(i);
                end loop;
                mvb_fifox_tx_dst_rdy(i) <= dst_rdy;
            end process;
        end generate;

        item_sent_g : for idx in 0 to RX_STREAMS-1 generate
        begin
            items_sent_p : process (CLK)
            begin
                if rising_edge(CLK) then
                    if (RESET = '1') then
                        s_item_done(idx) <= '0';
                    else
                        if (s_grant(idx) = '1') then
                            s_item_done(idx) <= selected_src_rdy(idx);
                            s_item_buf(idx)  <= selected_data(idx);
                        end if;

                        if (sel_shake_tx_src_rdy = '1' and sel_shake_tx_dst_rdy = '1') then
                            s_item_done(idx) <= '0';
                        end if;
                    end if;
                end if;
            end process;

            -- Bypassing logic to allow for instant read performance
            process (all)
            begin
                s_tx_data(idx)      <= selected_data(idx) when s_grant(idx) = '1' else s_item_buf(idx);
                s_item_read(idx)    <= selected_src_rdy(idx) when s_grant(idx) = '1' else s_item_done(idx);
            end process;
        end generate;

        process (all)
        begin
            if (or (s_item_read xor sel_shake_tx_vld) = '0') then
                -- All items were read
                sel_shake_tx_dst_rdy <= TX_DST_RDY;

                -- And at least one item is present
                if (or (sel_shake_tx_vld) = '1') then
                    TX_SRC_RDY <= '1';
                else
                    TX_SRC_RDY <= '0';
                end if;
            else
                sel_shake_tx_dst_rdy <= '0';
                TX_SRC_RDY           <= '0';
            end if;
        end process;
        TX_DATA <= slv_array_ser(s_tx_data);
        TX_VLD  <= s_item_read;

        assert MVB_ITEMS = 1
            report "[MVB_MERGE_STREAMS_ORDERED] MVB_ITEMS must be 1 for SIMPLE architecture"
            severity failure;

        assert SEL_SHAKEDOWN_EN = false
            report "[MVB_MERGE_STREAMS_ORDERED] SEL_SHAKEDOWN_EN must be false for SIMPLE architecture"
            severity failure;
    end generate;

    assert USE_FIFOX_MULTI = false
        report "[MVB_MERGE_STREAMS_ORDERED] USE_FIFOX_MULTI option is deprecated, use ARCH generic instead"
        severity warning;

end architecture;
