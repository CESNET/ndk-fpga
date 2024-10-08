-- merge_items.vhd: Merge MVB items from two streams to single MVB item
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This MVB_MERGE_ITEMS component allows to merge two different MVB streams by
-- merging items from both streams into one item. Both input MVB streams must
-- receive the same number of items in the same order, but they can be aligned
-- differently. TX MVB has same item aligment as RX0 MVB input.
entity MVB_MERGE_ITEMS is
    generic(
        -- Number of RX0 items, same for output (TX)
        RX0_ITEMS      : natural := 4;
        -- RX0 item width in bits
        RX0_ITEM_WIDTH : natural := 32;
        -- Number of RX1 items
        RX1_ITEMS      : natural := 4;
        -- RX1 item width in bits
        RX1_ITEM_WIDTH : natural := 16;
        -- TX item width in bits (must be sum of RX0 and RX1)
        TX_ITEM_WIDTH  : natural := RX0_ITEM_WIDTH+RX1_ITEM_WIDTH;
        -- Enable of FIFOX on RX0 input
        RX0_FIFO_EN    : boolean := False;
        -- Depth of FIFOs on inputs
        FIFO_DEPTH     : natural := 32;
        -- Enable output register on TX MVB
        OUTPUT_REG     : boolean := False;
        -- FPGA device string (required for FIFOs)
        DEVICE         : string := "STRATIX10"
    );
    port(
        -- Clock input
        CLK         : in  std_logic;
        -- Reset input synchronized with CLK
        RESET       : in  std_logic;

        -- RX0 MVB: data word with MVB items
        RX0_DATA    : in  std_logic_vector(RX0_ITEMS*RX0_ITEM_WIDTH-1 downto 0);
        -- RX0 MVB: valid of each MVB item
        RX0_VLD     : in  std_logic_vector(RX0_ITEMS-1 downto 0);
        -- RX0 MVB: source ready
        RX0_SRC_RDY : in  std_logic;
        -- RX0 MVB: destination ready
        RX0_DST_RDY : out std_logic;

        -- RX1 MVB: data word with MVB items
        RX1_DATA    : in  std_logic_vector(RX1_ITEMS*RX1_ITEM_WIDTH-1 downto 0);
        -- RX1 MVB: valid of each MVB item
        RX1_VLD     : in  std_logic_vector(RX1_ITEMS-1 downto 0);
        -- RX1 MVB: source ready
        RX1_SRC_RDY : in  std_logic;
        -- RX1 MVB: destination ready
        RX1_DST_RDY : out std_logic;

        -- TX MVB: Data word from both inputs (concatenated)
        TX_DATA     : out std_logic_vector(RX0_ITEMS*TX_ITEM_WIDTH-1 downto 0);
        -- TX MVB: Data word from RX0 input
        TX_DATA0    : out std_logic_vector(RX0_ITEMS*RX0_ITEM_WIDTH-1 downto 0);
        -- TX MVB: Data word from RX1 input
        TX_DATA1    : out std_logic_vector(RX0_ITEMS*RX1_ITEM_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD      : out std_logic_vector(RX0_ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY  : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of MVB_MERGE_ITEMS is

    signal fifo_rx0_data    : std_logic_vector(RX0_ITEMS*RX0_ITEM_WIDTH-1 downto 0);
    signal fifo_rx0_vld     : std_logic_vector(RX0_ITEMS-1 downto 0);
    signal fifo_rx0_src_rdy : std_logic;
    signal fifo_rx0_dst_rdy : std_logic;

    signal fifoxm_wr        : std_logic_vector(RX1_ITEMS-1 downto 0);
    signal fifoxm_full      : std_logic;
    signal fifoxm_do        : std_logic_vector(RX0_ITEMS*RX1_ITEM_WIDTH-1 downto 0);
    signal fifoxm_do_arr    : slv_array_t(RX0_ITEMS-1 downto 0)(RX1_ITEM_WIDTH-1 downto 0);
    signal fifoxm_rd        : std_logic_vector(RX0_ITEMS-1 downto 0);
    signal fifoxm_empty     : std_logic_vector(RX0_ITEMS-1 downto 0);

    signal demux_sel        : u_array_t(RX0_ITEMS-1 downto 0)(log2(RX0_ITEMS)-1 downto 0);
    signal must_wait        : std_logic;
    signal rd_vector        : std_logic_vector(RX0_ITEMS-1 downto 0);
    signal rx0_data_arr     : slv_array_t(RX0_ITEMS-1 downto 0)(RX0_ITEM_WIDTH-1 downto 0);
    signal tx_data1_arr     : slv_array_t(RX0_ITEMS-1 downto 0)(RX1_ITEM_WIDTH-1 downto 0);
    signal tx_data_arr      : slv_array_t(RX0_ITEMS-1 downto 0)(TX_ITEM_WIDTH-1 downto 0);

begin

    rx0_fifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS      => RX0_ITEMS,
        ITEM_WIDTH => RX0_ITEM_WIDTH,
        FIFO_DEPTH => FIFO_DEPTH,
        DEVICE     => DEVICE,
        FAKE_FIFO  => not RX0_FIFO_EN
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => RX0_DATA,
        RX_VLD     => RX0_VLD,
        RX_SRC_RDY => RX0_SRC_RDY,
        RX_DST_RDY => RX0_DST_RDY,

        TX_DATA    => fifo_rx0_data,
        TX_VLD     => fifo_rx0_vld,
        TX_SRC_RDY => fifo_rx0_src_rdy,
        TX_DST_RDY => fifo_rx0_dst_rdy
    );

    fifoxm_wr <= RX1_VLD and RX1_SRC_RDY;
    RX1_DST_RDY <= not fifoxm_full;

    fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH     => RX1_ITEM_WIDTH,
        ITEMS          => max(RX0_ITEMS,RX1_ITEMS)*FIFO_DEPTH,
        WRITE_PORTS    => RX1_ITEMS,
        READ_PORTS     => RX0_ITEMS,
        RAM_TYPE       => "AUTO",
        SAFE_READ_MODE => false,
        DEVICE         => DEVICE
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => RX1_DATA,
        WR     => fifoxm_wr,
        FULL   => fifoxm_full,

        DO     => fifoxm_do,
        RD     => fifoxm_rd,
        EMPTY  => fifoxm_empty
    );

    fifoxm_do_arr <= slv_array_deser(fifoxm_do,RX0_ITEMS,RX1_ITEM_WIDTH);

    process (all)
        variable v_vld_count : unsigned(log2(RX0_ITEMS+1)-1 downto 0);
        variable v_emp_count : unsigned(log2(RX0_ITEMS+1)-1 downto 0);
    begin
        v_vld_count := (others => '0');
        v_emp_count := (others => '0');
        demux_sel <= (others => (others => '0'));
        must_wait <= '0';
        rd_vector <= (others => '0');
        for i in 0 to RX0_ITEMS-1 loop
            demux_sel(i) <= resize(v_vld_count,log2(RX0_ITEMS));
            if (fifo_rx0_vld(i) = '1') then
                rd_vector(to_integer(v_vld_count)) <= '1';
                v_vld_count := v_vld_count + 1;
            end if;
            if (fifoxm_empty(i) = '0') then
                v_emp_count := v_emp_count + 1;
            end if;
        end loop;

        if (v_emp_count < v_vld_count) then
            must_wait <= '1';
        end if;
    end process;

    fifoxm_rd <= rd_vector and not must_wait and fifo_rx0_src_rdy and TX_DST_RDY;

    rx0_data_arr <= slv_array_deser(fifo_rx0_data,RX0_ITEMS,RX0_ITEM_WIDTH);
    fifo_rx0_dst_rdy <= TX_DST_RDY and not must_wait;

    tx_data_g : for i in 0 to RX0_ITEMS-1 generate
        tx_data1_arr(i) <= fifoxm_do_arr(to_integer(tsel(log2(RX0_ITEMS) = 0, to_unsigned(0, 1), demux_sel(i))));
        tx_data_arr(i) <= tx_data1_arr(i) & rx0_data_arr(i);
    end generate;

    out_reg_on_g: if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_DST_RDY = '1') then
                    TX_DATA    <= slv_array_ser(tx_data_arr,RX0_ITEMS,TX_ITEM_WIDTH);
                    TX_DATA0   <= fifo_rx0_data;
                    TX_DATA1   <= slv_array_ser(tx_data1_arr,RX0_ITEMS,RX1_ITEM_WIDTH);
                    TX_VLD     <= fifo_rx0_vld;
                    TX_SRC_RDY <= fifo_rx0_src_rdy and not must_wait;
                end if;
                if (RESET = '1') then
                    TX_SRC_RDY <= '0';
                end if;
            end if;
        end process;
    end generate;

    out_reg_off_g: if not OUTPUT_REG generate
        TX_DATA    <= slv_array_ser(tx_data_arr,RX0_ITEMS,TX_ITEM_WIDTH);
        TX_DATA0   <= fifo_rx0_data;
        TX_DATA1   <= slv_array_ser(tx_data1_arr,RX0_ITEMS,RX1_ITEM_WIDTH);
        TX_VLD     <= fifo_rx0_vld;
        TX_SRC_RDY <= fifo_rx0_src_rdy and not must_wait;
    end generate;

end architecture;
