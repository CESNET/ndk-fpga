-- mvb_serializer.vhd: N-MVB to 1-MVB convertor
-- Copyright (C) 2026 Dynanic Semiconductors Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MVB_SERIALIZER converts a wide, multi-item parallel MVB stream into
-- a continuous single-item serial stream.
-- It uses a combinational priority encoder to dynamically route the
-- lowest-indexed valid item to the output
entity MVB_SERIALIZER is
    generic (
        -- Number of MVB items, any positive
        ITEMS       : natural := 4;
        -- MVB item width
        ITEM_WIDTH  : natural := 256;
        -- MVB META width, any positive
        META_WIDTH  : natural := 64
    );
    port (
        CLK : in std_logic;
        RST : in std_logic;

        RX_MVB_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH - 1 downto 0);
        RX_MVB_META     : in  std_logic_vector(ITEMS*META_WIDTH - 1 downto 0) := (others => '0');
        RX_MVB_VLD      : in  std_logic_vector(ITEMS            - 1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        TX_MVB_DATA     : out std_logic_vector(ITEM_WIDTH - 1 downto 0);
        TX_MVB_META     : out std_logic_vector(META_WIDTH - 1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(1          - 1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of MVB_SERIALIZER is
    signal rx_data_arr    : slv_array_t(ITEMS - 1 downto 0)(ITEM_WIDTH - 1 downto 0);
    signal rx_meta_arr    : slv_array_t(ITEMS - 1 downto 0)(META_WIDTH - 1 downto 0);
    signal buf_data       : slv_array_t(ITEMS - 1 downto 0)(ITEM_WIDTH - 1 downto 0);
    signal buf_meta       : slv_array_t(ITEMS - 1 downto 0)(META_WIDTH - 1 downto 0);
    signal buf_vld        : std_logic_vector(ITEMS - 1 downto 0);

    signal rx_dst_rdy_s   : std_logic;
    signal tx_src_rdy_s   : std_logic;

    signal input_valid    : unsigned(max(1, log2(ITEMS)) - 1 downto 0);

begin

    rx_data_arr     <= slv_array_deser(RX_MVB_DATA, ITEMS);
    rx_meta_arr     <= slv_array_deser(RX_MVB_META, ITEMS);
    RX_MVB_DST_RDY  <= rx_dst_rdy_s;

    -- Output MUX
    TX_MVB_DATA     <= buf_data(to_integer(input_valid));
    TX_MVB_META     <= buf_meta(to_integer(input_valid));
    TX_MVB_VLD(0)   <= tx_src_rdy_s;
    TX_MVB_SRC_RDY  <= tx_src_rdy_s;

    -- -------------------------------------------------------------------------
    -- Priority Encoder: Find the lowest index with a valid item
    -- -------------------------------------------------------------------------
    find_vld_p : process (all)
        variable input_valid_v  : unsigned(max(1, log2(ITEMS)) - 1 downto 0);
        variable any_vld_tmp    : std_logic;
    begin
        input_valid_v := (others => '0');
        any_vld_tmp   := '0';

        for i in 0 to ITEMS-1 loop
            if (buf_vld(i) = '1') then
                input_valid_v := to_unsigned(i, input_valid_v'length);
                any_vld_tmp   := '1';
                exit;
            end if;
        end loop;
        tx_src_rdy_s   <= any_vld_tmp;
        input_valid    <= input_valid_v;
    end process;

    -- -------------------------------------------------------------------------
    -- Synchronous Buffer Update: Buffer management
    -- -------------------------------------------------------------------------
    update_buffer_p : process (all)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                buf_vld <= (others => '0');
            else
                -- If we are ready to receive and the source sends data
                if ((rx_dst_rdy_s = '1') and (RX_MVB_SRC_RDY = '1')) then
                    buf_data <= rx_data_arr;
                    buf_meta <= rx_meta_arr;
                    buf_vld  <= RX_MVB_VLD;

                -- If we are merely transmitting out of the current buffer
                elsif ((tx_src_rdy_s = '1') and (TX_MVB_DST_RDY = '1')) then
                    buf_vld(to_integer(input_valid)) <= '0';
                end if;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    -- Backpressure Logic (RX_DST_RDY)
    -- We can accept new data if the buffer is empty, OR
    -- if it has exactly 1 item left and it's being transmitted this cycle.
    -- -------------------------------------------------------------------------
    backpressure_p : process (all)
        variable any_vld      : std_logic;
        variable multiple_vld : std_logic;
    begin
        any_vld      := '0';
        multiple_vld := '0';

        -- Parallel OR-check to avoid generating an adder tree on the FPGA
        for i in 0 to ITEMS-1 loop
            if (buf_vld(i) = '1') then
                if (any_vld = '1') then
                    multiple_vld := '1';
                else
                    any_vld := '1';
                end if;
            end if;
        end loop;

        if (any_vld = '0') then
            rx_dst_rdy_s <= '1';
        elsif ((any_vld = '1') and (multiple_vld = '0') and (TX_MVB_DST_RDY = '1')) then
            rx_dst_rdy_s <= '1';
        else
            rx_dst_rdy_s <= '0';
        end if;
    end process;

end architecture;
