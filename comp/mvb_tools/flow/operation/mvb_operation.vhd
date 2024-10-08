-- mvb_operation.vhd: Multi-Value Bus Operation component
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component enables optional transaction forking and response
-- receiving based on :vhdl:portsignal:`RX_OP_EN`. Optionally forked data are sent
-- to **TX Operation Interface** and responses are received from **RX Operation Interface**.
-- :vhdl:portsignal:`RX_OP_VLD` vector must be same as operation received from
-- :vhdl:portsignal:`TX_OP_VLD` (no shakedown behaviour must be present in operation unit)
-- and responses must not be reordered.
-- When shakedown behaviour of OP unit is required, one can put SHAKEDOWN before **RX Interface**.
--
-- Both received data and responses are then transmitted on **TX Interface**.
--
-- No reordering of transactions is happening in this component. This means, when one
-- item requires operation to be executed, whole word will be blocked and waiting for
-- response. When no item requires execution, the word will leave the component asap.
-- without waiting for response.
--
-- Entity architecture.
--   .. image:: doc/mvb_operation.svg
entity MVB_OPERATION is
    generic (
        -- Number of MVB items in word
        MVB_ITEMS               : natural := 1;
        -- One MVB item width
        ITEM_WIDTH              : natural := 64;

        -- Width of consumable item. When one needs to transmit some data to TX_OP interface
        -- and they are not needed later, some resources in latency FIFO will be saved by sending
        --  it as consumable item.
        CONSUME_ITEM_WIDTH      : natural := 0;

        -- Operation response MVB item width
        RSP_ITEM_WIDTH          : natural := 24;

        -- When set to true, FIFOX will be instantiated to cover
        -- latency of operation
        LATENCY_FIFO_EN         : boolean := false;
        -- Latency FIFO depth, set to, or greater than latency of operation
        -- (eg. when operation is reading from BRAM with output register, set it to > 1)
        LATENCY_FIFO_DEPTH      : natural := 16;
        -- Latency FIFO ram type. Options:
        --
        -- * "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32)
        -- * "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32)
        -- * "URAM"  - effective when ITEMS*FIFO_WIDTH >= 288000
        --   and FIFO_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+))
        -- * "SHIFT" - effective when ITEMS <= 16
        -- * "AUTO"  - effective implementation dependent on ITEMS and DEVICE
        LATENCY_FIFO_RAM_TYPE   : string  := "AUTO";

        -- Enables pipe on RX_OP_RESPONSE interface
        RX_OP_PIPE_EN           : boolean := true;


        -- Defines what architecture is FIFO implemented on Options:
        --
        -- * "ULTRASCALE" (Xilinx)
        -- * "7SERIES"    (Xilinx)
        -- * "ARRIA10"    (Intel)
        -- * "STRATIX10"  (Intel)
        DEVICE                  : string  := "AGILEX"
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- ======================================================
        -- RX Interface
        --
        -- Standard MVB interface
        -- ======================================================
        RX_DATA         : in    std_logic_vector(MVB_ITEMS * ITEM_WIDTH - 1 downto 0);
        -- Data which will be consumed by operation. They are not transmitted to TX interface
        RX_DATA_CONSUME : in    std_logic_vector(MVB_ITEMS * CONSUME_ITEM_WIDTH - 1 downto 0) := (others => '0');
        -- Operation enable for each MVB item
        RX_OP_EN        : in    std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX_VLD          : in    std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX_SRC_RDY      : in    std_logic;
        RX_DST_RDY      : out   std_logic;

        -- ======================================================
        -- TX Operation Interface
        --
        -- Interface to unit executing the operation.
        -- ======================================================
        TX_OP_DATA          : out   std_logic_vector(MVB_ITEMS * ITEM_WIDTH - 1 downto 0);
        TX_OP_DATA_CONSUME  : out   std_logic_vector(MVB_ITEMS * CONSUME_ITEM_WIDTH - 1 downto 0);
        TX_OP_VLD           : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX_OP_SRC_RDY       : out   std_logic;
        TX_OP_DST_RDY       : in    std_logic;

        -- ======================================================
        -- RX Operation Interface
        --
        -- Interface for receiving responses from operation unit.
        -- ======================================================
        RX_OP_RESPONSE  : in    std_logic_vector(MVB_ITEMS * RSP_ITEM_WIDTH - 1 downto 0);
        -- Valid vector must exacly same as received from TX Operation Interface.
        RX_OP_VLD       : in    std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX_OP_SRC_RDY   : in    std_logic;
        RX_OP_DST_RDY   : out   std_logic;

        -- ======================================================
        -- TX Interface
        --
        -- Interface with previously received data and responses.
        -- ======================================================
        -- Data received from *RX Interface*
        TX_DATA         : out   std_logic_vector(MVB_ITEMS * ITEM_WIDTH - 1 downto 0);
        -- Responses from operation unit
        TX_RESPONSE     : out   std_logic_vector(MVB_ITEMS * RSP_ITEM_WIDTH - 1 downto 0);
        -- Response valid, eg. operation was executed on i-th item. This vector is same as
        -- received :vhdl:portsignal:`RX_OP_EN`.
        TX_RESPONSE_VLD : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX_VLD          : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX_SRC_RDY      : out   std_logic;
        TX_DST_RDY      : in    std_logic
    );
end entity;

architecture behavioral of MVB_OPERATION is

    signal rx_data_arr                  : slv_array_t(MVB_ITEMS - 1 downto 0)(ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH - 1 downto 0);

    signal rx_fork_tx_data              : std_logic_vector(2 * MVB_ITEMS * (ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH) - 1 downto 0);
    signal rx_fork_tx_vld               : std_logic_vector(2 * MVB_ITEMS - 1 downto 0);
    signal rx_fork_tx_data_arr          : slv_array_t(2 - 1 downto 0)(MVB_ITEMS * (ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH) - 1 downto 0);
    signal rx_fork_tx_data_data_arr     : slv_array_t(2 - 1 downto 0)(MVB_ITEMS * (ITEM_WIDTH + CONSUME_ITEM_WIDTH) - 1 downto 0);
    signal rx_fork_tx_data_op_en_arr    : slv_array_t(2 - 1 downto 0)(MVB_ITEMS - 1 downto 0);
    signal rx_fork_tx_vld_arr           : slv_array_t(2 - 1 downto 0)(MVB_ITEMS - 1 downto 0);
    signal rx_fork_tx_src_rdy           : std_logic_vector(2 - 1 downto 0);
    signal rx_fork_tx_dst_rdy           : std_logic_vector(2 - 1 downto 0);

    signal rx_op_pipe_tx_data           : std_logic_vector(MVB_ITEMS * RSP_ITEM_WIDTH - 1 downto 0);
    signal rx_op_pipe_tx_vld            : std_logic_vector(MVB_ITEMS - 1 downto 0);
    signal rx_op_pipe_tx_src_rdy        : std_logic;
    signal rx_op_pipe_tx_dst_rdy        : std_logic;

    signal discard_tx_data              : std_logic_vector(MVB_ITEMS * (ITEM_WIDTH + CONSUME_ITEM_WIDTH) - 1 downto 0);
    signal discard_tx_data_arr          : slv_array_t(MVB_ITEMS - 1 downto 0)(ITEM_WIDTH + CONSUME_ITEM_WIDTH - 1 downto 0);

    signal lat_fifox_tx_data            : std_logic_vector(MVB_ITEMS * (ITEM_WIDTH + 1) - 1 downto 0);
    signal lat_fifox_tx_data_arr        : slv_array_t(MVB_ITEMS - 1 downto 0)(ITEM_WIDTH - 1 downto 0);
    signal lat_fifox_tx_data_op_en      : std_logic_vector(MVB_ITEMS - 1 downto 0);
    signal lat_fifox_tx_data_op_sent    : std_logic_vector(MVB_ITEMS - 1 downto 0);
    signal lat_fifox_tx_data_wait_rsp   : std_logic;
    signal lat_fifox_tx_vld             : std_logic_vector(MVB_ITEMS - 1 downto 0);
    signal lat_fifox_tx_src_rdy         : std_logic;
    signal lat_fifox_tx_dst_rdy         : std_logic;

begin

    rx_data_g : for i in 0 to MVB_ITEMS - 1 generate
        rx_data_arr(i)(ITEM_WIDTH - 1 downto 0) <= RX_DATA((i+1) * ITEM_WIDTH - 1 downto i * ITEM_WIDTH);
        rx_data_arr(i)(ITEM_WIDTH) <= RX_OP_EN(i);
        rx_data_arr(i)(ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH - 1 downto ITEM_WIDTH + 1) <= RX_DATA_CONSUME((i+1) * CONSUME_ITEM_WIDTH - 1 downto i * CONSUME_ITEM_WIDTH);
    end generate;

    rx_fork_i : entity work.MVB_FORK
    generic map (
        OUTPUT_PORTS    => 2,
        ITEMS           => MVB_ITEMS,
        ITEM_WIDTH      => ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH,
        VERSION         => "register",
        USE_DST_RDY     => true
    ) port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_DATA         => slv_array_ser(rx_data_arr),
        RX_VLD          => RX_VLD,
        RX_SRC_RDY      => RX_SRC_RDY,
        RX_DST_RDY      => RX_DST_RDY,

        TX_DATA         => rx_fork_tx_data,
        TX_VLD          => rx_fork_tx_vld,
        TX_SRC_RDY      => rx_fork_tx_src_rdy,
        TX_DST_RDY      => rx_fork_tx_dst_rdy
    );

    rx_fork_tx_data_arr <= slv_array_deser(rx_fork_tx_data, 2);
    rx_fork_tx_vld_arr  <= slv_array_deser(rx_fork_tx_vld, 2);

    fork_sig_g : for i in 0 to MVB_ITEMS generate
        rx_fork_tx_data_data_arr(i)     <= rx_fork_tx_data_arr(i)(ITEM_WIDTH + 1 + CONSUME_ITEM_WIDTH - 1 downto ITEM_WIDTH + 1) & rx_fork_tx_data_arr(i)(ITEM_WIDTH - 1 downto 0);
        rx_fork_tx_data_op_en_arr(i)    <= rx_fork_tx_data_arr(i)(ITEM_WIDTH downto ITEM_WIDTH);
    end generate;

    -- ================================= --
    -- Path to operation component
    -- Drop item when operation should not be executed on it
    discard_i : entity work.MVB_DISCARD
    generic map (
        ITEMS       => MVB_ITEMS,
        ITEM_WIDTH  => ITEM_WIDTH + CONSUME_ITEM_WIDTH,
        OUTPUT_REG  => False
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => rx_fork_tx_data_data_arr(1),
        RX_DISCARD  => not rx_fork_tx_data_op_en_arr(1),
        RX_VLD      => rx_fork_tx_vld_arr(1),
        RX_SRC_RDY  => rx_fork_tx_src_rdy(1),
        RX_DST_RDY  => rx_fork_tx_dst_rdy(1),

        TX_DATA     => discard_tx_data,
        TX_VLD      => TX_OP_VLD,
        TX_SRC_RDY  => TX_OP_SRC_RDY,
        TX_DST_RDY  => TX_OP_DST_RDY
    );

    discard_tx_data_arr <= slv_array_deser(discard_tx_data, MVB_ITEMS);
    tx_op_g : for i in 0 to MVB_ITEMS - 1 generate
        TX_OP_DATA((i+1)*ITEM_WIDTH - 1 downto i*ITEM_WIDTH) <= discard_tx_data_arr(i)(ITEM_WIDTH - 1 downto 0);
        TX_OP_DATA_CONSUME((i+1)*CONSUME_ITEM_WIDTH - 1 downto i*CONSUME_ITEM_WIDTH) <= discard_tx_data_arr(i)(ITEM_WIDTH + CONSUME_ITEM_WIDTH - 1 downto ITEM_WIDTH);
    end generate;

    -- =============================== --
    -- Internal hanshake path
    lat_fifox_i : entity work.MVB_FIFOX
    generic map (
        ITEMS       => MVB_ITEMS,
        ITEM_WIDTH  => ITEM_WIDTH + 1,
        FIFO_DEPTH  => LATENCY_FIFO_DEPTH,
        RAM_TYPE    => LATENCY_FIFO_RAM_TYPE,
        DEVICE      => DEVICE,
        FAKE_FIFO   => not LATENCY_FIFO_EN
    ) port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_DATA         => rx_fork_tx_data_arr(0)(ITEM_WIDTH + 1 - 1 downto 0),
        RX_VLD          => rx_fork_tx_vld_arr(0),
        RX_SRC_RDY      => rx_fork_tx_src_rdy(0),
        RX_DST_RDY      => rx_fork_tx_dst_rdy(0),

        TX_DATA         => lat_fifox_tx_data,
        TX_VLD          => lat_fifox_tx_vld,
        TX_SRC_RDY      => lat_fifox_tx_src_rdy,
        TX_DST_RDY      => lat_fifox_tx_dst_rdy,

        STATUS          => open,
        AFULL           => open,
        AEMPTY          => open
    );

    rx_op_pipe_i : entity work.MVB_PIPE
    generic map (
        ITEMS       => MVB_ITEMS,
        ITEM_WIDTH  => RSP_ITEM_WIDTH,
        FAKE_PIPE   => not RX_OP_PIPE_EN,
        DEVICE      => DEVICE
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => RX_OP_RESPONSE,
        RX_VLD      => RX_OP_VLD,
        RX_SRC_RDY  => RX_OP_SRC_RDY,
        RX_DST_RDY  => RX_OP_DST_RDY,

        TX_DATA     => rx_op_pipe_tx_data,
        TX_VLD      => rx_op_pipe_tx_vld,
        TX_SRC_RDY  => rx_op_pipe_tx_src_rdy,
        TX_DST_RDY  => rx_op_pipe_tx_dst_rdy
    );

    lat_data_g : for i in 0 to MVB_ITEMS - 1 generate
        lat_fifox_tx_data_op_en(i) <= lat_fifox_tx_data(i * (ITEM_WIDTH + 1) + ITEM_WIDTH);
    end generate;
    lat_fifox_tx_data_op_sent <= lat_fifox_tx_vld and lat_fifox_tx_data_op_en;
    lat_fifox_tx_data_wait_rsp <= or lat_fifox_tx_data_op_sent;

    -- Optional handshake logic generated from truth table
    lat_fifox_tx_dst_rdy <= ((not lat_fifox_tx_data_wait_rsp) and TX_DST_RDY) or (rx_op_pipe_tx_src_rdy and TX_DST_RDY);
    rx_op_pipe_tx_dst_rdy <= lat_fifox_tx_data_wait_rsp and lat_fifox_tx_src_rdy and TX_DST_RDY;
    TX_SRC_RDY <= ((not lat_fifox_tx_data_wait_rsp) and lat_fifox_tx_src_rdy) or (lat_fifox_tx_src_rdy and rx_op_pipe_tx_src_rdy);

    tx_data_g : for i in 0 to MVB_ITEMS - 1 generate
        TX_DATA((i+1) * ITEM_WIDTH - 1 downto i * ITEM_WIDTH) <= lat_fifox_tx_data(i * (ITEM_WIDTH + 1) + ITEM_WIDTH - 1 downto i * (ITEM_WIDTH + 1));
        TX_RESPONSE_VLD(i) <= lat_fifox_tx_data(i * (ITEM_WIDTH + 1) + ITEM_WIDTH);
        TX_VLD <= lat_fifox_tx_vld;
    end generate;
    TX_RESPONSE <= rx_op_pipe_tx_data;

end architecture;
