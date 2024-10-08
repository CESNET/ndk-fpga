-- axi2_avmm_ddr_bridge.vhd: AXI-AVMM interface bridge unit
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXI2AVMM_BRIDGE is
    generic(
        AMM_BURST_COUNT_WIDTH : natural := 8;
        AMM_ADDR_WIDTH        : natural := 26;
        AMM_DATA_WIDTH        : natural := 512;
        AXI_ADDR_WIDTH        : natural := 32;
        AXI_DATA_WIDTH        : natural := 512;
        AXI_ID_WIDTH          : natural := 4;
        AXI_BURST_WIDTH       : natural := 2;
        AXI_SIZE_WIDTH        : natural := 3;
        AXI_RESP_WIDTH        : natural := 2;
        AXI_LEN_WIDTH         : natural := 8
    );
    port(
        MEM_CLK                 : in std_logic;
        MEM_RST                 : in std_logic;

        ----Avalon interface----
        AMM_ADDRESS             : in  std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
        AMM_BURST_COUNT         : in  std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
        AMM_WRITE_DATA          : in  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
        AMM_WRITE               : in  std_logic := '0';
        AMM_READ                : in  std_logic;
        AMM_READY               : out std_logic;

        AMM_READ_DATA           : out std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
        AMM_READ_DATA_VALID     : out std_logic;

        ----Xilinx interface----
        --Address Write Channel
        DDR_S_AXI_AWID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_AWADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0) := (others => '0');
        DDR_S_AXI_AWLEN         : out std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
        DDR_S_AXI_AWSIZE        : out std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
        DDR_S_AXI_AWBURST       : out std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
        DDR_S_AXI_AWVALID       : out std_logic;
        DDR_S_AXI_AWREADY       : in  std_logic;
        -- Write Channel
        DDR_S_AXI_WDATA         : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        DDR_S_AXI_WSTRB         : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        DDR_S_AXI_WLAST         : out std_logic;
        DDR_S_AXI_WVALID        : out std_logic;
        DDR_S_AXI_WREADY        : in  std_logic;
        -- Write response Channel
        DDR_S_AXI_BREADY        : out std_logic;
        DDR_S_AXI_BID           : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_BRESP         : in  std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
        DDR_S_AXI_BVALID        : in  std_logic;
        --Address Read Channel
        DDR_S_AXI_ARID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_ARADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0) := (others => '0');
        DDR_S_AXI_ARLEN         : out std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
        DDR_S_AXI_ARSIZE        : out std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
        DDR_S_AXI_ARBURST       : out std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
        DDR_S_AXI_ARVALID       : out std_logic;
        DDR_S_AXI_ARREADY       : in  std_logic;
        -- Read Channel
        DDR_S_AXI_RREADY        : out std_logic;
        DDR_S_AXI_RVALID        : in  std_logic;
        DDR_S_AXI_RLAST         : in  std_logic;
        DDR_S_AXI_RRESP         : in  std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
        DDR_S_AXI_RID           : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_RDATA         : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of AXI2AVMM_BRIDGE is

    --FSM declaration
    type t_fsm_ddr is (
        st_idle,
        st_write_single_word,
        st_waddr,
        st_write,
        st_read
    );

    -- Control logic (FSM)
    signal state, next_state: t_fsm_ddr := st_idle;

    -- Transactions in burst
    signal word_cnt_d : unsigned(AMM_BURST_COUNT_WIDTH -1 downto 0);
    signal word_cnt_q : unsigned(AMM_BURST_COUNT_WIDTH -1 downto 0);

begin
    -- Specific for Data bus width 512 bits
    -- Address is cut by log2(Bytes in transfer) ... in our case by 6 bits (31 downto 6)
    DDR_S_AXI_AWSIZE    <= std_logic_vector(to_unsigned(log2(AMM_DATA_WIDTH/8), AXI_SIZE_WIDTH));
    DDR_S_AXI_ARSIZE    <= std_logic_vector(to_unsigned(log2(AMM_DATA_WIDTH/8), AXI_SIZE_WIDTH));

    -- Byte enable: all bytes in transaction are enabled
    DDR_S_AXI_WSTRB     <= (others => '1');

    -- Number of transaction in one burst
    -- Avalon is giving exact number
    DDR_S_AXI_AWLEN     <= std_logic_vector(resize((unsigned(AMM_BURST_COUNT) - 1), AXI_LEN_WIDTH));
    DDR_S_AXI_ARLEN     <= std_logic_vector(resize((unsigned(AMM_BURST_COUNT) - 1), AXI_LEN_WIDTH));

    -- The data transfer for a sequence of read transactions with the same AxID value must be returned in the order
    -- in which the master issued the addresses
    DDR_S_AXI_AWID      <= (others => '0');
    DDR_S_AXI_ARID      <= (others => '0');

    --TODO:
    --Transactions from the same master, but with different ID values, have no ordering restrictions. They can complete in any order.
    --This can improve system performance, because it enables parallel processing of transactions.

    -- Burst type: INCR (Incrementing base address with each transaction)
    DDR_S_AXI_AWBURST   <= "01";
    DDR_S_AXI_ARBURST   <= "01";

    mem_p: process (all)
    begin
        if rising_edge(MEM_CLK) then
            if MEM_RST = '1' then
                state           <= st_idle;
                word_cnt_q      <= (others => '0');
            else
                state           <= next_state;
                word_cnt_q      <= word_cnt_d;
            end if;
        end if;
    end process;

    fsm_p: process(all)
    begin
        next_state          <= state;
        word_cnt_d          <= word_cnt_q;
        AMM_READY           <= '1';
        DDR_S_AXI_RREADY    <= '0';
        DDR_S_AXI_WVALID    <= '0';
        DDR_S_AXI_ARVALID   <= '0';
        DDR_S_AXI_AWVALID   <= '0';
        DDR_S_AXI_WLAST     <= '0';

        case(state) is
            when st_idle        =>
                word_cnt_d          <= (others => '0');

                if AMM_WRITE = '1' then
                    AMM_READY   <= '0';
                    next_state  <= st_waddr;
                    -- One transaction in burst:
                    if unsigned(AMM_BURST_COUNT) = 1 then
                        next_state  <= st_write_single_word;
                    end if;
                end if;

                if AMM_READ = '1' then
                    DDR_S_AXI_ARVALID   <= '1';
                    if DDR_S_AXI_ARREADY = '1' then
                        next_state          <= st_read;
                    end if;
                end if;

            when st_write_single_word =>
                if (AMM_WRITE = '1') and (unsigned(AMM_BURST_COUNT) = 1) then
                    AMM_READY           <= '0';
                    DDR_S_AXI_AWVALID   <= '1';
                    DDR_S_AXI_WVALID    <= '1';
                    if DDR_S_AXI_WREADY = '1' then
                        AMM_READY   <= '1';
                        next_state  <= st_write_single_word;
                    end if;
                else
                    AMM_READY           <= '0';
                    next_state          <= st_idle;
                end if;


            when st_waddr       =>
                if AMM_WRITE = '1' then
                    -- This state is sending first transaction in burst
                    AMM_READY           <= '0';
                    DDR_S_AXI_AWVALID   <= '1';
                    -- A deadlock condition can occur if the slave is waiting for WVALID before asserting AWREADY.
                    DDR_S_AXI_WVALID    <= '1';
                    if DDR_S_AXI_AWREADY = '1' then
                        AMM_READY           <= '1';
                        word_cnt_d          <= word_cnt_q + 1;
                        next_state          <= st_write;
                    end if;
                else
                    AMM_READY           <= '0';
                    next_state          <= st_idle;
                end if;

            when st_write       =>
                DDR_S_AXI_WVALID    <= '1';
                word_cnt_d          <= word_cnt_q + 1;

                if word_cnt_q = unsigned(AMM_BURST_COUNT) - 1  then
                    DDR_S_AXI_WLAST     <= '1';
                    word_cnt_d          <= (others => '0');
                    next_state          <= st_waddr;
                end if;

                if DDR_S_AXI_WREADY = '0' then
                    AMM_READY           <= '0';
                    DDR_S_AXI_WLAST     <= '0';
                    word_cnt_d          <= word_cnt_q;
                    next_state          <= st_write;
                end if;

            when st_read        =>
                AMM_READY           <= '0';
                DDR_S_AXI_RREADY    <= '1';
                word_cnt_d          <= word_cnt_q + 1;

                -- Reading last transaction in burst
                if word_cnt_q = unsigned(AMM_BURST_COUNT) - 1  then
                    next_state          <= st_idle;
                end if;

                if DDR_S_AXI_RVALID = '0' then
                    word_cnt_d          <= word_cnt_q;
                    next_state          <= st_read;
                end if;

            when others         =>
                AMM_READY   <= '0';
                next_state  <= st_idle;

        end case;
    end process;

    --Write address
    DDR_S_AXI_AWADDR((AMM_ADDR_WIDTH+log2(AMM_DATA_WIDTH/8))-1 downto log2(AMM_DATA_WIDTH/8)) <= AMM_ADDRESS;

    --Write data
    DDR_S_AXI_WDATA                 <= AMM_WRITE_DATA;

    --Response
    DDR_S_AXI_BREADY                <= '1';

    --Read address
    DDR_S_AXI_ARADDR((AMM_ADDR_WIDTH+log2(AMM_DATA_WIDTH/8))-1 downto log2(AMM_DATA_WIDTH/8)) <= AMM_ADDRESS;

    --Read data
    AMM_READ_DATA_VALID             <= DDR_S_AXI_RVALID;
    AMM_READ_DATA                   <= DDR_S_AXI_RDATA;

end architecture;
