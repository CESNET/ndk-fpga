-- axi2avmm_ddr_bridge.vhd: AXI-AVMM interface bridge unit
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš     <benes@dyna-nic.com>, 2026
--            Vlastimil Košař <kosar@dyna-nic.com>, 2026
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity AXI2AVMM_BRIDGE is
    generic (
        AMM_BURST_COUNT_WIDTH : natural := 8;
        AMM_ADDR_WIDTH        : natural := 26;
        AMM_DATA_WIDTH        : natural := 512;
        AXI_ADDR_WIDTH        : natural := 32;
        AXI_DATA_WIDTH        : natural := 512;
        AXI_ID_WIDTH          : natural := 4;
        AXI_BURST_WIDTH       : natural := 2;
        AXI_SIZE_WIDTH        : natural := 3;
        AXI_RESP_WIDTH        : natural := 2;
        AXI_LEN_WIDTH         : natural := 8;
        -- Use multiple AXI ID. When set to TRUE multiple AXI IDs are issued and
        -- slave (e.g. HBM controller) must support reordering buffer so responses
        -- are sent in requests order. Set to false if reordering buffer in slave
        -- is not used or available.
        -- TODO: Add optional reordering buffer to AXI2AVMM_BRIDGE
        USE_AXI_ID            : boolean := false;
        -- Wait for write response before issuing next transaction
        -- Used in EM2AVMM wrapper for HBM
        AWAIT_BVALID          : boolean := false
    );
    port (
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

        ----AXI4 interface----
        -- Address Write Channel
        DDR_S_AXI_AWID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_AWADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
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
        -- Address Read Channel
        DDR_S_AXI_ARID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        DDR_S_AXI_ARADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
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

    -- FSM declaration
    type t_fsm_ddr is (
        ST_IDLE,
        ST_WRITE_SINGLE_WORD_WAIT_DATA,
        ST_WRITE_SINGLE_WORD_WAIT_ADDR,
        ST_WADDR,
        ST_WRITE,
        ST_WADDR_WAIT,
        ST_WRITE_RESP
    );

    -- Where a finished write burst continues: straight back to idle, or through
    -- ST_WRITE_RESP first when the wrapper needs BVALID before the next request.
    function write_done_state return t_fsm_ddr is
    begin
        if (AWAIT_BVALID) then
            return ST_WRITE_RESP;
        else
            return ST_IDLE;
        end if;
    end function;

    constant ST_WRITE_DONE : t_fsm_ddr := write_done_state;

    -- Avalon-MM is word addressed, AXI byte addressed: this is the shift between them.
    constant ADDR_SHIFT : natural := log2(AMM_DATA_WIDTH/8);

    -- Control logic (FSM)
    signal state      : t_fsm_ddr := ST_IDLE;
    signal next_state : t_fsm_ddr := ST_IDLE;

    -- Transactions in burst
    signal word_cnt_d : unsigned(AMM_BURST_COUNT_WIDTH -1 downto 0);
    signal word_cnt_q : unsigned(AMM_BURST_COUNT_WIDTH -1 downto 0);
    signal addr_reg_q : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal addr_reg_d : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal bcnt_reg_q : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal bcnt_reg_d : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);

    signal sel_addr     : std_logic;
    signal wr_addr_word : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal aw_bcnt      : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);

    signal bready_int : std_logic;

    signal axi_wr_id_cnt : unsigned(AXI_ID_WIDTH-1 downto 0);
    signal axi_rd_id_cnt : unsigned(AXI_ID_WIDTH-1 downto 0);
begin

    assert AMM_DATA_WIDTH = AXI_DATA_WIDTH
        report "AXI2AVMM_BRIDGE: AMM_DATA_WIDTH must equal AXI_DATA_WIDTH, WDATA is wired straight through"
        severity failure;
    assert AXI_ADDR_WIDTH >= AMM_ADDR_WIDTH + ADDR_SHIFT
        report "AXI2AVMM_BRIDGE: AXI_ADDR_WIDTH is too small for the word-to-byte address shift"
        severity failure;
    assert 2**AMM_BURST_COUNT_WIDTH - 1 <= 2**AXI_LEN_WIDTH
        report "AXI2AVMM_BRIDGE: AMM_BURST_COUNT_WIDTH exceeds what AWLEN can express, bursts would be truncated"
        severity failure;

    -- AxSIZE is log2 of the bytes carried by one beat.
    DDR_S_AXI_AWSIZE    <= std_logic_vector(to_unsigned(ADDR_SHIFT, AXI_SIZE_WIDTH));
    DDR_S_AXI_ARSIZE    <= std_logic_vector(to_unsigned(ADDR_SHIFT, AXI_SIZE_WIDTH));

    -- Byte enable: all bytes in transaction are enabled
    DDR_S_AXI_WSTRB     <= (others => '1');

    -- Burst length: AXI counts beats from zero, Avalon gives the exact number.
    -- AWLEN follows the address mux: the live input while the Avalon request is
    -- still pending, the registered copy once the burst has moved past it.
    aw_bcnt             <= AMM_BURST_COUNT when sel_addr = '0' else bcnt_reg_q;
    DDR_S_AXI_AWLEN     <= std_logic_vector(resize((unsigned(aw_bcnt) - 1), AXI_LEN_WIDTH));
    DDR_S_AXI_ARLEN     <= std_logic_vector(resize((unsigned(AMM_BURST_COUNT) - 1), AXI_LEN_WIDTH));

    axi_id_on_g : if USE_AXI_ID generate
        -- counter of read id
        axi_rd_id_cnt_p : process (MEM_CLK)
        begin
            if (rising_edge(MEM_CLK)) then
                if (MEM_RST = '1') then
                    axi_rd_id_cnt <= (others => '0');
                elsif (DDR_S_AXI_ARVALID = '1' and DDR_S_AXI_ARREADY = '1') then
                    axi_rd_id_cnt <= axi_rd_id_cnt + 1;
                end if;
            end if;
        end process;

        -- counter for write id
        axi_wr_id_cnt_p : process (MEM_CLK)
        begin
            if (rising_edge(MEM_CLK)) then
                if (MEM_RST = '1') then
                    axi_wr_id_cnt <= (others => '0');
                elsif (DDR_S_AXI_AWVALID = '1' and DDR_S_AXI_AWREADY = '1') then
                    axi_wr_id_cnt <= axi_wr_id_cnt + 1;
                end if;
            end if;
        end process;

        DDR_S_AXI_ARID <= std_logic_vector(axi_rd_id_cnt);
        DDR_S_AXI_AWID <= std_logic_vector(axi_wr_id_cnt);
    end generate;

    axi_id_off_g : if not USE_AXI_ID generate
        -- The data transfer for a sequence of read transactions with the same AxID value must be returned in the order
        -- in which the master issued the addresses
        DDR_S_AXI_AWID      <= (others => '0');
        DDR_S_AXI_ARID      <= (others => '0');
    end generate;

    -- TODO:
    -- Transactions from the same master, but with different ID values, have no ordering restrictions. They can complete in any order.
    -- This can improve system performance, because it enables parallel processing of transactions.

    -- Burst type: INCR (Incrementing base address with each transaction)
    DDR_S_AXI_AWBURST   <= "01";
    DDR_S_AXI_ARBURST   <= "01";

    mem_p : process (MEM_CLK)
    begin
        if rising_edge(MEM_CLK) then
            if (MEM_RST = '1') then
                state           <= ST_IDLE;
                word_cnt_q      <= (others => '0');
                addr_reg_q      <= (others => '0');
                bcnt_reg_q      <= (others => '0');
            else
                state           <= next_state;
                word_cnt_q      <= word_cnt_d;
                addr_reg_q      <= addr_reg_d;
                bcnt_reg_q      <= bcnt_reg_d;
            end if;
        end if;
    end process;

    fsm_p : process (all)
    begin
        next_state          <= state;
        word_cnt_d          <= word_cnt_q;
        addr_reg_d          <= addr_reg_q;
        bcnt_reg_d          <= bcnt_reg_q;
        sel_addr            <= '0';
        AMM_READY           <= '1';
        DDR_S_AXI_WVALID    <= '0';
        DDR_S_AXI_ARVALID   <= '0';
        DDR_S_AXI_AWVALID   <= '0';
        DDR_S_AXI_WLAST     <= '0';
        bready_int          <= '0';

        case (state) is
            when ST_IDLE        =>
                word_cnt_d          <= (others => '0');

                if (AMM_WRITE = '1') then
                    AMM_READY           <= '0';
                    DDR_S_AXI_AWVALID   <= '1';
                    DDR_S_AXI_WVALID    <= '1';

                    addr_reg_d          <= AMM_ADDRESS;
                    bcnt_reg_d          <= AMM_BURST_COUNT;
                    -- One transaction in burst:
                    if (unsigned(AMM_BURST_COUNT) = 1) then
                        DDR_S_AXI_WLAST <= '1';
                        if (DDR_S_AXI_WREADY = '1' and DDR_S_AXI_AWREADY = '1') then
                            AMM_READY   <= '1';
                            next_state  <= ST_WRITE_DONE;
                        elsif (DDR_S_AXI_WREADY = '0' and DDR_S_AXI_AWREADY = '1') then
                            next_state  <= ST_WRITE_SINGLE_WORD_WAIT_DATA;
                        elsif (DDR_S_AXI_WREADY = '1' and DDR_S_AXI_AWREADY = '0') then
                            next_state  <= ST_WRITE_SINGLE_WORD_WAIT_ADDR;
                        end if;
                    else
                        if (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY   <= '1';
                            word_cnt_d  <= to_unsigned(1, word_cnt_d'length);
                            next_state  <= ST_WRITE;
                        elsif (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '0') then
                            next_state  <= ST_WRITE;
                        elsif (DDR_S_AXI_AWREADY = '0' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY   <= '1';
                            word_cnt_d  <= to_unsigned(1, word_cnt_d'length);
                            next_state  <= ST_WADDR;
                        end if;
                    end if;
                end if;

                if (AMM_READ = '1') then
                    AMM_READY           <= DDR_S_AXI_ARREADY;
                    DDR_S_AXI_ARVALID   <= '1';
                end if;

            when ST_WRITE_SINGLE_WORD_WAIT_DATA =>
                AMM_READY           <= '0';
                DDR_S_AXI_WVALID    <= '1';
                DDR_S_AXI_WLAST     <= '1';
                if (DDR_S_AXI_WREADY = '1') then
                    AMM_READY   <= '1';
                    next_state  <= ST_WRITE_DONE;
                end if;

            when ST_WRITE_SINGLE_WORD_WAIT_ADDR =>
                AMM_READY            <= '0';
                DDR_S_AXI_AWVALID    <= '1';
                -- Like the other two states that hold AWVALID, the address phase is
                -- driven from the registered copy, not from the Avalon inputs.
                sel_addr             <= '1';
                if (DDR_S_AXI_AWREADY = '1') then
                    AMM_READY   <= '1';
                    next_state  <= ST_WRITE_DONE;
                end if;

            when ST_WADDR       =>
                -- The address phase is still waiting for AWREADY, and AXI4 forbids
                -- dropping AWVALID before its handshake, even if the master pauses.
                DDR_S_AXI_AWVALID   <= '1';
                sel_addr            <= '1';
                -- Mid-burst: the default '1' would accept a read this state never issues.
                AMM_READY           <= '0';

                if (AMM_WRITE = '1') then
                    -- This state is sending first transaction in burst
                    -- A deadlock condition can occur if the slave is waiting for WVALID before asserting AWREADY.
                    DDR_S_AXI_WVALID    <= '1';

                    -- Avalon defines the burst count only on the first beat, so the end
                    -- of the burst is found with the latched copy.
                    if (word_cnt_q = unsigned(bcnt_reg_q) - 1) then
                        DDR_S_AXI_WLAST     <= '1';
                        if (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY           <= '1';
                            word_cnt_d          <= (others => '0');
                            next_state          <= ST_WRITE_DONE;
                        elsif (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '0') then
                            next_state          <= ST_WRITE;
                        elsif (DDR_S_AXI_AWREADY = '0' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY           <= '1';
                            word_cnt_d          <= (others => '0');
                            next_state          <= ST_WADDR_WAIT;
                        end if;
                    else
                        if (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY           <= '1';
                            word_cnt_d          <= word_cnt_q + 1;
                            next_state          <= ST_WRITE;
                        elsif (DDR_S_AXI_AWREADY = '1' and DDR_S_AXI_WREADY = '0') then
                            next_state          <= ST_WRITE;
                        elsif (DDR_S_AXI_AWREADY = '0' and DDR_S_AXI_WREADY = '1') then
                            AMM_READY           <= '1';
                            word_cnt_d          <= word_cnt_q + 1;
                        end if;
                    end if;
                elsif (DDR_S_AXI_AWREADY = '1') then
                    -- Address accepted while the master was paused: only data beats are
                    -- left, so ST_WRITE takes over and nothing drives AWVALID again.
                    next_state          <= ST_WRITE;
                end if;

            when ST_WRITE       =>
                -- Same as ST_WADDR: READY stays low unless a write beat is consumed.
                AMM_READY           <= '0';
                if (AMM_WRITE = '1') then
                    DDR_S_AXI_WVALID    <= '1';
                    word_cnt_d          <= word_cnt_q + 1;

                    -- Avalon defines the burst count only on the first beat, so the end
                    -- of the burst is found with the latched copy.
                    if (word_cnt_q = unsigned(bcnt_reg_q) - 1) then
                        DDR_S_AXI_WLAST     <= '1';
                        word_cnt_d          <= (others => '0');
                        next_state          <= ST_WRITE_DONE;
                    end if;

                    if (DDR_S_AXI_WREADY = '0') then
                        -- WLAST must stay stable until WREADY, so freezing the counter
                        -- keeps the last beat condition above true for the whole stall.
                        word_cnt_d          <= word_cnt_q;
                        next_state          <= ST_WRITE;
                    else
                        AMM_READY           <= '1';
                    end if;
                end if;

            when ST_WADDR_WAIT  =>
                AMM_READY           <= '0';
                sel_addr            <= '1';
                DDR_S_AXI_AWVALID   <= '1';
                if (DDR_S_AXI_AWREADY = '1') then
                    next_state  <= ST_WRITE_DONE;
                end if;

            when ST_WRITE_RESP  =>
                bready_int <= '1';
                -- The burst is not committed yet, so a read of the address just written
                -- is held back and other reads pass. Only the base address is compared.
                if (AMM_READ = '1' and AMM_ADDRESS /= addr_reg_q) then
                    AMM_READY           <= DDR_S_AXI_ARREADY;
                    DDR_S_AXI_ARVALID   <= '1';
                else
                    AMM_READY  <= '0';
                end if;
                if (DDR_S_AXI_BVALID = '1') then
                    next_state  <= ST_IDLE;
                end if;

        end case;
    end process;

    -- Read ready is always ready, it is responsibility of initiator to be able
    -- to handle all responses for dispatched read requests.
    DDR_S_AXI_RREADY                <= '1';

    -- Write address: the registered copy takes over once the burst has moved on.
    wr_addr_word     <= AMM_ADDRESS when sel_addr = '0' else addr_reg_q;
    DDR_S_AXI_AWADDR <= std_logic_vector(shift_left(resize(unsigned(wr_addr_word), AXI_ADDR_WIDTH), ADDR_SHIFT));

    -- Write data
    DDR_S_AXI_WDATA                 <= AMM_WRITE_DATA;

    -- Response
    gen_bready: if not AWAIT_BVALID generate
        DDR_S_AXI_BREADY            <= '1';
    else generate
        DDR_S_AXI_BREADY            <= bready_int;
    end generate;

    -- Read address
    DDR_S_AXI_ARADDR <= std_logic_vector(shift_left(resize(unsigned(AMM_ADDRESS), AXI_ADDR_WIDTH), ADDR_SHIFT));

    -- Read data
    AMM_READ_DATA_VALID             <= DDR_S_AXI_RVALID;
    AMM_READ_DATA                   <= DDR_S_AXI_RDATA;

end architecture;
