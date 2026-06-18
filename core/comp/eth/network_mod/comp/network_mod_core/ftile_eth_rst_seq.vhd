-- ftile_eth_rst_seq.vhd: Reset Sequence Controller for F-Tile Ethernet Hard IP
-- Implements the reset sequence as specified in:
--   Intel F-Tile Ethernet Hard IP User Guide, "Reset Sequence" section
--
-- The sequence follows Intel's recommended order:
--   1. Full reset release: deassert i_rst_n with i_tx_rst_n and i_rx_rst_n already deasserted
--   2. Wait for o_rst_ack_n to deassert (IP out of full reset)
--   3. TX reset cycle: assert i_tx_rst_n -> wait for o_tx_lanes_stable=0 and o_tx_rst_ack_n=0 -> deassert
--   4. RX reset cycle: assert i_rx_rst_n -> wait for o_rx_pcs_ready=0 and o_rx_rst_ack_n=0 -> deassert
--
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity FTILE_ETH_RST_SEQ is
    port (
        CLK             : in  std_logic;      -- Clock (F-Tile IP clock domain, e.g. CLK_ETH_IN)
        RST             : in  std_logic;      -- Asynchronous reset input (active high, e.g. RESET_ETH)

        -- Status inputs from F-Tile Ethernet IP
        RST_ACK_N       : in  std_logic;      -- o_rst_ack_n from IP (active low)
        TX_RST_ACK_N    : in  std_logic;      -- o_tx_rst_ack_n from IP (active low)
        RX_RST_ACK_N    : in  std_logic;      -- o_rx_rst_ack_n from IP (active low)
        TX_LANES_STABLE : in  std_logic;      -- o_tx_lanes_stable from IP
        RX_PCS_READY    : in  std_logic;      -- o_rx_pcs_ready from IP

        -- Reset outputs to F-Tile Ethernet IP (active low)
        RST_N           : out std_logic;      -- -> i_rst_n of IP
        TX_RST_N        : out std_logic;      -- -> i_tx_rst_n of IP
        RX_RST_N        : out std_logic;      -- -> i_rx_rst_n of IP

        -- Status outputs
        READY           : out std_logic;      -- Reset sequence completed, IP operational
        -- Current FSM state for debug
        DBG_STATE       : out std_logic_vector(3 downto 0);

        -- Runtime RX link recovery trigger (rising edge triggered)
        RX_LINK_RST     : in  std_logic := '0'
    );
end entity;

architecture FULL of FTILE_ETH_RST_SEQ is

    type t_state is (
        S_RST_FULL,         -- Full reset: all resets asserted
        S_DEASSERT_DP,      -- Deassert datapath resets before releasing full reset
        S_RELEASE_FULL,     -- Release full reset, wait for ack
        S_TX_RESET,         -- Assert TX reset, wait for lanes unstable
        S_TX_ACK_WAIT,      -- Wait for TX reset acknowledge
        S_TX_RELEASE,       -- Release TX reset, wait for lanes stable
        S_RX_RESET,         -- Assert RX reset, wait for PCS not ready
        S_RX_ACK_WAIT,      -- Wait for RX reset acknowledge
        S_RX_RELEASE,       -- Release RX reset, wait for PCS ready
        S_IDLE              -- Normal operation
    );

    signal state             : t_state;
    signal rst_sync          : std_logic;
    signal dp_deassert_cnt   : natural range 0 to 7;
    signal rx_link_rst_d     : std_logic;

begin

    -- Synchronize the asynchronous reset to the clock domain
    rst_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK         => CLK,
        ASYNC_RST   => RST,
        OUT_RST(0)  => rst_sync
    );

    -- Delay register for RX_LINK_RST rising edge detection
    process (CLK)
    begin
        if rising_edge(CLK) then
            rx_link_rst_d <= RX_LINK_RST;
            if (rst_sync = '1') then
                rx_link_rst_d <= '0';
            end if;
        end if;
    end process;

    -- ---------------------------------------------------------------
    -- Reset sequence state machine
    -- ---------------------------------------------------------------
    fsm_proc : process (CLK)
    begin
        if rising_edge(CLK) then
            if (rst_sync = '1') then
                state           <= S_RST_FULL;
                dp_deassert_cnt <= 0;
            else
                case state is

                    when S_RST_FULL =>
                        dp_deassert_cnt <= 0;
                        state           <= S_DEASSERT_DP;

                    when S_DEASSERT_DP =>
                        -- Ensure i_tx_rst_n and i_rx_rst_n are deasserted for several
                        -- clock cycles before releasing i_rst_n (per Intel specification:
                        -- "Drive the i_rst_n reset signal high while i_tx_rst_n and
                        -- i_rx_rst_n reset signals are already deasserted")
                        if (dp_deassert_cnt = 3) then
                            state <= S_RELEASE_FULL;
                        else
                            dp_deassert_cnt <= dp_deassert_cnt + 1;
                        end if;

                    when S_RELEASE_FULL =>
                        -- Wait for IP to acknowledge release from full reset
                        if (RST_ACK_N = '1') then
                            state <= S_TX_RESET;
                        end if;

                    when S_TX_RESET =>
                        -- TX reset asserted, wait for TX lanes to become unstable
                        if (TX_LANES_STABLE = '0') then
                            state <= S_TX_ACK_WAIT;
                        end if;

                    when S_TX_ACK_WAIT =>
                        -- Wait for TX datapath to acknowledge being in reset
                        if (TX_RST_ACK_N = '0') then
                            state <= S_TX_RELEASE;
                        end if;

                    when S_TX_RELEASE =>
                        -- TX reset released, wait for TX lanes to stabilize
                        if (TX_LANES_STABLE = '1') then
                            state <= S_RX_RESET;
                        end if;

                    when S_RX_RESET =>
                        -- RX reset asserted, wait for RX PCS to become not ready
                        if (RX_PCS_READY = '0') then
                            state <= S_RX_ACK_WAIT;
                        end if;

                    when S_RX_ACK_WAIT =>
                        -- Wait for RX datapath to acknowledge being in reset
                        if (RX_RST_ACK_N = '0') then
                            state <= S_RX_RELEASE;
                        end if;

                    when S_RX_RELEASE =>
                        -- RX reset released, wait for RX PCS to become ready
                        if (RX_PCS_READY = '1') then
                            state <= S_IDLE;
                        end if;

                    when S_IDLE =>
                        -- Normal operation; check for RX link recovery request
                        if (RX_LINK_RST = '1' and rx_link_rst_d = '0') then
                            state <= S_RX_RESET;
                        end if;

                end case;
            end if;
        end if;
    end process;

    -- ---------------------------------------------------------------
    -- Output logic
    -- ---------------------------------------------------------------
    -- i_rst_n: asserted during full reset only
    RST_N <= '0' when (state = S_RST_FULL or state = S_DEASSERT_DP) else '1';

    -- i_tx_rst_n: asserted during full reset and TX reset cycle
    TX_RST_N <= '0' when (state = S_RST_FULL or state = S_TX_RESET or state = S_TX_ACK_WAIT) else '1';

    -- i_rx_rst_n: asserted during full reset and RX reset cycle
    RX_RST_N <= '0' when (state = S_RST_FULL or state = S_RX_RESET or state = S_RX_ACK_WAIT) else '1';

    -- Status
    READY <= '1' when (state = S_IDLE) else '0';

    DBG_STATE <= X"0" when state = S_RST_FULL     else
                 X"1" when state = S_DEASSERT_DP   else
                 X"2" when state = S_RELEASE_FULL  else
                 X"3" when state = S_TX_RESET      else
                 X"4" when state = S_TX_ACK_WAIT   else
                 X"5" when state = S_TX_RELEASE    else
                 X"6" when state = S_RX_RESET      else
                 X"7" when state = S_RX_ACK_WAIT   else
                 X"8" when state = S_RX_RELEASE    else
                 X"9";                                   -- S_IDLE

end architecture;
