-- hbm_fb2cdg1_reset.vhd: Silicom ThunderFjord fb2cdg1 HBM reset
-- Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- This component addresses post-boot calibration failures.
-- It monitors the HBM calibration status and triggers retries until a successful calibration is achieved.

-- Note: This issue has been resolved by using Quartus 26.1.
entity HBM_FB2CDG1_RESET is
    generic (
        -- Duration of the retry reset in clock cycles
        -- Minimum is two clock cycles
        RESET_DURATION  : natural := 4;
        -- How long to wait for HBM_RESET_IN_PROG after the reset has been released
        -- before the calibration status is trusted anyway. See ST_CAL_ACK below.
        ACK_TIMEOUT     : natural := 1024;
        HBM_PORTS       : natural := 16
    );
    port (
        CLK                  : in std_logic;
        HBM_ONLY_RESET_RESET : in std_logic;

        PLL_LOCKED           : in std_logic;
        HBM_CAL_SUCCESS      : in std_logic;
        HBM_CAL_FAIL         : in std_logic;
        HBM_RESET_IN_PROG    : in std_logic;

        AXI_RESET_N : out std_logic_vector(HBM_PORTS - 1 downto 0);
        HBM_RESET_N : out std_logic
    );
end entity;

architecture FULL of HBM_FB2CDG1_RESET is

    type hbm_reset_fsm is (
        ST_CAL_INIT,    -- Let the HBM_ONLY_RESET try
        ST_CAL_REQ,     -- The calibration failed. Try again.
        ST_CAL_ACK,     -- Reset released, wait until the HBM restarts the calibration
        ST_CAL_RES,     -- Wait for the result of the calibration
        ST_CAL_DONE     -- Calibration done
    );

    signal state      : hbm_reset_fsm := ST_CAL_INIT;
    signal next_state : hbm_reset_fsm := ST_CAL_INIT;

    signal hbm_cal_success_meta   : std_logic;
    signal hbm_cal_success_s      : std_logic;

    signal hbm_cal_fail_meta      : std_logic;
    signal hbm_cal_fail_s         : std_logic;

    signal hbm_reset_in_prog_meta : std_logic;
    signal hbm_reset_in_prog_s    : std_logic;

    constant CNT_WIDTH : natural := max(log2(RESET_DURATION), log2(ACK_TIMEOUT));

    signal cnt_q : unsigned(CNT_WIDTH - 1 downto 0);
    signal cnt_d : unsigned(CNT_WIDTH - 1 downto 0);

    signal axi_fabric_rst_async_high : std_logic;
    signal axi_fabric_rst_sync_high  : std_logic_vector(HBM_PORTS - 1 downto 0);

    signal pll_reset             : std_logic;
    signal hbm_only_reset        : std_logic;
    signal fsm_reset             : std_logic;

    signal hbm_reset_n_d         : std_logic;
    signal hbm_reset_n_q         : std_logic := '0';

begin

    hbm_only_reset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => CLK,
        ASYNC_RST  => HBM_ONLY_RESET_RESET,
        OUT_RST(0) => hbm_only_reset
    );

    pll_reset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => CLK,
        ASYNC_RST  => not PLL_LOCKED,
        OUT_RST(0) => pll_reset
    );

    sync_cal_s_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            hbm_cal_success_meta <= HBM_CAL_SUCCESS;
            hbm_cal_success_s    <= hbm_cal_success_meta;

            hbm_cal_fail_meta    <= HBM_CAL_FAIL;
            hbm_cal_fail_s       <= hbm_cal_fail_meta;

            hbm_reset_in_prog_meta  <= HBM_RESET_IN_PROG;
            hbm_reset_in_prog_s     <= hbm_reset_in_prog_meta;
        end if;
    end process;

    fsm_reset <= hbm_only_reset or pll_reset;

    reset_seq_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (fsm_reset = '1') then
                state         <= ST_CAL_INIT;
                cnt_q         <= (others => '0');
                -- Hold the HBM in reset while the request is active
                hbm_reset_n_q <= '0';
            else
                state         <= next_state;
                cnt_q         <= cnt_d;
                hbm_reset_n_q <= hbm_reset_n_d;
            end if;
        end if;
    end process;

    HBM_RESET_N <= hbm_reset_n_q;

    reset_comb_p: process(all)
    begin
        next_state    <= state;
        hbm_reset_n_d <= '1';
        cnt_d         <= (others => '0');

        case (state) is
            when ST_CAL_INIT =>
                next_state    <= ST_CAL_ACK;

            when ST_CAL_REQ  =>
                hbm_reset_n_d <= '0';
                cnt_d         <= cnt_q + 1;

                if (cnt_q = RESET_DURATION - 1) then
                    cnt_d      <= (others => '0');
                    next_state <= ST_CAL_ACK;
                end if;

            -- The calibration status is only meaningful once the HBM has reacted to the
            -- reset. Until then HBM_CAL_FAIL still reports the result of the previous
            -- attempt, and sampling it straight away would assert the reset again and
            -- never give the calibration a chance to run. Wait for HBM_RESET_IN_PROG,
            -- which also covers the latency of the synchronisers above. Should the pulse
            -- be missed entirely, fall through after ACK_TIMEOUT cycles, by which time
            -- the status outputs have settled anyway.
            when ST_CAL_ACK  =>
                cnt_d <= cnt_q + 1;

                if (hbm_reset_in_prog_s = '1') or (cnt_q = ACK_TIMEOUT - 1) then
                    next_state <= ST_CAL_RES;
                end if;

            when ST_CAL_RES  =>
                if (hbm_reset_in_prog_s = '0') then
                    if (hbm_cal_success_s = '1') then
                        next_state <= ST_CAL_DONE;
                    end if;

                    if (hbm_cal_fail_s = '1') then
                        next_state <= ST_CAL_REQ;
                    end if;
                end if;

            when ST_CAL_DONE =>
                null;

            when others      =>
                next_state <= ST_CAL_INIT;
        end case;
    end process;

    -- User logic reset
    axi_fabric_rst_async_high <= pll_reset or (not HBM_CAL_SUCCESS) or HBM_RESET_IN_PROG;

    axi_reset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => HBM_PORTS
    )
    port map (
        CLK        => CLK,
        ASYNC_RST  => axi_fabric_rst_async_high,
        OUT_RST    => axi_fabric_rst_sync_high
    );

    AXI_RESET_N <= not axi_fabric_rst_sync_high;

end architecture;
