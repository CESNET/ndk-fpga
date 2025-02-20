-- frequency_meter_core.vhd: An Equal Precision Frequency Meter
-- Copyright (C) 2025 CESNET
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Contains the "Frequency" counters and some additional logic like Async crossings.
-- One counter runs on the "reference" clock signal, the other on the "measured" clock signal.
-- Both counters increment their values by 1 each clock cycle of the respective clock signal
-- since the `MASTER_ENABLE` asserts until it drops low again.
-- The output `*_CNTR_VLD` is asserted for a single clock cycle after the `MASTER_ENABLE` drops
-- (delayed for a couple of clock cycles).
--
entity FREQUENCY_METER_CORE is
generic (
    -- Width of the "reference frequency counter".
    -- Watch out for overflow (indicated by a bit in an MI register).
    REFERENCE_CNTR_WIDTH : natural := 32;
    -- Width of the "measured frequency counter".
    -- Watch out for overflow (indicated by a bit in an MI register).
    MEASURED_CNTR_WIDTH  : natural := 32;
    -- Maximum number of measured frequencies.
    MEASURED_FREQUENCIES : natural := 10;
    -- Utilize DSPs for the "frequency counters".
    DSP_CNTR_EN          : boolean := False;
    -- Target device.
    DEVICE               : string := "AGILEX"
);
port (
    MASTER_CLK         : in  std_logic;
    MASTER_RESET       : in  std_logic;
    -- Enables both "frequency counters" when high.
    MASTER_ENABLE      : in  std_logic;
    IN_PROGRESS        : in  std_logic;

    REFERENCE_CLK      : in  std_logic;
    REFERENCE_RESET    : in  std_logic;

    MEASURED_CLK       : in  std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    MEASURED_RESET     : in  std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    -- ========================================================================
    -- Reference data output interface
    --
    -- Runs on the MASTER_CLK
    -- ========================================================================
    -- Signal the components readiness to start another measurement.
    REFERENCE_CNTR_RDY : out std_logic;
    -- Output of the "reference frequency counter".
    REFERENCE_CNTR     : out std_logic_vector(REFERENCE_CNTR_WIDTH-1 downto 0);
    -- Signals valid output of the "reference frequency counter"
    -- Asserts for a single clock cycle after the MASTER_ENABLE drops.
    REFERENCE_CNTR_VLD : out std_logic;
    -- Reference counter overflowed. Always valid.
    REFERENCE_CNTR_OVF : out std_logic;
    -- Read request from the outside.
    REFERENCE_CNTR_RD  : in  std_logic;

    -- ========================================================================
    -- Measured data output interface
    --
    -- Runs on the MASTER_CLK
    -- ========================================================================
    -- Signal the components readiness to start another measurement.
    MEASURED_CNTR_RDY  : out std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    -- Output of the "measured frequency counter".
    MEASURED_CNTR      : out slv_array_t(MEASURED_FREQUENCIES-1 downto 0)(MEASURED_CNTR_WIDTH -1 downto 0);
    -- Signals valid output of the "measured frequency counter"
    -- Asserts for a single clock cycle after the MASTER_ENABLE drops.
    MEASURED_CNTR_VLD  : out std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    -- Measured counter overflowed. Always valid.
    MEASURED_CNTR_OVF  : out std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    -- Read request from the outside.
    MEASURED_CNTR_RD   : in  std_logic_vector(MEASURED_FREQUENCIES-1 downto 0)
);
end entity;

architecture FULL of FREQUENCY_METER_CORE is

    -- Shift register stages for delaying the synced Enable signals
    -- 1 + 1 for input regs + 1 for reserve
    constant CNTR_DLY_STAGES : natural := 3;

    signal enable_ref_cntr         : std_logic;
    signal in_progress_refclk      : std_logic;
    signal enable_meas_cntr        : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal in_progress_measclk     : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    signal ref_cnt_result          : std_logic_vector(REFERENCE_CNTR_WIDTH+1-1 downto 0);
    signal ref_cnt_result_msb      : std_logic;
    signal ref_cntr_overflowed     : std_logic;
    signal ref_cntr_ovf_edge       : std_logic;

    signal meas_cnt_result         : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(MEASURED_CNTR_WIDTH+1-1 downto 0);
    signal meas_cnt_result_msb     : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_cntr_overflowed    : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_cntr_ovf_edge      : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    signal in_progress_refclk_dly  : std_logic_vector(CNTR_DLY_STAGES+1-1 downto 0);
    signal ref_cntr_result_vld     : std_logic;

    signal in_progress_measclk_dly : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(CNTR_DLY_STAGES+1-1 downto 0);
    signal meas_cntr_result_vld    : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    signal ref_asfifox_din         : std_logic_vector(REFERENCE_CNTR_WIDTH-1 downto 0);
    signal ref_asfifox_wr          : std_logic;
    signal ref_asfifox_full        : std_logic;
    signal ref_asfifox_wr_full     : std_logic;
    signal ref_asfifox_wr_err      : std_logic;
    signal ref_asfifox_dout        : std_logic_vector(REFERENCE_CNTR_WIDTH-1 downto 0);
    signal ref_asfifox_rd          : std_logic;
    signal ref_asfifox_empty       : std_logic;

    signal meas_asfifox_din        : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(MEASURED_CNTR_WIDTH-1 downto 0);
    signal meas_asfifox_wr         : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_asfifox_full       : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_asfifox_wr_full    : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_asfifox_wr_err     : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_asfifox_dout       : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(MEASURED_CNTR_WIDTH-1 downto 0);
    signal meas_asfifox_rd         : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_asfifox_empty      : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

begin

    -- ========================================================================
    -- Input clock domain crossings
    -- ========================================================================

    -- -----------
    --  Reference
    -- -----------
    ref_clk_enable_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG   => False,
        TWO_REG  => False
    )
    port map(
        ACLK     => MASTER_CLK     ,
        ARST     => MASTER_RESET   ,
        ADATAIN  => MASTER_ENABLE  ,

        BCLK     => REFERENCE_CLK  ,
        BRST     => REFERENCE_RESET,
        BDATAOUT => enable_ref_cntr
    );

    ref_clk_inprogress_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG   => False,
        TWO_REG  => False
    )
    port map(
        ACLK     => MASTER_CLK        ,
        ARST     => MASTER_RESET      ,
        ADATAIN  => IN_PROGRESS       ,

        BCLK     => REFERENCE_CLK     ,
        BRST     => REFERENCE_RESET   ,
        BDATAOUT => in_progress_refclk
    );

    -- ----------
    --  Measured
    -- ----------
    sync_enables_g : for mf in 0 to MEASURED_FREQUENCIES-1 generate
        meas_clk_enable_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG   => False,
            TWO_REG  => False
        )
        port map(
            ACLK     => MASTER_CLK          ,
            ARST     => MASTER_RESET        ,
            ADATAIN  => MASTER_ENABLE       ,

            BCLK     => MEASURED_CLK    (mf),
            BRST     => MEASURED_RESET  (mf),
            BDATAOUT => enable_meas_cntr(mf)
        );

        meas_clk_inprogress_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG   => False,
            TWO_REG  => False
        )
        port map(
            ACLK     => MASTER_CLK             ,
            ARST     => MASTER_RESET           ,
            ADATAIN  => IN_PROGRESS            ,

            BCLK     => MEASURED_CLK       (mf),
            BRST     => MEASURED_RESET     (mf),
            BDATAOUT => in_progress_measclk(mf)
        );
    end generate;

    -- ========================================================================
    -- Frequency counters
    -- ========================================================================

    -- -----------
    --  Reference
    -- -----------
    -- Count clock cycles for the duration of the Interval given by the (synced) MASTER_ENABLE.
    -- Runs on the "Reference" frequency.
    -- MSB of the output indicates overflow.
    reference_freq_counter_i : entity work.DSP_COUNTER
    generic map(
        DEVICE       => DEVICE                ,
        INPUT_REGS   => True                  ,
        INPUT_WIDTH  => 1                     ,
        OUTPUT_WIDTH => REFERENCE_CNTR_WIDTH+1,
        DSP_ENABLE   => DSP_CNTR_EN
    )
    port map(
        CLK        => REFERENCE_CLK  ,
        CLK_EN     => enable_ref_cntr,
        RESET      => REFERENCE_RESET,
        INCREMENT  => "1"            ,
        MAX_VAL    => (others => '1'),
        RESULT     => ref_cnt_result
    );

    ref_cnt_result_msb <= ref_cnt_result(REFERENCE_CNTR_WIDTH);

    ref_cntr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG   => False,
        TWO_REG  => False
    )
    port map(
        ACLK     => REFERENCE_CLK      ,
        ARST     => REFERENCE_RESET    ,
        ADATAIN  => ref_cnt_result_msb ,

        BCLK     => MASTER_CLK         ,
        BRST     => MASTER_RESET       ,
        BDATAOUT => ref_cntr_overflowed
    );

    -- Rises the overflow signal only for a single clock cycle.
    -- Using only the MSB could lead to multiple overflows, which could avoid detection in some cases.
    ref_cnt_edge_detect_i : entity work.EDGE_DETECT
    port map(
        CLK  => MASTER_CLK         ,
        DI   => ref_cntr_overflowed,
        EDGE => ref_cntr_ovf_edge
    );

    -- ----------
    --  Measured
    -- ----------
    meas_counters_g : for mf in 0 to MEASURED_FREQUENCIES-1 generate

        -- Count clock cycles for the duration of the Interval given by the (synced) MASTER_ENABLE.
        -- Runs on the "Measured" frequencies.
        -- MSB of each counter output indicates overflow.
        measured_freq_counter_i : entity work.DSP_COUNTER
        generic map(
            DEVICE       => DEVICE               ,
            INPUT_REGS   => True                 ,
            INPUT_WIDTH  => 1                    ,
            OUTPUT_WIDTH => MEASURED_CNTR_WIDTH+1,
            DSP_ENABLE   => DSP_CNTR_EN
        )
        port map(
            CLK        => MEASURED_CLK    (mf),
            CLK_EN     => enable_meas_cntr(mf),
            RESET      => MEASURED_RESET  (mf),
            INCREMENT  => "1"                 ,
            MAX_VAL    => (others => '1')     ,
            RESULT     => meas_cnt_result (mf)
        );

        meas_cnt_result_msb(mf) <= meas_cnt_result(mf)(MEASURED_CNTR_WIDTH);

        -- Synchronize the overflow bit
        meas_cntr_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG   => False,
            TWO_REG  => False
        )
        port map(
            ACLK     => MEASURED_CLK        (mf),
            ARST     => MEASURED_RESET      (mf),
            ADATAIN  => meas_cnt_result_msb (mf),

            BCLK     => MASTER_CLK              ,
            BRST     => MASTER_RESET            ,
            BDATAOUT => meas_cntr_overflowed(mf)
        );

        -- Rises the overflow signal only for a single clock cycle.
        -- Using only the MSB could lead to multiple overflows, which could avoid detection in some cases.
        meas_cnt_edge_detect_i : entity work.EDGE_DETECT
        port map(
            CLK  => MASTER_CLK              ,
            DI   => meas_cntr_overflowed(mf),
            EDGE => meas_cntr_ovf_edge  (mf)
        );

    end generate;

    -- ========================================================================
    -- Result validation logic
    -- ========================================================================

    -- -----------
    --  Reference
    -- -----------
    in_progress_refclk_dly(0) <= in_progress_refclk;
    ref_enable_shreg_g: for s in 0 to CNTR_DLY_STAGES-1 generate
        process(REFERENCE_CLK)
        begin
            if rising_edge(REFERENCE_CLK) then
                in_progress_refclk_dly(s+1) <= in_progress_refclk_dly(s);
                if (REFERENCE_RESET = '1') then
                    in_progress_refclk_dly(s+1) <= '0';
                end if;
            end if;
        end process;
    end generate;

    -- Falling edge of the delayed Enable signal (delayed for counter's output stability).
    ref_cntr_result_vld <= in_progress_refclk_dly(CNTR_DLY_STAGES) and not in_progress_refclk_dly(CNTR_DLY_STAGES-1);

    -- ----------
    --  Measured
    -- ----------
    meas_shregs_g: for mf in 0 to MEASURED_FREQUENCIES-1 generate

        in_progress_measclk_dly(mf)(0) <= in_progress_measclk(mf);

        meas_enable_shreg_g: for s in 0 to CNTR_DLY_STAGES-1 generate
            process(MEASURED_CLK(mf))
            begin
                if rising_edge(MEASURED_CLK(mf)) then
                    in_progress_measclk_dly(mf)(s+1) <= in_progress_measclk_dly(mf)(s);
                    if (MEASURED_RESET(mf) = '1') then
                        in_progress_measclk_dly(mf)(s+1) <= '0';
                    end if;
                end if;
            end process;
        end generate;

        -- Falling edge of the delayed Enable signal (delayed for counter's output stability).
        meas_cntr_result_vld(mf) <= in_progress_measclk_dly(mf)(CNTR_DLY_STAGES) and not in_progress_measclk_dly(mf)(CNTR_DLY_STAGES-1);

    end generate;

    -- ========================================================================
    -- Store and synchronize the data of the "frequency counters"
    -- Note: ASYNC_BUS_HANDSHAKE could be used to save resources
    -- ========================================================================

    -- -----------
    --  Reference
    -- -----------
    ref_asfifox_din <= ref_cnt_result(REFERENCE_CNTR_WIDTH-1 downto 0);
    ref_asfifox_wr  <= ref_cntr_result_vld;

    -- Detect write to ASFIFOX when it's full (+synchronization to MI clock)
    -- ref_asfifox_wr_full <= ref_asfifox_wr and ref_asfifox_full;
    ref_cntr_ready_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG   => False,
        TWO_REG  => False
    )
    port map(
        ACLK     => REFERENCE_CLK       ,
        ARST     => REFERENCE_RESET     ,
        ADATAIN  => not ref_asfifox_full,

        BCLK     => MASTER_CLK          ,
        BRST     => MASTER_RESET        ,
        BDATAOUT => REFERENCE_CNTR_RDY
    );

    ref_asfifox_i : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => REFERENCE_CNTR_WIDTH,
        ITEMS               => 4                   ,
        RAM_TYPE            => "AUTO"              ,
        FWFT_MODE           => True                ,
        OUTPUT_REG          => True                ,
        DEVICE              => DEVICE              ,
        ALMOST_FULL_OFFSET  => 0                   ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        WR_CLK    => REFERENCE_CLK    ,
        WR_RST    => REFERENCE_RESET  ,
        WR_DATA   => ref_asfifox_din  ,
        WR_EN     => ref_asfifox_wr   ,
        WR_FULL   => ref_asfifox_full ,
        WR_AFULL  => open             ,
        WR_STATUS => open             ,

        RD_CLK    => MASTER_CLK       ,
        RD_RST    => MASTER_RESET     ,
        RD_DATA   => ref_asfifox_dout ,
        RD_EN     => ref_asfifox_rd   ,
        RD_EMPTY  => ref_asfifox_empty,
        RD_AEMPTY => open             ,
        RD_STATUS => open
    );

    ref_asfifox_rd <= REFERENCE_CNTR_RD;

    -- ----------
    --  Measured
    -- ----------
    meas_asfifox_din <= slv_array_slice(meas_cnt_result, REFERENCE_CNTR_WIDTH-1, 0);
    meas_asfifox_wr  <= meas_cntr_result_vld;

    -- Detect write to ASFIFOX when it's full (+synchronization to MI clock)
    -- meas_asfifox_wr_full <= meas_asfifox_wr and meas_asfifox_full;

    meas_asfifox_g : for mf in 0 to MEASURED_FREQUENCIES-1 generate

        meas_cntr_ready_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG   => False,
            TWO_REG  => False
        )
        port map(
            ACLK     => MEASURED_CLK         (mf),
            ARST     => MEASURED_RESET       (mf),
            ADATAIN  => not meas_asfifox_full(mf),

            BCLK     => MASTER_CLK               ,
            BRST     => MASTER_RESET             ,
            BDATAOUT => MEASURED_CNTR_RDY    (mf)
        );

        meas_asfifox_i : entity work.ASFIFOX
        generic map (
            DATA_WIDTH          => MEASURED_CNTR_WIDTH,
            ITEMS               => 4                  ,
            RAM_TYPE            => "AUTO"             ,
            FWFT_MODE           => True               ,
            OUTPUT_REG          => True               ,
            DEVICE              => DEVICE             ,
            ALMOST_FULL_OFFSET  => 0                  ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            WR_CLK    => MEASURED_CLK      (mf),
            WR_RST    => MEASURED_RESET    (mf),
            WR_DATA   => meas_asfifox_din  (mf),
            WR_EN     => meas_asfifox_wr   (mf),
            WR_FULL   => meas_asfifox_full (mf),
            WR_AFULL  => open                  ,
            WR_STATUS => open                  ,

            RD_CLK    => MASTER_CLK            ,
            RD_RST    => MASTER_RESET          ,
            RD_DATA   => meas_asfifox_dout (mf),
            RD_EN     => meas_asfifox_rd   (mf),
            RD_EMPTY  => meas_asfifox_empty(mf),
            RD_AEMPTY => open                  ,
            RD_STATUS => open
        );

    end generate;

    meas_asfifox_rd <= MEASURED_CNTR_RD;

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    REFERENCE_CNTR     <= ref_asfifox_dout;
    REFERENCE_CNTR_VLD <= not ref_asfifox_empty;
    REFERENCE_CNTR_OVF <= ref_cntr_ovf_edge;

    MEASURED_CNTR      <= meas_asfifox_dout;
    MEASURED_CNTR_VLD  <= not meas_asfifox_empty;
    MEASURED_CNTR_OVF  <= meas_cntr_ovf_edge;

end architecture;
