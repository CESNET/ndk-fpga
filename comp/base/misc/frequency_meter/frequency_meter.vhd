-- frequency_meter.vhd: An Equal Precision implementation of the Frequency Meter
-- Copyright (C) 2025 CESNET
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The component FREQUENCY_METER measures frequency of a (Clock) signal using the Equal Precision algorithm.
-- For this, it needs a reference (Clock) signal of known frequency.
--
-- The "Measured frequency" is measured within an Interval, which is configurable via the MI bus (see the
-- MI Address Space below). Start the measurement by a Write to the Command register.
-- During this Interval, two counters are enabled, one running on the Reference Clock,
-- the other on the Measured Clock. After it has passed, the counters' data will be ready to be fetched (=> loaded to MI registers).
-- Check the Status register for information about whether the measurement is running or has completed, if the data are ready,
-- or if any errors occurred (and which one(s)).
--
-- .. note::
--
--     In the case of an overflow error (status(6-7)), either make a new design with wider counter(s) or
--     just lower the duration of the measurement by writing a new value to the Interval length register.
--     Be aware that lower lengths of the Interval (slightly) decrease the accuracy of the measurement.
--
-- .. note::
--
--     Issuing a MI reset command (cmd(1)) during an in-progress measurement without stopping it (re)starts the
--     measurement anew, so there is no need to start it again by writing to the command register (cmd(0)).
--
-- The component cannot calculate the final frequency (is not yet implemented).
-- At this time, it can simply be done in software using formula: Fmeas = Fref * Nmeas/Nref, where
-- F<meas/ref> is the Measured or Reference frequency and N<meas/ref> are the data from the counters.
-- It is recommended to use the provided python tool to calculate the final value of the measured frequency(ies).
--
-- Other yet-to-be-implemented features include storing the counters' values from multiple measurements and
-- a histogram of these values.
--
-- **MI Address Space**
--
-- +----------------+---------------------------------------------------------------------------------------+
-- | Address offset | MI Register description                                                               |
-- +================+=======================================================================================+
-- |           0x00 | Command register (Write-only):                                                        |
-- |                |  - cmd(0) - start (1) / stop (0) measuring the frequency (see Status(1))              |
-- |                |  - cmd(1) - reset the measurement logic (except the interval length!)                 |
-- |                |  - cmd(2) - fetch measured data when ready (see Status(2))                            |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x04 | Status register (Read-only):                                                          |
-- |                |  - status(0) - ready to measure (is able to accept the command to start measuring)    |
-- |                |  - status(1) - measuring in process (write in Command reg)                            |
-- |                |  - status(2) - measurement done (measuring interval ended)                            |
-- |                |  - status(3) - counters' data are ready to be fetched                                 |
-- |                |  - status(4) - fetched data are ready to be read                                      |
-- |                |  - status(5) - an error occurred during the measurement (Counters' data are invalid)  |
-- |                |  - status(6) - the Reference Frequency Counter overflowed                             |
-- |                |  - status(7) - at least one Measured Frequency Counter overflowed                     |
-- |                |  - status(8) - the Reference Clock was reset during the measurement                   |
-- |                |  - status(9) - at least one of the Measured Clocks were reset during the measurement  |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x08 | Interval length register (Read and Write)                                             |
-- |                |  - default: 2**(INTERVAL_LEN_WIDTH/2)                                                 |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x0C | The Reference Clock frequency in Hz (Read-only)                                       |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x10 | Measured Frequencies register (Read-only):                                            |
-- |                |  - the number of measured frequencies                                                 |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x14 | Reference Frequency Counter data register (Read-only):                                |
-- |                |  - issue multiple Read requests when the Counter is wider than the MI bus             |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x18 | Measured Frequency Counter data register(s) (Read-only):                              |
-- |                |  - issue one Read request to this register for each Counters' data                    |
-- |                |  - starts from index 0 and increments after each read to this address, resets at max  |
-- |                |  - current index can be read from the Read Pointer register                           |
-- +----------------+---------------------------------------------------------------------------------------+
-- |           0x1C | Read Pointer register (Read-only):                                                    |
-- |                |  - index of the next Measured Frequency Counter data register that will be read       |
-- +----------------+---------------------------------------------------------------------------------------+
--
entity FREQUENCY_METER is
generic (
    MI_DATA_WIDTH        : natural := 32;
    MI_ADDR_WIDTH        : natural := 32;

    -- Maximum width of the Interval length signal => the highest possible value is 2**INTERVAL_LEN_WIDTH-1.
    -- This value of the Interval length signal can be set over the MI.
    -- Defines the length of the Interval during which the frequency measurement takes place.
    -- Counts by 1 to its maximum which is when the "frequency counters" are sampled.
    -- Values over 32 (=MI_DATA_WIDTH) are currently not supported!
    INTERVAL_LEN_WIDTH   : natural := 32;
    -- Width of the "Reference Frequency Counter".
    -- Watch out for overflow (indicated by a bit in the Status register).
    -- Must not be over 32!
    REFERENCE_CNTR_WIDTH : natural := 31;
    -- Width of the "Measured Frequency Counter" (all of them if there is more than one).
    -- Watch out for overflow (indicated by a bit in the Status register).
    -- Must not be over 32!
    MEASURED_CNTR_WIDTH  : natural := 31;
    -- Maximum number of measured frequencies.
    MEASURED_FREQUENCIES : natural := 10;
    -- Frequency of the reference clock signal in Hz.
    -- Used in the final calculation when the CALCULATE_FREQ generic is True.
    -- Recommended to read before the SW calculation (when the CALCULATE_FREQ generic is False).
    REFERENCE_CLK_FREQ   : natural := 200_000_000;
    -- Utilize DSPs for both "frequency counters".
    DSP_CNTR_EN          : boolean := False;

    -- Calculate the unknown frequency in the FPGA.
    -- Uses extra resources.
    -- Not supported yet!
    CALCULATE_FREQ       : boolean := False;
    -- Store measured data and/or calculated frequencies in a FIFO to read out later.
    -- Could be useful for further analysis.
    -- Not supported yet! (Also leads to a generic for FIFO_SIZE)
    STORE_DATA_EN        : boolean := False;
    -- Store measured data and/or calculated frequencies in a histogram.
    -- Could be useful for further analysis.
    -- Not supported yet!
    HISTOGRAM_EN         : boolean := False;
    -- Target device.
    DEVICE               : string := "AGILEX"
);
port (
    REFERENCE_CLK   : in  std_logic;
    REFERENCE_RESET : in  std_logic;

    MEASURED_CLK    : in  std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    MEASURED_RESET  : in  std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    -- MI interface
    MI_CLK          : in  std_logic;
    MI_RESET        : in  std_logic;

    MI_DWR          : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR         : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
  --MI_BE           : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0); NOT SUPPORTED
    MI_RD           : in  std_logic;
    MI_WR           : in  std_logic;
    MI_ARDY         : out std_logic;
    MI_DRD          : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_DRDY         : out std_logic
);
end entity;

architecture FULL of FREQUENCY_METER is

    signal command_reg_wr_en        : std_logic;
    signal interval_len_reg_wr_en   : std_logic;
    signal meas_cntr_reg_rd_en      : std_logic;
    signal cmd_reg_start_meas       : std_logic;
    signal cmd_reg_stop_meas        : std_logic;
    signal cmd_reg_reset_meas       : std_logic;
    signal mi_meas_reset            : std_logic;
    signal cmd_reg_fetch_results    : std_logic;

    signal measure_enabled          : std_logic;
    signal interval_len             : unsigned(INTERVAL_LEN_WIDTH-1 downto 0);
    signal ready_to_measure         : std_logic;
    signal results_ready_to_be_read : std_logic;
    signal some_meas_cntr_ovf       : std_logic;
    signal runtime_rst_ref          : std_logic;
    signal runtime_rst_meas         : std_logic;
    signal measurement_error        : std_logic;
    signal status                   : std_logic_vector(MI_DATA_WIDTH-1 downto 0);

    signal mi_wr_en                 : std_logic;
    signal mi_wait                  : std_logic;
    signal mi_data_ready            : std_logic;
    signal mi_data_read             : std_logic_vector(MI_DATA_WIDTH-1 downto 0);

    signal mi_meas_reset_refclk     : std_logic;
    signal meas_reset_refclk        : std_logic;
    signal ref_reset_miclk          : std_logic;
    signal mi_meas_reset_measclk    : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_reset_measclk       : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_reset_miclk         : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    signal interval_finished        : std_logic;
    signal interval_ticks_cnt       : unsigned(INTERVAL_LEN_WIDTH-1 downto 0);

    signal ref_cntr_ready           : std_logic;
    signal ref_cntr_val             : std_logic_vector(REFERENCE_CNTR_WIDTH-1 downto 0);
    signal ref_cntr_val_vld         : std_logic;
    signal ref_cntr_overflowed      : std_logic;
    signal ref_cntr_read            : std_logic;
    signal meas_cntr_ready          : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_cntr_val            : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(MEASURED_CNTR_WIDTH-1 downto 0);
    signal meas_cntr_val_vld        : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_cntr_overflowed     : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);
    signal meas_cntr_read           : std_logic_vector(MEASURED_FREQUENCIES-1 downto 0);

    signal results_ready            : std_logic;
    signal read_results             : std_logic;

    signal mi_ref_cntr_val          : std_logic_vector                                 (MI_DATA_WIDTH-1 downto 0);
    signal mi_meas_cntr_val         : slv_array_t     (MEASURED_FREQUENCIES-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_meas_cntr_rd_ptr      : unsigned(log2(MEASURED_FREQUENCIES)-1 downto 0);

begin

    -- It is possible to support longer intervals without changing the MI address space,
    -- however, it is not expected to be necessary.
    -- Implement this by automatic shifting of write/read data from the interval register by
    -- 32 bits like it's done for reading the "Measured Frequency Counter data registers".
    -- (All on the same address and a different register is read with each MI read request.)
    assert INTERVAL_LEN_WIDTH <= MI_DATA_WIDTH
        report "The generic INTERVAL_LEN_WIDTH (="           & integer'image(INTERVAL_LEN_WIDTH) & ")" &
               ") must not be greater than MI_DATA_WIDTH (=" & integer'image(MI_DATA_WIDTH     ) & ")!"
        severity Failure;

    assert REFERENCE_CNTR_WIDTH <= MI_DATA_WIDTH
        report "The generic REFERENCE_CNTR_WIDTH (="         & integer'image(REFERENCE_CNTR_WIDTH) & ")" &
               ") must not be greater than MI_DATA_WIDTH (=" & integer'image(MI_DATA_WIDTH       ) & ")!"
        severity Failure;

    assert MEASURED_CNTR_WIDTH <= MI_DATA_WIDTH
        report "The generic MEASURED_CNTR_WIDTH (="          & integer'image(MEASURED_CNTR_WIDTH) & ")" &
               ") must not be greater than MI_DATA_WIDTH (=" & integer'image(MI_DATA_WIDTH      ) & ")!"
        severity Failure;

    -- ========================================================================
    -- MI access logic
    -- ========================================================================

    MI_ARDY <= (MI_RD or MI_WR) and not mi_wait;

    mi_wr_en <= MI_WR and not mi_wait;

    -- Register resolution
    command_reg_wr_en      <= '1' when (mi_wr_en = '1') and (MI_ADDR(4 downto 2) = "000") else '0'; -- 0x00
    interval_len_reg_wr_en <= '1' when (mi_wr_en = '1') and (MI_ADDR(4 downto 2) = "010") else '0'; -- 0x08
    meas_cntr_reg_rd_en    <= '1' when (MI_RD    = '1') and (MI_ADDR(4 downto 2) = "110") else '0'; -- 0x18

    -- Command resolution
    cmd_reg_start_meas    <= '1' when (command_reg_wr_en = '1') and (MI_DWR(0) = '1') else '0';
    cmd_reg_stop_meas     <= '1' when (command_reg_wr_en = '1') and (MI_DWR(0) = '0') else '0';
    cmd_reg_reset_meas    <= '1' when (command_reg_wr_en = '1') and (MI_DWR(1) = '1') else '0';
    cmd_reg_fetch_results <= '1' when (command_reg_wr_en = '1') and (MI_DWR(2) = '1') else '0';

    -- Extend reset pulse
    pulse_extend_i : entity work.PULSE_EXTEND
    generic map(
        N => 20
    )
    port map(
        RST => MI_RESET          ,
        CLK => MI_CLK            ,
        I   => cmd_reg_reset_meas,
        O   => mi_meas_reset
    );

    -- Delay ARDY after accepting command to Reset (cmd_reg_reset_meas)
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (cmd_reg_reset_meas = '1') then
                mi_wait <= '1';
            end if;
            if (MI_RESET = '1') or ((mi_meas_reset = '1') and (mi_wait = '1')) then
                mi_wait <= '0';
            end if;
        end if;
    end process;

    -- ---------------
    --  MI registers
    -- ---------------
    measure_enable_reg : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (cmd_reg_start_meas = '1') and (ready_to_measure = '1') then
                measure_enabled <= '1';
            end if;
            if (MI_RESET = '1') or (cmd_reg_stop_meas = '1') or (interval_finished = '1') then
                measure_enabled <= '0';
            end if;
        end if;
    end process;

    interval_len_reg : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (interval_len_reg_wr_en = '1') then
                interval_len <= resize(unsigned(MI_DWR), INTERVAL_LEN_WIDTH);
            end if;
            if (MI_RESET = '1') then
                interval_len <= (others => '0');
                interval_len(INTERVAL_LEN_WIDTH/2) <= '1';
            end if;
        end if;
    end process;

    -- component is ready to measure (to accept the start_measure command)
    ready_to_measure <= ref_cntr_ready and (and meas_cntr_ready);

    -- measurement results are fetched and ready to be read
    results_ready_to_be_read <= cmd_reg_fetch_results and results_ready;

    -- at least one of the Measured Counters overflowed
    some_meas_cntr_ovf <= or meas_cntr_overflowed;

    -- Reference Reset came during active measurement
    runtime_rst_ref  <= ref_reset_miclk  and measure_enabled;
    -- Measured Reset came during active measurement
    runtime_rst_meas <= (or meas_reset_miclk) and measure_enabled;

    measurement_error <= ref_cntr_overflowed or
                         some_meas_cntr_ovf  or
                         runtime_rst_ref     or
                         runtime_rst_meas;

    status_reg : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            status(0) <= ready_to_measure;
            status(1) <= measure_enabled;
            status(2) <= interval_finished;
            status(3) <= results_ready;
            if (results_ready_to_be_read = '1') then
                status(4) <= '1';
            end if;
            if (measurement_error = '1') then
                status(5) <= '1';
            end if;
            if (ref_cntr_overflowed = '1') then
                status(6) <= '1';
            end if;
            if (some_meas_cntr_ovf = '1') then
                status(7) <= '1';
            end if;
            if (runtime_rst_ref = '1') then
                status(8) <= '1';
            end if;
            if (runtime_rst_meas = '1') then
                status(9) <= '1';
            end if;

            if (MI_RESET = '1') or (mi_meas_reset = '1') then
                status <= (others => '0');
            end if;
        end if;
    end process;

    -- ---------------
    --  MI Read logic
    -- ---------------
    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            -- if (mi_wait = '0') then
            -- end if;
            MI_DRD  <= mi_data_read;
            MI_DRDY <= mi_data_ready;
            if (MI_RESET = '1') then
                MI_DRDY <= '0';
            end if;
        end if;
    end process;

    mi_data_ready <= MI_RD and not mi_wait;

    process(all)
    begin
        case MI_ADDR(4 downto 2) is
            when "001"  => mi_data_read <= std_logic_vector(resize(unsigned(status             ), MI_DATA_WIDTH)); -- 0x04
            when "010"  => mi_data_read <= std_logic_vector(resize(         interval_len        , MI_DATA_WIDTH)); -- 0x08
            when "011"  => mi_data_read <= std_logic_vector(to_unsigned(    REFERENCE_CLK_FREQ  , MI_DATA_WIDTH)); -- 0x0C
            when "100"  => mi_data_read <= std_logic_vector(to_unsigned(    MEASURED_FREQUENCIES, MI_DATA_WIDTH)); -- 0x10
            when "101"  => mi_data_read <=                                  mi_ref_cntr_val                      ; -- 0x14
            when "110"  => mi_data_read <=                                  mi_meas_cntr_val(0)                  ; -- 0x18
            when "111"  => mi_data_read <= std_logic_vector(resize(         mi_meas_cntr_rd_ptr , MI_DATA_WIDTH)); -- 0x1C
            when others => mi_data_read <= X"FEEDBEEF";
        end case;
    end process;

    -- ========================================================================
    -- Reset logic
    -- ========================================================================

    -- -----------
    --  Reference
    -- -----------
    -- Synchronize the MI Reset command to the Reference Clock.
    sync_meas_rst_2_refclk_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => False,
        OUT_REG  => False,
        REPLICAS => 1
    )
    port map(
        CLK        => REFERENCE_CLK       ,
        ASYNC_RST  => mi_meas_reset       ,
        OUT_RST(0) => mi_meas_reset_refclk
    );
    meas_reset_refclk <= mi_meas_reset_refclk or REFERENCE_RESET;

    -- Synchronize the Reference Reset to the MI Clock.
    sync_ref_rst_2_miclk_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => False,
        OUT_REG  => False,
        REPLICAS => 1
    )
    port map(
        CLK        => MI_CLK         ,
        ASYNC_RST  => REFERENCE_RESET,
        OUT_RST(0) => ref_reset_miclk
    );

    -- ----------
    --  Measured
    -- ----------
    sync_meas_rst_g : for mf in 0 to MEASURED_FREQUENCIES-1 generate
        -- Synchronize the MI Reset command to the Measured Clock.
        sync_meas_rst_2_measclk_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => False,
            OUT_REG  => False,
            REPLICAS => 1
        )
        port map(
            CLK        => MEASURED_CLK         (mf),
            ASYNC_RST  => mi_meas_reset            ,
            OUT_RST(0) => mi_meas_reset_measclk(mf)
        );
        meas_reset_measclk(mf) <= mi_meas_reset_measclk(mf) or MEASURED_RESET(mf);

        -- Synchronize the Measured Reset to the MI Clock.
        sync_meas_rst_2_miclk_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => False,
            OUT_REG  => False,
            REPLICAS => 1
        )
        port map(
            CLK        => MI_CLK              ,
            ASYNC_RST  => MEASURED_RESET  (mf),
            OUT_RST(0) => meas_reset_miclk(mf)
        );
    end generate;

    -- ========================================================================
    -- Core logic
    -- ========================================================================
    interval_finished <= '0' when (interval_ticks_cnt < interval_len) else '1';

    process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (measure_enabled = '1') and (interval_finished = '0') then
                interval_ticks_cnt <= interval_ticks_cnt + 1;
            end if;
            if (MI_RESET = '1') or (mi_meas_reset = '1') then
                interval_ticks_cnt <= (others => '0');
            end if;
        end if;
    end process;

    measuring_core_i : entity work.FREQUENCY_METER_CORE
    generic map (
        REFERENCE_CNTR_WIDTH => REFERENCE_CNTR_WIDTH,
        MEASURED_CNTR_WIDTH  => MEASURED_CNTR_WIDTH ,
        MEASURED_FREQUENCIES => MEASURED_FREQUENCIES,
        DSP_CNTR_EN          => DSP_CNTR_EN         ,
        DEVICE               => DEVICE
    )
    port map(
        MASTER_CLK         => MI_CLK               ,
        MASTER_RESET       => MI_RESET             ,
        MASTER_ENABLE      => measure_enabled      ,
        IN_PROGRESS        => not interval_finished,

        REFERENCE_CLK      => REFERENCE_CLK        ,
        REFERENCE_RESET    => meas_reset_refclk    ,

        MEASURED_CLK       => MEASURED_CLK         ,
        MEASURED_RESET     => meas_reset_measclk   ,

        REFERENCE_CNTR_RDY => ref_cntr_ready       ,
        REFERENCE_CNTR     => ref_cntr_val         ,
        REFERENCE_CNTR_VLD => ref_cntr_val_vld     ,
        REFERENCE_CNTR_OVF => ref_cntr_overflowed  ,
        REFERENCE_CNTR_RD  => ref_cntr_read        ,

        MEASURED_CNTR_RDY  => meas_cntr_ready      ,
        MEASURED_CNTR      => meas_cntr_val        ,
        MEASURED_CNTR_VLD  => meas_cntr_val_vld    ,
        MEASURED_CNTR_OVF  => meas_cntr_overflowed ,
        MEASURED_CNTR_RD   => meas_cntr_read
    );

    -- Reference and Measured data reads assert at the same time.
    ref_cntr_read <= read_results;
    meas_cntr_read <= (others => read_results);

    results_ready <= interval_finished and ref_cntr_val_vld and (and meas_cntr_val_vld);
    read_results <= results_ready and cmd_reg_fetch_results;

    -- -----------
    --  Reference
    -- -----------
    read_ref_data_reg_p : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (read_results = '1') then
                mi_ref_cntr_val <= std_logic_vector(resize(unsigned(ref_cntr_val), MI_DATA_WIDTH));
            end if;
            if (MI_RESET = '1') or (cmd_reg_reset_meas = '1') then
                mi_ref_cntr_val <= (others => '0');
            end if;
        end if;
    end process;

    -- ----------
    --  Measured
    -- ----------
    read_meas_data_reg_p : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (read_results = '1') then
                mi_meas_cntr_val <= array_item_resize_l(meas_cntr_val, MI_DATA_WIDTH);
            elsif (meas_cntr_reg_rd_en = '1') then -- shift segments
                mi_meas_cntr_val(MEASURED_FREQUENCIES-2 downto 0) <= mi_meas_cntr_val(MEASURED_FREQUENCIES-1 downto 1);
                mi_meas_cntr_val(MEASURED_FREQUENCIES-1         ) <= mi_meas_cntr_val(                              0);
            end if;
            if (MI_RESET = '1') or (cmd_reg_reset_meas = '1') then
                mi_meas_cntr_val <= (others => (others => '0'));
            end if;
        end if;
    end process;

    read_pointer_reg_p : process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (meas_cntr_reg_rd_en = '1') then
                mi_meas_cntr_rd_ptr <= mi_meas_cntr_rd_ptr + 1;
            end if;
            if (MI_RESET = '1') or (cmd_reg_reset_meas = '1') or (read_results = '1') or (mi_meas_cntr_rd_ptr >= MEASURED_FREQUENCIES) then
                mi_meas_cntr_rd_ptr <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
