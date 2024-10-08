-- dsp_counter_intel.vhd: It's a counter that can, but does not have to, use a DSP block on Stratix 10 or Agilex FPGA.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

architecture BEHAV of DSP_COUNTER_INTEL is

    -- this function converts boolean to std_logic (because the COUNT_DOWN singal is of type std_logic in entity DSP_COUNTER_STRATIX_10_ATOM)
    function bool_to_sl (COUNT_DOWN : boolean) return std_logic is
    begin
        if (COUNT_DOWN = true) then
            return '1';
        else
            return '0';
        end if;
    end function;

    signal count_by_behind_regs : std_logic_vector(COUNT_BY_WIDTH-1 downto 0); -- COUNT_BY signal delayed by input registers (0 or 1 clock cycle, depends if input regs are enabled)
    signal clk_en_behind_regs   : std_logic; -- CLK_EN signal delayed by input registers (0 or 1 clock cycle, depends if input regs are enabled)
    signal cnt_result           : std_logic_vector(RESULT_WIDTH-1 downto 0); -- intern result of the counter
    ------------------------ AUTO_RESET signals -----------------------
    signal cnt_result_msb_dly   : std_logic; -- holds the MSB of previous result of the counter, it is used to detect overflow and underflow
    signal freeze_at_max        : std_logic; -- stops the counter when over/underflow is detected
    signal init_underflow       : std_logic; -- used when counting down; signals, if the counter has initially underflowed ('1') or not ('0'), because the counter starts at value 0, it underflows with the first subtraction
    signal init_underflow_dly   : std_logic := '0'; -- stores the init_underflow value until reset
    signal underflow            : std_logic; -- used when counting down; is '1' when underflow is detected, then with init_underflow decides the right time to assert freeze_at_max

begin

    -- assert to check if MAX_VAL is set correctly - it is only important when AUTO_RESET = false
    assert ((AUTO_RESET = true) or (((COUNT_DOWN = false) and (and MAX_VAL = '1')) or ((COUNT_DOWN = true) and (or MAX_VAL = '0'))))
    report "Wrong value of MAX_VAL, check port decription for more information." severity failure;

    -- -------------------------------------------------------------------------
    -- delaying CLK_EN if input registers are enabled
    -- -------------------------------------------------------------------------
    clk_en_behind_regs_g : if (INPUT_REGS = false) generate
        clk_en_behind_regs <= CLK_EN;
    else generate
        clk_en_behind_regs_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                clk_en_behind_regs <= CLK_EN;
            end if;
        end process;
    end generate;

    -- -------------------------------------------------------------------------
    -- counter with AUTO_RESET set to false
    -- -------------------------------------------------------------------------
    auto_reset_g : if (AUTO_RESET = false) generate

        -- delaying the MSB of cnt_result to be used for over/underflow detection
        cnt_result_msb_dly_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    cnt_result_msb_dly <= '0';
                elsif ((clk_en_behind_regs = '1') and (freeze_at_max = '0')) then
                    cnt_result_msb_dly <= cnt_result(RESULT_WIDTH-1);
                end if;
            end if;
        end process;

        -- -----------------------------------------------------------------
        -- AUTO_RESET logic when counting down
        -- -----------------------------------------------------------------
        freeze_g : if (COUNT_DOWN = true) generate

            -- AUTO_RESET logic: underflow is detected when MSB goes from '0' (MSB of previous result) to '1' (MSB of current result)
            underflow <= not cnt_result_msb_dly and cnt_result(RESULT_WIDTH-1);
            -- storing the value of init_underflow so it can be reset and also used to calculate new init_underflow (via line above)
            init_underflow_dly_p : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RESET = '1') then
                        init_underflow_dly <= '0';
                    elsif ((clk_en_behind_regs = '1') and (freeze_at_max = '0')) then
                        -- the counter has initially overflowed if it has overflowed right now (underflow) or some other time before (init_underflow_dly)
                        init_underflow_dly <= underflow or init_underflow_dly;
                    end if;
                end if;
            end process;
            -- the counter has to stop counting (freeze) when it underflows for the second time
            freeze_at_max <= underflow and init_underflow_dly;

        -- -----------------------------------------------------------------
        -- AUTO_RESET logic when counting up
        -- -----------------------------------------------------------------
        else generate

            -- AUTO_RESET logic: overflow is detected when MSB goes from '1' (MSB of previous result) to '0' (MSB of current result) and the counter is stopped (frozen)
            freeze_at_max <= cnt_result_msb_dly and not cnt_result(RESULT_WIDTH-1);

        end generate;


        -- ---------------------------------------------------------------------
        -- counter without using DSP (with AUTO_RESET set to false)
        -- ---------------------------------------------------------------------
        auto_rst_cnt_variant_g : if (DSP_ENABLE = false) generate

            -- -----------------------------------------------------------------
            -- generating input register according to INPUT_REGS
            -- -----------------------------------------------------------------
            input_regs_en_g : if (INPUT_REGS = false) generate
                count_by_behind_regs <= COUNT_BY;
            else generate
                input_reg_p : process (CLK)
                begin
                    if (rising_edge(CLK)) then
                        if (RESET = '1') then
                            count_by_behind_regs <= (others => '0');
                        elsif ((CLK_EN = '1') and (freeze_at_max = '0')) then
                            count_by_behind_regs <= COUNT_BY;
                        end if;
                    end if;
                end process;
            end generate;

            -- -----------------------------------------------------------------
            -- counting down or up according to COUNT_DOWN generic
            -- -----------------------------------------------------------------
            count_down_or_up_p : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RESET = '1') then
                        cnt_result <= (others => '0');
                    elsif ((clk_en_behind_regs = '1') and (freeze_at_max = '0')) then
                        if (COUNT_DOWN = true) then
                            cnt_result <= std_logic_vector(unsigned(cnt_result) - unsigned(count_by_behind_regs));
                        else
                            cnt_result <= std_logic_vector(unsigned(cnt_result) + unsigned(count_by_behind_regs));
                        end if;
                    end if;
                end if;
            end process;

            -- assigning cnt_result to the output of the counter until it overflows/underflows (when freeze_at_max is undefined then RESULT is also undefined - this is to match the standard behaviour of non DSP counter in the 1st cycle)
            RESULT <= MAX_VAL when freeze_at_max = '1' else
                      cnt_result when freeze_at_max = '0';

        -- ---------------------------------------------------------------------
        -- counter using DSP
        -- ---------------------------------------------------------------------
        else generate

            device_g : if (DEVICE = "STRATIX10") generate

                dsp_counter_stratix_10_atom_i: entity work.DSP_COUNTER_STRATIX_10_ATOM
                generic map (
                    COUNT_BY_WIDTH => COUNT_BY_WIDTH,
                    RESULT_WIDTH   => RESULT_WIDTH,
                    COUNT_DOWN     => bool_to_sl(COUNT_DOWN),
                    REG_0_EN       => INPUT_REGS
                )
                port map (
                    CLK      => CLK,
                    CLK_EN0  => (CLK_EN and not freeze_at_max),
                    CLK_EN1  => (clk_en_behind_regs and not freeze_at_max),
                    RESET    => RESET,
                    COUNT_BY => COUNT_BY,
                    RESULT   => cnt_result
                );

                -- if DEVICE is "AGILEX"
                else generate

                    dsp_counter_stratix_10_atom_i: entity work.DSP_COUNTER_AGILEX_ATOM
                    generic map (
                        COUNT_BY_WIDTH => COUNT_BY_WIDTH,
                        RESULT_WIDTH   => RESULT_WIDTH,
                        COUNT_DOWN     => bool_to_sl(COUNT_DOWN),
                        REG_0_EN       => INPUT_REGS
                    )
                    port map (
                        CLK      => CLK,
                        CLK_EN0  => (CLK_EN and not freeze_at_max),
                        CLK_EN1  => (clk_en_behind_regs and not freeze_at_max),
                        RESET    => RESET,
                        COUNT_BY => COUNT_BY,
                        RESULT   => cnt_result
                    );

            end generate;

            -- assigning cnt_result to the output of the counter until it overflows/underflows
            RESULT <= MAX_VAL when freeze_at_max = '1' else cnt_result;

        end generate;

    -- -------------------------------------------------------------------------
    -- counter with AUTO_RESET set to true
    -- -------------------------------------------------------------------------
    else generate

        -- ---------------------------------------------------------------------
        -- counter not using DSP
        -- ---------------------------------------------------------------------
        auto_rst_cnt_variant_g : if (DSP_ENABLE = false) generate

            -- -----------------------------------------------------------------
            -- generating input register according INPUT_REGS
            -- -----------------------------------------------------------------
            input_regs_en_g : if (INPUT_REGS = false) generate

                count_by_behind_regs <= COUNT_BY;

            else generate

                input_reg_p : process (CLK)
                begin
                    if (rising_edge(CLK)) then
                        if (RESET = '1') then
                            count_by_behind_regs <= (others => '0');
                        elsif (CLK_EN = '1') then
                            count_by_behind_regs <= COUNT_BY;
                        end if;
                    end if;
                end process;

            end generate;

            -- -----------------------------------------------------------------
            -- counting down or up
            -- -----------------------------------------------------------------
            count_down_or_up_p : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RESET = '1') then
                        cnt_result <= (others => '0');
                    elsif (clk_en_behind_regs = '1') then
                        if (COUNT_DOWN = true) then
                            cnt_result <= std_logic_vector(unsigned(cnt_result) - unsigned(count_by_behind_regs));
                        else
                            cnt_result <= std_logic_vector(unsigned(cnt_result) + unsigned(count_by_behind_regs));
                        end if;
                    end if;
                end if;
            end process;

            RESULT <= cnt_result;

        -- ---------------------------------------------------------------------
        -- counter using DSP
        -- ---------------------------------------------------------------------
        else generate

            device_g : if (DEVICE = "STRATIX10") generate

                dsp_counter_stratix_10_atom_i: entity work.DSP_COUNTER_STRATIX_10_ATOM
                generic map (
                    COUNT_BY_WIDTH => COUNT_BY_WIDTH,
                    RESULT_WIDTH   => RESULT_WIDTH,
                    COUNT_DOWN     => bool_to_sl(COUNT_DOWN),
                    REG_0_EN       => INPUT_REGS
                )
                port map (
                    CLK      => CLK,
                    CLK_EN0  => CLK_EN,
                    CLK_EN1  => clk_en_behind_regs,
                    RESET    => RESET,
                    COUNT_BY => COUNT_BY,
                    RESULT   => RESULT
                );

                -- if DEVICE is "AGILEX"
                else generate

                    dsp_counter_stratix_10_atom_i: entity work.DSP_COUNTER_AGILEX_ATOM
                    generic map (
                        COUNT_BY_WIDTH => COUNT_BY_WIDTH,
                        RESULT_WIDTH   => RESULT_WIDTH,
                        COUNT_DOWN     => bool_to_sl(COUNT_DOWN),
                        REG_0_EN       => INPUT_REGS
                    )
                    port map (
                        CLK      => CLK,
                        CLK_EN0  => CLK_EN,
                        CLK_EN1  => clk_en_behind_regs,
                        RESET    => RESET,
                        COUNT_BY => COUNT_BY,
                        RESULT   => RESULT
                    );

            end generate;

        end generate;

    end generate;

end architecture;
