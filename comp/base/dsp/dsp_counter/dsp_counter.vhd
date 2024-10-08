-- dsp_counter.vhd: It's a DSP counter (where the DSP can be disabled) that can be impemented on different devices (Agilex, Stratix 10, Ultrascale, Virtex-7).
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;

-- NOTE: When the rst signal deasserts at the exact time as clk asserts (happens very rarely) and when DSPs are enabled, the simulation ends with an error,
--       it seems like it is because the DSP does not react in time and starts counting one cycle later that it should - identified on Stratix 10 only

-- Another NOTE: Please beware that the counter on Xilix with DSPs enabled has different latency for each extra chained DSP block and reacts later on CE and reset signals
--               1 DSP has max OUTPUT_WIDTH=48, chaining each other DSP results in latency+1
--               rather than reading comments I recommend running the simulation and studying the wave diagram

entity DSP_COUNTER is
    Generic (
        -- set the device on which the counter will be impemented: AGILEX (Intel), STRATIX10 (Intel), 7SERIES (Xilinx), ULTRASCALE (Xilinx)
        DEVICE       : string  := "AGILEX";
        -- enable input registers, then the latency will be 2 clock cycles
        INPUT_REGS   : boolean := true;
        -- the width of the counter input (max 27 when using DSPs on Stratix 10); configurable only on Intel FPGAs, in other devices INPUT_WIDTH = OUTPUT_WIDTH
        INPUT_WIDTH  : natural := 27;
        -- the width of the counter output (max 64 for counters on Intel FPGAs, "unlimited" for others - DSPs can be chained)
        OUTPUT_WIDTH : natural := 64;
        -- set as true to use DSP for the counter
        DSP_ENABLE   : boolean := true
        );
    Port (
        -- clock input
        CLK       :  in std_logic;
        -- enable input
        CLK_EN    :  in std_logic;
        -- reset input
        RESET     :  in std_logic;
        -- the input of the counter - the counter counts up by this number
        INCREMENT :  in std_logic_vector(INPUT_WIDTH-1 downto 0);
        -- the maximum value the counter can reach; MAX_VAL is expected to be (others => '1') when using counter on Stratix 10,
        -- for other devices condition (MAX_VAL % INCREMENT = 0) must hold
        MAX_VAL   :  in std_logic_vector(OUTPUT_WIDTH-1 downto 0) := (others => '1');
        -- the output value of the counter
        RESULT    : out std_logic_vector(OUTPUT_WIDTH-1 downto 0)
    );
end entity;

architecture STRUCT of DSP_COUNTER is

    signal increment_resized : std_logic_vector(OUTPUT_WIDTH-1 downto 0); -- counter on Xilinx expects the output width to be the same as the input width

begin

    -- when using counter on Stratix 10, MAX_VAL must be se to (others => '1')
    assert (((DEVICE /= "STRATIX10") or (DEVICE /= "AGILEX")) or (and MAX_VAL = '1'))
    report "Wrong value of MAX_VAL, check port decription for more information." severity failure;

    assert ((DEVICE = "AGILEX") or (DEVICE = "STRATIX10") or (DEVICE = "ULTRASCALE") or (DEVICE = "7SERIES"))
    report "Wrong / unsupported device !! See comment near DEVICE generic." severity failure;

    increment_resized <= std_logic_vector(resize(unsigned(INCREMENT), OUTPUT_WIDTH)); -- for counter on Xilinx

    device_g : if ((DEVICE = "STRATIX10") or (DEVICE = "AGILEX")) generate

        dsp_counter_i: entity work.DSP_COUNTER_INTEL
        generic map (
            INPUT_REGS     => INPUT_REGS  ,
            COUNT_BY_WIDTH => INPUT_WIDTH ,
            RESULT_WIDTH   => OUTPUT_WIDTH,
            DSP_ENABLE     => DSP_ENABLE  ,
            COUNT_DOWN     => false       ,
            DEVICE         => DEVICE
        )
        port map (
            CLK        => CLK      ,
            CLK_EN     => CLK_EN   ,
            RESET      => RESET    ,
            COUNT_BY   => INCREMENT,
            MAX_VAL    => MAX_VAL  ,
            RESULT     => RESULT
        );

    else generate

        -- when DSPs are enabled, the latecy is + 1 clock cycle than expected (=> 2 or 3),
        -- also the CE signal is delayed along with the input data, those registers also have reset and the output register has delayed reset signal
        dsp_counter_i : entity work.COUNT_DSP
        generic map (
            REG_IN     => tsel(INPUT_REGS = true, 1, 0), -- more than 1 input register does not work anyway
            DATA_WIDTH => OUTPUT_WIDTH                 ,
            DSP_EN     => DSP_ENABLE                   ,
            DIR        => true                         ,
            DEVICE     => DEVICE
        )
        port map (
            CLK    => CLK              ,
            ENABLE => CLK_EN           ,
            RESET  => RESET            ,
            A      => increment_resized,
            MAX    => MAX_VAL          ,
            P      => RESULT
        );

    end generate;

end STRUCT;
