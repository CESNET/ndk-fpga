-- dsp_comparator.vhd: It's a comparator that can use DSP bloks on different Devices,
--                     or can be implemented in common logic.
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

-- This is a  comparator that can use DSP bloks on different Devices but can also be implemented in
-- common logic.
--
-- .. NOTE::
--      Default and recommended latency for comparator using DSPs is 2 clock cycles,
--      latency of 1 clock cycle is achieved when input registers are disabled.
entity DSP_COMPARATOR is
    Generic (
        -- The width of inputs; maximum width of 25 bits applies only in modes ">= " or "<= " when
        -- using DSP blocks, "unlimited" in other cases
        INPUT_DATA_WIDTH : natural := 25;
        -- Enable input registers
        INPUT_REGS_EN    : boolean := true;
        -- This option allows user to choose the function of the comparator (the space after ">="
        -- or "<=" is necessary!):
        --
        -- * "><=" is the default mode which outputs results as specified above the RESULT port
        -- * ">= " outputs result in form of '11' if the 1st number is larger or equal than the 2nd
        --   number, else '00'  - in this mode, only one DSP block is used (when enabled)
        -- * "<= " outputs result in form of '11' if the 1st number is smaller or equal than the
        --   2nd number, else '00' - in this mode, only one DSP block is used (when enabled)
        MODE             : string  := ">= ";
        -- Set True to use DSP(s) for the comparator
        DSP_ENABLE       : boolean := true;
        -- Target FPGA, the allowed options are:
        --
        -- * "STRATIX10"
        -- * "AGILEX"
        -- * "ULTRASCALE"
        -- * "7SERIES"
        DEVICE           : string  := "AGILEX"
        );
    Port (
        CLK     :  in std_logic;
        CLK_EN  :  in std_logic;
        RESET   :  in std_logic;
        -- The 1st number for comparison
        INPUT_1 :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- The 2nd number for comparison
        INPUT_2 :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- The final value of the comparator, the RESULT will be:
        --
        -- * "01" (1 in dec) when the 1st number (INPUT_1) > 2nd number (INPUT_2) - applies only for mode "><="
        -- * "10" (2 in dec) when the 2nd number (INPUT_2) > 1st number (INPUT_1) - applies only for mode "><="
        -- * "00" when both numbers are equal                                     - applies only for mode "><="
        RESULT  : out std_logic_vector(1 downto 0)
    );
end entity;

architecture FULL of DSP_COMPARATOR is

    -- this function enables the usage of DSP blocks for the comparator
    function use_dsp return boolean is
    begin
        if ((DEVICE = "STRATIX10") or (DEVICE = "AGILEX") or (DEVICE = "ULTRASCALE") or (DEVICE = "7SERIES")) then
            return DSP_ENABLE;
        else
            return false;
        end if;
    end function;

begin

    device_g : if (((DEVICE = "ULTRASCALE") or (DEVICE = "7SERIES")) and use_dsp) generate

        signal cmp_dsp_output        : std_logic_vector(1 downto 0); -- Xilinx cmp result in its format
        signal dsp_comparator_output : std_logic_vector(1 downto 0); -- Xilinx cmp result converted to local format

    begin

        comparator_i: entity work.CMP_DSP
        generic map (
            DATA_WIDTH => INPUT_DATA_WIDTH         ,
            REG_IN     => tsel(INPUT_REGS_EN, 1, 0),
            REG_OUT    => 1
        )
        port map (
            CLK    => CLK    ,
            CE_IN  => CLK_EN ,
            CE_OUT => CLK_EN ,
            RESET  => RESET  ,
            A      => INPUT_1,
            B      => INPUT_2,
            P      => cmp_dsp_output
        );

        -- convert output of CMP_DSP to local output format
        dsp_comparator_output <= "00" when (cmp_dsp_output = "11") else
                                 "01" when (cmp_dsp_output = "00") else
                                 "10"; --  (cmp_dsp_output = "10");

        result_g : case MODE generate

            when "><="  => RESULT <= dsp_comparator_output;
            when ">= "  => RESULT <= "11" when ((dsp_comparator_output = "00") or (dsp_comparator_output = "01")) else "00";
            when "<= "  => RESULT <= "11" when ((dsp_comparator_output = "00") or (dsp_comparator_output = "10")) else "00";
            when others => RESULT <= "XX";

        end generate;

    else generate

        comparator_i: entity work.DSP_COMPARATOR_INTEL
        generic map (
            INPUT_DATA_WIDTH => INPUT_DATA_WIDTH,
            INPUT_REGS_EN    => INPUT_REGS_EN   ,
            DSP_EN           => use_dsp         ,
            MODE             => MODE            ,
            DEVICE           => DEVICE
        )
        port map (
            CLK     => CLK    ,
            CLK_EN  => CLK_EN ,
            RESET   => RESET  ,
            INPUT_1 => INPUT_1,
            INPUT_2 => INPUT_2,
            RESULT  => RESULT
        );

    end generate;

end architecture;
