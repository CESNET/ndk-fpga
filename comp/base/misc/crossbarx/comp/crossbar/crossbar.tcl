# crossbar.tcl: Local Vivado constraints for CROSSBARX_CROSSBAR
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# These constraints are used only with USE_CLK2, because plan_sel_reg exists only with USE_CLK2.
# CLK2 must have double frequency of CLK and the same first rising edge.
# Plan 0 of uinstr_*_reg is read on the CLK2 edge in the middle of the CLK period.
# Plan 1 of uinstr_*_reg is read on the CLK2 edge that is aligned with the next CLK edge.
if {[llength [get_cells -quiet {plan_sel_reg_reg*}]] > 0} {
    set clk_obj  [get_clocks -quiet -of_objects [get_ports CLK]]
    set clk2_obj [get_clocks -quiet -of_objects [get_ports CLK2]]
    set clk_ok   0
    if {[llength $clk_obj] == 1 && [llength $clk2_obj] == 1 && $clk_obj ne $clk2_obj} {
        set clk_per   [get_property PERIOD $clk_obj]
        set clk2_per  [get_property PERIOD $clk2_obj]
        set clk_rise  [lindex [get_property WAVEFORM $clk_obj] 0]
        set clk2_rise [lindex [get_property WAVEFORM $clk2_obj] 0]
        if {abs($clk_per - 2*$clk2_per) < 0.001 && abs($clk_rise - $clk2_rise) < 0.001} {
            set clk_ok 1
        }
    }

    if {$clk_ok} {
        set plan0_regs [get_cells -quiet {uinstr_*_reg_reg[0][*}]
        set plan1_regs [get_cells -quiet {uinstr_*_reg_reg[1][*}]

        # Plan 0 is not read on the aligned CLK2 edge. The hold check moves one CLK2 cycle back.
        if {[llength $plan0_regs] > 0} {
            set_multicycle_path -hold -end 1 -from $plan0_regs
        }
        # Plan 1 is read two CLK2 cycles after it is written. The hold check stays on the aligned CLK2 edge.
        if {[llength $plan1_regs] > 0} {
            set_multicycle_path -setup -end 2 -from $plan1_regs
            set_multicycle_path -hold  -end 1 -from $plan1_regs
        }
    } else {
        send_msg_id {CROSSBARX_CROSSBAR-1} {CRITICAL WARNING} "USE_CLK2 is set, but CLK2 does not have double frequency of CLK with aligned edges. The multicycle constraints are not used."
    }
}
