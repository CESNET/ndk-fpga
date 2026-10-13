# crossbar.sdc: Local Quartus constraints for CROSSBARX_CROSSBAR
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# These constraints are used only with USE_CLK2, because plan_sel_reg exists only with USE_CLK2.
# CLK2 must have double frequency of CLK and aligned edges, for example two outputs of one PLL.
# Quartus reads this file before the clocks are created, so this file cannot check the clocks.
# Plan 0 of uinstr_*_reg is read on the CLK2 edge in the middle of the CLK period.
# Plan 1 of uinstr_*_reg is read on the CLK2 edge that is aligned with the next CLK edge.
if {[get_collection_size [get_registers -nowarn "plan_sel_reg*"]] > 0} {
    set plan0_regs [get_registers -nowarn "uinstr_*_reg\[0\]\[*"]
    set plan1_regs [get_registers -nowarn "uinstr_*_reg\[1\]\[*"]

    # Plan 0 is not read on the aligned CLK2 edge. The hold check moves one CLK2 cycle back.
    if {[get_collection_size $plan0_regs] > 0} {
        set_multicycle_path -hold -end 1 -from $plan0_regs
    }
    # Plan 1 is read two CLK2 cycles after it is written. The hold check stays on the aligned CLK2 edge.
    if {[get_collection_size $plan1_regs] > 0} {
        set_multicycle_path -setup -end 2 -from $plan1_regs
        set_multicycle_path -hold  -end 1 -from $plan1_regs
    }
}
