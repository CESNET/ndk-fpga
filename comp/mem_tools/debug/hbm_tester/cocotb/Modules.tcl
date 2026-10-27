# Modules.tcl: cocotb-only top level, wrapping the real HBM_TESTER component
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# The wrapper is test-only and must stay out of any app build, so it has its own Modules.tcl and
# references the real component as a COMPONENTS entry.
lappend COMPONENTS [list "HBM_TESTER" "$OFM_PATH/comp/mem_tools/debug/hbm_tester" "FULL"]

lappend MOD "$ENTITY_BASE/hbm_tester_tb_wrapper.vhd"
