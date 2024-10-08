/* sv_pcie_pkg.sv
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

`include "if.sv"

package sv_pcie_pkg;

    import sv_common_pkg::*;
    import math_pkg::*;

    typedef enum {PCIE_RQ_READ, PCIE_RQ_WRITE} pcie_rq_type_t;
    `include "ifg_setup.sv"

    `include "pcie_cbs.sv"
    `include "pcie_tag_manager.sv"
    `include "pcie_transaction.sv"
    `include "pcie_sequencer.sv"
    `include "ifg_delay.sv"
    `include "ram.sv"
    `include "agent.sv"

    //avalon agent
    `include "avalon_rq_monitor.sv"
    `include "avalon_rc_driver.sv"
    `include "avalon_agent.sv"

    //axi agent
    `include "axi_rq_monitor.sv"
    `include "axi_rc_driver.sv"
    `include "axi_agent.sv"

    //common agent
    `include "pcie_agent.sv"
endpackage
