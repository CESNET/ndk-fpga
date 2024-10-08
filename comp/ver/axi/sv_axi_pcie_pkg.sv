/*!
 * \file       sv_axi_pcie_pkg.sv
 * \brief      SystemVerilog package with PCIe AXI bus
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

package sv_axi_pcie_pkg;

    import math_pkg::*;
    import sv_common_pkg::*;
    import sv_axi_pkg::*;

    `include "axi4s_rc_agent.sv"
    `include "axi4s_rq_agent.sv"

endpackage
