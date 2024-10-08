/*!
 * \file       sv_ndp_software_pkg.sv
 * \brief      NDP software pkg
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

package sv_ndp_software_pkg;

    import sv_common_pkg::*;
    import sv_flup_pkg::*;

    `include "ram_base.sv"
    `include "ram.sv"
    `include "ram_rand.sv"

    `include "pcie_root_axi.sv"
    `include "mi32_module.sv"
    `include "ndp_software.sv"
    `include "ndp_software_rx.sv"
    `include "ndp_software_tx.sv"
    `include "npp_software_rx.sv"
    `include "npp_software_tx.sv"

endpackage
