/*!
 * \file        sv_axi_completer_pkg.sv
 * \brief       SV package with AXI4S completer MI root
 * \author      Martin Spinler <spinler@cesnet.cz>
 * \date        2021
 * \copyright   CESNET, z. s. p. o.
 */

package sv_axi_completer_miroot_pkg;

    import sv_common_pkg::*;
    import sv_axi_pkg::*;
    import sv_axi_pcie_pkg::*;

    `include "axi4s_completer_miroot.sv"

endpackage
