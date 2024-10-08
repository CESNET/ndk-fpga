/*!
 * \file       sv_mi32slave_pkg.sv
 * \brief      New MI32 verification package - slave interface version
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

`include "mi32_ifc_slave.sv"

package sv_mi32_pkg;

	import sv_common_pkg::*;

	`include "mi32_transaction.sv"
	`include "mi32_monitor_new.sv"
	`include "mi32_responder.sv"

endpackage
