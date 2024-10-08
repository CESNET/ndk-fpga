/*
 * math_pkg.sv: FrameLink Monitor
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------

package math_pkg;

// ------------- log2() -------------------------------------------------------
function int log2 (input int n);
  $write("WARNING: Usage of deprecated log2 function from math_pkg! Use standard SV $clog2() instead.\n");
  return $clog2(n);
endfunction : log2

// ----------- abs() ----------------------------------------------------------
let abs(n) = (n < 0) ? (-n) : n;

// ----------- max() ----------------------------------------------------------
let max(a,b) = (a > b) ? a : b;

// ----------- min() ----------------------------------------------------------
let min(a,b) = (a < b) ? a : b;

endpackage : math_pkg
