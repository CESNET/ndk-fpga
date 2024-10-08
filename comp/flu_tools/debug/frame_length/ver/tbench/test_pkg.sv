/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
/*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;
  import math_pkg::*;
  `include "scoreboard.sv"

  parameter DATA_WIDTH    = 512;
  parameter SOP_POS_WIDTH = 3;
  parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);

  parameter CLK_PERIOD = 5ns;
  parameter RESET_TIME = 10*CLK_PERIOD;

  int       GENERATOR_FLU_PACKET_SIZE_MAX = 512;
  int       GENERATOR_FLU_PACKET_SIZE_MIN = 1;

  parameter DRIVER_DELAYEN_WT         = 1;
  parameter DRIVER_DELAYDIS_WT        = 3;
  parameter DRIVER_DELAYLOW           = 0;
  parameter DRIVER_DELAYHIGH          = 3;
  parameter DRIVER_INSIDE_DELAYEN_WT  = 1;
  parameter DRIVER_INSIDE_DELAYDIS_WT = 3;
  parameter DRIVER_INSIDE_DELAYLOW    = 0;
  parameter DRIVER_INSIDE_DELAYHIGH   = 3;
  parameter DRIVER_START_POS_LOW      = 0;
  parameter DRIVER_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;

  parameter MONITOR_DELAYEN_WT         = 1;
  parameter MONITOR_DELAYDIS_WT        = 3;
  parameter MONITOR_DELAYLOW           = 0;
  parameter MONITOR_DELAYHIGH          = 3;

  parameter TRANSACTION_COUT = 10000;
endpackage
