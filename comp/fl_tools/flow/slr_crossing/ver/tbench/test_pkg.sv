/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2014
 */
/*
 * Copyright (C) 2014 CESNET
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
  `include "scoreboard.sv"

  parameter DATA_WIDTH = 64;
  parameter DREM_WIDTH = 3;
  parameter USE_OUTREG = 1;

  parameter CLK_PERIOD = 5ns;
  parameter RESET_TIME = 10*CLK_PERIOD;

  parameter GENERATOR_FL_PACKET_COUNT      = 2;
  int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{32,32};
  int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{8,8};

  parameter DRIVER_DELAYEN_WT         = 1;
  parameter DRIVER_DELAYDIS_WT        = 3;
  parameter DRIVER_DELAYLOW           = 0;
  parameter DRIVER_DELAYHIGH          = 3;
  parameter DRIVER_INSIDE_DELAYEN_WT  = 1;
  parameter DRIVER_INSIDE_DELAYDIS_WT = 3;
  parameter DRIVER_INSIDE_DELAYLOW    = 0;
  parameter DRIVER_INSIDE_DELAYHIGH   = 3;

  parameter MONITOR_DELAYEN_WT         = 1;
  parameter MONITOR_DELAYDIS_WT        = 3;
  parameter MONITOR_DELAYLOW           = 0;
  parameter MONITOR_DELAYHIGH          = 3;
  parameter MONITOR_INSIDE_DELAYEN_WT  = 1;
  parameter MONITOR_INSIDE_DELAYDIS_WT = 3;
  parameter MONITOR_INSIDE_DELAYLOW    = 0;
  parameter MONITOR_INSIDE_DELAYHIGH   = 3;

  parameter TRANSACTION_COUT = 10000;
endpackage
