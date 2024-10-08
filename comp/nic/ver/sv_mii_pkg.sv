/*!
 * \file sv_mii_pkg.sv
 * \brief SystemVerilog package with MII
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



`include "mii_ifc.sv"



package sv_mii_pkg;

    import sv_common_pkg::*; // Import SV common classes

    `include "mii_transaction.sv"
    `include "mii_driver.sv"
    `include "mii_monitor.sv"


    parameter CDGMII_WIDTH = 2048;
    parameter CDGMII_CLK_PERIOD = 5.12ns;
    typedef MiiTransaction CdgmiiTransaction;
    typedef MiiMonitor #(CDGMII_WIDTH, 64) CdgmiiMonitor;
    typedef MiiDriver #(CDGMII_WIDTH, 64) CdgmiiDriver;
    // CDGMII with Four Thirds Data Rate
    parameter CDGMII_FTDR_WIDTH = 1536;
    parameter CDGMII_FTDR_CLK_PERIOD = 3.84ns;
    typedef MiiMonitor #(CDGMII_FTDR_WIDTH, 64) CdgmiiFtdrMonitor;
    typedef MiiDriver #(CDGMII_FTDR_WIDTH, 64) CdgmiiFtdrDriver;
    // CDGMII with Double Data Rate
    parameter CDGMII_DDR_WIDTH = 1024;
    parameter CDGMII_DDR_CLK_PERIOD = 2.56ns;
    typedef MiiMonitor #(CDGMII_DDR_WIDTH, 64) CdgmiiDdrMonitor;
    typedef MiiDriver #(CDGMII_DDR_WIDTH, 64) CdgmiiDdrDriver;


    parameter CGMII_WIDTH = 512;
    parameter CGMII_CLK_PERIOD = 5.12ns;
    typedef MiiTransaction CgmiiTransaction;
    typedef MiiMonitor #(CGMII_WIDTH, 64) CgmiiMonitor;
    typedef MiiDriver #(CGMII_WIDTH, 64) CgmiiDriver;


    parameter XLGMII_WIDTH = 256;
    parameter XLGMII_CLK_PERIOD = 6.4ns;
    typedef MiiTransaction XlgmiiTransaction;
    typedef MiiMonitor #(XLGMII_WIDTH, 64) XlgmiiMonitor;
    typedef MiiDriver #(XLGMII_WIDTH, 64) XlgmiiDriver;


    parameter XGMII_SDR_WIDTH = 64;
    parameter XGMII_SDR_CLK_PERIOD = 6.4ns;
    typedef MiiTransaction XgmiiTransaction;
    typedef MiiMonitor #(XGMII_SDR_WIDTH, 32) XgmiiSdrMonitor;
    typedef MiiDriver #(XGMII_SDR_WIDTH, 32) XgmiiSdrDriver;
    // XGMII with Double Data Rate
    parameter XGMII_DDR_WIDTH = 32;
    parameter XGMII_DDR_CLK_PERIOD = 3.2ns;
    typedef MiiMonitor #(XGMII_DDR_WIDTH, 32) XgmiiDdrMonitor;
    typedef MiiDriver #(XGMII_DDR_WIDTH, 32) XgmiiDdrDriver;


    parameter GMII_WIDTH = 8;
    parameter GMII_CLK_PERIOD = 8ns;
    typedef MiiTransaction GmiiTransaction;
    typedef MiiMonitor #(GMII_WIDTH, 8) GmiiMonitor;
    typedef MiiDriver #(GMII_WIDTH, 8) GmiiDriver;

endpackage
