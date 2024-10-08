/*
 * dpi_sw_access_ifc.sv: Software (C/C++) accessible MI32 DUT connections using DPI with callback interface
 * Copyright (C) 2021 CESNET
 * Author(s): Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

package dpi_sw_access;

    typedef class DPISoftwareAccessInterface;
    DPISoftwareAccessInterface dpi_swai[string];

    interface class DPISoftwareAccessInterface;
        /* TODO: rewrite with generic data width */
        pure virtual task write32(int unsigned address, int unsigned value);
        pure virtual task read32 (int unsigned address, output int unsigned value);
    endclass

    function int dpiconnect(string devpath, DPISoftwareAccessInterface ifc);
        if (dpi_swai.exists(devpath)) begin
            $write("DPI device with name '%s' already registered!\n", devpath);
            $stop();
            return -1;
        end
        dpi_swai[devpath] = ifc;
        return 0;
    endfunction

    task dpi_write32(string devpath, int unsigned address, int unsigned value);
        if (!dpi_swai.exists(devpath)) begin
            $write("dpi_write error: interface %s not connected!\n", devpath);
            $stop();
        end
        dpi_swai[devpath].write32(address, value);
    endtask

    task dpi_read32(string devpath, int unsigned address, output int unsigned value);
        if (!dpi_swai.exists(devpath)) begin
            $write("dpi_read error: interface %s not connected!\n", devpath);
            $stop();
        end
        dpi_swai[devpath].read32(address, value);
    endtask

    export "DPI-C" task dpi_read32;
    export "DPI-C" task dpi_write32;

    import "DPI-C" context task dpicall(string name, string params, output int retval);
endpackage
