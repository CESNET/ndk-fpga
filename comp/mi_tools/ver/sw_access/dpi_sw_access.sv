/*
 * dpi_sw_access.sv: Software (C/C++) accessible MI32 DUT connections using DPI
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

`include "../mi32_ifc.sv"

package dpi_sw_access;
  typedef struct {
    int unsigned memory_size;
    int unsigned design_id;
    int unsigned design_hw_id;
    string board_name;
    string design_name;
  } dpi_device_info;

  typedef struct {
    string name;
    int unsigned index;
    int unsigned version;
    int unsigned space_base;
    int unsigned space_size;
  } dpi_device_component_info;

  dpi_device_component_info mi32_comps[10][$];
  dpi_device_info mi32_info[10];
  string mi32_devicetree[10];
  virtual   iMi32.tb mi32[10];
  int unsigned DRDY_MAX_WAIT = 128;
  int unsigned ARDY_MAX_WAIT = 128;

  function void dpiconnect(int inst, virtual iMi32.tb m);
    if(inst >= 10) begin
      $write("\ndpiconnect error: interface number %0d out of available range (from 0 to 9)!!!\n", inst);
      $stop();
    end
    mi32[inst]          = m;         // Store pointer interface
    mi32[inst].cb.DWR  <= 0;
    mi32[inst].cb.ADDR <= 0;
    mi32[inst].cb.RD   <= 0;
    mi32[inst].cb.WR   <= 0;
    mi32[inst].cb.BE   <= 4'b1111;
    mi32_devicetree[inst] = "";
    devicetree_regenerate(inst);
  endfunction

  function void dpiconnect_setinfo(int inst, int unsigned memory_size, string board_name, string design_name, int unsigned design_id, int unsigned design_hw_id);
    if(inst >= 10) return;
    mi32_info[inst].memory_size  = memory_size;
    mi32_info[inst].board_name   = board_name;
    mi32_info[inst].design_name  = design_name;
    mi32_info[inst].design_id    = design_id;
    mi32_info[inst].design_hw_id = design_hw_id;
  endfunction

  function void dpiconnect_addcomponent(int inst, string name, int unsigned version, int unsigned space_base, int unsigned space_size);
    dpi_device_component_info ci;
    if(inst >= 10) return;
    ci.name = name;
    ci.index = 0;
    ci.version = version;
    ci.space_base = space_base;
    ci.space_size = space_size;
    for(int i=0; i<mi32_comps[inst].size(); i++)
      if(name == mi32_comps[inst][i].name)
        ci.index ++;
    mi32_comps[inst].push_back(ci);
  endfunction

  function int dpiconnect_devicetree_addcomponent(int inst, string comp);
    if(inst >= 10) return 0;
    mi32_devicetree[inst] = {mi32_devicetree[inst], comp, "\n"};
    return devicetree_regenerate(inst);
  endfunction

  function int devicetree_regenerate(int inst);
    integer dts;
    string dut;
    if(inst >= 10) return 0;
    dut = {"DeviceTree-dut", $sformatf("%0d",inst)};
    dts = $fopen({dut, ".dts"}, "w");
    if(dts == 0) return 0;
    $fwrite(dts, "/dts-v1/;\n\n");
    $fwrite(dts, "/ {\n\n");
    $fwrite(dts, "  firmware {\n");
    $fwrite(dts, "    build-tool = \"ModelSim\";\n");
    $fwrite(dts, "    build-author = \"Lukas Kekely\";\n");
    $fwrite(dts, "    build-revision = \"123456\";\n");
    $fwrite(dts, "    build-time = <0x0>;\n");
    $fwrite(dts, "    card-name = \"NFB-VERIFICATION\";\n\n");
    $fwrite(dts, "    mi0: mi_bus {\n");
    $fwrite(dts, "      compatible = \"netcope,bus,mi\";\n");
    $fwrite(dts, "      resource = \"PCI0,BAR0\";\n");
    $fwrite(dts, "      width = <0x20>;\n");
    $fwrite(dts, "      #address-cells = <1>;\n");
    $fwrite(dts, "      #size-cells = <1>;\n\n");
    $fwrite(dts, mi32_devicetree[inst]);
    $fwrite(dts, "    };\n  };\n};\n");
    $fclose(dts);
    if($system({"dtc -I dts -O dtb -o ", dut, ".dtb ", dut, ".dts"})) return 0;
    return 1;
  endfunction

  function void dpiconnect_display(int inst);
    if(inst >= 10) return;
    $write("\n############################################################\n");
    $write("# MI32 Device %0d\n", inst);
    $write("############################################################\n");
    $write("Basic info:\n");
    $write("    board = %s\n", mi32_info[inst].board_name);
    $write("    design = %s\n", mi32_info[inst].design_name);
    $write("    identification = sw:0x%08x hw:0x%08x\n", mi32_info[inst].design_id, mi32_info[inst].design_hw_id);
    $write("\nComponents:\n");
    for(int i=0; i<mi32_comps[inst].size(); i++) begin
      $write("    %s #%0d - version=%0d.%0d, space=0x%08x-0x%08x\n", mi32_comps[inst][i].name, mi32_comps[inst][i].index, mi32_comps[inst][i].version>>16, mi32_comps[inst][i].version&'hffff, mi32_comps[inst][i].space_base, mi32_comps[inst][i].space_base+mi32_comps[inst][i].space_size-1);
    end
    $write("############################################################\n\n");
  endfunction

  function void dpiconnect_devicetree_display(int inst);
    integer dts;
    string dut, line;
    if(inst >= 10) return;
    dut = {"DeviceTree-dut", $sformatf("%0d",inst)};
    $write("\n############################################################\n");
    $write("# MI32 Device %0d (DeviceTree)\n", inst);
    $write("############################################################\n");
    dts = $fopen({dut, ".dts"}, "r");
    if(dts != 0) begin
      while($fgets(line, dts))
        $write(line);
    end
    $write("############################################################\n\n");
  endfunction

  function int dpiinfo(int unsigned inst, output dpi_device_info di);
    if(inst >= 10 || mi32[inst] == null) begin
      $write("\ndpiinfo error: accessing uninitialized MI32 interface!!!\n");
      return -1;
    end
    di = mi32_info[inst];
    return 0;
  endfunction;

  function int dpicomponent(int unsigned inst, int unsigned index, output dpi_device_component_info ci);
    if(inst >= 10 || mi32[inst] == null) begin
      $write("\ndpicomponent error: accessing uninitialized MI32 interface!!!\n");
      return -1;
    end
    if(mi32_comps[inst].size() <= index)
      return -1;
    ci = mi32_comps[inst][index];
    return 0;
  endfunction;

  task dpiwrite(int unsigned ifc, int unsigned address, int unsigned value);
    if(mi32[ifc] == null) begin
      $write("\ndpiwrite error: interface #%0d not connected!!!\n", ifc);
      $stop();
    end
    mi32[ifc].cb.ADDR <= address;
    mi32[ifc].cb.DWR  <= value;
    mi32[ifc].cb.WR   <= 1;
    @(mi32[ifc].cb);
    waitForArdy(ifc);
    mi32[ifc].cb.WR   <= 0;
  endtask

  task dpiread(int unsigned ifc, int unsigned address, output int unsigned value);
    if(mi32[ifc] == null) begin
      $write("\ndpiread error: interface #%0d not connected!!!\n", ifc);
      $stop();
    end
    mi32[ifc].cb.ADDR <= address;
    mi32[ifc].cb.RD   <= 1;
    @(mi32[ifc].cb);
    waitForArdy(ifc);
    mi32[ifc].cb.RD   <= 0;
    waitForDrdy(ifc);
    value = mi32[ifc].cb.DRD;
  endtask

  task dpiwait(int unsigned ifc, int unsigned cycles);
    if(mi32[ifc] == null) begin
      $write("\ndpiwait error: interface #%0d not connected!!!\n", ifc);
      $stop();
    end
    for(int unsigned i=0; i<cycles; i++)
        @(mi32[ifc].cb);
  endtask

  task waitForArdy(int unsigned ifc);
    for(int unsigned c = 0; c < ARDY_MAX_WAIT; c++)
        if(mi32[ifc].cb.ARDY)
            return;
        else
            @(mi32[ifc].cb);
    $write("\nDPI%0d error: waiting too long for ARDY!!!\n", ifc);
    $stop();
  endtask

  task waitForDrdy(int unsigned ifc);
    for(int unsigned c = 0; c < DRDY_MAX_WAIT; c++)
        if(mi32[ifc].cb.DRDY)
            return;
        else
            @(mi32[ifc].cb);
    $write("\nDPI%0d error: waiting too long for DRDY!!!\n", ifc);
    $stop();
  endtask

  export "DPI-C" function dpiinfo;
  export "DPI-C" function dpicomponent;
  export "DPI-C" task dpiread;
  export "DPI-C" task dpiwrite;
  export "DPI-C" task dpiwait;
  import "DPI-C" context task dpicall(string name, string params, output int retval);
endpackage
