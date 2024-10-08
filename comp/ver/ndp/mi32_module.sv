/*
 * mi32_module.sv: MI32 module for DMA
 * Copyright (C) 2013 CESNET
 * Author: Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_mi32_pkg::*;

// --------------------------------------------------------------------------
// -- MI32 Module Class
// --------------------------------------------------------------------------

class Mi32DmaBaseModule;

   // -- Private Class Atributes --

   //! Module identification
   string       inst;
   //! Module is enabled
   bit          enabled;

   int verbosity = 0;

   const integer REG_CONTROL     = 0;
   const integer REG_STATUS      = 1;
   const integer REG_SWPOINTER   = 2;
   const integer REG_HWPOINTER   = 3;
   const integer REG_BUFFER      = 4;
   const integer REG_INTERRUPT   = 5;
   const integer REG_TIMEOUT     = 6;
   const integer REG_MAXREQUEST  = 7;
   const integer REG_DESCBASE    = 8;
   const integer REG_UPDATEBASE  = 10;

    function new (string inst);
        this.enabled = 0;
        this.inst    = inst;
    endfunction

    virtual function logic[31:0] getAddr(integer register, integer channel, integer dir);
    endfunction

    virtual task setEnabled();
    endtask

    virtual task setDisabled();
    endtask

    virtual task writeRegBe(int register, int channel, int dir, int data,int byte_enable);
    endtask

    virtual task writeReg(int register, int channel, int dir, int data);
    endtask

    virtual task readReg(int register, int channel, int dir, output int data);
    endtask

    task startControllerWithDiscard(int channel, int dir);
        writeReg(REG_CONTROL, channel, dir, 3);
    endtask

    task startController(int channel, int dir);
        writeReg(REG_CONTROL, channel, dir, 1);
    endtask

    task stopController(int channel, int dir);
        writeReg(REG_CONTROL, channel, dir, 0);
    endtask

    task setBufferSize(int channel, int dir, int size);
        writeReg(REG_BUFFER, channel, dir, size-1);
    endtask

    task setTimeout(int channel, int dir, int timeout);
        writeReg(REG_TIMEOUT, channel, dir, timeout);
    endtask

    task setSwPointer(int channel, int dir, int ptr);
        writeReg(REG_SWPOINTER, channel, dir, ptr);
    endtask

    task setIntPointer(int channel, int dir, int ptr);
        writeReg(REG_INTERRUPT, channel, dir, ptr);
    endtask

    task setDescSize(int channel, int dir, int req);
        writeRegBe(REG_MAXREQUEST, channel, dir, req*2**16, 4'b1100);
    endtask

    task setMaxRequest(int channel, int dir, int req);
        writeRegBe(REG_MAXREQUEST, channel, dir, req, 4'b0011);
    endtask

    task setDescBase(int channel, int dir, longint base);
        writeReg(REG_DESCBASE,   channel, dir, base);
        writeReg(REG_DESCBASE+1, channel, dir, base >> 32);
    endtask

    task setUpdateBase(int channel, int dir, longint base);
        writeReg(REG_UPDATEBASE,   channel, dir, base);
        writeReg(REG_UPDATEBASE+1, channel, dir, base >> 32);
    endtask

    task getStatus(int channel, int dir, output int data);
        readReg(REG_STATUS, channel, dir, data);
    endtask

    task getHwPointer(int channel, int dir, output int ptr);
        readReg(REG_HWPOINTER, channel, dir, ptr);
    endtask

endclass
/*!
* \brief MI32 Module Class
*
* This class is responsible for sending and receiving transaction via MI32
* interface. Unit must be enabled by "setEnable()" function call.
* Running can be stoped by "setDisable()" function call.
*/
class Mi32Module extends Mi32DmaBaseModule;
   //! MI32 Driver
   Mi32Driver   miDriver;
   //! MI32 Monitor
   Mi32Monitor  miMonitor;
   //! MI32 interface
   virtual iMi32.tb mi;
   //! Transaction queue
   Mi32Transaction transQue[$];
   //! Response queue
   Mi32Transaction responseQue[$];

   // -- Public Class Methods --

   // ------------------------------------------------------------------------
   //! Constructor
   /*!
    * Creates module object and MI32 driver and monitor object.
    */
   function new (string inst, virtual iMi32.tb mi);
      super.new(inst);
      miDriver  = new("MI32 Driver", null, mi);
      miMonitor = new("MI32 Monitor", mi);

      this.mi      = mi;
   endfunction: new

   function logic[31:0] getAddr(integer register, integer channel, integer dir);
      return register*8'h4 + channel*8'h40 + dir*32'h1000;
   endfunction: getAddr


   // ------------------------------------------------------------------------
   //! Run Module
   /*
    * Get transactions from RAM and send it to scoreboard
    */
   task run();
      Mi32Transaction transaction;

      while (enabled) begin                   // Repeat while enabled
         // Wait while queue is empty
         while (transQue.size()==0) @(mi.cb);

         // Send transaction
         transaction = transQue.pop_front();
         if (transaction.rw == 1)
            miDriver.executeTransaction(transaction);
         else begin
            miMonitor.executeTransaction(transaction);
            responseQue.push_back(transaction);
         end
      end
   endtask : run

   // ------------------------------------------------------------------------
   //! Enable Module
   /*!
    * Enable Module and runs Module process
    */
   task setEnabled();
      enabled = 1; // Module Enabling
      fork
         run();                // Creating module subprocess
      join_none;               // Don't wait for ending
   endtask : setEnabled

   // ------------------------------------------------------------------------
   //! Disable Module
   task setDisabled();
      enabled = 0; // Disable Module
   endtask : setDisabled


   // -- Start Controller ----------------------------------------------------
   //! Start Controller
   /*!
    * Init and start Controller
    * \param channel - channel number
    * \param dir - 0 for rx, 1 for tx direction
    */

   task writeRegBe(int register, int channel, int dir, int data,int byte_enable);
      Mi32Transaction tr = new();

      tr.address = getAddr(register, channel, dir);
      tr.data    = data;
      tr.be      = byte_enable;
      tr.rw      = 1;

      if (verbosity)
         $write("MI32 Write %x => %x\n", tr.data, tr.address);

      transQue.push_back(tr);
   endtask : writeRegBe

   task writeReg(int register, int channel, int dir, int data);
      writeRegBe(register,channel,dir,data,4'b1111);
   endtask : writeReg

   task readReg(int register, int channel, int dir, output int data);
      Mi32Transaction tr = new();

      tr.address = getAddr(register, channel, dir);
      tr.be      = '1;
      tr.rw      = 0;

      transQue.push_back(tr);
      while (responseQue.size()==0 || responseQue[0].address != tr.address)
        @(mi.cb);

      tr = responseQue.pop_front();
      data = tr.data;

      if (verbosity)
         $write("MI32 Read %x <= %x\n", tr.data, tr.address);
   endtask : readReg

endclass : Mi32Module
