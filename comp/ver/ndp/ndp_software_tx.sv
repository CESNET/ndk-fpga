/*!
 * \file       ndp_software_tx.sv
 * \brief      NDP TX software
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

// --------------------------------------------------------------------------
// -- DMA TX module software class
// --------------------------------------------------------------------------

class NdpTxSoftware #(int pChannels) extends NdpSoftware #(pChannels);

   /* Status constants */
   const integer STATUS_STOPPED     = 1;
   const integer STATUS_RUNNING     = 2;
   const integer STATUS_STOPPING    = 3;
   const integer STATUS_FILLING     = 4;

   DriverCbs   cbs[$];
   tTransMbx   transMbx;

   int unsigned pendingPtr[];

   semaphore chanLock[];

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size, tTransMbx transMbx);
      super.new(inst, mi, ram, buff_size, page_size);
      this.transMbx = transMbx;

      pendingPtr = new[pChannels];
      chanLock   = new[pChannels];
      for (int channel = 0; channel < pChannels; channel++) begin
         pendingPtr[channel] = 0;
         chanLock[channel] = new(1);
      end

   endfunction

   function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
   endfunction

   task startController(int channel);
      resetHwPtr(channel);

      hwPtr[channel]          = 0;
      swPtr[channel]          = 0;
      pendingPtr[channel]     = 0;

      miModule.setSwPointer   (channel, 1, pendingPtr[channel]);
      miModule.setBufferSize  (channel, 1, SW_BUFFER_SIZE);
      miModule.setTimeout     (channel, 1, 1024);
//    miModule.setIntPointer  (channel, 1, channel*16+1);
      miModule.setMaxRequest  (channel, 1, 512);
      miModule.setDescBase    (channel, 1, baseDescPtr[channel]);
      miModule.setUpdateBase  (channel, 1, baseUpdate[channel]);

      if (!setDisable) begin
         if (verbosity)
            $write("DMA TX%02d start\n", channel);
         status[channel]         = STATUS_RUNNING;
         miModule.startController(channel, 1);
      end
   endtask

   task stopController(int channel);
      int ctrlStatus;
      int hwPtrRam;
      int hwPtrReg;

      if (pendingPtr[channel] != swPtr[channel]) begin
         pendingPtr[channel] = swPtr[channel];
         miModule.setSwPointer(channel, 1, pendingPtr[channel]);
      end

      status[channel] = STATUS_STOPPING;

      /* depracated
      if (verbosity)
         $write("DMA TX%02d stop request: waiting for buffer empty status\n", channel);
      do begin
         for(int i=0; i<16; i++) @(miModule.mi.cb);
         miModule.getStatus(channel, 1, ctrlStatus);
      end while((ctrlStatus & 8'h18) != 8'h10);
      */

      if (verbosity)
         $write("DMA TX%02d stop request: sending stop command\n", channel);
      miModule.stopController(channel, 1);

      if (verbosity)
         $write("DMA TX%02d stop request: waiting for stopped status\n", channel);
      /* Wait while status_reg:running flag active */
      do begin
         for(int i=0; i<16; i++)
               #(TICK);
         miModule.getStatus(channel, 1, ctrlStatus);
      end while((ctrlStatus & 8'h01) != 8'h00);

      if (verbosity)
         $write("DMA TX%02d stop request: waiting for HW pointer value 0x%x\n", channel, swPtr[channel]);
      do begin
         for(int i=0; i<16; i++)
               #(TICK);
         miModule.getHwPointer(channel, 1, hwPtrReg);
      end while(hwPtrReg != swPtr[channel]);

      miModule.getHwPointer(channel, 1, hwPtrReg);
      if (verbosity)
         $write("DMA TX%02d stop request: waiting for RAM pointer value 0x%x\n", channel, hwPtrReg);
      do begin
         for(int i=0; i<16; i++)
               #(TICK);
         hwPtrRam = getHwPtr(channel);
      end while(hwPtrReg != hwPtrRam);

      status[channel] = STATUS_STOPPED;
      if (verbosity)
         $write("DMA TX%02d stop request: done\n", channel);
   endtask

   task run();
      int status_free = 0;
      int channel;
      string label;
      Transaction to;
      FrameLinkUPTransaction transaction;

      fork
         updateSwPointers();
      join_none;

      while (enabled) begin
         transaction = new;
         if (transMbx.try_get(to)) begin
            $cast(transaction,to);

            do begin
               if (status_free > 0)
                  chanLock[channel].put();
               #(TICK);
               channel = $urandom_range(pChannels-1);
               status_free = chanLock[channel].try_get();
            end while(status_free <= 0 || status[channel] != STATUS_RUNNING);

            transaction.channel = channel;

            status[channel] = STATUS_FILLING;
            #(0);
            if (enabled) begin
               label = $sformatf( "Monitor%0d", channel);
               $cast(to, transaction);
               foreach (cbs[channel]) cbs[channel].pre_tx(to, label);
               putTransaction(transaction);
               foreach (cbs[channel]) cbs[channel].post_tx(to, label);
            end
            status[channel] = STATUS_RUNNING;
            chanLock[channel].put();
         end else begin
            #(TICK);
         end
      end
   endtask

   task updateSwPointers();
      int unsigned swPtr;
      while (enabled) begin
         for(int i=0; i<32; i++)
               #(TICK);

         for (int channel = 0; channel < pChannels; channel++) begin
            swPtr = this.swPtr[channel];
            if (pendingPtr[channel] != swPtr) begin
               pendingPtr[channel] = swPtr;
               miModule.setSwPointer(channel, 1, pendingPtr[channel]);
            end
         end
      end
   endtask

   function int getFreeSpace(int channel);
      hwPtr[channel] = getHwPtr(channel);
      getFreeSpace = SW_BUFFER_SIZE - ((swPtr[channel] - hwPtr[channel]) % SW_BUFFER_SIZE);
   endfunction

   task putTransaction(FrameLinkUPTransaction tr);
      int part;
      int channel;
      int unsigned ndpSize;
      shortint unsigned size;
      byte unsigned data[];

      /* Add 8B SZE header and align */
      size = tr.data.size + 8;
      ndpSize = ((size + 7) / 8) * 8;
      channel = tr.channel;

      /* Wait until packet fits in buffer. Leave at least 1B space free */
      while(getFreeSpace(channel) <= ndpSize) begin
        #(TICK);
      end

      /* Add 8B SZE header with exact size and copy data */
      data = new[ndpSize];
      data[0:1] = {<<byte{size}};
      for (int i = 0; i < tr.data.size; i++) begin
         data[i + 8] = tr.data[i];
      end

      /* If it's a buffer turnover, Write data to RAM in two segments */
      part = size >= SW_BUFFER_SIZE - swPtr[channel] ? SW_BUFFER_SIZE - swPtr[channel] : size;
      ram.write(baseBuffer[channel] + swPtr[channel], part, data);
      if (size > part)
         ram.writeFromOffset(baseBuffer[channel], size - part, part, data);

      swPtr[channel] = (swPtr[channel] + ndpSize) % SW_BUFFER_SIZE;
   endtask

   task setDisabled();
      setDisable = 1;
      repeat (64)
        #(TICK);
      fork begin
         for (int ch = 0; ch < pChannels; ch++) begin
            chanLock[ch].get();
            if (status[ch] == STATUS_RUNNING)
               stopController(ch);
            chanLock[ch].put();
         end
         enabled = 0;
      end join_none;
   endtask

   virtual task stopControllers();
      int channel;
      while (enabled) begin
         assert(randomize());
         repeat(stopDelay)
             #(TICK);

         channel = $urandom_range(pChannels-1);
         chanLock[channel].get();
         if (status[channel] == STATUS_RUNNING) begin
            fork begin
               automatic int j = channel;
               stopController(j);
               chanLock[channel].put();
               repeat (insideStopDelay)
                  #(TICK);
               chanLock[channel].get();
               if (!setDisable)
                  startController(j);
               chanLock[channel].put();
            end join_none;
         end
      end
   endtask

endclass
