/*!
 * \file       ndp_software_rx.sv
 * \brief      NDP RX software
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

// --------------------------------------------------------------------------
// -- DMA RX module software class
// --------------------------------------------------------------------------

class NdpRxSoftware #(int pChannels) extends NdpSoftware #(pChannels);

   /* Status constants */
   const integer STATUS_STOPPED     = 1;
   const integer STATUS_RUNNING     = 2;
   const integer STATUS_STOPPING    = 3;

   /* Main variables */
   MonitorCbs  cbs[$];

   function new (string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size);
      super.new(inst, mi, ram, buff_size, page_size);
   endfunction

   function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
   endfunction

   task startController(int channel);
      resetHwPtr(channel);

      swPtr[channel]          = 0;
      hwPtr[channel]          = 0;

      miModule.setSwPointer   (channel, 0, 0);
      miModule.setBufferSize  (channel, 0, SW_BUFFER_SIZE);
      miModule.setTimeout     (channel, 0, 8192);
//    miModule.setIntPointer  (channel, 0, channel*16+1);
      miModule.setMaxRequest  (channel, 0, 256);
      miModule.setDescBase    (channel, 0, baseDescPtr[channel]);
      miModule.setUpdateBase  (channel, 0, baseUpdate[channel]);

      if (verbosity)
         $write("DMA RX%02d start\n", channel);
      status[channel]         = STATUS_RUNNING;
      miModule.startController(channel, 0);
//    miModule.startControllerWithDiscard(channel, 0);
   endtask

   task stopController(int channel);
      int ctrlStatus;
      int hwPtrRam;
      int hwPtrReg;

      status[channel] = STATUS_STOPPING;
      if (verbosity)
         $write("DMA RX%02d stop request\n", channel);
      miModule.stopController(channel, 0);

      do begin
         for(int i=0; i<16; i++)
               #(TICK);
         miModule.getStatus(channel, 0, ctrlStatus);
      end while((ctrlStatus & 1) != 0);

      miModule.getHwPointer(channel, 0, hwPtrReg);
      do begin
            #(TICK);
      end while (hwPtrReg != swPtr[channel]);

      if (verbosity)
         $write("DMA RX%02d stop request done, hwPtr %x\n", channel, hwPtrReg);
      status[channel] = STATUS_STOPPED;
   endtask

   task run();
      int channel;
      string label;
      Transaction to;
      FrameLinkUPTransaction transaction;

      while(enabled) begin
         transaction = new;
         getTransaction(transaction);
         channel = transaction.channel;
         label = $sformatf( "Monitor%0d", channel);
         #(0);
         if (enabled) begin
            $cast(to, transaction);
            foreach (cbs[channel]) cbs[channel].pre_rx(to, label);

            foreach (cbs[channel]) cbs[channel].post_rx(to, label);
         end
      end
   endtask

   virtual task stopControllers();
      int channel;
      while (enabled) begin
         assert(randomize());
         repeat (stopDelay)
               #(TICK);

         channel = $urandom_range(pChannels-1);
         if (status[channel] == STATUS_RUNNING) begin
            fork begin
               automatic int j = channel;
               stopController(j);
               repeat (insideStopDelay)
               #(TICK);
               if (!setDisable)
                  startController(j);
            end join_none;
         end
      end
   endtask

   task setDisabled();
      setDisable = 1;
      repeat (64)
            #(TICK);
      fork begin
         for (int ch = 0; ch < pChannels; ch++)
            if(status[ch] == STATUS_RUNNING)
               stopController(ch);
         enabled = 0;
      end join_none;
   endtask

   task getTransaction(FrameLinkUPTransaction tr);
      int part;
      int channel;
      int hwPtr;
      int swPtr;

      byte unsigned data[];
      byte unsigned szeHeader[2];
      int unsigned ndpSize;
      shortint unsigned size;

      while (enabled) begin
         for (channel = 0; channel < pChannels; channel++) begin
            if (status[channel] == STATUS_STOPPED)
               continue;

            this.hwPtr[channel] = getHwPtr(channel);
            hwPtr = this.hwPtr[channel];
            swPtr = this.swPtr[channel];

            if (swPtr != hwPtr) begin
               ram.read(baseBuffer[channel] + swPtr, 2, szeHeader);
               {<<byte{size}} = szeHeader;
               ndpSize = ((size + 7) / 8) * 8;

               if (verbosity > 1)
                  $write("New data for DMA Channel %d on address: %x, buffer size: %x, packet size: %x | end: %x, str: %x -> %x\n", channel, baseBuffer[channel] + swPtr, (hwPtr - swPtr) % SW_BUFFER_SIZE, size, hwPtr, swPtr, swPtr + ndpSize);
               if (size == 0) begin
                  $write("Zero segsize\n");
                  $stop();
                  return;
               end
               data = new[size];

               part = size >= SW_BUFFER_SIZE - swPtr ? SW_BUFFER_SIZE - swPtr : size;
               ram.read(baseBuffer[channel] + swPtr, part, data);
               if (size > part)
                  ram.readToOffset(baseBuffer[channel], size - part, part, data);

               swPtr = (swPtr + ndpSize) % SW_BUFFER_SIZE;
               this.swPtr[channel] = swPtr;
               miModule.setSwPointer(channel, 0, swPtr);

               tr.data     = data;
               tr.header   = new[16];
               tr.channel  = channel;
               return;
            end
         end
           #(TICK);
      end
   endtask

endclass
