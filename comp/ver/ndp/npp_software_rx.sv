/*!
 * \file       npp_software_rx.sv
 * \brief      NPP RX software: packet controllers
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

// --------------------------------------------------------------------------
// -- DMA RX module software class
// --------------------------------------------------------------------------

class NppRxSoftware #(int pChannels, int DMA_TYPE) extends NppSoftware #(pChannels);

   /* Status constants */
   const integer STATUS_STOPPED     = 0;
   const integer STATUS_RUNNING     = 1;
   const integer STATUS_STOPPING    = 2;

   /* Main variables */
   MonitorCbs  cbs[$];

   int unsigned swPtrPrep[];

   longint unsigned descAddrShifts[][];
   longint unsigned descLengths[][];

   longint unsigned constLengths[];

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size);
      super.new(inst, mi, ram, buff_size, page_size);

      swPtrPrep      = new[pChannels];
      descAddrShifts = new[pChannels];
      descLengths    = new[pChannels];
      constLengths   = new[pChannels];

      for (int channel = 0; channel < pChannels; channel++) begin
         descAddrShifts[channel] = new[DESC_COUNT];
         descLengths[channel] = new[DESC_COUNT];
      end
   endfunction

   function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
   endfunction

   function void writeDescriptor(int channel, int descIndex, int dataAddress, int descLength);
      longint descAddress = baseDesc[channel] + 8*descIndex;
      longint descData = ((descLength & 16'hFFFF) << 48) | (dataAddress & 48'hFFFFFFFFFFFF);
      byte unsigned data [] = new[8];

      {<<byte{data}} = descData;
      ram.write(descAddress, 8, data);
   endfunction

   task startController(int channel);
      if (DMA_TYPE == 3) begin
         constLengths[channel] = $urandom_range(PAGE_SIZE*1, PAGE_SIZE*0.1)/8*8;
      end

      resetHwPtr(channel);

      swPtrPrep[channel]      = 0;
      swPtr[channel]          = 0;
      hwPtr[channel]          = 0;

      miModule.setSwPointer   (channel, 0, 0);
      miModule.setBufferSize  (channel, 0, DESC_COUNT);
      miModule.setTimeout     (channel, 0, 128);
      if (DMA_TYPE == 3) begin
         miModule.setDescSize(channel,0,constLengths[channel]);
      end
//    miModule.setIntPointer  (channel, 0, channel*16+1);
      miModule.setMaxRequest  (channel, 0, 256);
      miModule.setDescBase    (channel, 0, baseDesc[channel]);
      miModule.setUpdateBase  (channel, 0, baseUpdate[channel]);

      if (verbosity)
         $write("DMA RX%02d start\n", channel);
      status[channel]         = STATUS_RUNNING;
      miModule.startController(channel, 0);
      fork
         automatic int j = channel;
         prepareNewDescriptors(j);
      join_none;

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
         #(TICK);
         miModule.getStatus(channel, 0, ctrlStatus);
      end while((ctrlStatus & 1) != 0);

      miModule.getHwPointer(channel, 0, hwPtrReg);
      do begin
         hwPtrRam = getHwPtr(channel);
         #(TICK);
      end while (hwPtrRam != hwPtrReg);
      do begin
         #(TICK);
      end while (hwPtrRam != swPtr[channel]);

      if (verbosity)
         $write("DMA RX%02d stop request done, hwPtr %x\n", channel, hwPtrReg);
      status[channel] = STATUS_STOPPED;
   endtask

   task setDisabled();
      setDisable = 1;
      fork begin
         for (int ch = 0; ch < pChannels; ch++)
            stopController(ch);
         enabled = 0;
      end join_none;
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
         if(enabled) begin
            $cast(to, transaction);
            foreach (cbs[channel]) cbs[channel].pre_rx(to, label);

            foreach (cbs[channel]) cbs[channel].post_rx(to, label);
         end
      end
   endtask

   task getTransaction(FrameLinkUPTransaction tr);
      int channel;
      byte unsigned data[];
      int unsigned size;
      int unsigned offset;
      int unsigned part_size;
      int unsigned rest_size;
      int sw;
      int hw;
      int address;
      int part_address;

      byte unsigned szeHeader[2];
      byte unsigned pacData[64];

      int index = sw;
      longint unsigned descLen = 0;

      while(enabled) begin
         for(channel = 0; channel < pChannels; channel++) begin
            /* Skip stopped channels */
            if(status[channel] == STATUS_STOPPED)
               continue;

            hwPtr[channel] = getHwPtr(channel);
            hw    = hwPtr[channel];
            sw    = swPtr[channel];

            if(hw != sw) begin
               tr.channel  = channel;
               tr.header   = new[16];

               if (verbosity)
                  $write("DMA RX%d: New pointer: %x, %x\n", channel, hw, sw);
               /* Read header with packet length */
               address = baseBuffer[channel] + PAGE_SIZE*1.5*sw + descAddrShifts[channel][sw];
               ram.read(address, 2, szeHeader);
               size = (szeHeader[1] << 8) + szeHeader[0];

               /* TODO: Add check that we have enough filled descriptors */
               if (verbosity)
                  $write("DMA RX%d: New packet on address %x, size: %d | swPtr: %d, hwPtr: %d\n", channel, address, size, sw, hw);

               if (verbosity) begin
                  $write("packet data head:\n");
                  ram.read(address, 64, pacData);
                  for (int i=0;i<2;i++) begin
                     for (int e=0;e<4;e++) begin
                        for (int h=0;h<8;h++) begin
                           $write("%2x ",pacData[i*8*4+e*8+h]);
                        end
                        $write(" ");
                     end
                     $write("\n");
                  end
               end

               if(size == 0) begin
                  $error("DMA RX%d: Zero segsize\n", channel);
                  return;
               end

               data = new[size];

               /* generate new descriptors */
               index = sw;
               descLen = 0;
               rest_size = size;
               offset = 0;
               while(descLen < size) begin
                  part_address = baseBuffer[channel] + PAGE_SIZE*1.5*index + descAddrShifts[channel][index];
                  part_size = descLengths[channel][index];
                  if (rest_size < part_size) begin
                     part_size = rest_size;
                  end;
                  rest_size = rest_size - part_size;

                  ram.readToOffset(part_address, part_size, offset, data);
                  offset = offset + part_size;

                  if (verbosity) begin
                     $write("DMA RX%d:   Packet part on address %x, size: %d\n", channel, part_address, part_size);
                     $write("add: descLen: %x,a  index: %d\n",descLen,index);
                  end
                  descLen = descLen + descLengths[channel][index];

                  index = (index + 1) % DESC_COUNT;
               end;

               if (verbosity)
                  $write("end: descLen: %x, index: %d\n",descLen,index);
               swPtr[channel] = index;

               tr.data = data;
               return;
            end
         end
            #(TICK);
      end
   endtask

   task stopControllers();
      int channel;
      while(enabled) begin
         assert(randomize());
         repeat(stopDelay)
                #(TICK);

         channel = $urandom_range(pChannels-1);
         if(status[channel] == STATUS_RUNNING && !setDisable) begin
            fork begin
               automatic int j = channel;
               stopController(j);
               repeat (insideStopDelay)
                        #(TICK);
               startController(j);
            end join_none;
         end
      end
   endtask

   task prepareNewDescriptors(int channel);
      while (enabled) begin
         integer unsigned addrShift;
         integer unsigned length;
         int increment;
         int index;

         while (status[channel] != STATUS_RUNNING) begin
                #(TICK);
         end

         increment = (DESC_COUNT - 1) - ((swPtrPrep[channel] - swPtr[channel]) % DESC_COUNT);
         increment = $urandom_range(increment);

         if (increment != 0) begin
            while (increment) begin
               index = swPtrPrep[channel];

               if (DMA_TYPE == 3) begin
                  length = constLengths[channel];
               end else begin
                  length = $urandom_range(PAGE_SIZE*1, PAGE_SIZE*0.1)/8*8;
               end
               addrShift = $urandom_range(PAGE_SIZE*1.5-length)/8*8;

               writeDescriptor(channel, index, baseBuffer[channel] + PAGE_SIZE*1.5*index + addrShift, length);

               descAddrShifts[channel][index] = addrShift;
               descLengths[channel][index] = length;

               swPtrPrep[channel] = (index + 1) % DESC_COUNT;
               increment = increment - 1;
            end
            miModule.setSwPointer(channel, 0, swPtrPrep[channel]);
         end

         increment = $urandom_range(5000);
         while(increment) begin
            increment = increment - 1;
                #(TICK);
         end
      end
   endtask

endclass
