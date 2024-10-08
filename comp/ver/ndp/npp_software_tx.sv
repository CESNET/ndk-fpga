/*!
 * \file       npp_software_tx.sv
 * \brief      NPP TX software: packet controllers
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

// --------------------------------------------------------------------------
// -- DMA TX module software class
// --------------------------------------------------------------------------

class NppTxSoftware #(int pChannels) extends NppSoftware #(pChannels);

   /* Constants */
   const integer STATUS_STOPPED     = 1;
   const integer STATUS_RUNNING     = 2;
   const integer STATUS_STOPPING    = 3;

   // Override global parameter
   //const integer SW_BUFFER_SIZE     = 1048576 / 4;
   const integer DESC_COUNT         = SW_BUFFER_SIZE / PAGE_SIZE;

   /* Main variables */
   DriverCbs   cbs[$];
   tTransMbx   transMbx;

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size, tTransMbx transMbx);
      super.new(inst, mi, ram, buff_size, page_size);
      this.transMbx = transMbx;
   endfunction

   function void writeDescriptor(int channel, int descIndex, int dataAddress, int descLength, int eop, int desc_type);
      longint descAddress = baseDesc[channel] + 8*descIndex;
      longint descData;
      byte unsigned data [] = new[8];

      if (desc_type==0) begin
         descData = ((descLength & (2**16-1)) << 46) | (dataAddress & (2**30-1));
         if (!eop)
            descData |= (1 << 45);
      end else if (desc_type==1) begin
         descData = (dataAddress >> 30);
         descData |= (1 << 62);
      end else
          $error("Icorrect descriptor type passed.\n");

//      $write("DMA TX%02d : generating descriptor type %d on address 0x%x\n", channel, desc_type, descAddress);
//      $write("             data addr:   0x%x\n", dataAddress);
//      $write("             data length: 0x%x\n", descLength);
//      $write("             eop:         %d\n", eop);
//      $write("             descriptor:  0x%x\n", descData);

      {<<byte{data}} = descData;
      ram.write(descAddress, 8, data);
   endfunction

   function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
   endfunction

   task startController(int channel);
      resetHwPtr(channel);
      hwPtr[channel]          = 0;
      swPtr[channel]          = 0;

      lastDescAddr[channel] = 0;
      firstDesc[channel] = 1;

      miModule.setSwPointer   (channel, 1, swPtr[channel]);
      miModule.setBufferSize  (channel, 1, DESC_COUNT);
      miModule.setTimeout     (channel, 1, 1024);
//    miModule.setIntPointer  (channel, 1, channel*16+1);
      miModule.setMaxRequest  (channel, 1, 512);
      miModule.setDescBase    (channel, 1, baseDesc[channel]);
      miModule.setUpdateBase  (channel, 1, baseUpdate[channel]);

      if (verbosity)
         $write("DMA TX%d start\n", channel);
      miModule.startController(channel, 1);
      status[channel]         = STATUS_RUNNING;
   endtask

   task stopController(int channel);
      int ctrlStatus;
      int hwPtrRam;
      int hwPtrReg;

      status[channel] = STATUS_STOPPING;
      if (verbosity)
         $write("DMA TX%02d stop request\n", channel);

      miModule.stopController(channel, 1);

      do begin
            #(TICK);
         miModule.getStatus(channel, 1, ctrlStatus);
      end while((ctrlStatus & 8'h01) != 8'h00);

      miModule.getHwPointer(channel, 1, hwPtrReg);
      do begin
            #(TICK);
         hwPtrRam = getHwPtr(channel);
      end while(hwPtrReg != hwPtrRam);

      status[channel] = STATUS_STOPPED;
      if (verbosity)
         $write("DMA TX%02d stop request done\n", channel);
   endtask

   task run();
      int channel;
      string label;
      Transaction to;
      FrameLinkUPTransaction transaction;

      while(enabled) begin
         transaction = new;
         transMbx.get(to);
         $cast(transaction,to);

         do begin
                #(TICK);
            channel = $urandom_range(pChannels-1);
         end while(status[channel] != STATUS_RUNNING);

         transaction.channel = channel;

         #(0);
         if(enabled) begin
            label = $sformatf( "Monitor%0d", channel);
            $cast(to, transaction);
            foreach (cbs[channel]) cbs[channel].pre_tx(to, label);
            putTransaction(transaction);
            foreach (cbs[channel]) cbs[channel].post_tx(to, label);
         end
      end
   endtask : run

   function int getFreeSpace(int channel);
      hwPtr[channel] = getHwPtr(channel);
      getFreeSpace = DESC_COUNT - ((swPtr[channel] - hwPtr[channel]) % DESC_COUNT);
   endfunction : getFreeSpace;

   task putTransaction(FrameLinkUPTransaction tr);
      int channel;
      int unsigned size;
      byte unsigned partData[];
      longint partAddress;
      longint partSize;
      longint restSize;
      int partCount;
      longint head;
      longint partOffset;
      longint dataOffset;
      int eop;

      size     = tr.data.size;
      channel  = tr.channel;

//      offset = $urandom_range(512);
//      address = baseBuffer[channel] + PAGE_SIZE*swPtr[channel] + offset;
//      data = new[size];
//      for(int i = 0; i < tr.data.size; i++) begin
//         data[i] = tr.data[i];
//      end

      restSize = size;
      head = 0;
      dataOffset = 0;
      partCount = 0;
      if (verbosity)
         $write("TX %02d: new Packet!! size: %x\n",channel,size);
      while (restSize>0) begin
         partOffset = $urandom_range(PAGE_SIZE-1);
         partSize = $urandom_range(restSize,restSize/2);

         // check minimum part size
         if (partSize==0) begin
            partSize = 1;
         end

         // check descriptor space overflow in PAGE_SIZE*1.5 space
         if (head+partOffset+restSize>=PAGE_SIZE*1.5) begin
            partOffset = PAGE_SIZE*1.5-head-restSize;
            partSize = restSize;
         end

//			partOffset = 0;      // force offset
//         partSize = restSize; // force one descriptor per packet

         head = head + partOffset;
         partAddress = head + baseBuffer[channel] + PAGE_SIZE*1.5*swPtr[channel];

         partData = new[partSize];
         //$write("part data top:\n");
         for (int i=0; i<partSize;i++) begin
            partData[i] = tr.data[i+dataOffset];
         //   if (i<64) begin
         //      $write("%02x ",partData[i]);
         //   end
         end
         //$write("\npart data tail:\n");
         //for (int i=0;i<partSize;i++) begin
         //   if (i>partSize-64) begin
         //      $write("%02x ",partData[i]);
         //   end
         //end
         //$write("\n");

         if (verbosity)
            $write("TX %02d:    new descriptor: part %02d, address %x, size %x, offset %x, head %x, rest size %x, data offset %x, type",channel,partCount+1,partAddress,partSize,partOffset,head,restSize-partSize,dataOffset);

         ram.write(partAddress, partSize, partData);

         eop = (partSize==restSize);
         assert(randomize());
         // ((        top 34 bits differ from previous        ) || ( random  ) || (   the first one  ))
         if ((partAddress >> 30)!=(lastDescAddr[channel] >> 30) || (type1Desc) || (firstDesc[channel])) begin
            writeDescriptor(channel,swPtr[channel]+partCount,partAddress,partSize,eop,1);
            partCount = partCount + 1;
            if (verbosity)
               $write(" 01 and");
         end
         writeDescriptor(channel,swPtr[channel]+partCount,partAddress,partSize,eop,0);
         partCount = partCount + 1;
         if (verbosity)
            $write(" 00\n");

         // update 'previous' address
         lastDescAddr[channel] = partAddress;
         firstDesc[channel] = 0;

         dataOffset = dataOffset + partSize;
         head = head + partSize;
         restSize = restSize - partSize;
      end

//      root.writeData(address, size, data);
//      writeDescriptor(channel, swPtr[channel], address, size);

      /* Wait until packet fits in buffer. Leave at least 1 descriptor space free */
      while(getFreeSpace(channel) <= partCount+1) begin
            #(TICK);
      end

      swPtr[channel] = (swPtr[channel] + partCount) % DESC_COUNT;
      miModule.setSwPointer(channel, 1, swPtr[channel]);

   endtask

   task stopControllers();
      int channel;
      while(enabled) begin
         assert(randomize());
         repeat(stopDelay)
                #(TICK);

         channel = $urandom_range(pChannels-1);
         if(status[channel] == STATUS_RUNNING) begin
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

endclass
