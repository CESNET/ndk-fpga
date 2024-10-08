/*!
 * \file       dma_software.sv
 * \brief      Base class for DMA software
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

// --------------------------------------------------------------------------
// -- DMA module software class
// --------------------------------------------------------------------------

class DmaSoftware #(int pChannels);

   time TICK = 5ns;

   /* Main variables */
   string inst;
   Ram         ram;
   Mi32DmaBaseModule  miModule;

   int enabled;

   int verbosity = 0;

   int unsigned swPtr[];
   int unsigned hwPtr[];

   int unsigned status[];
   int setDisable;

   longint unsigned baseBuffer[];
   longint unsigned baseUpdate[];
   longint unsigned baseDesc[];
   longint unsigned baseDescPtr[];
   integer SW_BUFFER_SIZE;
   integer PAGE_SIZE;

   /* Random variables - TODO */
   rand int stopDelay;
      int stopDelayLow             = 2000;
      int stopDelayHigh            = 5000;

   rand int insideStopDelay;
      int insideStopDelayLow       = 500;
      int insideStopDelayHigh      = 2500;

   // -- Constrains --
   constraint cDelays {
      stopDelay         inside { [stopDelayLow:stopDelayHigh] };
      insideStopDelay   inside { [insideStopDelayLow:insideStopDelayHigh] };
   }

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size);
      miModule       = mi;
      this.ram       = ram;
      this.inst      = inst;
      swPtr          = new[pChannels];
      hwPtr          = new[pChannels];
      status         = new[pChannels];
      baseBuffer     = new[pChannels];
      baseUpdate     = new[pChannels];
      baseDesc       = new[pChannels];
      baseDescPtr    = new[pChannels];
      SW_BUFFER_SIZE = buff_size;
      PAGE_SIZE = page_size;

      setDisable     = 0;

      for (int channel = 0; channel < pChannels; channel++) begin
         status[channel] = 0;
      end
   endfunction

   virtual function void initBuffers();
   endfunction


   task resetHwPtr(int channel);
      byte unsigned i[];
      i = new[4];
      {>>{i}} = 0;
      ram.write(baseUpdate[channel], 4, i);
   endtask

   function int getHwPtr(int channel);
      int ptr;
      byte unsigned i[] = new[4];
      ram.read(baseUpdate[channel], 4, i);
      ptr = {<<byte{i}};
      return ptr;
   endfunction

   virtual task startController(int channel);
   endtask

   virtual task stopController(int channel);
   endtask

   virtual task setEnabled();
      enabled = 1;

      for (int channel = 0; channel < pChannels; channel++) begin
         startController(channel);
      end

      fork
         run();
         stopControllers();
      join_none;
   endtask

   virtual task setDisabled();
      enabled = 0;
   endtask

   virtual task run();
   endtask

   virtual task stopControllers();
   endtask

endclass


class NdpSoftware #(int pChannels) extends DmaSoftware #(pChannels);

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size);
      super.new(inst, mi, ram, buff_size, page_size);
   endfunction

   function void writeDescriptor(longint descAddr, longint descData);
      byte unsigned data [] = new[8];

      {<<byte{data}} = descData;
      ram.write(descAddr, 8, data);
   endfunction

   virtual function void initDescriptors(int channel);
      const integer DESC_TYPE_PTR      = 1;
      const integer DESC_AGGR_MAX      = PAGE_SIZE / 4;
      const integer BUFFER_PAGES       = SW_BUFFER_SIZE / PAGE_SIZE;

      int aggregate = 0;
      int descIndex = 0;
      int bufferPageIndex = 0;

      while (bufferPageIndex < BUFFER_PAGES - DESC_AGGR_MAX) begin
         writeDescriptor(baseDesc[channel] + descIndex*8, baseBuffer[channel] + bufferPageIndex*PAGE_SIZE + ((DESC_AGGR_MAX-1) << 1));
         bufferPageIndex += DESC_AGGR_MAX;
         descIndex++;
      end

      /* Last, turn-over and initial descriptors */
      writeDescriptor(baseDesc[channel] + descIndex*8, baseBuffer[channel] + bufferPageIndex*PAGE_SIZE + ((BUFFER_PAGES - bufferPageIndex - 1) << 1));
      descIndex++;
      writeDescriptor(baseDesc[channel] + descIndex*8, baseDesc[channel] + DESC_TYPE_PTR);
      writeDescriptor(baseDescPtr[channel],            baseDesc[channel] + DESC_TYPE_PTR);
   endfunction

   virtual function void initBuffers();
      for (int channel = 0; channel < pChannels; channel++) begin
         baseDescPtr[channel] = ram.malloc(8);
         baseUpdate [channel] = ram.malloc(8);
      end

      for (int channel = 0; channel < pChannels; channel++)
         baseDesc   [channel] = ram.malloc(PAGE_SIZE, PAGE_SIZE-1);  // TODO
      for (int channel = 0; channel < pChannels; channel++)
         baseBuffer [channel] = ram.malloc(SW_BUFFER_SIZE, SW_BUFFER_SIZE-1);

      for (int channel = 0; channel < pChannels; channel++)
         initDescriptors(channel);
   endfunction

endclass


class NppSoftware #(int pChannels) extends DmaSoftware #(pChannels);

   const integer DESC_COUNT         = SW_BUFFER_SIZE / PAGE_SIZE;

   longint unsigned lastDescAddr[];
   int firstDesc[];

   rand int type1Desc;
   int type1DescChance = 10; // [%]

   // -- Constrains --
   constraint cType1Desc {
      type1Desc dist { 1'b1 := type1DescChance,
                       1'b0 := 100-type1DescChance
                     };
   }

   function new(string inst, Mi32DmaBaseModule mi, Ram ram, integer buff_size, integer page_size);
      super.new(inst, mi, ram, buff_size, page_size);
      lastDescAddr = new[pChannels];
   endfunction

   virtual function void initBuffers();
      for (int channel = 0; channel < pChannels; channel++) begin
         baseDescPtr[channel] = ram.malloc(8);
         baseUpdate [channel] = ram.malloc(8);
      end

      for(int channel = 0; channel < pChannels; channel++)
         baseDesc   [channel] = ram.malloc(DESC_COUNT*8, DESC_COUNT*8-1);
      for(int channel = 0; channel < pChannels; channel++)
         baseBuffer [channel] = ram.malloc(SW_BUFFER_SIZE*1.5, SW_BUFFER_SIZE*1.5-1);
   endfunction

endclass
