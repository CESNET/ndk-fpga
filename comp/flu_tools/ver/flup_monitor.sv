/*
 * flup_monitor.sv: FrameLinkUnaligned Plus Monitor
 * Copyright (C) 2011 CESNET
 * Author(s): Jan Kucera <jan.kucera@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */


/**
 * FrameLinkUnaligned Plus Monitor.
 * This class is responsible for creating transaction objects from
 * FrameLinkUnaligned interface signals.
 * After the transaction is received it is sent
 * by callback to processing units (typicaly scoreboard).
 * Unit must be enabled
 * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
 * function call.
 */
class FrameLinkUPMonitor #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3, int pHdrWidth=128, int pChanWidth=4) extends Monitor;

   // -- Private Class Atributes --

   //! Data from the first word of the new trans.
   byte unsigned interframe_aux[];
   //! Header from the new trans.
   byte unsigned interframe_header[pHdrWidth/8];
   //! Channel from the new trans.
   int interframe_channel;

   //! SOP_POS of the new transaction
   int     last_sop_pos;
   //! New transaction has already started
   bit     started;
   //! Interface pointer
   virtual iFrameLinkUPTx#(pDataWidth,pEopWidth,pSopWidth,pHdrWidth,pChanWidth).monitor sw;

   // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param flu Receive interface
    */
   function new(string inst, virtual iFrameLinkUPTx#(pDataWidth,pEopWidth,pSopWidth,pHdrWidth,pChanWidth).monitor sw);

      super.new(inst);              // Call super constructor

      this.enabled     = 0;         // Monitor is disabled by default
      this.busy        = 0;         // Monitor is not busy by default
      this.started     = 0;         // No transaction in progress
      this.sw          = sw;        // Store pointer interface
      this.inst        = inst;      // Store driver identifier
   endfunction

   /**
    * Run Monitor.
    * Receive transactions and send them for processing by callback.
    */
   task run();
      FrameLinkUPTransaction transaction;
      Transaction tr;

      //$write($time, " Monitor_run start.\n");

      while (enabled) begin              // Repeat in forewer loop
         transaction = new;               // Create new transaction object
         $cast(tr, transaction);

         // Call transaction preprocesing, if is available
         foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

         // Receive Transaction
         receiveTransaction(transaction); // Receive Transaction

         // Necessary for not calling callback after monitor disabling
         if (!enabled) break;

         //$write($time, " :\n");
         //transaction.display(inst);

         #(0); // Necessary for not calling callback before driver

         // Call transaction postprocesing, if is available
         foreach (cbs[i]) cbs[i].post_rx(tr, inst);

         // Monitor received transaction and is not busy
         busy = 0;
      end
      //$write($time, " Monitor_run end.\n");
   endtask : run

   /*
    * Wait for SOP and SRC_RDY.
    */
   task waitForSOP();
      //$write($time, " waitForSOP start.\n");
      do begin
         if ((!sw.monitor_cb.SOP) ||
             (!sw.monitor_cb.SRC_RDY) ||
             (!sw.monitor_cb.DST_RDY))
            @(sw.monitor_cb);
         if (!enabled) begin
            //$write($time, " waitForSOP return.\n");
            return;
         end
      end while (!(sw.monitor_cb.SOP &&
                   sw.monitor_cb.SRC_RDY &&
                   sw.monitor_cb.DST_RDY)); //Detect Start of Packet
      //$write($time, " waitForSOP end.\n");
  endtask : waitForSOP

   /**
    * Wait for DST_RDY and SRC_RDY.
    */
   task waitForDstRdy();
      do begin
         if ((!sw.monitor_cb.DST_RDY) || (!sw.monitor_cb.SRC_RDY))
            @(sw.monitor_cb);
      //Detect Destination Ready
      end while ((!sw.monitor_cb.DST_RDY) || (!sw.monitor_cb.SRC_RDY));
  endtask : waitForDstRdy

   /**
    * Receive FrameLinkUnaligned transaction to tr object.
    * @param transaction Output transaction.
    */
   task receiveTransaction(FrameLinkUPTransaction transaction);
      byte unsigned aux[];
      byte unsigned header[pHdrWidth/8];
      logic [3:0] channel;

      int sopstep = pDataWidth/(2**pSopWidth); // in bits
      int thisword_sop; // Where should we start reading (in bytes)
      int thisword_eop; // Where should we end reading (in bytes)
      bit shared;

      //$write($time, " recieveTransaction start.\n");

      if (!started) begin
         // Start receiving new transaction
         waitForSOP(); // Wait for SOP
         if (!enabled) begin
            //$write($time, " recieveTransaction return.\n");
            return;
         end

         // Get header word byte by byte
         for (int i = 0; i < pHdrWidth/8; i++) begin
            header[i] = sw.monitor_cb.HEADER[8*i +: 8];
         end;  // for

         // Get channel
         channel = sw.monitor_cb.CHANNEL;

         last_sop_pos = sw.monitor_cb.SOP_POS;
         started = 1;
      end
      else begin
         // Continue receiving transaction
         header = interframe_header;
         channel = interframe_channel;

         aux = new[interframe_aux.size()](interframe_aux);
         interframe_aux.delete();
      end;

      // Monitor receives transaction
      busy = 1;

      // -------- Process data in Frame word by word -----------
      do begin
         waitForDstRdy();

         // Detect word that contains pieces of two frames
         if (sw.monitor_cb.SOP && sw.monitor_cb.EOP &&
             sw.monitor_cb.SOP_POS*sopstep > sw.monitor_cb.EOP_POS*8)
            shared = 1;
         else
            shared = 0;

         // Determine where the word starts
         if (sw.monitor_cb.SOP && !shared)
            // If the first word is shared, then it was already read.
            // If it is not shared, read it now.
            thisword_sop = last_sop_pos*sopstep/8;
         else
            // If there is no SOP in this word OR this word is shared
            thisword_sop = 0;

         // Determine where the word ends
         if (sw.monitor_cb.EOP)
            thisword_eop = sw.monitor_cb.EOP_POS;
         else
            thisword_eop = (pDataWidth/8)-1;

         // Get data word byte by byte
         for (int i = thisword_sop; i <= thisword_eop; i++) begin
            aux = new[aux.size + 1](aux); // Enlarge aux array
            aux[aux.size-1] =
               sw.monitor_cb.DATA[8*i +: 8];
         end;  // for


         // Detect End of Frame
         if (!sw.monitor_cb.EOP) begin // No EOP
            @(sw.monitor_cb);
         end
         else begin // Yes EOP
            started = 0;
            if (!sw.monitor_cb.SOP) begin // No SOP
               // No new frame here together with the end of this one
            end
            else begin  // EOP and SOP
               // New frame also begins here
               last_sop_pos = sw.monitor_cb.SOP_POS;

               // New transaction starts only if SOP is after EOP
               if (last_sop_pos*sopstep/8 > sw.monitor_cb.EOP_POS)
                  started = 1;

               // Get header word byte by byte
               for (int i = 0; i < pHdrWidth/8; i++) begin
                  interframe_header[i] = sw.monitor_cb.HEADER[8*i +: 8];
               end;  // for

               // Get channel
               interframe_channel = sw.monitor_cb.CHANNEL;

               // Get data word byte by byte
               interframe_aux = new[(pDataWidth-last_sop_pos*sopstep)/8];
               for (int i=0; i<(pDataWidth-thisword_sop*sopstep)/8; i++) begin
                  interframe_aux[i] =
                     sw.monitor_cb.DATA[last_sop_pos*sopstep+8*i +: 8];
               end;  // for
            end;

            break;
         end // else
      end while (1);

      // --------- Store received data into transaction -------------
      transaction.data = new [aux.size];
      transaction.data = aux;
      transaction.header = new [pHdrWidth/8];
      transaction.header = header;
      transaction.channel = channel;
      aux.delete();

      @(sw.monitor_cb);

      //$write($time, " recieveTransaction end.\n");

   endtask : receiveTransaction

endclass: FrameLinkUPMonitor
