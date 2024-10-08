/*
 * flu_monitor.sv: FrameLinkUnaligned Monitor
 * Copyright (C) 2011 CESNET
 * Author(s): Viktor Pus <pus@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */


/**
 * FrameLinkUnaligned Monitor.
 * This class is responsible for creating transaction objects from
 * FrameLinkUnaligned interface signals.
 * After the transaction is received it is sent
 * by callback to processing units (typicaly scoreboard).
 * Unit must be enabled
 * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
 * function call.
 */
class FrameLinkUMonitor #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3)
   extends Monitor;

   // -- Private Class Atributes --
   //! Data from the first word of the new trans.
   byte unsigned interframe_aux[];
   //! SOP_POS of the new transaction
   int     last_sop_pos;
   //! New transaction has already started
   bit     started;
   //! Interface pointer
   virtual iFrameLinkUTx#(pDataWidth,pEopWidth,pSopWidth).monitor flu;

   //! Enable monitoring of the FLU gap
   bit      gapMeasureEn;
   //! Minimimal gap value (in bytes)
   int     minGapVal;
   //! Maximal gap value, if negative - maximal gap can be infinity (in bytes)
   int     maxGapVal;
   //! Actual measured gap (in bytes)
   int     actGapVal;

   // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param flu Receive interface
    */
   function new(string inst,
                virtual iFrameLinkUTx#(pDataWidth,pEopWidth,pSopWidth).monitor
                  flu
               );

      super.new(inst);              // Call super constructor

      this.enabled     = 0;         // Monitor is disabled by default
      this.busy        = 0;         // Monitor is not busy by default
      this.started     = 0;         // No transaction in progress
      this.flu         = flu;       // Store pointer interface
      this.inst        = inst;      // Store driver identifier

      this.gapMeasureEn = 0;        // Don't measure the gap by default
   endfunction

   /**
    * Enable detection of the gap between end and start of the frame
    * @param minGapVal minimal gap value
    * @param maxGapVal maximal gap value, if negative - maximal gap will be set to infinity
    */
   task enableGapDetection(int minGapVal,int maxGapVal);
       this.minGapVal = minGapVal;
       this.maxGapVal = maxGapVal;
       this.actGapVal = -1;
       this.gapMeasureEn = 1;
   endtask

   /**
    * Disable detection of the gap between end and start of the frame
    */
    task disableGapDetection();
        this.gapMeasureEn = 0;
    endtask

   /**
    * Check computed gap value
    */
    task checkGapValue();
        if ( this.gapMeasureEn == 1) begin
            // Gap measuring is enabled, check the measured value
            if (!(this.minGapVal <= this.actGapVal &&  this.maxGapVal >= this.actGapVal &&
                  this.maxGapVal != -1)
                &&
                !(this.minGapVal <= this.actGapVal && this.maxGapVal == -1))
            begin

                $write("Measured gap is out of specified range!\n");
                $write("Gap equals to %d\n",this.actGapVal);
                $stop;
            end
        end
    endtask

   /**
    * Run Monitor.
    * Receive transactions and send them for processing by callback.
    */
   task run();
      FrameLinkUTransaction transaction;
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
         if ((!flu.monitor_cb.SOP) ||
             (!flu.monitor_cb.SRC_RDY) ||
             (!flu.monitor_cb.DST_RDY))
            begin
                //Wait one clock and update the gap counter
                @(flu.monitor_cb);
                // Update the gap value
                if(this.actGapVal != -1) this.actGapVal += pDataWidth/8;
            end
         if (!enabled) begin
            //$write($time, " waitForSOP return.\n");
            return;
         end
      end while (!(flu.monitor_cb.SOP &&
                   flu.monitor_cb.SRC_RDY &&
                   flu.monitor_cb.DST_RDY)); //Detect Start of Packet
      //$write($time, " waitForSOP end.\n");
  endtask : waitForSOP

   /**
    * Wait for DST_RDY and SRC_RDY.
    */
   task waitForDstRdy();
      do begin
         if ((!flu.monitor_cb.DST_RDY) || (!flu.monitor_cb.SRC_RDY))
            @(flu.monitor_cb);
      //Detect Destination Ready
      end while ((!flu.monitor_cb.DST_RDY) || (!flu.monitor_cb.SRC_RDY));
  endtask : waitForDstRdy

   /**
    * Receive FrameLinkUnaligned transaction to tr object.
    * @param transaction Output transaction.
    */
   task receiveTransaction(FrameLinkUTransaction transaction);
      byte unsigned aux[];
      int sopstep = pDataWidth/(2**pSopWidth); // in bits
      int thisword_sop; // Where should we start reading (in bytes)
      int thisword_eop; // Where should we end reading (in bytes)
      bit shared;
      int bsopstep  = sopstep / 8; //in bytes

      //$write($time, " recieveTransaction start.\n");

      if (!started) begin
         // Start receiving new transaction
         waitForSOP(); // Wait for SOP
         if (!enabled) begin
            //$write($time, " recieveTransaction return.\n");
            return;
         end
         last_sop_pos = flu.monitor_cb.SOP_POS;
         started = 1;
      end
      else begin
         // Continue receiving transaction
         aux = new[interframe_aux.size()](interframe_aux);
         interframe_aux.delete();
      end;

      // Monitor receives transaction
      busy = 1;

      // -------- Process data in Frame word by word -----------
      do begin
         waitForDstRdy();

         // Detect word that contains pieces of two frames
         if (flu.monitor_cb.SOP && flu.monitor_cb.EOP &&
             flu.monitor_cb.SOP_POS*sopstep > flu.monitor_cb.EOP_POS*8)begin
            shared = 1;
            //Word is shared, compute the gap and check it!
            if (this.actGapVal != -1) begin
               this.actGapVal = flu.monitor_cb.SOP_POS*bsopstep -
                                (flu.monitor_cb.EOP_POS+1);
                checkGapValue();
            end
         end
         else begin
            shared = 0;

            // Word is not shared, just check if the SOP is available
            if(flu.monitor_cb.SOP && this.actGapVal != -1) begin
                // Update the gap value and check it!
                this.actGapVal += flu.monitor_cb.SOP_POS*bsopstep;
                checkGapValue();
            end
         end

         // Determine where the word starts
         if (flu.monitor_cb.SOP && !shared)
            // If the first word is shared, then it was already read.
            // If it is not shared, read it now.
            thisword_sop = last_sop_pos*sopstep/8;
         else
            // If there is no SOP in this word OR this word is shared
            thisword_sop = 0;

         // Determine where the word ends
         if (flu.monitor_cb.EOP) begin
            thisword_eop = flu.monitor_cb.EOP_POS;

            // EOP has been detected, compute the free space
            this.actGapVal = pDataWidth/8 - (flu.monitor_cb.EOP_POS+1);
         end
         else
            thisword_eop = (pDataWidth/8)-1;

         // Get data word byte by byte
         for (int i = thisword_sop; i <= thisword_eop; i++) begin
            aux = new[aux.size + 1](aux); // Enlarge aux array
            aux[aux.size-1] =
               flu.monitor_cb.DATA[8*i +: 8];
         end;  // for


         // Detect End of Frame
         if (!flu.monitor_cb.EOP) begin // No EOP
            @(flu.monitor_cb);
         end
         else begin // Yes EOP
            started = 0;
            if (!flu.monitor_cb.SOP) begin // No SOP
               // No new frame here together with the end of this one
            end
            else begin  // EOP and SOP
               // New frame also begins here
               last_sop_pos = flu.monitor_cb.SOP_POS;

               // New transaction starts only if SOP is after EOP
               if (last_sop_pos*sopstep/8 > flu.monitor_cb.EOP_POS)
                  started = 1;

               // Get data word byte by byte
               interframe_aux = new[(pDataWidth-last_sop_pos*sopstep)/8];
               for (int i=0; i<(pDataWidth-thisword_sop*sopstep)/8; i++) begin
                  interframe_aux[i] =
                     flu.monitor_cb.DATA[last_sop_pos*sopstep+8*i +: 8];
               end;  // for
            end;

            break;
         end // else
      end while (1);

      // --------- Store received data into transaction -------------
      transaction.data = new [aux.size];
      transaction.data = aux;
      aux.delete();

      @(flu.monitor_cb);

      //$write($time, " recieveTransaction end.\n");

   endtask : receiveTransaction

endclass : FrameLinkUMonitor
