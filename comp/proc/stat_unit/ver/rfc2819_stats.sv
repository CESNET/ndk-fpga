/* \file scoreboard.sv
 * \brief RFC2819 statistics for IBUF units
 * \author Pavel Benacek
 * \date 2013, 2016, 2018
 */
/*
 * Copyright (C) 2011 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 *
 */

  // --------------------------------------------------------------------------
  // -- RFC2819 Update class
  // --------------------------------------------------------------------------
  /*!
   * \brief RFC2819 class which holds information about update statistics
   *
   * This class is responsible for holding of RFC2819 update information
   *
   */

  class RFC2819Update;

      // ---------------------
      // -- Class Variables --
      // ---------------------
      //! New packet is beeing processed
      bit newPacket;
      //! Packet length (without CRC)
      int unsigned packetLength;
      //! CRC error
      bit crcErr;
      //! Frame with multicast address
      bit multicastFrame;
      //! Frame with broadcast address
      bit broadcastFrame;
      //! Discarded packet due to buffer overflow
      bit discardedFrame;
      //! MTU error
      bit MTUErr;
      //! Minimal TU erro
      bit mintuErr;

      // -- Constructor ---------------------------------------------------------
      //! Constructor
      function new ();
         // Initialize default values
         newPacket      = 0;
         packetLength   = 0;
         crcErr         = 0;
         multicastFrame = 0;
         discardedFrame  = 0;
         MTUErr = 0;
         mintuErr = 0;
      endfunction

  endclass : RFC2819Update

  // --------------------------------------------------------------------------
  // -- RFC2819 analyser class
  // --------------------------------------------------------------------------
  /*!
   * \brief IBUF Model
   *
   * This class is responsible adding transaction into transaction table and
   * offers possibility to modify transaction.
   *
   */

  class RFC2819Statistics;

   // ---------------------
   // -- Class Variables --
   // ---------------------
   //! Total number of transfered packets
   int unsigned totalFrames;
   //! Total number of drop events
   int unsigned totalDropEvents;
   //! Total number of transfered octets
   int unsigned totalTransOctet;
   //! Discarded frames due to bad CRC checksum
   int unsigned crcErr;
   //! Discarded frames due to maximal MTU
   int unsigned overMtu;
   //! Discarded frames due to minimal allowed length
   int unsigned belowMin;
   //! Received number of broadcast frames
   int unsigned bcastFrames;
   //! Received number of multicast frames
   int unsigned mcastFrames;
   //! Received number of fragment frames
   int unsigned fragmentFrames;
   //! Received number of jabber frames
   int unsigned jabberFrames;
   //! Received number of undersize packets
   int unsigned undersizeFrames;
   //! Histogram of sizes
   int unsigned frames64;
   int unsigned frames65_127;
   int unsigned frames128_255;
   int unsigned frames256_511;
   int unsigned frames512_1023;
   int unsigned frames1024_1518;
   int unsigned framesOver_1518;

   //! Mailbox with update structures
   mailbox #(RFC2819Update) updateMbx;

   //! Bit enabled
   bit enabled;

   // -------------------
   // -- Class Methods --
   // -------------------

   // -- Public Class Methods --

   // -- Constructor ---------------------------------------------------------
   //! Constructor
   function new (mailbox #(RFC2819Update) updateMbx = null);
      // Initialize all internal statistics
      this.totalFrames       = 0;
      this.totalDropEvents   = 0;
      this.totalTransOctet   = 0;
      this.crcErr            = 0;
      this.overMtu           = 0;
      this.belowMin          = 0;
      this.bcastFrames       = 0;
      this.mcastFrames       = 0;
      this.fragmentFrames    = 0;
      this.jabberFrames      = 0;
      this.frames64          = 0;
      this.frames65_127      = 0;
      this.frames128_255     = 0;
      this.frames256_511     = 0;
      this.frames512_1023    = 0;
      this.frames1024_1518   = 0;
      this.framesOver_1518   = 0;
      this.undersizeFrames   = 0;

      //Initialize mailbox pointer
      this.updateMbx = updateMbx;
    endfunction

  // -- Update internal counters ---------------------------------------------------
  //! Updates all internal counters with recpect to RFC2819
  /*!
   * Function updates all counters with respect to passed update structure
   */
    task update(RFC2819Update up);
      // Helping variables
      int unsigned totalPacketLength = up.packetLength + 4;
      //Compute statisticis
      //Discarded statistics are processed at the end of communication
      //or if the frame is beeing discarded (it won't be added into cgmii
      //transaction table).
      if(up.discardedFrame == 1) totalDropEvents++;
      if(up.newPacket == 0)begin
         if(up.broadcastFrame == 1) bcastFrames++;
         if(up.multicastFrame == 1 && up.broadcastFrame == 0) mcastFrames++;
      end

      if(up.newPacket == 1)begin
         totalFrames++;
         totalTransOctet += totalPacketLength;
         if(up.crcErr == 1) crcErr++;
         if(up.MTUErr == 1) overMtu++;
         if(up.mintuErr == 1) belowMin++;
         if(up.mintuErr == 1 && up.crcErr == 1) fragmentFrames++;
         if(totalPacketLength > 1518 && up.crcErr == 1) jabberFrames++;
         //Compute histograms
         if(totalPacketLength == 64) frames64++;
         if(totalPacketLength >= 65 && totalPacketLength <= 127) frames65_127++;
         if(totalPacketLength >= 128 && totalPacketLength <= 255) frames128_255++;
         if(totalPacketLength >= 256 && totalPacketLength <= 511) frames256_511++;
         if(totalPacketLength >= 512 && totalPacketLength <= 1023) frames512_1023++;
         if(totalPacketLength >= 1024 && totalPacketLength <= 1518) frames1024_1518++;
         if(totalPacketLength > 1518) framesOver_1518++;
         if(totalPacketLength < 64) undersizeFrames++;
      end
    endtask : update

   // -- Process all interla requests  ----------------------------------------
   //! This function process all internal update requests
   /*!
    * Function updates all counters with respect to passed update structures
    */
    task runUpdates();
       RFC2819Update up;
      while(enabled || updateMbx.num() > 0)begin
         this.updateMbx.get(up);
         update(up);
      end
    endtask : runUpdates

    //! Enable RFC2819 module
    /*!
     * Enable module and runs monitor process
     */
    virtual task setEnabled();
      enabled = 1; // Driver Enabling
      fork
         runUpdates();                // Creating driver subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled

    //! Module RFC2819 module
    /*!
     * Disable module
     */
    virtual task setDisabled();
      enabled = 0; // Disable Driver
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! Display RFC2819 statistics
    /*!
     * Displays the current value of RFC2819 statistics
     *
     * \param prefix - output prefix
     */
    function void display(string prefix="");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      //RFC2819 statistics
      $write("Received frames:\t                      %10d\n",totalFrames);
      $write("Buffer overflow events:\t               %10d\n",totalDropEvents);
      $write("Total number of transfered octets:\t    %10d\n",totalTransOctet);
      $write("Discarded due to bad CRC:\t             %10d\n",crcErr);
      $write("Discarded due to length over MTU:\t     %10d\n",overMtu);
      $write("Discarded due to length below min.:\t   %10d\n",belowMin);
      $write("Total Received broadcast frames:\t      %10d\n",bcastFrames);
      $write("Total Received multicast frames:\t      %10d\n",mcastFrames);
      $write("Total Received fragment frames:\t       %10d\n",fragmentFrames);
      $write("Total Received jabber frames:\t         %10d\n",jabberFrames);
      $write("Total Frames;length 64B:\t              %10d\n",frames64);
      $write("Total Frames;length >= 65 & <=127:\t    %10d\n",frames65_127);
      $write("Total Frames;length >= 128 & <=255:\t   %10d\n",frames128_255);
      $write("Total Frames;length >= 256 & <=511:\t   %10d\n",frames256_511);
      $write("Total Frames;length >= 512 & <=1023:\t  %10d\n",frames512_1023);
      $write("Total Frames;length >= 1024 & <=1518:\t %10d\n",frames1024_1518);
      $write("Total Frames;length > 1518:\t           %10d\n",framesOver_1518);
      $write("Total Undersize Frames:\t              %10d\n",undersizeFrames);
      $write("\n");
    endfunction: display


 endclass : RFC2819Statistics

