/*
 * \file pcd_transaction.sv
 * \brief PACODAG Transaction
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \author Jan Kucera <xkucer73@stud.fit.vutbr.cz>
 * \date 2009, 2014
 */
 /*
 * Copyright (C) 2009, 2014 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- PACODAG Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief PACODAG Transaction Class
   *
   * This class describe PACODAG transaction and simplyfy transaction random
   * generation.
   */
  class PacodagTransaction extends Transaction;

    // -- Public Class Atributes --
    //! Randomization parameters
     //! Number of packet parts
    int partCount     = 2;
     //! Maximal part size
    int partSizeMax[] = '{32,32};
     //! Minimal part size
    int partSizeMin[] = '{ 8, 8};

    //! Randomized transaction data [part][byte]
    rand byte unsigned data[][];

    // -- Constrains --
    constraint c1 {
      data.size       == partCount;

      foreach (data[i])
        data[i].size inside {
                             [partSizeMin[i]:partSizeMax[i]]
                            };
      };


    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Display transaction
    /*!
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     *
     * \param prefix - output prefix
     */
    virtual function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end

       for (integer i=0; i < partCount; i++) begin
         $write("Part no: %1d, Part size: %1d, Data:", i, data[i].size);

         for (integer j=0; j < data[i].size; j++)
         begin
           if (j%16==0) $write("\n%4x:",j);
           if (j%8==0) $write(" ");
           $write("%x ",data[i][j]);
         end
         $write("\n");
       end
       $write("\n");
    endfunction : display

    //-------------------------------------------------------------------------
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to -
     */
     virtual function Transaction copy(Transaction to = null);
       PacodagTransaction tr;
       if (to == null)
         tr = new();
       else
         $cast(tr, to);

       tr.partCount   = partCount;
       tr.partSizeMax = new[partCount];
       tr.partSizeMin = new[partCount];
       tr.data        = new [partCount];
       for (integer i=0; i < partCount; i++)
         tr.data[i]   = new[data[i].size];

       tr.partSizeMax = partSizeMax;
       tr.partSizeMin = partSizeMin;
       tr.data        = data;

       copy = tr;
     endfunction: copy

    // -------------------------------------------------------------------------
    //! Compare
    /*!
     * Compares the current value of the object instance with the current value
     * of the specified object instance, according to the specified kind.
     * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
     * different, FALSE is returned and a descriptive text of the first
     * difference found is returned in the specified stringvariable. The kind
     * argument may be used to implement different comparison functions (e.g.,
     * full compare, comparison of rand properties only, comparison of all
     * properties physically implemented in a protocol and so on.)
     *
     * \param to - compared transaction
     * \param diff - difference between compared transaction
     * \param kind - type of comparison
     */
     virtual function bit compare(input Transaction to,
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       PacodagTransaction tr;
       $cast(tr, to);

       if (partCount != tr.partCount)
       begin
         same = 0;
         diff = $sformatf( "partCount does not match");
       end

       for (integer i=0; i<partCount; i++)
       begin
         if (data[i].size != tr.data[i].size)
         begin
           same = 0;
           diff = $sformatf( "partSize[%0d] does not match", i);
         end
       end

       for (integer i=0; i < partCount; i++)
         for (integer j=0; j < data[i].size; j++)
           if (data[i][j] != tr.data[i][j])
           begin
             same = 0;
             diff = $sformatf( "data[%0d][%0d] does not match", i, j);
           end

       compare = same;
     endfunction: compare

  endclass : PacodagTransaction


  // --------------------------------------------------------------------------
  // -- PACODAG Statistics Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief PACODAG Transaction Class
   *
   * This class describe PACODAG statistics transaction.
   */
  class PacodagStatsTransaction extends Transaction;

    // -- Public Class Atributes --
    //! Statistics for PACODAG
     //! Incoming protocol error
    bit frameErr = 0;
     //! MAC address not accepted
    bit macErr = 0;
     //! Frame doesn't have minimal length
    bit mintuErr = 0;
     //! Frame exceeds maximal length
    bit mtuErr = 0;
     //! Frame has bad CRC
    bit crcErr = 0;
     //! Packet length
    int unsigned frameLen;


    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Display transaction
    /*!
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the display() method.
     *
     * \param prefix - output prefix
     */
    virtual function void display(string prefix = "");
       if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end

       $write("frameErr: %d\n", frameErr);
       $write("macErr: %d\n", macErr);
       $write("mintuErr: %d\n", mintuErr);
       $write("mtuErr: %d\n", mtuErr);
       $write("crcErr: %d\n", crcErr);
       $write("frameLen: %d\n", frameLen);

       $write("\n");
    endfunction : display

    //-------------------------------------------------------------------------
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to -
     */
     virtual function Transaction copy(Transaction to = null);
       PacodagStatsTransaction tr;
       if (to == null)
         tr = new();
       else
         $cast(tr, to);

       tr.frameErr = frameErr;
       tr.macErr = macErr;
       tr.mintuErr = mintuErr;
       tr.mtuErr = mtuErr;
       tr.crcErr = crcErr;
       tr.frameLen = frameLen;

       copy = tr;
     endfunction: copy

    // -------------------------------------------------------------------------
    //! Compare
    /*!
     * Compares the current value of the object instance with the current value
     * of the specified object instance, according to the specified kind.
     * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
     * different, FALSE is returned and a descriptive text of the first
     * difference found is returned in the specified stringvariable. The kind
     * argument may be used to implement different comparison functions (e.g.,
     * full compare, comparison of rand properties only, comparison of all
     * properties physically implemented in a protocol and so on.)
     *
     * \param to - compared transaction
     * \param diff - difference between compared transaction
     * \param kind - type of comparison
     */
     virtual function bit compare(input Transaction to,
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       PacodagStatsTransaction tr;
       $cast(tr, to);

       if (frameErr != tr.frameErr)
       begin
         same = 0;
         diff = "frameErr does not match";
       end

       if (macErr != tr.macErr)
       begin
         same = 0;
         diff = "frameErr does not match";
       end

       if (mintuErr != tr.mintuErr)
       begin
         same = 0;
         diff = "mintuErr does not match";
       end

       if (mtuErr != tr.mtuErr)
       begin
         same = 0;
         diff = "mtuErr does not match";
       end

       if (crcErr != tr.crcErr)
       begin
         same = 0;
         diff = "crcErr does not match";
       end

       if (frameLen != tr.frameLen)
       begin
         same = 0;
         diff = "frameLen does not match";
       end

       compare = same;
     endfunction: compare

  endclass : PacodagStatsTransaction
