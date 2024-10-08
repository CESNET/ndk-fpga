/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

  // --------------------------------------------------------------------------
  // -- Mi Transaction Class
  // --------------------------------------------------------------------------
  class MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) extends sv_common_pkg::Transaction;

     // -- Public Class Atributes --
     // Randomization parameters
     logic [ADDR_WIDTH-1:0] maxAddress = '1;
     logic [ADDR_WIDTH-1:0] minAddress = '0;
     int unsigned distRead     = 30;
     int unsigned distWrite    = 10;
     int unsigned distNone     = 1;
     //int unsigned meta_enabled = 0;

     //variables
     tr_type_t      tr_type;  // requeset/response
     rand op_type_t op;       // operation

     rand logic [ADDR_WIDTH-1:0]     address;
     rand logic [DATA_WIDTH-1:0]     data;
     rand logic [META_WIDTH-1:0]     meta;
     rand logic [DATA_WIDTH/8-1:0]   be;

     // -- Constrains --
     constraint c1 {
       address                  <= maxAddress;
       address                  >= minAddress;
       address % (DATA_WIDTH/8) == 0;
       op dist {OP_WRITE := distWrite, OP_READ := distRead, OP_NONE := distNone};
       be != 0;
     };

    /*
     * Displays the current value of the transaction or data described by this
     * instance in a human-readable format on the standard output. Each line of
     * the output will be prefixed with the specified prefix. This method prints
     * the value returned by the psdisplay() method.
     */
    virtual function void display(string prefix = "");
        if (prefix != "")
        begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end

        $write("Mi Transaction\n\ttype     : %s\n\toperation: %s\n\taddress : 0x%08x\n\tdata    : 0x%08x\n\tbe      : %0b\n\tmetadata : 0x%08x\n",
                 tr_type, op, address, data, be, meta);
    endfunction

     //-- Copy -----------------------------------------------------------------
     // Copy constructor
     virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr;
        if (to == null)
          tr = new();
        else
          $cast(tr, to);

        tr.maxAddress = maxAddress;
        tr.minAddress = minAddress;
        tr.distWrite  = distWrite;
        tr.distRead   = distRead;
        tr.distNone   = distNone;

        tr.address       = address;
        tr.data          = data;
        tr.be            = be;
        tr.tr_type       = tr_type;
        tr.op            = op;
        tr.meta          = meta;

        return tr;
     endfunction

     // -- Compare --------------------------------------------------------------
     /* Compares the current value of the object instance with the current value
      * of the specified object instance, according to the specified kind.
      * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
      * different, FALSE is returned and a descriptive text of the first
      * difference found is returned in the specified stringvariable. The kind
      * argument may be used to implement different comparison functions (e.g.,
      * full compare, comparison of rand properties only, comparison of all
      * properties physically implemented in a protocol and so on.)
      */
     virtual function bit compare(input sv_common_pkg::Transaction to,
                                  output string diff, input int kind = -1);
       bit same = 1; // Suppose that are same
       logic [DATA_WIDTH-1:0] mask;
       MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr;

       if (! $cast(tr, to))
          $display("Cast error\n");

       // check type and opertion
       if (tr_type != tr.tr_type) begin
         same = 0;
         diff = "request response is not match";
       end

       if (op != tr.op) begin
         same = 0;
         diff = "type/direction does not match";
       end

       //check address and be
       if (address != tr.address) begin
         same = 0;
         diff = "addresses does not match";
       end

       // check type and opertion
       if (be != tr.be) begin
         same = 0;
         diff = "byte enable does not match";
       end

       //if READ REQUEST transaction then dont compare data.
       if (tr_type == TR_REQUEST && op == OP_READ) begin
            mask = 0;
       end else begin
            for (int unsigned it = 0; it < DATA_WIDTH/8; it++) begin
                 mask[(it+1)*8-1 -: 8] = be[it] ? 8'hff : 8'h00;
            end
       end

       if ((data & mask) != (tr.data & mask)) begin
         same = 0;
         diff = "data does not match";
       end

       if (META_WIDTH != 0 && meta != tr.meta) begin
         same = 0;
         diff = "meta does not match";
       end

       return same;
     endfunction: compare
   endclass
