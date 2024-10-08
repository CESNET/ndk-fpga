/*!
 * \file mii_ifc.sv
 * \brief General MII transaction
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



import crc32_ethernet_pkg::*;     // Import CRC functions



class MiiTransaction extends Transaction;

    // -- Public Class Atributes --
    //! Randomization parameters
     //! Maximal data size
    int dataSizeMax = 1518;
     //! Minimal data size
    int dataSizeMin = 64;
     //! Enable MII error weight
    int miiErrorEn_wt  = 1;
     //! Disable MII error weight
    int miiErrorDis_wt = 10;
     //! Enable CRC error weight
    int crcErrorEn_wt    = 0;
     //! Disable CRC error weight
    int crcErrorDis_wt   = 1;

    //! Randomized transaction data
    rand byte unsigned data[];

    //! Randomized MII error flag
    rand bit miiError;
    //! Randomized MII error position
    rand int unsigned miiErrorPos;
    //! Randomized CRC error flag
    rand bit crcError;
    //! Transaction CRC
    byte unsigned crc[] = new[4];

    // -- Constrains --
    constraint c1 {
        (data.size + crc.size) inside { [dataSizeMin:dataSizeMax] };
        crcError dist { 1'b1 := crcErrorEn_wt, 1'b0 := crcErrorDis_wt };
        miiError dist { 1'b1 := miiErrorEn_wt, 1'b0 := miiErrorDis_wt };
        miiErrorPos inside { [0:(data.size - 1)] };
    };


    // -- Public Class Methods --

    function void display(string prefix="");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("Data size: %1d, Data:", data.size);
        for(int i=0; i < data.size; i++) begin
            if(i%16==0)
                $write("\n%4x:", i);
            if(i%8==0)
                $write(" ");
            $write("%x ",data[i]);
        end
        $write("\nCRC: ");
        for(int i=0; i < crc.size; i++)
            $write("%x ", crc[i]);
        $write("\n");
        if(crcError)
            $write("Error was injected into CRC\n");
        if(miiError)
            $write("Error was injected into MII packet\n");
        $write("\n");
    endfunction

    virtual function Transaction copy(Transaction to = null);
        MiiTransaction tr;
        if(to == null)
            tr = new();
        else
            assert($cast(tr, to));
        tr.dataSizeMax = dataSizeMax;
        tr.dataSizeMin = dataSizeMin;
        tr.miiErrorEn_wt = miiErrorEn_wt;
        tr.miiErrorDis_wt = miiErrorDis_wt;
        tr.crcErrorEn_wt = crcErrorEn_wt;
        tr.crcErrorDis_wt = crcErrorDis_wt;
        tr.data = data;
        tr.miiError = miiError;
        tr.miiErrorPos = miiErrorPos;
        tr.crcError = crcError;
        tr.crc = crc;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        MiiTransaction tr;
        assert($cast(tr, to));
        if(data.size != tr.data.size) begin
            diff = "dataSize does not match";
            return 0;
        end
        for(int i=0; i < data.size; i++)
            if(data[i] != tr.data[i]) begin
                diff = $sformatf( "data[%0d] does not match", i);
                return 0;
            end
        if(kind == -1)
            for(int i=0; i<crc.size; i++)
                if(crc[i] != tr.crc[i]) begin
                    diff = $sformatf( "crc[%0d] does not match", i);
                    return 0;
                end
        return 1;
    endfunction


    // -- Private Class Methods --

    function void post_randomize();
        int pos;
        byte val;
        bit [31:0] crcValue;
        crcValue = ~crc32_ethernet(data, 32'hffffffff);  // Compute correct CRC
        crc = {<< byte{crcValue}};
        if(crcError) begin  // Inject CRC Error
            assert(std::randomize(pos, val) with {
                pos inside { [0:3] };
            });
            if(crc[pos] == val)
                crc[pos] = ~val;
            else
                crc[pos] = val;
        end
    endfunction

endclass
