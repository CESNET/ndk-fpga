// sequence_item.sv: Item for LBUS sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_item extends uvm_sequence_item;
    `uvm_object_utils(uvm_lbus::sequence_item)

    // ------------------------------- //
    // Structure of LBUS sequence item //
    // ------------------------------- //

    rand logic [4*128-1 : 0] data;
    rand logic [4    -1 : 0] ena;
    rand logic [4    -1 : 0] sop;
    rand logic [4    -1 : 0] eop;
    rand logic [4    -1 : 0] err;
    rand logic [4*4  -1 : 0] mty;
    rand logic               rdy;

    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

        assert($cast(rhs_, rhs))
        else begin
            `uvm_fatal(this.get_full_name(), "Failed to cast transaction object.")
            return;
        end

        // Item copying
        super.do_copy(rhs);
        data = rhs_.data;
        ena  = rhs_.ena;
        sop  = rhs_.sop;
        eop  = rhs_.eop;
        err  = rhs_.err;
        mty  = rhs_.mty;
        rdy  = rhs_.rdy;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item rhs_;

        assert($cast(rhs_, rhs))
        else begin
            `uvm_fatal(this.get_full_name(), "Failed to cast transaction object.")
            return 0;
        end

        // Item comparison
        return (
            super.do_compare(rhs, comparer) &&
            (data === rhs_.data           ) &&
            (ena  === rhs_.ena            ) &&
            (sop  === rhs_.sop            ) &&
            (eop  === rhs_.eop            ) &&
            (err  === rhs_.err            ) &&
            (mty  === rhs_.mty            ) &&
            (rdy  === rhs_.rdy            )
        );

    endfunction

    function string convert2string();
        string output_string;

        // Item stringifying
        output_string = $sformatf("\n\tDATA %0h\n\tENA %0b\n\tSOP %0b\n\tEOP %0b\n\tERR %0b\n\tMTY %0d\n\tRDY %0b\n",
            data,
            ena,
            sop,
            eop,
            err,
            mty,
            rdy
        );

        return output_string;
    endfunction

endclass
