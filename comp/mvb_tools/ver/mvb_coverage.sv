//-- mvb_coverage.sv: Coverage for mvb interface.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

// -- Coverage of one item of Mvb interface.
// -- To cover all items of one Mvb interface make one class for each item.
class MvbTxCover #(ITEMS = 4, ITEM_WIDTH = 8);
    string inst;    // -- Name of instance.
    virtual iMvbTx #(ITEMS, ITEM_WIDTH).monitor vif;    // -- Virtual interface that is covered.

    // -- The index parameter determines which item is covered.
    covergroup cov_mvb_tx (int index) @(vif.monitor_cb);
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Coverage of transferred data.
        data : coverpoint vif.monitor_cb.DATA[(index+1)*ITEM_WIDTH-1 -:ITEM_WIDTH] iff (vif.monitor_cb.VLD[index]&vif.monitor_cb.SRC_RDY&vif.monitor_cb.DST_RDY){
            bins low    = {[ITEM_WIDTH'(0)                                  : ITEM_WIDTH'(2**(ITEM_WIDTH-2))]};
            bins mid    = {[ITEM_WIDTH'(2**(ITEM_WIDTH-2)+1)                : ITEM_WIDTH'(2**ITEM_WIDTH-1-2**(ITEM_WIDTH-2)-1)]};
            bins higth  = {[ITEM_WIDTH'(2**ITEM_WIDTH-1-2**(ITEM_WIDTH-2))  : ITEM_WIDTH'(2**ITEM_WIDTH-1)]};
        }
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of SRC_RDY.
        src_rdy : coverpoint vif.monitor_cb.SRC_RDY {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of DST_RDY.
        dst_rdy : coverpoint vif.monitor_cb.DST_RDY {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of transferred transactions.
        read_sequence : coverpoint vif.monitor_cb.SRC_RDY & vif.monitor_cb.DST_RDY {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]   => 0);
            bins long    = (0 => 1[*17:32]  => 0);
            bins longest = default;
        }
    endgroup

    function new (string inst, int unsigned index, virtual iMvbTx #(ITEMS, ITEM_WIDTH).monitor itf);
        this.vif        = itf;
        this.inst       = inst;
        this.cov_mvb_tx = new(index);
    endfunction

    function void display();
        $write("%s \tcoverage %f %%\n", inst, cov_mvb_tx.get_inst_coverage());
    endfunction

endclass
