/*
 * file       : scoreboard.sv
 * description: scoreboard and simple model of connection component
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST_SCOREBOARD_SV_
`define TEST_SCOREBOARD_SV_

////////////////////////////////////////////////////////////////////////////////
//Decladation of callback classes
`uvm_analysis_imp_decl(_avalon_tx)
`uvm_analysis_imp_decl(_avalon_rx)

`uvm_analysis_imp_decl(_mfb_rx_ptc)
`uvm_analysis_imp_decl(_mfb_tx_ptc)

`uvm_analysis_imp_decl(_mfb_rx_mi)
`uvm_analysis_imp_decl(_mfb_tx_mi)

////////////////////////////////////////////////////////////////////////////////
// Scoreboard. This scoreboard check if DUT behavioral is correct. Scoreboard
// have to change endianity of header.
class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(env::scoreboard)

    ////////////////////////////////
    // setup callback
    uvm_analysis_imp_avalon_tx  #(packet::transaction#(ITEM_WIDTH, MFB_META_RX_WIDTH), scoreboard) analysis_imp_avalon_tx;
    uvm_analysis_imp_avalon_rx  #(packet::transaction#(ITEM_WIDTH, MFB_META_TX_WIDTH), scoreboard) analysis_imp_avalon_rx;

    uvm_analysis_imp_mfb_rx_ptc #(mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH), scoreboard)         analysis_imp_mfb_rx_ptc;
    uvm_analysis_imp_mfb_tx_ptc #(mfb_tx::transaction_monitor #(ITEM_WIDTH, MFB_META_TX_WIDTH), scoreboard) analysis_imp_mfb_tx_ptc;

    uvm_analysis_imp_mfb_rx_mi #(mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH), scoreboard)         analysis_imp_mfb_rx_mi;
    uvm_analysis_imp_mfb_tx_mi #(mfb_tx::transaction_monitor #(ITEM_WIDTH, MFB_META_TX_WIDTH), scoreboard) analysis_imp_mfb_tx_mi;

    ////////////////////////////////
    // Variables
    mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) ptc_to_pcie[$];
    mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) mi_to_pcie[$];
    packet::transaction   #(ITEM_WIDTH, MFB_META_TX_WIDTH) pcie_to_ptc[$];
    packet::transaction   #(ITEM_WIDTH, MFB_META_TX_WIDTH) pcie_to_mi[$];
    int unsigned transactions_ptc_to_pcie = 0;
    int unsigned transactions_mi_to_pcie  = 0;
    int unsigned transactions_pcie_to_ptc = 0;
    int unsigned transactions_pcie_to_mi  = 0;

    ////////////////////////////////
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
        //avalon
        analysis_imp_avalon_tx  = new("analysis_imp_avalon_tx", this);
        analysis_imp_avalon_rx  = new("analysis_imp_avalon_rx", this);
        //ptc
        analysis_imp_mfb_rx_ptc = new("analysis_imp_mfb_rx_ptc", this);
        analysis_imp_mfb_tx_ptc = new("analysis_imp_mfb_tx_ptc", this);
        //mi
        analysis_imp_mfb_rx_mi = new("analysis_imp_mfb_rx_mi", this);
        analysis_imp_mfb_tx_mi = new("analysis_imp_mfb_tx_mi", this);
    endfunction

    //////////////////////////////
    //avalon rx/tx callbacks function
    function void write_avalon_tx(packet::transaction#(ITEM_WIDTH, MFB_META_RX_WIDTH) tr);
       string error = "PCIE TX\n";
       logic [MFB_META_RX_WIDTH-1:0] hdr = {
                      tr.meta[159:128],
                      tr.meta[31:0],
                      tr.meta[63:32],
                      tr.meta[95:64],
                      tr.meta[127:96]};

       if(ptc_to_pcie.size() != 0 && ptc_to_pcie[0].data === tr.data && ptc_to_pcie[0].meta === hdr) begin
           ptc_to_pcie.pop_front();
           transactions_ptc_to_pcie++;
       end else if(mi_to_pcie.size() != 0 && mi_to_pcie[0].data === tr.data && mi_to_pcie[0].meta === hdr) begin
           mi_to_pcie.pop_front();
           transactions_mi_to_pcie++;
       end else begin
           if (ptc_to_pcie.size() != 0 ) begin
               error = {error, "\nRX PTC:\n", ptc_to_pcie[0].convert2string()};
           end else begin
               $sformat(error, "%s\n RX PTC QUEUE SIZE %d\n", error, ptc_to_pcie.size());
           end

           if(mi_to_pcie.size() != 0) begin
               error = {error, "\nRX MI :\n",  mi_to_pcie[0].convert2string()};
           end else begin
               $sformat(error, "%s\n RX MI QUEUE SIZE %d\n", error, mi_to_pcie.size());
           end

            `uvm_fatal(this.get_full_name(), {"\nAVALON TX:\n", tr.convert2string(), error , "\n"});
       end
    endfunction

    function void write_avalon_rx(packet::transaction #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr);
         packet::transaction #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr_clone;
         logic [7:0] op_type;

         $cast(tr_clone, tr.clone());
         op_type = tr_clone.meta[127:120];

         if (op_type === 8'b00001010 ||  op_type === 8'b01001010) begin
            pcie_to_ptc.push_back(tr_clone);
         end else if (op_type === 8'b00001011 || op_type === 8'b01001011) begin
            pcie_to_ptc.push_back(tr_clone);
         end else begin
            pcie_to_mi.push_back(tr_clone);
         end
    endfunction

    //////////////////////////////
    // PTC rx/tx callback function
    function void write_mfb_rx_ptc(mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) tr);
        mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) clone_tr;

        $cast(clone_tr, tr.clone());
        ptc_to_pcie.push_back(clone_tr);
    endfunction

    function void write_mfb_tx_ptc(mfb_tx::transaction_monitor #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr);
         packet::transaction #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr_avalon;
         logic [MFB_META_TX_WIDTH-1:0] hdr;

         if (pcie_to_ptc.size() == 0) begin
            `uvm_fatal(this.get_full_name(), {"\nAVALON RX:\n\t NO TRANSACTION", "\n\nMFB PTC:\n\t", tr.convert2string()});
             return;
         end

         transactions_pcie_to_ptc++;
         tr_avalon = pcie_to_ptc.pop_front();
         hdr       = {
                      //tr_avalon.bar_range,
                      //tr_avalon.prefix,
                      tr_avalon.meta[162:160],
                      tr_avalon.meta[159:128],
                      tr_avalon.meta[31:0],
                      tr_avalon.meta[63:32],
                      tr_avalon.meta[95:64],
                      tr_avalon.meta[127:96]};

         if(tr.data !== tr_avalon.data || tr.meta !== hdr) begin
            `uvm_fatal(this.get_full_name(), {"\nAVALON RX:\n", tr_avalon.convert2string(), "\n\nMFB PTC TX:\n", tr.convert2string()})
         end
    endfunction

    //////////////////////////////
    // MI rx/tx calbacks function
    function void write_mfb_rx_mi(mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) tr);
        mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH) clone_tr;

        $cast(clone_tr, tr.clone());
        mi_to_pcie.push_back(clone_tr);
    endfunction

    function void write_mfb_tx_mi(mfb_tx::transaction_monitor #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr);
         string err_text;
         packet::transaction #(ITEM_WIDTH, MFB_META_TX_WIDTH) tr_avalon;
         logic [MFB_META_TX_WIDTH-1:0] hdr;

         if (pcie_to_mi.size() == 0) begin
            $display("HDR %h\n", tr.hdr[127:120]);

            `uvm_fatal(this.get_full_name(), {"\nAVALON RX:\n\t NO TRANSACTION", "\n\nMFB MI TX:\n\t", tr.convert2string()});
             return;
         end

         transactions_pcie_to_mi++;
         tr_avalon = pcie_to_mi.pop_front();
         hdr       = {
                      //tr_avalon.bar_range,
                      //tr_avalon.prefix,
                      tr_avalon.meta[162:160],
                      tr_avalon.meta[159:128],
                      tr_avalon.meta[31:0],
                      tr_avalon.meta[63:32],
                      tr_avalon.meta[95:64],
                      tr_avalon.meta[127:96]};

         if(tr.data !== tr_avalon.data || tr.meta !== hdr) begin
             $sformat(err_text, "\nAVALON RX META: %0h\nMFB MI TX:      %h\n", hdr, tr.meta);
             `uvm_info (this.get_full_name(), err_text  ,UVM_LOW)
             `uvm_fatal(this.get_full_name(), {"\nAVALON RX:\n\t", tr_avalon.convert2string(), "\n\nMFB MI TX:\n\t", tr.convert2string()});
         end
    endfunction

    //////////////////////////////
    // REPORT PHASE
    virtual function void report_phase(uvm_phase phase);
        string s = "";

        $sformat(s, "%s\nPCIE TO PTC \n\tPACKET LEFT IN DESIGN %d\n\tCOMPARE TRANSACTIONS %d\n", s, pcie_to_ptc.size(), transactions_pcie_to_ptc);
        $sformat(s, "%s\nPCIE TO MI  \n\tPACKET LEFT IN DESIGN %d\n\tCOMPARE TRANSACTIONS %d\n", s, pcie_to_mi.size(),  transactions_pcie_to_mi);
        $sformat(s, "%s\nPTC  TO PCIE\n\tPACKET LEFT IN DESIGN %d\n\tCOMPARE TRANSACTIONS %d\n", s, ptc_to_pcie.size(), transactions_ptc_to_pcie);
        $sformat(s, "%s\nMI   TO PCIE\n\tPACKET LEFT IN DESIGN %d\n\tCOMPARE TRANSACTIONS %d\n", s, mi_to_pcie.size(),  transactions_mi_to_pcie);
        `uvm_info(this.get_full_name(), s ,UVM_LOW);
    endfunction
endclass

`endif
