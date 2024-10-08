/* speed_meas.sv : Speed meter MFB2AXI bridge
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */


class speed_cbs_rx #(MFB_ITEM_WIDTH) extends sv_common_pkg::DriverCbs;

    mfb_speed_data data;

    function new (mfb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_tx(Transaction transaction, string inst);
        MfbTransaction #(MFB_ITEM_WIDTH) t_mfb;
        $cast(t_mfb, transaction);

        data.add(t_mfb.data.size()*MFB_ITEM_WIDTH);
    endtask
endclass

class speed_cbs_tx #(AXI_ITEM_WIDTH) extends MonitorCbs;

    mfb_speed_data data;

    function new (mfb_speed_data data);
        this.data = data;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        AxiTransaction #(AXI_ITEM_WIDTH) t_axi;
        $cast(t_axi, transaction);

        data.add(t_axi.data.size()*AXI_ITEM_WIDTH);
    endtask
endclass

