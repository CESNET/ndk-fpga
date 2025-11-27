// fce.sv: convert function xilinx to pcie
// Copyright (C) 2025 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

typedef enum {MFB_META_SOF, MFB_META_EOF, MFB_META_NONE} meta_position_t;
typedef enum {MFB_RQ, MFB_RC, MFB_CQ, MFB_CC} direction_t;
typedef enum {DEV_XILINX, DEV_INTEL, DEV_DMA} device_t;

function automatic int unsigned meta_width_get(direction_t dir, device_t DEVICE);
    automatic int unsigned ret = 0;

    if (DEVICE == DEV_XILINX || DEVICE == DEV_INTEL) begin
        unique case (dir)
            MFB_RQ: ret = sv_pcie_meta_pack::PCIE_RQ_META_WIDTH;
            MFB_RC: ret = sv_pcie_meta_pack::PCIE_RC_META_WIDTH;
            MFB_CQ: ret = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;
            MFB_CC: ret = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;
        endcase
    end else begin
        $error("Unsupported DEVICE %s DIRECTION %s\n", DEVICE, dir);
        $stop(1);
    end

    return ret;
endfunction

