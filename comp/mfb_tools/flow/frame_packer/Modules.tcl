# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author(s): David Beneš <xbenes52@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set METADATA_INSERTOR_BASE          "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_PIPE_BASE                   "$OFM_PATH/comp/mfb_tools/flow/pipe"
set MFB_FIFO_BASE                   "$OFM_PATH/comp/mfb_tools/storage/fifox"
set BARREL_SHIFTER_GEN_BASE         "$OFM_PATH/comp/base/logic/barrel_shifter"
set AFTER_ONE_GEN_BASE              "$OFM_PATH/comp/base/logic/after_one"
set BEFORE_ONE_GEN_BASE             "$OFM_PATH/comp/base/logic/before_one"
set BIN2HOT_GEN_BASE                "$OFM_PATH/comp/base/logic/bin2hot"
set DEMUX_GEN_BASE                  "$OFM_PATH/comp/base/logic/demux"
set MUX_GEN_BASE                    "$OFM_PATH/comp/base/logic/mux"
set MVB_FIFO_GEN_BASE               "$OFM_PATH/comp/mvb_tools/storage/fifo"
set LAST_VLD_BASE                   "$OFM_PATH/comp/mvb_tools/aggregate/last_vld"
set FIFOX_BASE                      "$OFM_PATH/comp/base/fifo/fifox"

lappend PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES  "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Inlude of components for prototype
lappend COMPONENTS [list "METADATA_INSERTOR"        $METADATA_INSERTOR_BASE         "FULL"]
lappend COMPONENTS [list "MFB_PIPE"                 $MFB_PIPE_BASE                  "FULL"]
lappend COMPONENTS [list "MFB_FIFOX"                $MFB_FIFO_BASE                  "FULL"]
lappend COMPONENTS [list "BARREL_SHIFTER_GEN"       $BARREL_SHIFTER_GEN_BASE        "FULL"]
lappend COMPONENTS [list "AFTER_ONE_GEN"            $AFTER_ONE_GEN_BASE             "FULL"]
lappend COMPONENTS [list "BEFORE_ONE_GEN"           $BEFORE_ONE_GEN_BASE            "FULL"]
lappend COMPONENTS [list "BIN2HOT_GEN"              $BIN2HOT_GEN_BASE               "FULL"]
lappend COMPONENTS [list "DEMUX_GEN"                $DEMUX_GEN_BASE                 "FULL"]
lappend COMPONENTS [list "MUX_GEN"                  $MUX_GEN_BASE                   "FULL"]
lappend COMPONENTS [list "MVB_FIFO_GEN"             $MVB_FIFO_GEN_BASE              "FULL"]
lappend COMPONENTS [list "LAST_VLD"                 $LAST_VLD_BASE                  "FULL"]
lappend COMPONENTS [list "FIFOX"                    $FIFOX_BASE                     "FULL"]

lappend MOD "$ENTITY_BASE/fp_meta_concatenate.vhd"
lappend MOD "$ENTITY_BASE/fp_channel_demux.vhd"
lappend MOD "$ENTITY_BASE/fp_mux_ctrl.vhd"
lappend MOD "$ENTITY_BASE/fp_timeout_ext.vhd"
lappend MOD "$ENTITY_BASE/fp_dropper.vhd"
lappend MOD "$ENTITY_BASE/fp_tmp_reg.vhd"
lappend MOD "$ENTITY_BASE/fp_data_sel.vhd"
#lappend MOD "$ENTITY_BASE/out_ctrl.vhd"
lappend MOD "$ENTITY_BASE/fp_fifo_ctrl.vhd"
lappend MOD "$ENTITY_BASE/fp_spkt_lng.vhd"
lappend MOD "$ENTITY_BASE/fp_channel.vhd"
lappend MOD "$ENTITY_BASE/fp_block_vld.vhd"
lappend MOD "$ENTITY_BASE/fp_auxiliary_gen.vhd"
lappend MOD "$ENTITY_BASE/fp_ptr_ctrl.vhd"
lappend MOD "$ENTITY_BASE/fp_bs_calc.vhd"
lappend MOD "$ENTITY_BASE/fp_bs_ctrl.vhd"
lappend MOD "$ENTITY_BASE/fp_ver_module.vhd"
lappend MOD "$ENTITY_BASE/fp_bs_per_packet.vhd"
lappend MOD "$ENTITY_BASE/fp_merger.vhd"
lappend MOD "$ENTITY_BASE/frame_packer.vhd"
