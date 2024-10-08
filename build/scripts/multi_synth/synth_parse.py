# synth_parse.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import argparse
from os import popen
from glob import glob

##########
# Parsing script arguments
##########

parser = argparse.ArgumentParser()

parser.add_argument("target_dir", help="Name of target directory with subdirectories containing multi_synth outputs")
parser.add_argument("-o", "--output", help="Name of file for csv output to put in the target_dir (default: out.csv)", default="out.csv")

args = parser.parse_args()

if args.target_dir[-1] == "/":
    args.target_dir = args.target_dir[:-1]
of_name = args.target_dir + "/" + args.output

dirs = glob(args.target_dir + "/project_*")
print(args.target_dir)
print(dirs)

quartus_syn_util = "/*.syn.rpt"
quartus_imp_util = "/*.fit.rpt"
quartus_imp_time = "/*.sta.rpt"
vivado_runs_dir  = "/*.runs"
vivado_syn       = ""
vivado_imp       = ""
#vivado_syn       = vivado_runs_dir+"/synth_1"
#vivado_imp       = vivado_runs_dir+"/impl_1"
vivado_syn_util  = vivado_syn + "/*_utilization_synth.rpt"
vivado_imp_util  = vivado_imp + "/*_utilization_placed.rpt"
vivado_imp_time  = vivado_imp + "/*_timing_summary_routed.rpt"


def grep(string, file, cut, cut_1=None):
    cut1_s = f"""cut -d"," -f{cut_1}""" if cut_1 is not None else ""
    tmp = popen(f"""grep "{string}" "{file}" | sed "s/\\s\\s*/ /g" | {cut1_s} cut -d" " -f{cut}""")
    ret = tmp.readline().strip()
    tmp.close()
    return ret


def grep_awk(string, file, cut1, cut2):
    tmp = popen(f"""grep "{string}" "{file}" | awk '{{print ${cut1} " (" ${cut2} "%)"}}'""")
    ret = tmp.readline().strip().replace(",", "")
    tmp.close()
    return ret


def append_proc(proc, text):
    try:
        proc = float(text) * 100 / float(proc)
        text += " (%6.2f%%)" % proc
    except Exception:
        pass
    return proc


with open(of_name, "w") as of:
    of.write(("Combination Name;"

              "Quartus Synthesis ALMs;"
              "Quartus Synthesis Logic ALUTs;"
              "Quartus Synthesis Memory ALUTs;"
              "Quartus Synthesis Registers;"
              "Quartus Synthesis Block Memory Bits (Approximate M20Ks);"
              "Quartus Synthesis DSPs;"

              "Quartus Implementation LABs;"
              "Quartus Implementation ALMs;"
              "Quartus Implementation Logic ALUTs;"
              "Quartus Implementation Memory ALUTs;"
              "Quartus Implementation Registers;"
              "Quartus Implementation M20Ks;"
              "Quartus Implementation DSPs;"
             #"Quartus Implementation Worst Case Data Delay;"
              "Quartus Implementation Worst Case Slack;"

              "Vivado Synthesis Logic LUTs;"
              "Vivado Synthesis Memory LUTs;"
              "Vivado Synthesis Registers;"
              "Vivado Synthesis CARRYs;"
              "Vivado Synthesis BRAMs;"
              "Vivado Synthesis URAMs;"
              "Vivado Synthesis DSPs;"

              "Vivado Implementation CLBs;"
              "Vivado Implementation Logic LUTs;"
              "Vivado Implementation Memory LUTs;"
              "Vivado Implementation Registers;"
              "Vivado Implementation CARRYs;"
              "Vivado Implementation BRAMs;"
              "Vivado Implementation URAMs;"
              "Vivado Implementation DSPs;"
              "Vivado Implementation Worst Case Data Delay;"
              "Vivado Implementation Worst Case Slack;"
              "\n"
              ))
    for i, d in enumerate(dirs):
        comb_name = d.split("/")[-1]
        comb_name = comb_name.split("_")[1:]
        comb_name = "_".join(comb_name)

        # Quartus values parsing
        # synthesis
        q_syn_alm = grep("Estimate of Logic utilization (ALMs needed)", d + quartus_syn_util, 9)
        q_syn_llut = grep("Combinational ALUT usage for logic", d + quartus_syn_util, 8)
        q_syn_mlut = grep("Memory ALUT usage                 ", d + quartus_syn_util, 6)
        q_syn_reg = grep("Dedicated logic registers         ", d + quartus_syn_util, 6)
        q_syn_brambits = grep("Total block memory bits           ", d + quartus_syn_util, 7)
        if q_syn_brambits == "":
            q_syn_bram_aprox = ("", "",)
        else:
            q_syn_bram_aprox = (str(int(q_syn_brambits) // 20480), str(int(q_syn_brambits) * 2 // 20480),)
        q_syn_bram_aprox = " (" + " - ".join(q_syn_bram_aprox) + ")"

        q_syn_dsp = grep("Total DSP Blocks                  ", d + quartus_syn_util, 6)
        # implementation
        q_imp_llut = grep("Combinational ALUT usage for logic", d + quartus_imp_util, 8)
        q_imp_mlut = grep("Memory ALUT usage                 ", d + quartus_imp_util, 6)
        q_imp_reg = grep("Dedicated logic registers         ", d + quartus_imp_util, 6)
        q_imp_reg_proc = grep("Primary logic registers           ", d + quartus_imp_util, 9)
        q_imp_reg_proc = append_proc(q_imp_reg_proc, q_imp_reg)
        q_imp_lab = grep("Total LABs: ", d + quartus_imp_util, 9)
        q_imp_lab_proc = grep("Total LABs: ", d + quartus_imp_util, 1)
        q_imp_lab_proc = append_proc(q_imp_lab_proc, q_imp_lab)
        q_imp_alm = grep("Logic utilization (ALMs needed", d + quartus_imp_util, 12)
        q_imp_alm_proc = grep("Logic utilization (ALMs needed", d + quartus_imp_util, 14)
        q_imp_alm_proc = append_proc(q_imp_alm_proc, q_imp_alm)
        q_imp_bram = grep("M20K blocks                       ", d + quartus_imp_util, 5)
        q_imp_bram_proc = grep("M20K blocks                       ", d + quartus_imp_util, 7)
        q_imp_bram_proc = append_proc(q_imp_bram_proc, q_imp_bram)
        q_imp_dsp = grep("DSP Blocks Needed ", d + quartus_imp_util, 7)
        q_imp_dsp_proc = grep("DSP Blocks Needed ", d + quartus_imp_util, 9)
        q_imp_dsp_proc = append_proc(q_imp_dsp_proc, q_imp_dsp)
        q_imp_slack = grep("Path #1: Setup slack is", d + quartus_imp_time, 8)
        #tmp = popen("grep \"Data Delay    \" "+d+quartus_imp_time+" | sed \"s/\s\s*/ /g\" | cut -d\" \" -f5")
        #q_imp_time = tmp.readline().strip()
        #tmp.close()

        # Vivado values parsing
        # synthesis
        v_syn_llut = grep("LUT as Logic  ", d + vivado_syn_util, 6, 14)
        v_syn_mlut = grep("LUT as Memory ", d + vivado_syn_util, 6, 14)
        v_syn_reg = grep("CLB Registers ", d + vivado_syn_util, 5, 13)
        v_syn_carry = grep("CARRY8        ", d + vivado_syn_util, 4, 12)
        v_syn_bram = grep("Block RAM Tile", d + vivado_syn_util, 6, 14)
        v_syn_uram = grep("URAM          ", d + vivado_syn_util, 4, 12)
        v_syn_dsp = grep("DSPs          ", d + vivado_syn_util, 4, 12)

        # implementation
        v_imp_llut = grep("LUT as Logic  ", d + vivado_imp_util, 6)
        v_imp_llut_proc = grep("LUT as Logic  ", d + vivado_imp_util, 10)
        v_imp_llut_proc = append_proc(v_imp_llut_proc, v_imp_llut)
        v_imp_mlut = grep("LUT as Memory ", d + vivado_imp_util, 6)
        v_imp_mlut_proc = grep("LUT as Memory ", d + vivado_imp_util, 10)
        v_imp_mlut_proc = append_proc(v_imp_mlut_proc, v_imp_mlut)
        v_imp_reg = grep("CLB Registers ", d + vivado_imp_util, 5)
        v_imp_reg_proc = grep("CLB Registers ", d + vivado_imp_util, 9)
        v_imp_reg_proc = append_proc(v_imp_reg_proc, v_imp_reg)
        v_imp_carry = grep("CARRY8        ", d + vivado_imp_util, 4)
        v_imp_carry_proc = grep("CARRY8        ", d + vivado_imp_util, 8)
        v_imp_carry_proc = append_proc(v_imp_carry_proc, v_imp_carry)
        v_imp_clb   = grep("CLB           ", d + vivado_imp_util, 4)
        v_imp_clb_proc = grep("CLB           ", d + vivado_imp_util, 8)
        v_imp_clb_proc = append_proc(v_imp_clb_proc, v_imp_clb)
        v_imp_bram = grep("Block RAM Tile", d + vivado_imp_util, 6)
        v_imp_bram_proc = grep("Block RAM Tile", d + vivado_imp_util, 10)
        v_imp_bram_proc = append_proc(v_imp_bram_proc, v_imp_bram)
        v_imp_uram = grep("URAM          ", d + vivado_imp_util, 4)
        v_imp_uram_proc = grep("URAM          ", d + vivado_imp_util, 8)
        v_imp_uram_proc = append_proc(v_imp_uram_proc, v_imp_uram)
        v_imp_dsp = grep("DSPs          ", d + vivado_imp_util, 4)
        v_imp_dsp_proc = grep("DSPs      |", d + vivado_imp_util, 8)
        v_imp_dsp_proc = append_proc(v_imp_dsp_proc, v_imp_dsp)
        v_imp_slack = grep("Worst Slack", d + vivado_imp_time, 4, 2)[:-2]
        v_imp_time = grep("Data Path Delay", d + vivado_imp_time, 5)[:-2]

        # Conecatenate to output line
        out_line = [comb_name,

                    q_syn_alm,
                    q_syn_llut,
                    q_syn_mlut,
                    q_syn_reg,
                    q_syn_brambits + q_syn_bram_aprox,
                    q_syn_dsp,

                    q_imp_lab,
                    q_imp_alm,
                    q_imp_llut,
                    q_imp_mlut,
                    q_imp_reg,
                    q_imp_bram,
                    q_imp_dsp,
                    #q_imp_time,
                    q_imp_slack,

                    v_syn_llut,
                    v_syn_mlut,
                    v_syn_reg,
                    v_syn_carry,
                    v_syn_bram,
                    v_syn_uram,
                    v_syn_dsp,

                    v_imp_clb,
                    v_imp_llut,
                    v_imp_mlut,
                    v_imp_reg,
                    v_imp_carry,
                    v_imp_bram,
                    v_imp_uram,
                    v_imp_dsp,
                    v_imp_time,
                    v_imp_slack,
                    "\n"]
        out_line = ["-" if x == "" else x for x in out_line]
        of.write(";".join(out_line))
