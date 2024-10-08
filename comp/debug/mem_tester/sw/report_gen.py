#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

# sudo yum install pandoc
# sudo yum install texlive-latex
# sudo yum install texlive
# pandoc mem_tester_report.md -o mem_tester_report.pdf -V geometry:a4paper -V geometry:margin=2cm -f markdown-implicit_figures

import subprocess
import argparse
import json
import numpy as np

import nfb
from mem_tester import MemTester
from mem_logger.mem_logger import MemLogger
from logger_tools.logger_tools import LoggerTools
from graph_gen.graph_gen import GraphGen
from pdf_gen.pdf_gen import PDFGen


class ReportGen:
    def __init__(self, graph_gen, dev="/dev/nfb0"):
        self.graph_gen      = graph_gen
        self.dev            = dev

        self.iterCnt         = 0
        self.currIter        = 0
        self.prevIter        = 0

        self.tools      = LoggerTools()
        self.tester_comp = MemTester.DT_COMPATIBLE
        self.logger_comp = MemLogger.DT_COMPATIBLE
        self.tester_cnt  = MemTester.compatible_cnt(dev=dev, comp=self.tester_comp)
        self.logger_cnt  = MemTester.compatible_cnt(dev=dev, comp=self.logger_comp)
        assert self.tester_cnt <= self.logger_cnt

        self.logger_config = []
        for i in range(0, self.logger_cnt):
            self.open(i)
            self.logger_config.append(self.mem_tester.mem_logger.config)

        self.data = {
            'info': {
                'dev':              self.dev,
                'tester_comp':      self.tester_comp,
                'tester_cnt':       self.logger_comp,
                'logger_comp':      self.logger_comp,
                'logger_cnt':       self.logger_cnt,
                'logger_config':    self.logger_config,
            },
        }

    def open(self, index):
        logger = MemLogger(dev=self.dev, index=index)
        self.mem_tester = MemTester(logger, dev=self.dev, index=index)

    def test(self, key, descript, index, params, test_param=None, param_values=None):
        data = {
            'descript':     descript,
            'params':       params,
            'test_param':   test_param,
            'param_values': param_values,
            'stats':        [],
            'status':       [],
            'errs':         [],
        }

        self.open(index)
        cnt = len(param_values) if test_param is not None else 1

        for i in range(0, cnt):
            curr_params = params
            if test_param is not None:
                curr_params[test_param] = param_values[i]

            self.mem_tester.config_test(**curr_params)
            self.mem_tester.execute_test()
            config, status, stats, errs = self.mem_tester.get_test_result()

            stats['latency'].pop('hist')

            data['stats'].append(stats)
            data['status'].append(status)
            data['errs'].append(errs)

        data['stats']  = tools.parse_dict_list(data['stats'])
        data['status']  = tools.parse_dict_list(data['status'])
        if key not in self.data:
            self.data[key] = {}
        self.data[key][index] = data

    def get_burst_seq(self, index, cnt, burst_scale=1.0):
        burst_width = self.logger_config[index]['MEM_BURST_WIDTH']
        burst_lim   = int((2 ** burst_width - 1) * burst_scale)
        res = np.linspace(1, burst_lim, cnt)
        return [int(i) for i in res]


########
# MAIN #
########

# https://stackoverflow.com/questions/3173320/text-progress-bar-in-terminal-with-block-characters
def print_progress(progress, txt='Complete', prefix='Progress', decimals=1, length=30, fill='█', printEnd="\r"):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
        printEnd    - Optional  : end character (e.g. "\r", "\r\n") (Str)
    """
    iteration = progress[0]
    total     = progress[1]
    finished  = progress[2]
    progress[0] += 1

    if finished:
        return

    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print(f'\r{prefix} |{bar}| {percent}% {txt:<30}', end=printEnd)
    # Print New Line on Complete
    if iteration >= total:
        progress[2] = True
        print()


def parseParams():
    parser = argparse.ArgumentParser(description="""Report generator for mem_tester component""")
    parser.add_argument('-d', '--device', default=nfb.libnfb.Nfb.default_device,
                        metavar='device', help="""device with target FPGA card.""")
    parser.add_argument('format', nargs='?', default='pdf', choices=['md', 'pdf'],
                        help="""Format of the output report)""")
    args = parser.parse_args()
    return args


def run_cmd(cmd):
    return subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE).stdout.read().strip().decode("utf-8")


def latency_table(pdf, bursts, latencies):
    header  = ['Latency x burst']
    data    = [
        ['min [ns]'],
        ['avg [ns]'],
        ['max [ns]'],
    ]
    for i, b in enumerate(bursts):
        header.append(f'{b:<.0f} [B]')
        data[0].append(f"{latencies['latency']['min_ns'][i]:<.1f}")
        data[1].append(f"{latencies['latency']['avg_ns'][i]:<.1f}")
        data[2].append(f"{latencies['latency']['max_ns'][i]:<.1f}")
    pdf.table(header, data)


if __name__ == '__main__':
    args        = parseParams()

    data_file   = 'data.json'
    report_file = 'mem_tester_report'
    img_path    = 'fig/'

    tools       = LoggerTools()
    graph_gen   = GraphGen(folder=img_path, ratio=(13, 6), output=[".png"])
    gen         = ReportGen(graph_gen, dev=args.device)
    pdf         = PDFGen()

    burst_seq   = gen.get_burst_seq(0, 50, burst_scale=0.25)
    test_params = {'burst_cnt': burst_seq[0]}
    progress    = [0, 12 * gen.tester_cnt, False]
    addr_scale  = 0.05

    for index in range(0, gen.tester_cnt):
        ## Run tests ##
        print_progress(progress, 'full memory test')
        gen.test('indexing', 'Test different types of indexing', index, test_params, 'rand_addr', [False, True])

        print_progress(progress, 'different burst counts')
        test_params = {'rand_addr': False, 'addr_lim_scale': addr_scale}
        gen.test('seq-burst', 'Test different burst lengths', index, test_params, 'burst_cnt', burst_seq)

        print_progress(progress, 'different burst counts')
        test_params = {'rand_addr': True, 'addr_lim_scale': addr_scale}
        gen.test('rand-burst', 'Test different burst lengths', index, test_params, 'burst_cnt', burst_seq)

        print_progress(progress, 'different burst counts')
        test_params = {'rand_addr': False, 'addr_lim_scale': addr_scale, 'only_one_simult_read': True}
        gen.test('seq-burst-one-simult', 'Test different burst lengths', index, test_params, 'burst_cnt', burst_seq)

        print_progress(progress, 'different burst counts')
        test_params = {'rand_addr': True, 'addr_lim_scale': addr_scale, 'only_one_simult_read': True}
        gen.test('rand-burst-one-simult', 'Test different burst lengths', index, test_params, 'burst_cnt', burst_seq)

        ## Get data ##

        print_progress(progress, 'processing data')
        with open(data_file, 'w') as f:
            f.write(json.dumps(gen.data, sort_keys=True, indent=4))

        seq_data  = gen.data['seq-burst'][index]['stats']
        rand_data = gen.data['rand-burst'][index]['stats']
        seq_data_one_simult  = gen.data['seq-burst-one-simult'][index]['stats']
        rand_data_one_simult = gen.data['rand-burst-one-simult'][index]['stats']

        ## Plot ##

        mem_width = gen.mem_tester.mem_logger.config["MEM_DATA_WIDTH"] / 8
        burst_seq_b = [i * mem_width for i in burst_seq]

        # Plot data flow
        print_progress(progress, 'generating graphs')
        graph_gen.init_plots()  # title="Data flow")
        graph_gen.basic_plot(burst_seq_b, [
            seq_data['wr_flow_gbs'],
            seq_data['rd_flow_gbs'],
            rand_data['wr_flow_gbs'],
            rand_data['rd_flow_gbs'],
        ], colors=[
            'royalblue',
            'green',
            'darkred',
            'tomato'
        ], width=2)
        graph_gen.legend([
            "seq write",
            "seq read",
            "rand write",
            "rand read",
        ])
        graph_gen.set_xlabel("burst size [B]")
        graph_gen.set_ylabel("data flow [Gbps]")
        graph_gen.plot_save(f"{index}_flow")

        # Plot latency histogram
        for type in ("seq", "rand", "seq_one_simult", "rand_one_simult"):
            print_progress(progress, 'generating graphs')
            if type == "seq":
                data = seq_data
            elif type == "rand":
                data = rand_data
            elif type == "seq_one_simult":
                data = seq_data_one_simult
            elif type == "rand_one_simult":
                data = rand_data_one_simult

            # Prepare data
            hist = data["latency"]["hist_ns"]
            hist_arr = tools.dict_to_numpy(hist)
            offset = gen.mem_tester.mem_logger.latency_hist_step() / 2
            limits = (min(burst_seq_b), max(burst_seq_b), min(data['latency']['min_ns']) - offset, max(data['latency']['max_ns']) - offset)
            hist_arr /= np.array(data["rd_req_cnt"])

            graph_gen.init_plots()  # title="Read latency")
            graph_gen.basic_plot(burst_seq_b, [
                data['latency']["min_ns"],
                #data['latency']["avg_ns"],
                data['latency']["max_ns"],
            ], style='--', colors=['black', 'black', 'black'], width=3)
            graph_gen.plot_2d(hist_arr, limits=limits, min=0, log=True)
            graph_gen.set_xlabel("burst size [B]")
            graph_gen.set_ylabel("latency [ns]")
            graph_gen.plot_save(f"{index}_latency_" + type)

            #zoom_burst = 0
            #x = list(data['latency']['hist_ns'].keys())
            #y = [i[zoom_burst] for i in data['latency']['hist_ns'].values()]
            #graph_gen.init_plots()  #title="Read latency")
            #graph_gen.histogram_plot(x, [y], log=True)
            #graph_gen.set_xlabel("latency [ns]")
            #graph_gen.set_ylabel("occurrence")
            #graph_gen.plot_save(f"{index}_latency_" + type + f'_zoom_{zoom_burst}')

    ## Generate PDF ##
    print_progress(progress, 'generating report')
    pdf.heading(1, "Memory tester report")
    pdf.text(
        "This document shows measurement that was made using mem_tester and mem_logger components."
    )

    info  = gen.data['info']
    card  = run_cmd(f'nfb-info -q card    -d {args.device}')
    proj  = run_cmd(f'nfb-info -q project -d {args.device}')
    build = run_cmd(f'nfb-info -q build   -d {args.device}')

    pdf.heading(2, "Test conditions")
    header  = ['Parameter', 'Value']
    data    = []
    data.append(["device          ",   info['dev']])
    data.append(["card name       ",   card])
    data.append(["project name    ",   proj])
    data.append(["build time      ",   build])
    data.append(["mem_tester count",   info['tester_cnt']])
    data.append(["mem_logger count",   info['logger_cnt']])
    pdf.table(header, data)

    header  = ['Interface', 'DATA WIDTH', 'ADDRESS WIDTH', 'BURST WIDTH', 'Frequency [MHz]']
    data    = []
    for i in range(info['logger_cnt']):
        data.append([
            i,
            info['logger_config'][i]['MEM_DATA_WIDTH'],
            info['logger_config'][i]['MEM_ADDR_WIDTH'],
            info['logger_config'][i]['MEM_BURST_WIDTH'],
            info['logger_config'][i]['MEM_FREQ_KHZ'] / 10**3,
        ])
    pdf.table(header, data)

    for index in range(0, gen.tester_cnt):
        pdf.heading(1, f"Test result on interface {index}")
        pdf.text(f"*test was performed on the whole memory address space with burst count {burst_seq[0]} ({burst_seq_b[0]} B)")
        full_data = gen.data['indexing'][0]
        if len(full_data['errs'][0]) == 0:
            pdf.heading(2, "Test was SUCCESSFUL!")
        else:
            pdf.heading(2, "Test FAILED!")
            pdf.text(f"Errors:\n {full_data['errs'][0]}")

        full_data = full_data['stats']
        header = ['Statistic', 'Sequential indexing', 'Random indexing']

        def get_row(txt, data, unit):
            return [txt, f"{data[0]:<.2f} {unit}", f"{data[1]:<.2f} {unit}"]

        data = []
        data.append(get_row("total time",       full_data['total_time_ms'],     "ms"))
        data.append(get_row("write time",       full_data['wr_time_ms'],        "ms"))
        data.append(get_row("read time",        full_data['rd_time_ms'],        "ms"))
        data.append(get_row("total data flow",  full_data['total_flow_gbs'],    "Gbps"))
        data.append(get_row("write data flow",  full_data['wr_flow_gbs'],       "Gbps"))
        data.append(get_row("read data flow",   full_data['rd_flow_gbs'],       "Gbps"))
        data.append(get_row("min read latency", full_data['latency']['min_ns'], "ns"))
        data.append(get_row("avg read latency", full_data['latency']['avg_ns'], "ns"))
        data.append(get_row("max read latency", full_data['latency']['max_ns'], "ns"))
        pdf.table(header, data)

        pdf.heading(2, "Maximum data flow")
        pdf.text(f"*following tests were performed on {addr_scale * 100:<.2f}% of the whole memory address space and tested different burst counts")
        pdf.image(img_path + f'{index}_flow.png')

        table_bursts = burst_seq_b[0:20:4]

        pdf.heading(2, "Read latency (maximum data flow)")

        pdf.heading(3, "Test with sequential addressing")
        pdf.image(img_path + f'{index}_latency_seq.png')
        latency_table(pdf, table_bursts, seq_data)

        pdf.heading(3, "Test with random addressing")
        pdf.image(img_path + f'{index}_latency_rand.png')
        latency_table(pdf, table_bursts, rand_data)

        pdf.heading(2, "Read latency (sequential read)")
        pdf.text("*mem_tester waits for every read response before starting another")
        pdf.heading(3, "Test with sequential addressing")
        pdf.image(img_path + f'{index}_latency_seq_one_simult.png')
        latency_table(pdf, table_bursts, seq_data_one_simult)

        pdf.heading(3, "Test with random addressing")
        pdf.image(img_path + f'{index}_latency_rand_one_simult.png')
        latency_table(pdf, table_bursts, rand_data_one_simult)

    print_progress(progress, 'finishing report')
    pdf.save(report_file)

    md_to_pdf = f"pandoc {report_file}.md -o {report_file}.pdf -V geometry:a4paper -V geometry:margin=2cm -f markdown-implicit_figures"
    if args.format == "pdf":
        out = run_cmd(md_to_pdf)

    print_progress(progress, 'DONE')
