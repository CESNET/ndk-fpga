#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for loading statistics from mem_logger component

import argparse
import numpy as np
import nfb
from ofm.comp.debug.data_logger.data_logger import DataLogger
import ofm.comp.debug.data_logger.logger_stats as Stats


class MemLogger(DataLogger):

    DT_COMPATIBLE = "netcope,mem_logger"

    def __init__(self, **kwargs):
        try:
            super().__init__(**kwargs)
        except Exception as e:
            raise Exception(f"ERROR while opening MemLogger component:\n    {e}")

        self.stats = self.init_stats()

    def set_config(self, latency_to_first):
        self.set_ctrlo(latency_to_first & 1)

    def init_stats(self):
        stats = Stats.LoggerStats('Mem logger', logger=self)

        # Constants #

        constants = [
            "MEM_DATA_WIDTH",
            "MEM_ADDR_WIDTH",
            "MEM_BURST_WIDTH",
            "MEM_FREQ_KHZ",
        ]
        stats.add_stats(
            name='Constants',
            names=constants,
            indexes=list(range(len(constants))),
            constructor=lambda i, n: Stats.Constant(i, n)
        )
        stats.load()

        freq = stats['Constants']['MEM_FREQ_KHZ'] * 1000.0
        word_b = stats['Constants']['MEM_DATA_WIDTH']

        # Counters #

        counters = [
            "no req + not rdy",
            "no req + rdy",
            "wr + not rdy",
            "rd + not rdy",
            "wr ticks",
            "rd ticks",
            "total ticks",
            "wr req cnt",
            "wr req words",
            "rd req cnt",
            "rd req words",
            "rd resp words",
            "err zero burst",
            "err simult rw",
        ]

        def counter_i(name):
            return counters.index(name)

        # Requests #

        reqs = ['wr req cnt', 'wr req words', 'rd req cnt', 'rd req words', 'rd resp words']
        stats.add_stats(
            name='Requests',
            names=reqs,
            indexes=list(map(counter_i, reqs)),
            constructor=lambda i, n: Stats.Counter(i, n)
        )

        # Data flow #

        stats_flow = Stats.LoggerStats('Data flow')
        stats.add_stat(stats_flow)

        stats_flow.add_stat(Stats.FlowCounter(
            index_words=counter_i('wr req words'), index_ticks=counter_i('wr ticks'),
            freq=freq, word_bits=word_b, name='wr flow'
        ))
        stats_flow.add_stat(Stats.FlowCounter(
            index_words=counter_i('rd resp words'), index_ticks=counter_i('rd ticks'),
            freq=freq, word_bits=word_b, name='rd flow'
        ))

        # Values #

        stats_val = Stats.LoggerStats('Values')
        stats.add_stat(stats_val)

        stats_val.add_stat(Stats.Value(
            index=0, name='latency',
            convert=Stats.ConvertTime(freq, units='ns'),
            format=Stats.FormatDefaultValue(units='ns', format=Stats.FormatDefault(decimal=1))
        ))
        if self.config["VALUE_CNT"] > 1:
            stats_val.add_stat(Stats.Value(index=1, name='paralel reads'))

        # Duration #

        stats_dur = Stats.LoggerStats('Test duration')
        stats.add_stat(stats_dur)

        stats_dur.add_stat(Stats.TimeCounter(
            index=counter_i('wr ticks'), freq=freq,
            name='wr time', units='ms'
        ))
        stats_dur.add_stat(Stats.TimeCounter(
            index=counter_i('rd ticks'), freq=freq,
            name='rd time', units='ms'
        ))
        stats_dur.add_stat(Stats.TimeCounter(
            index=counter_i('total ticks'), freq=freq,
            name='total time', units='ms'
        ))

        # Errors #

        errs = ['err zero burst', 'err simult rw']
        stats.add_stats(
            name='Errors',
            names=errs,
            indexes=list(map(counter_i, errs)),
            constructor=lambda i, n: Stats.Counter(i, n)
        )

        # Ready signal status #

        rdy_status = ["no req + not rdy", "no req + rdy", "wr + not rdy", "rd + not rdy"]
        stats.add_stats(
            name='Ready signal status',
            names=rdy_status,
            indexes=list(map(counter_i, rdy_status)),
            constructor=lambda i, n: Stats.Counter(i, n)
        )

        # Special statistics #

        BIT_LATENCY_TO_FIRST = 0
        ctrlo = self.load_ctrl(True)
        latency_to_first = (ctrlo >> BIT_LATENCY_TO_FIRST) & 1
        stats.add_stat(Stats.Custom(name='latency to first word', data=latency_to_first))

        stats.add_calc_stats(self.calc_stats)

        return stats

    def calc_stats(self, data):
        data['Data flow']['total flow'] = np.array(data['Data flow']['wr flow']) + np.array(data['Data flow']['rd flow'])

        return data


def parseParams():
    parser = argparse.ArgumentParser(
        description="mem_logger control script",
    )

    access = parser.add_argument_group('card access arguments')
    access.add_argument(
        '-d', '--device', default=nfb.libnfb.Nfb.default_dev_path,
        metavar='device', help="""device with target FPGA card"""
    )
    access.add_argument(
        '-i', '--index', type=int, metavar='index',
        default=0, help="""index inside DevTree"""
    )

    common = parser.add_argument_group('common arguments')
    common.add_argument(
        '--rst', action='store_true',
        help="""reset mem_tester and mem_logger"""
    )
    common.add_argument(
        '-j', '--stats-json', action='store_true',
        help="""prints mem_logger statistics in json"""
    )
    args = parser.parse_args()
    return args


def main():
    args = parseParams()
    logger = MemLogger(dev=args.device, index=args.index)
    logger.stats.load()

    print(logger.stats.to_str())

    if args.rst:
        logger.rst()

    if args.stats_json:
        print(logger.stats.data())

    #logger.set_config(latency_to_first=True)


if __name__ == '__main__':
    main()
