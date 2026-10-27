# test_backpressure.py: unit test of the backpressure generator
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import random
from itertools import islice

from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator


def test_levels_unroll_the_runs():
    cfg = BackpressureConfig(1, 7, 0.4)
    random.seed(5)
    runs = list(islice(BackpressureGenerator(cfg), 200))
    random.seed(5)
    levels = list(islice(BackpressureGenerator(cfg).levels(), sum(on + off for on, off in runs)))

    assert levels == [lvl for on, off in runs for lvl in [1] * on + [0] * off]


def test_levels_follow_the_low_probability():
    assert set(islice(BackpressureGenerator(BackpressureConfig(1, 5, 0.0)).levels(), 500)) == {1}
    assert set(islice(BackpressureGenerator(BackpressureConfig(1, 5, 1.0)).levels(), 500)) == {0}
