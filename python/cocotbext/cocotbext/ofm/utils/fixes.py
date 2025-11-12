# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

from functools import partial as partial_f, wraps


# This 'partial' wrapper just adds __qualname__, which is necessary for use in cocob_bus.monitors.Monitor.add_callback()
@wraps(partial_f)
def partial(func, /, *args, **kwargs):
    wrapped = partial_f(func, *args, **kwargs)
    wrapped.__qualname__ = func.__qualname__
    return wrapped
