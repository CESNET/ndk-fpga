# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>

import os
from pathlib import Path


_symlink_dirs = {
    "apps": "ndk_apps",
    "core": "ndk_core",
    "build": "ndk_build",
    "cards": "ndk_cards",
    "extra": "ndk_extra",
    "comp": "comp",
    "tests": "tests",
}


def build_init(app):
    srcdir = Path(app.srcdir)
    for k, v in _symlink_dirs.items():
        try:
            os.symlink(srcdir / '../..' / k, srcdir / v)
        except FileExistsError:
            pass


def build_finish(app, exception):
    srcdir = Path(app.srcdir)
    for v in _symlink_dirs.values():
        os.remove(srcdir / v)


def setup(app):
    app.connect('builder-inited', build_init)
    app.connect('build-finished', build_finish)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
