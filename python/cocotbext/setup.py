#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>


from setuptools import setup, find_namespace_packages

setup(
    name="cocotbext-ofm",
    version="0.0.1",
    author="Martin Spinler",
    author_email="spinler@cesnet.cz",
    description="cocotb extension for OFM",

    keywords=['python'],
    packages=find_namespace_packages(include=["cocotbext.*"]),
    install_requires=["cocotb", "cocotb-bus", "pylibfdt"],
    python_requires=">=3.5",
    classifiers=[
        "Programming Language :: Python :: 3",
        "Operating System :: OS Independent",
        "Topic :: Scientific/Engineering :: Electronic Design Automation (EDA)",
    ],
)
