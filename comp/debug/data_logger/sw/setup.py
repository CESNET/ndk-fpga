#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

from setuptools import setup

# Install:
# python3 setup.py install --user
# Must be in package directory

setup(
    name='logger_tools',
    version='0.1.1',
    description='Package with data_logger tools',
    author='Lukáš Nevrkla',
    author_email='xnevrk03@stud.fit.vutbr.cz',
    packages=[
        'data_logger',
        'mem_logger',
        "graph_gen",
        "logger_tools",
        "pdf_gen",
    ],
    install_requires=[
        'nfb',
        'matplotlib',
        'numpy'
    ],
)
