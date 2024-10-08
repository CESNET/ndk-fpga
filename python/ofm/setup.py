from setuptools import setup

VERSION = '0.0.1'
DESCRIPTION = 'Open FPGA Modules package'

src = "comp"

submodules = {
    "ofm.comp.debug.data_logger.data_logger":       f"{src}/debug/data_logger/sw/data_logger",
    "ofm.comp.debug.data_logger.mem_logger":        f"{src}/debug/data_logger/sw/mem_logger",
    "ofm.comp.mfb_tools.flow.rate_limiter":         f"{src}/mfb_tools/flow/rate_limiter/sw",
    "ofm.comp.mfb_tools.flow.timestamp_limiter":    f"{src}/mfb_tools/flow/timestamp_limiter/sw",
    "ofm.comp.mfb_tools.logic.speed_meter":         f"{src}/mfb_tools/logic/speed_meter/sw",
}

setup(
    name='ofm',
    version=VERSION,
    author='Tomas Hak',
    author_email='xhakto01@vut.cz',
    description=DESCRIPTION,
    packages=[
        *submodules.keys(),
    ],
    package_dir={"": ".", **submodules},
    install_requires=[],

    keywords=['python'],
    classifiers=[
        "Programming Language :: Python :: 3",
    ]
)
