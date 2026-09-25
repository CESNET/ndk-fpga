# GLS module scripts

`gls_mod.py` utilizes the GLS module(s) in the FPGA and the GenLoopSwitch Python module in the OFM Python package (see ndk-fpga/python/ofm).

It is used mainly for throughput measurements and analysis.
Further information is available in the [GLS module documentation](https://cesnet.github.io/ndk-fpga/devel/comp/mfb_tools/debug/gen_loop_switch/readme.html) or [GLS module tutorial](https://cesnet.github.io/ndk-fpga/devel/ndk_core/doc/testing.html#gls-module-tutorial).

`dma_throughput_sweep.py` automates `gls_mod.py` across the RX/TX DMA scenarios and a range of
frame lengths. It tags each run with the FW build identity and plots the results. Every chart
shows both the bit rate in Gbps and the frame rate in Mpps. The `compare` subcommand overlays
several such runs (e.g. two FW versions) on common charts. Before the sweep it can also set the
kernel DMA buffer count and size (via `nfb-dma`, requires sudo) and records that setting in the
results for comparability. See the
[GLS module tutorial](https://cesnet.github.io/ndk-fpga/devel/ndk_core/doc/testing.html#automated-dma-throughput-sweeps-and-fw-comparison)
or run it with `-h`.
