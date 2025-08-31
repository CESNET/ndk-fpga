# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# builds cocotb virtual environment
.PHONY: cocotb-venv
cocotb-venv:
	source $(OFM_PATH)env.sh ; ndk_fpga_venv_prepare "venv-$(TOP_LEVEL_ENT)" ; pip install .
