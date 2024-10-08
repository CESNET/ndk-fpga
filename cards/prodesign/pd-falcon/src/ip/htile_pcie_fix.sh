#!/bin/bash
# htile_pcie_fix.sh:
# Copyright (C) 2024 CESNET
# Author: Denis Kurka <xkurka05@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

filename="./htile_pcie_1x16/synth/htile_pcie_1x16.v"

sed -i 's/\(\.virtual_pf[123]_user_vsec_cap_enable\s*\)("enable")/\1("disable")/g' "$filename"
sed -i 's/\(\.pf[123]_forward_user_vsec\s*\)("true")/\1("false")/g' "$filename"
