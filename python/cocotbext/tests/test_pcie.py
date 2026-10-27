# test_pcie.py: unit test of the PCIe MFB metadata layouts
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import random
import re
from pathlib import Path

import pytest

from cocotbext.ofm.pcie import CQMfbMeta, CQUser, RQMfbMeta

META_PACK = Path(__file__).resolve().parents[3] / "comp" / "base" / "pkg" / "pcie_meta_pack.vhd"


def vhdl_constants():
    """Natural constants of pcie_meta_pack.vhd, evaluated in declaration order."""
    consts = {}
    for name, expr in re.findall(r"constant\s+(\w+)\s*:\s*natural\s*:=\s*([^;]+);", META_PACK.read_text()):
        consts[name] = eval(expr, {}, consts)
    return consts


# layout class, VHDL prefix, VHDL name of every field in layout order
LAYOUTS = [
    (CQMfbMeta, "CQ", ["HEADER", "PREFIX", "BAR", "FBE", "LBE", "TPH_PRESENT", "TPH_TYPE", "TPH_ST_TAG"]),
    (RQMfbMeta, "RQ", ["HEADER", "PREFIX", "FBE", "LBE"]),
]


@pytest.mark.parametrize("layout, prefix, names", LAYOUTS, ids=[x[1] for x in LAYOUTS])
def test_field_offsets_match_pcie_meta_pack(layout, prefix, names):
    consts = vhdl_constants()
    for (field, offset), name in zip(layout.offsets().items(), names):
        assert offset == consts[f"PCIE_{prefix}_META_{name}_O"], f"{prefix} field {field}"
    assert len(layout.items) == len(names)
    assert consts[f"PCIE_{prefix}_META_WIDTH"] == len(layout())


@pytest.mark.parametrize("layout", [x[0] for x in LAYOUTS])
def test_serialize_roundtrip(layout):
    rnd = random.Random(random.getrandbits(32))
    meta = layout()
    for field, width in layout.items:
        setattr(meta, field, rnd.getrandbits(width))

    back = layout.deserialize(meta.serialize())

    assert all(getattr(back, field) == getattr(meta, field) for field, _ in layout.items)


def test_cq_user_follows_the_512_bit_tuser_of_pg213():
    offsets = CQUser.offsets()

    assert (offsets["byte_en"], offsets["sop0"], offsets["eop0"], offsets["discontiune"]) == (16, 80, 86, 96)
    assert (offsets["tph_present"], offsets["tph_type"], offsets["tph_sh_tag"], offsets["parity"]) == (97, 99, 103, 119)
    assert len(CQUser()) == 183
