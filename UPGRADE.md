# Upgrade Guide

This document describes breaking changes between NDK-FPGA versions and provides
instructions on how to adapt existing projects using older versions of this repo.

---

## Unreleased / Current `devel`

### DMA package now depends on MFB and MVB packages

**Affected:** Any `Modules.tcl` that references `dma_bus_pack.vhd` directly as a `PACKAGES`/`MOD` entry.

**What changed:**

`dma_bus_pack.vhd` now imports `work.mfb` and `work.mvb` (from `mfb_pkg.vhd`
and `mvb_pkg.vhd` respectively). Most `Modules.tcl` files simply listed the
VHDL source path in the `PACKAGES` (or `MOD`) variable, which does **not**
resolve new transitive package dependencies.

The repository's own `Modules.tcl` files have been updated to use the
`COMPONENTS` variable instead, which allows the build system to automatically
pull in all required packages (including `MFB_PKG` and `MVB_PKG`).

**How to fix:**

Replace the plain `PACKAGES`/`MOD` reference in your `Modules.tcl` with a `COMPONENTS` entry:

**Old:**

```tcl
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
```

**New:**

```tcl
lappend COMPONENTS [list "DMA_PACKAGE" "$OFM_PATH/comp/base/pkg" "DMA_PKG"]
```
