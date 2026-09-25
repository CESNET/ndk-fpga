# Upgrade Guide

This document describes breaking changes between NDK-FPGA versions and provides
instructions on how to adapt existing projects using older versions of this repo.

---

## Unreleased / Current `devel`

### Stop using `combo_user_const`; put application constants into the new `ndk_app_pkg`

**What changed:** `combo_user_const` is obsolete. Generated constants were split
into `ndk_fpga_top_pkg` (card top-level), `ndk_fpga_common_pkg` (NDK core) and
`ndk_app_pkg` (your application). All `VhdlPkg*` procs now accept an optional
`-pkg <name>` argument; without it they still target `combo_user_const`, so old
configs keep working.

**How to migrate your application:**

1. In your `*_const.tcl` (e.g. `app_conf.tcl`), add `-pkg ndk_app_pkg`:

   ```tcl
   setVhdlPkgInt -pkg ndk_app_pkg MY_APP_PARAM 42
   ```

   `ndk_app_pkg` is generated and registered automatically; no extra setup needed.

2. In your VHDL, replace the old import and use **only** the application package:

   **Old:**

   ```vhdl
   use work.combo_user_const.all;
   ```

   **New:**

   ```vhdl
   use work.ndk_app_pkg.all;
   ```

   Do not import `ndk_fpga_top_pkg`/`ndk_fpga_common_pkg` in application code —
   core parameters are supplied to your application as generics from parent
   instances (`APPLICATION_CORE` entity). If you need a constant that has no
   generic, re-declare it into `ndk_app_pkg` in your `*_const.tcl`:

   ```tcl
   setVhdlPkgInt -pkg ndk_app_pkg DMA_RX_CHANNELS $DMA_RX_CHANNELS
   ```

   If your code never used constants from `combo_user_const`, just delete the
   `use` clause (this was all that `apps/minimal` needed).

**Maintainers of custom cards:** in `cards/<vendor>/<card>/src/fpga.vhd` use
`work.ndk_fpga_top_pkg.all` instead of `combo_const`/`combo_user_const` and
define `set DMA_ENDPOINTS ...` in your `card_const.tcl` — see commit
`530fa1dc3` or any upstream card for reference.

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
