---
name: vhdl-lint
description: Fast VHDL name/type-resolution checks via vhdl_ls after edits, without a full compiler run.
---

# Fast VHDL checks with vhdl_ls

After editing VHDL, check it with `vhdl_ls` (rust_hdl's VHDL language server) before
reaching for a compiler. It only does name/type resolution, not full elaboration, but
it's near-instant, so it's the right first check after every edit; fall back to
`make -C comp/<path>/synth TARGET=nvc` (see `AGENTS.md`) for a deeper elaboration-level
check before considering a change done.

Only useful if the `vhdl_ls` binary is actually installed — check `which vhdl_ls`
first, and skip this skill entirely if it isn't (fall back to `nvc` alone).

## One-time setup: generate `vhdl_ls.toml`

```
make -C tests/all_modules
```

This scans the repo's `Modules.tcl` hierarchy and writes `vhdl_ls.toml` at the
repository root, the project config `vhdl_ls` needs.
Regenerate only when files are added/removed/renamed.

If it fails with "DMA MEDUSA IP source codes are missing" (a private IP not available
everywhere): `tests/all_modules/Makefile` hardcodes the DMA variant used for
generation, so command-line overrides don't work — edit
`tests/all_modules/Vivado.tcl` to select the open DMA variant instead, regenerate, then
revert the edit (it's only needed for this generation step, not for real builds):

```
sed -i 's/set ::env(DMA_TYPE) 3/set ::env(DMA_TYPE) 4/' tests/all_modules/Vivado.tcl
make -C tests/all_modules
git checkout tests/all_modules/Vivado.tcl
```

## Checking a file

```
python3 .agents/skills/vhdl-lint/vhdl_check.py comp/base/fifo/fifox/fifox.vhd [more files...]
```

No background process needed: `vhdl_ls` resolves diagnostics lazily per opened
document rather than eagerly analyzing the whole project, so a fresh process still
returns diagnostics for an opened file in well under a second regardless of overall
project size. The script starts `vhdl_ls`, opens the given file(s) with their current
on-disk content, prints `file:line:col: severity: message` for each diagnostic, and
exits non-zero if any is error-severity.

Assumes `vhdl_ls.toml` is at the repository root (the script default); pass
`--root DIR` if the config lives elsewhere.

## Prefer an IDE-exposed check tool over this script, if one exists

Some MCP-enabled IDEs keep their own `vhdl_ls` warm for the whole session and expose it
to the agent as a callable tool. That's strictly better than this script — it talks to
an already-indexed instance instead of paying startup cost per call, and may reflect
unsaved editor buffer state. Check MCP list and the available tools for
anything diagnostics/lint-shaped before falling back to `vhdl_check.py`.
