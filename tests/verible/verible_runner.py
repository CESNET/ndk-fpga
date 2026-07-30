#!/usr/bin/env python3
# verible_runner.py: Verible linter runner script. To waive linter violations, see this: https://github.com/chipsalliance/verible/tree/master/verible/verilog/tools/lint#waiving-lint-violations-lint-waiver
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

import argparse
import os
import subprocess
import sys


def parse_exclusions(exclusions_path: str) -> tuple[str, ...]:
    """
    Reads an exclusions file and returns a tuple of directory paths (relative to
    the repository root) to exclude from Verible linter scans.

    Lines beginning with '#' or empty lines are ignored. Each remaining line is a
    directory path relative to the repository root (e.g. "extra/" or
    "comp/base/ver/"); the directory and everything beneath it is skipped.
    """

    paths: list[str] = []
    with open(exclusions_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            paths.append(os.path.normpath(line))
    return tuple(paths)


def get_source_paths(
    root_path: str,
    extensions: tuple[str, ...] = (".sv",),
    exclude_dirs: tuple[str, ...] = (),
) -> list[str]:
    """
    Returns paths to all source files with specific extensions, excluding the
    specified directories (given as paths relative to root_path).
    """

    exclude_set = set(exclude_dirs)
    paths = []
    for root, dirs, files in os.walk(root_path):
        rel_root = os.path.relpath(root, root_path)
        kept_dirs = []
        for d in dirs:
            rel_d = d if rel_root == "." else os.path.join(rel_root, d)
            if os.path.normpath(rel_d) in exclude_set:
                continue
            kept_dirs.append(d)
        dirs[:] = kept_dirs
        for name in files:
            if name.endswith(extensions):
                paths.append(os.path.join(root, name))
    return paths


def get_linter_output(path: str, rules_config_path: str) -> str | None:
    """
    Runs the Verible linter and returns its output, if any.
    """

    output = subprocess.run(
        args=[
            "verible-verilog-lint",
            "--ruleset=none",
            f"--rules_config={rules_config_path}",
            path,
        ],
        capture_output=True,
    )
    if output.returncode != 0:
        return output.stderr.decode()
    else:
        return None


def main():
    repo_root = os.getcwd()
    script_dir = os.path.dirname(__file__)
    rules_config_path = os.path.join(script_dir, "rules")
    exclusions_path = os.path.join(script_dir, "exclusions")

    exclude_dirs = parse_exclusions(exclusions_path)

    SEP = "-" * 150

    outputs = []
    for path in get_source_paths(repo_root, exclude_dirs=exclude_dirs):
        output = get_linter_output(path, rules_config_path)
        if output:
            outputs.append(output)
            print(f"{SEP}\n{output}")

    if outputs:
        print(SEP)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    argparse.ArgumentParser(
        description="Verible linter runner script. To waive linter violations, see this:\n"
        "https://github.com/chipsalliance/verible/tree/master/verible/verilog/tools/lint"
        "#waiving-lint-violations-lint-waiver.",
        formatter_class=argparse.RawTextHelpFormatter,
    ).parse_args()
    main()
