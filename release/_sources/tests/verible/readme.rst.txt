Verible Tools
=============

Verible Linter
--------------

Verible linter is one of the Verible tools.
The rules for the linter can be set by specifying a rule configuration.
The rule configuration is defined in the *rules* file in this directory.

Example
^^^^^^^

.. code-block:: shell

   verible-verilog-lint --ruleset=none --rules_config=tests/verible/rules comp/mfb_tools/edit/frame_trimmer/uvm/tbench/testbench.sv

Verible Runner Script
---------------------

The ``verible_runner.py`` script in this directory runs the Verible linter over all ``*.sv`` files in the repository and reports any violations.
It is intended to be executed from the repository root so that paths in the *exclusions* file resolve correctly:

.. code-block:: shell

   python3 tests/verible/verible_runner.py

The script uses the rule configuration from the *rules* file in this directory and exits with a non-zero status if any violation is reported.

Exclusions
^^^^^^^^^^

The *exclusions* file lists directories to skip during the scan.
Each non-empty, non-comment line is a directory path relative to the repository root, for example::

   extra/
   comp/base/ver/
   comp/mfb_tools/debug/gen_loop_switch/sim/

The directory and everything beneath it is excluded.
Lines beginning with ``#`` and empty lines are ignored.
Paths are normalized, so a trailing slash is optional.
To exclude a verification directory, append its path (relative to the repository root) to this file.

Line Length Fix Script
----------------------

The ``line_length_fix.py`` script in this directory attempts to auto-fix ``line-length`` linter violations using ``verible-verilog-format``.
It is intended to be executed from the repository root, same as ``verible_runner.py``:

.. code-block:: shell

   python3 tests/verible/line_length_fix.py             # dry-run (shows diffs, no changes)
   python3 tests/verible/line_length_fix.py --apply      # modify files in-place
   python3 tests/verible/line_length_fix.py --quiet      # summary only, no per-file diffs
   python3 tests/verible/line_length_fix.py --files path/a.sv path/b.sv

Why this script exists
^^^^^^^^^^^^^^^^^^^^^^

``verible-verilog-lint`` has an ``--autofix`` flag, but it does **not** support the ``line-length`` rule (it only fixes trivial rules like trailing spaces or repeated semicolons).
``verible-verilog-format`` can wrap long lines, but it is a holistic formatter: a full run rewrites indentation, alignment, and token spacing across the entire file.
There is no built-in "fix only line-length" mode.

This script bridges that gap by formatting **only the violating lines** via the formatter's ``--lines=N`` flag, leaving the rest of the file untouched.

How it works
^^^^^^^^^^^^

For each ``*.sv`` file (using the same exclusions as ``verible_runner.py``):

1. Runs ``verible-verilog-lint`` with only the ``line-length`` rule to find violating line numbers.
2. Formats each violating line with ``verible-verilog-format --lines=N --inplace``, using ``--column_limit=120`` (auto-detected from the *rules* file), ``--indentation_spaces=4``, ``--try_wrap_long_lines=true``, and all ``*_alignment=preserve`` flags to minimize non-line-length changes.
3. Processes lines **bottom-to-top** so that line expansions (1 line → 2+) don't shift the line numbers of remaining violations above.
4. **Reverts incidental spacing changes** on touched lines (see below).
5. Re-lints to report any violations that could not be auto-fixed.

Spacing revert
^^^^^^^^^^^^^^

The formatter removes spaces between tokens on lines it touches (e.g. ``env #(`` → ``env#(``), which are changes unrelated to line length.
By default, the script reverts these using regex rules applied **only to lines the formatter changed** (identified via ``difflib``); untouched lines are not affected.

The current rules restore the space before ``#(`` (parameterized type / instance syntax).
To add more patterns, extend the ``_SPACING_RESTORE_RULES`` list in the script:

.. code-block:: python

   _SPACING_RESTORE_RULES = [
       (re.compile(r"(\w)#\("), r"\1 #("),   # env#( → env #(
       # (re.compile(r"..."), r"..."),         # add more here
   ]

Use ``--no-revert-spacing`` to disable this feature and keep the raw formatter output.

Options
^^^^^^^

``--apply``
    Modify files in-place. Without this, runs in dry-run mode (shows unified diffs, modifies nothing).
``--line-length N``
    Maximum line length (default: auto-detected from the *rules* file, currently 120).
``--quiet``
    Suppress per-file reports and diffs; show summary only.
``--files PATH [PATH ...]``
    Process specific files instead of scanning the whole repository.
``--no-revert-spacing``
    Do not revert incidental spacing changes introduced by the formatter.

Limitations
^^^^^^^^^^^

* **Not all violations can be auto-fixed.** Long string literals cannot be split, and some parameterized ``#(...)`` constructs are not wrapped by ``--try_wrap_long_lines`` (which verible itself calls "a short-term measure to reduce risk-of-harm"). These are reported as ``remaining`` for manual fixing.
* **Spacing revert is not exhaustive.** Even with revert enabled, some non-line-length changes may remain on touched lines (e.g. operator spacing inside wrapped expressions). Always review with ``git diff`` after ``--apply``.
* The ``line-length`` rule is the only rule targeted. Other linter rules from the *rules* file are not affected.

Line Length Manual Fix Script
-----------------------------

The ``line_length_manual_fix.py`` script is a **second-pass** fixer for line-length violations that ``verible-verilog-format`` could not handle (the ones reported as ``remaining`` by ``line_length_fix.py``).

.. code-block:: shell

   python3 tests/verible/line_length_manual_fix.py             # dry-run
   python3 tests/verible/line_length_manual_fix.py --apply      # modify files
   python3 tests/verible/line_length_manual_fix.py --quiet      # summary only
   python3 tests/verible/line_length_manual_fix.py --files path/a.sv

Strategies (applied per violating line, bottom-to-top):

1. **Wrap parameter lists**: ``Type #(A, B, C, ...)`` is split into multi-line at commas, matching the codebase style.  Joins continuation lines first if the ``#(`` spans multiple lines.  Uses the innermost ``#(`` when nested.
2. **Move inline comment**: if a ``// comment`` pushes the line over the limit, it is moved to the line above.
3. **Waiver**: for lines that cannot be broken (long expressions, type declarations with no comma breakpoints), inserts ``// verilog_lint: waive line-length`` on the line above.  This is the verible in-file waiver syntax that suppresses the violation for the next non-comment line.

Typical workflow::

   # Step 1: auto-fix what the formatter can wrap
   python3 tests/verible/line_length_fix.py --apply

   # Step 2: fix the rest (wrap param lists, move comments, waive unbreakable)
   python3 tests/verible/line_length_manual_fix.py --apply

   # Step 3: verify
   python3 tests/verible/verible_runner.py

GitLab CI
---------

The ``veriblelint`` job, defined in ``tests/ci/check.gitlab-ci.yaml``, runs the Verible linter in GitLab CI as part of the ``check`` stage.
It installs Verible through ``tests/verible/install.sh`` and then executes ``tests/verible/verible_runner.py``, which lints every ``*.sv`` file in the repository (skipping the directories listed in the *exclusions* file) using the rule configuration from the *rules* file in this directory.
Any violation is printed to the job log and causes the job to fail.

Reference
---------

* https://github.com/chipsalliance/verible
