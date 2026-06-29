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

GitLab CI
---------

The ``veriblelint`` job, defined in ``tests/ci/check.gitlab-ci.yaml``, runs the Verible linter in GitLab CI as part of the ``check`` stage.
It installs Verible through ``tests/verible/install.sh`` and then executes ``tests/verible/verible_runner.py``, which lints every ``*.sv`` file in the repository (skipping the directories listed in the *exclusions* file) using the rule configuration from the *rules* file in this directory.
Any violation is printed to the job log and causes the job to fail.

Reference
---------

* https://github.com/chipsalliance/verible
