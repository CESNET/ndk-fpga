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

GitLab Runner
-------------

The current implementation of the GitLab runner applies the Verible linter to each modified source file (*.sv* file) within a GitLab merge request and displays the output in the GitLab log, if a rule is violated.
It uses the rule configuration defined in the *rules* file in this directory.
The runner needs to be provided with a GitLab API token.

Reference
---------

* https://github.com/chipsalliance/verible
