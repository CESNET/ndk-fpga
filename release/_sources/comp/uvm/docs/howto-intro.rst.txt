.. howto-intro.rst: User-friendly introduction to UVM verification in this repository
.. Copyright (C) 2025 CESNET z. s. p. o.
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _uvm_howto_intro:

***********************************************
UVM HOWTO — Introduction for Newcomers
***********************************************

This document is a **beginner-friendly introduction** to the UVM verification
methodology as used in this repository. After reading it, you should understand:

* What UVM is and how verification is organized here
* The main building blocks (test, environment, UVCs, scoreboard, model)
* How to find your way in the codebase and write your first verification

For a step-by-step tutorial that produces a runnable test, continue with
:ref:`uvm_howto_first_ver`. For deeper UVM and SystemVerilog concepts, see
:ref:`uvm_manual`.

----

What is UVM and why do we use it?
=================================

**UVM** (Universal Verification Methodology) is a standard way to build
*simulation-based verification* for digital hardware (RTL). Instead of writing
one-off test scripts, we build a **reusable verification environment** that:

1. **Drives** the design (DUT — Design Under Test) with meaningful stimulus
   (e.g. packets, register accesses, resets).
2. **Observes** what the design does on its interfaces (monitors).
3. **Checks** that the design behaves correctly, usually by comparing its
   outputs to an **expected** behavior (model + scoreboard).

UVM gives us a common structure (phases, components, sequences, configuration)
so that environments are consistent, reusable, and easier to maintain. In this
repo we use UVM with **pre-built verification components (UVCs)** that already
know how to drive and monitor NDK interfaces (MFB, MVB, MI, reset, etc.).

----

Where is the UVM code in this repository?
=========================================

Two places matter most:

* **Extension UVCs (this library)**
  Path: ``comp/uvm/``
  Here live the **reusable** UVM components: agents and environments for
  protocols like MVB, MFB, MI, reset, logic_vector, logic_vector_array, PCIe,
  etc. You typically **use** these, not modify them. Examples:

  * ``comp/uvm/reset/`` — reset generation and synchronization
  * ``comp/uvm/logic_vector_mvb/`` — high-level “logic vector” over MVB
  * ``comp/uvm/logic_vector_array_mfb/`` — high-level “logic vector array” over MFB
  * ``comp/uvm/mi/`` — MI (Memory Interface) agent
  * ``comp/uvm/common/`` — comparers, sequence libraries, shared utilities

* **Your component’s verification**
  Path: next to the RTL you verify, in a ``uvm/`` directory, e.g.
  ``some_component/uvm/tbench/``
  This is **your** testbench: environment, tests, testbench module, and scripts.
  You create and edit these files; they **instantiate and configure** the UVCs
  from ``comp/uvm/``.

Typical layout for a component’s UVM tree:

::

   component/
   ├── rtl or vhd files (DUT)
   └── uvm/
       ├── tbench/
       │   ├── env/           # Environment, sequencer, scoreboard, model
       │   ├── tests/         # Test classes (e.g. base.sv)
       │   ├── testbench.sv    # Top-level module, DUT, interfaces
       │   └── generic.sv     # Parameters (mirror DUT generics)
       ├── Modules.tcl        # What to compile (UVCs + your files)
       ├── top_level.fdo     # How to run simulation (test name, flags)
       └── signals.fdo       # Waveform signals (optional)

----

The big picture: what runs when
==============================

A single verification run looks like this:

1. **Testbench** (SystemVerilog ``module``)
   * Creates clock and reset.
   * Instantiates the **DUT** and **interfaces** that connect the DUT to the
     verification world.
   * Puts pointers to those interfaces into the **UVM config database** so UVCs
     can find them.
   * Calls **run_test()**, which builds the UVM tree and runs the chosen test.

2. **Test** (e.g. ``test::base``)
   * Is the UVM “root” of your verification.
   * In **build_phase**: creates your **environment**.
   * In **run_phase**: starts **sequences** (e.g. reset, then RX traffic), waits
     for work to finish, then drops the objection so simulation can end.

3. **Environment** (e.g. ``uvm_fifox::env``)
   * In **build_phase**: creates **UVCs** (e.g. reset agent, RX/TX logic_vector_mvb
     envs), **model**, and **scoreboard**.
   * In **connect_phase**:
     * Connects UVCs to the **virtual sequencer** (so the test can start
       sequences on the right sequencers).
     * Connects **analysis ports**: RX monitor → model input; model output and
       TX monitor → scoreboard (comparer).
   * Does not run sequences itself; the **test** does that.

4. **UVCs (from comp/uvm)**
   * **RX side**: sequencer + driver + monitor. Sequences produce high-level
     transactions; the UVC converts them to protocol signals and drives the
     interface; the monitor captures transactions and sends them to the
     scoreboard/model.
   * **TX side**: monitor (and often a simple “ready” driver). The monitor
     sends DUT outputs to the scoreboard.
   * **Reset**: drives reset and synchronizes other UVCs (e.g. “start after
     reset”).

5. **Model**
   * Receives the **same** stimulus as the DUT (e.g. from RX analysis port).
   * Implements the **expected** behavior (e.g. for a FIFO: output = input in
     order).
   * Sends expected transactions to the **scoreboard**.

6. **Scoreboard (comparer)**
   * Receives **expected** transactions from the model and **actual** from the TX
   * monitor.
   * Compares them (e.g. ordered with ``uvm_common::comparer_ordered``).
   * Reports **VERIFICATION SUCCESS** or **VERIFICATION FAILED** in
     **report_phase**.

So in one sentence: the **test** builds the **environment** (UVCs + model +
scoreboard), starts **sequences** to drive and reset the DUT, and the
**scoreboard** checks that DUT outputs match the **model**.

----

UVM concepts you will use every day
===================================

Phases
------

UVM runs components in **phases**. The ones you care about first:

* **build_phase** — Create child components (agents, model, scoreboard). No
  connections yet.
* **connect_phase** — Connect ports (monitors → model/scoreboard, sequencers in
  virtual sequencer).
* **run_phase** — “Live” simulation: run sequences, drive and monitor. Your
  test raises an **objection** at the start and drops it when the test is done;
  simulation ends when all objections are dropped.
* **report_phase** — Print summary (e.g. VERIFICATION SUCCESS/FAILED).

Configuration database (config_db)
----------------------------------

Interfaces are not passed by hand through the hierarchy. The testbench puts
them in the **config database**; UVCs take them out by **name**. Names must
match. Example in testbench:

.. code-block:: systemverilog

   uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
   uvm_config_db #(virtual mvb_if #(1, DATA_WIDTH))::set(null, "", "vif_mvb_rx", mvb_rx);

When you create a UVC, you give it a **config object** that contains
``interface_name = "vif_mvb_rx"``; the UVC then does
``uvm_config_db #(...)::get(..., "vif_mvb_rx", ...)`` and gets the same
interface. So: **same name in testbench and in UVC config**.

Sequences and sequencers
------------------------

* **Sequencer** — Accepts sequence items and passes them to the driver.
* **Sequence** — Generates items (e.g. “100 random packets”) and sends them to
  a sequencer via ``start_item(req); ... finish_item(req);`` or macros like
  ``uvm_do``.
* **Virtual sequencer** — Holds references to all “real” sequencers (reset, RX,
  TX, …). The test starts one **virtual sequence** that then starts sequences on
  each sub-sequencer (e.g. reset on ``m_reset``, RX traffic on ``m_rx``).

So: **test** starts sequences on the **virtual sequencer**; the virtual
sequencer is just a bundle of handles to the UVC sequencers.

Model and scoreboard
--------------------

* **Model** — Reference (expected) behavior. Input = same as DUT input (from RX
  monitor). Output = what the spec says (e.g. FIFO: same data, same order).
* **Scoreboard** — Compares model output vs DUT output (from TX monitor). In
  this repo we usually use **uvm_common::comparer_ordered** or
  **comparer_unordered**; they implement ``write_model(...)`` and
  ``write_dut(...)`` and report mismatches. At the end, the scoreboard prints
  VERIFICATION SUCCESS only if all comparisons passed and no transactions are
  stuck.

----

Writing your first verification (roadmap)
=========================================

Follow this path; the details are in :ref:`uvm_howto_first_ver`.

1. **Create the directory layout**
   Next to your DUT: ``uvm/tbench/env/``, ``uvm/tbench/tests/``, and files
   ``env/pkg.sv``, ``env/env.sv``, ``env/sequencer.sv``, ``tests/pkg.sv``,
   ``tests/base.sv``, ``generic.sv``, ``testbench.sv``, ``Modules.tcl``,
   ``top_level.fdo``, (optional) ``signals.fdo``.

2. **Implement a minimal environment**
   * Environment: only a virtual sequencer (no UVCs yet).
   * Test: create env in build_phase; in run_phase raise objection, wait some
     time, drop objection.
   * Testbench: clock, interfaces, register interfaces in config_db, ``run_test()``,
     ``$stop(2)``.
   Run with ``vsim -do top_level.fdo`` and confirm it finishes without errors.

3. **Add reset and RX UVC**
   * In env build_phase: create configs and instantiate ``uvm_reset::agent`` and
     ``uvm_logic_vector_mvb::env_rx`` (or the UVC that matches your DUT
     interface).
   * In connect_phase: connect reset sync to RX; assign virtual sequencer
     ``m_reset`` and ``m_rx`` to the agents’ sequencers.
   * In test run_phase: start reset sequence and RX sequence (e.g.
     ``uvm_reset::sequence_start`` and ``uvm_logic_vector::sequence_simple``)
     in parallel (e.g. ``fork ... join_any``).
   Check in the waveform that reset and RX traffic appear.

4. **Add TX UVC**
   * Add ``uvm_logic_vector_mvb::env_tx`` (or your protocol’s TX env), connect
     it in connect_phase and in the virtual sequencer.
   TX UVC usually drives “ready” and monitors DUT output; no extra sequence is
   needed for basic operation.

5. **Add model and scoreboard**
   * **Model**: has analysis_fifo for RX input and analysis_port for expected
     output. In run_phase, ``get`` from RX, apply expected function (e.g. FIFO:
     pass-through), ``write`` to output.
   * **Scoreboard**: contains e.g. ``uvm_common::comparer_ordered``; connect
     model output to ``analysis_imp_model`` and TX monitor to
     ``analysis_imp_dut``.
   * In env: connect RX analysis_port → model input; model output → comparer
     model port; TX analysis_port → comparer DUT port.
   * Implement ``used()`` in env (model + scoreboard) so the test can wait until
     all transactions are compared.
   * In report_phase of the scoreboard: print VERIFICATION SUCCESS or FAILED
     depending on comparer success and used().

After that you have a **full first verification**: stimulus, observation, and
automatic checking. Then you can add more tests, use the factory to swap
sequences (:ref:`uvm_howto_extend_verification`), or run multiver
(:ref:`uvm_howto_others`).

----

Where to go next
================

* **Step-by-step first verification (with code)** — :ref:`uvm_howto_first_ver`:
  same flow as above with full code examples and figures.

* **UVM and SystemVerilog reference** — :ref:`uvm_manual`: phases, agents,
  sequences, scoreboard, factory, coding guidelines.

* **Extending verification (register model, factory, sequences)** —
  :ref:`uvm_howto_extend_verification`: register model, UVM factory, custom
  sequences, sequence configuration, PCAP, external programs.

* **Automation and multiver** — :ref:`uvm_howto_others`: multiver script,
  VERIFICATION SUCCESS in transcript.

* **Simulation examples (MFB+MI, MVB+MI, etc.)** — :ref:`uvm_simulation`:
  ready-made simulation examples and sequence snippets.

----

Quick reference: important UVCs in comp/uvm
===========================================

* **reset** — Reset agent; use ``uvm_reset::agent``, ``sequence_start``;
  ``sync_connect`` for other UVCs.
* **logic_vector_mvb** — One item per cycle over MVB; ``env_rx`` / ``env_tx``,
  ``uvm_logic_vector::sequence_simple``.
* **logic_vector_array_mfb** — Packet (byte array) over MFB; for packet-level
  tests.
* **mi** — MI interface (read/write); agent, regmodel, sequences.
* **common** — ``comparer_ordered``, ``comparer_unordered``,
  ``sequence_library``, ``sequence_item`` base.

When your DUT uses an interface that is not exactly one of these, check the
manual and existing UVM examples in the repo for “converting” UVCs (e.g.
logic_vector over MVB) or adapt an existing testbench from a similar component.
