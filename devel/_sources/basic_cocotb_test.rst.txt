===========================
Getting Started with cocotb
===========================

This guide shows how to create a basic test for flow/storage hardware components (such as pipes, FIFOs, etc.) using the cocotb framework. Cocotb allows you to write testbenches in Python, which are then used to verify VHDL/Verilog designs.

The examples in this guide use the MVB FIFOX component test located at ``comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py`` as a reference.


Quick Start
-----------

For beginners, the easiest way to get started is:

1. **Create a ``cocotb`` folder** in the directory of the component you want to test
2. **Copy template files** from an existing test (e.g., ``comp/mvb_tools/storage/fifox/cocotb/``)
3. **Modify the files** for your component:
   - Update the ``TOPLEVEL`` in the Makefile to match your component name
   - Adjust signal names and bus parameters in the testbench
   - Update the model function to compute expected outputs for your component
4. **Run the test** using the Makefile

.. note:: For automatic generation of a test template, use the ``generate_test_template`` script in ``ndk-fpga/build/scripts/cocotb``. This creates a basic test structure that you can customize.


Test Structure
==============

A cocotb test consists of two main parts:

**1. Testbench Class** - Reusable setup code that encapsulates all test infrastructure:

   - **Drivers** - Objects that write stimulus data to the DUT (Device Under Test) input interfaces
   - **Monitors** - Objects that read output data from the DUT and convert it to transactions
   - **Scoreboard** - Compares actual outputs (from monitors) against expected outputs
   - **Expected outputs** - List of transactions that the DUT should produce
   - **Optional objects** - Probes for throughput measurement, bit drivers for backpressure testing
   - **Reset sequence** - Hardware reset initialization

   The testbench class is typically reusable across multiple tests and can be copied/adapted for similar components.

**2. Test Function** - The actual test with:

   - ``@cocotb.test()`` decorator (required) - Marks the function as a cocotb test
   - ``async`` function definition (required) - Enables coroutine-based simulation
   - Test logic - Stimulus generation, DUT interaction, and verification

Example test file structure:

.. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py
   :language: python
   :linenos:
   :encoding: utf-8


Test Flow
---------

A typical test follows these steps:

1. **Start clock** - Initialize the clock generator using ``cocotb.start_soon(Clock(...).start())``. The clock drives the synchronous logic of the DUT.

2. **Initialize testbench** - Create the testbench object, which sets up all drivers, monitors, and the scoreboard.

3. **Reset** - Run the hardware reset sequence (typically 8-16 clock cycles with RESET high). This ensures the DUT starts in a known state.

4. **Configure stimulus** - Set up idle generators (to create realistic gaps in data) and backpressure drivers (to test DUT behavior when output is blocked).

5. **Generate and send data** - Create random transactions using helper functions like ``random_transactions`` or custom generators. Send them to the DUT via the driver's ``append()`` method.

6. **Model expected output** - For each sent transaction, compute what the DUT should output and add it to the ``expected_output`` list. This is typically done in a ``model()`` method.

7. **Wait for completion** - Use a waiting loop to ensure all transactions are processed before checking results. Without this, the scoreboard might evaluate prematurely.

8. **Check results** - Raise ``tb.scoreboard.result`` to display pass/fail. The scoreboard automatically compares each received transaction against the expected output.


Required Files
==============

To run a cocotb test, you need these files in your ``cocotb/`` folder:

**pyproject.toml** - Python dependencies
   This file declares the Python packages required for the test (cocotb, cocotbext-ndk, etc.). The build system uses it to create a virtual environment with all dependencies.

   .. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/pyproject.toml
      :language: toml
      :linenos:
      :encoding: utf-8

**cocotb_test_sig.fdo** - Simulator waveform signals
   This script defines which signals will be visible in the simulator's waveform viewer. Use it to debug failing tests by inspecting signal timing.

   .. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/cocotb_test_sig.fdo
      :language: bash
      :linenos:
      :encoding: utf-8

**Makefile** - Build and run configuration
   The Makefile specifies the simulator to use (Modelsim, Vivado, etc.), the top-level entity, and cocotb configuration. It handles building the simulation and running the test.

   .. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/Makefile
      :language: bash
      :linenos:
      :encoding: utf-8

.. note:: Adjust component-specific values (TOPLEVEL, generics, parameters) and relative paths in all files to match your component.


Running the Test
================

1. **Create Python virtual environment:**

   .. code-block:: bash

       make cocotb-venv

   This creates a virtual environment (typically in ``venv-<hash>/``) with all dependencies from ``pyproject.toml``.

2. **Activate the environment:**

   .. code-block:: bash

       source venv-xxx/bin/activate

   Replace ``venv-xxx`` with the actual virtual environment folder name.

3. **Run the test:**

   .. code-block:: bash

       make

   This builds the simulation (if needed) and runs the cocotb test. Results are printed to the terminal, and waveforms are saved for debugging.

   To run the test in console-only mode (without launching the GUI waveform viewer), use:

   .. code-block:: bash

       make SIM_FLAGS=-c

   This is useful for automated testing or when running tests on remote servers.

.. tip:: Use ``export COCOTB_LOG_LEVEL=DEBUG`` before running to enable debug logging for troubleshooting. See the :ref:`Debug Logging` section for more details.

.. tip:: If a test fails, examine the waveform file to understand the timing and identify the issue. The signals defined in ``cocotb_test_sig.fdo`` will be visible.

In case of having trouble with the automation, the test can also be run manually by following the subsequent steps.

1. **Create Python virtual environment:**

   To manually create the virtual environment, issue:

   .. code-block:: bash

       python<version> -m venv venv-xxx

   Use ``python3.11`` as this is the mainline NDK-FPGA Python version.

2. **Activate the environment:**

   .. code-block:: bash

       source venv-xxx/bin/activate

3. **Fetch the depedencies:**

   .. code-block:: bash

       source <ndk-fpga>/env.sh && pip install .

4. **Run the test:**

   Run the test as described above.

See Also
--------

- :doc:`cocotb_tips_and_tricks` - Tips for debug logging, random seed control, and optional signals
- :doc:`cocotbext` - Overview of cocotbext-ndk extension with drivers, monitors, and utilities
