=============================================================
Getting Started with Verifications Using cocotb/cocotbext-ndk
=============================================================

In this section, you will learn how to create a basic test for a flow/storage hardware component (such as a pipe,
FIFO, etc.).

To get started, first create a ``cocotb`` folder in the directory where the tested component is located,
and put all the scripts implemented in this tutorial into it.


.. note:: For automatic generation of a test template use the ``generate_test_template`` script in ``ndk-fpga/build/scripts/cocotb``.


Creating a Test
===============

As an example, a simple test of an MVB FIFOX component will be used.
It can be found at ``ndk-fpga/comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py``.

.. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py
   :language: python
   :linenos:
   :encoding: utf-8

This test can be used as a template for tests of basic `flow` and `storage` components, and can be easily adapted for
most other verifications.

It consists of two basic parts: the testbench class and the test itself.

The testbench is the more reusable of the two and usually looks basically the same, so it can be copied and adapted.
Its purpose is to initialize and encapsulate objects that drive the test. It sets up drivers,
monitors, a scoreboard, expected outputs, and other optional objects, such as a bit driver for ready signals,
adds probes, and so on. It also includes a simulated reset.

The second part is the test part. It can consist of one test (typical for simple components) or multiple tests
(more common for larger designs, such as the whole firmware of a card). Every test must have the ``@cocotb.test()``
decorator and be ``async``.

A test begins with the clock starting, testbench initialization, and a reset.
After the reset, a bit driver is started to test the component's reaction to backpressure (dst_rdy).
Random data is then generated, which can either be done
using ``random_transactions`` or random data that is then inserted into transaction objects (this is the
case in the test above). The generated transaction is then passed to the ``model`` method of the testbench,
which inserts it into the ``expected_output`` list. The generated transaction is also inserted into
the driver's send queue using the ``append`` method, from where it is then written onto the bus.

The data is then read from the bus by a monitor, which should pack it into a transaction of the same type as was
modeled and pass it to the test's scoreboard via a callback. The scoreboard pops the transaction from the
front of the expected output queue that the monitor is connected to and compares this transaction with the transaction
it received from the monitor. If they are not the same, a test failure is raised.

A waiting loop is implemented to ensure that the test doesn't report scoreboard results prematurely before all the transactions have been received.
Otherwise, the scoreboard may receive a different number of transactions than it expected, which will lead to an error.

After all the packets are received, ``tb.scoreboard.result`` is raised, and the test results are shown.


Running the Test
================

To successfully build and run the simulation, it's necessary to implement a couple more files.
Examples of these can again be found in the ``ndk-fpga/comp/mvb_tools/storage/fifox/cocotb/``
folder.

First, it is necessary to implement a ``pyproject.toml`` with all test dependencies listed:

.. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/pyproject.toml
   :language: toml
   :linenos:
   :encoding: utf-8

Use a special ``cocotb_test_sig.fdo`` file to define the signals that will be displayed in the simulator's waveform.

.. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/cocotb_test_sig.fdo
   :language: bash
   :linenos:
   :encoding: utf-8

Finally, create a ``Makefile`` that will run the simulation:

.. literalinclude:: ../../comp/mvb_tools/storage/fifox/cocotb/Makefile
   :language: bash
   :linenos:
   :encoding: utf-8

.. note:: Don't forget to adjust the values that are component-specific and the relative paths if needed.

You can run the simulation by creating a python virtual environment using make cocotb-venv, entering the created virtual environment,
and running the ``Makefile``:

.. code-block:: bash

    make cocotb-venv
    source venv-xxx/bin/activate
    make
