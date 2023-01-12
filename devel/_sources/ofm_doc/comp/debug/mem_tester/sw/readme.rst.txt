.. _mem_tester_sw:

MEM_TESTER Software
-------------------

C Program
^^^^^^^^^

**Most Need Arguments**

- ``-d path``   ... Path to the device
- ``-c comp``   ... Compatible of the mem_tester component [default: ``netcope,mem_tester``]
- ``-t type``   ... Run test [type = all / seq / rand]
- ``-p``        ... Print registers
- ``--rst``     ... Reset mem_tester component
- ``--rst-emif``... Reset EMIF IP and mem_tester component

.. note::
  For complete list of supported parameters use ``-h`` or ``--help``.

**Basic Usage**

.. code-block::

  make 
  ./mem_tester -t all

**AMM_GEN Usage**

Manual write to the external memory:

- First, fill the manual r/w buffer using ``-m burst_id data`` command:
  
  - ``burst_id`` parameter (in range: ``0 to BURST_CNT - 1``) selects which AMM word will be set
  - ``data`` parameter is a new AMM word (512b number in hexa)

- Set address at which should be data written using ``-a addr`` argument
- After running the program with ``-w`` flag, data will be saved to external memory

Manual read from the external memory:

- Set address from which should be data read using ``-a addr`` argument
- Run program with ``-r`` flag
- Wait until ``buff vld`` bit is set (use ``-p`` flag to print the current state of all bits and registers)
- Data will be then inside manual r/w buffer, which can be printed using ``-p`` flag

Pytest Tester (mem_tester.py)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Run script using: ``python3 -m pytest -sv mem_tester.py``

Report Generator (report_gen.py)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Run script using: ``python3 report_gen.py``
Output report will be in the same folder: ``mem_tester_report.pdf``,
including raw data and graphs: ``raw.xml`` and ``fig/*``.

