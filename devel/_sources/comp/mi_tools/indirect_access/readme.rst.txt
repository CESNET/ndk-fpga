.. _mi_indirect_access:


MI indirect access
--------------------

Through this component it is possible to send MI transactions indirectly to one or more output interfaces.
That means you have to set the parameters of the MI transaction (by sending Write requests) to a set of registers, which are also accessed by MI.

.. vhdl:autoentity:: MI_INDIRECT_ACCESS

.. warning::
    Check the status bit before sending each request to avoid possible errors.
    The LSB of the Status register indicates business of the component- if set high, the component is **busy** and you must not send any requests.

You can, of course, send Read requests addressed to the Status register to check the current status of the component.

.. image:: doc/indirect_access.svg
    :align: center
    :width: 100 %
    :alt: MI indirect access block scheme

Usage
^^^^^^

Set the ID of the desired output interface, Address , Data to be  written (in case it's a Write reqest), and the Command of the indirect request.
Set LSB of the Command register (cmd(0)) to '1' to send indirect Write request or set cmd(1) to '1' to send indirect Read request.

.. warning::
    The indirect request will be sent immediately after recieving a command, so you must set this register last.

Address space
^^^^^^^^^^^^^^^^^

.. list-table:: Tab. 1
    :align: center
    :widths: 25 20
    :header-rows: 1

    * - Register
      - Address
    * - Output interface
      - 0x00
    * - Address
      - 0x04
    * - Write data
      - 0x08
    * - Read data
      - 0x0C
    * - Command
      - 0x10
    * - Status
      - 0x14

