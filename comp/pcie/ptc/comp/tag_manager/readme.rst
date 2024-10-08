.. _ptc_tag_manager:

PTC Tag Manager
---------------

The purpose of the Tag Manager is to convert between the ID tagging space of the DMA transactions and the ID tagging space of the PCIe transactions.
The DMA tagging consists of a Unit ID (one for each unit which generates requests) and a Tag.
This way, each unit can have its own independent space of transaction Tags.
On the other hand, PCIe transactions require Tags to be unique accross all read requests, which are currently waiting for a response.
The Tag Manager dynamically assigns a free PCIe Tag to each upstream read request and stores the corresponding DMA Unit ID and Tag.
For downstream read responses, the mapping is done the other way around based on the previously stored information.
The Tag Manager is also responsible for freeing of the PCIe Tags, checking of their availability and of the availability of storage space in the downstream MVB+MFB Storage FIFO.
(The MVB+MFB Storage FIFO must be kept from overflowing to prevent fall of DST_RDY on the downstream IP core interface.)

Block diagram
^^^^^^^^^^^^^

The core part of the unit is the Tag mapping N_LOOP_OP.
It is a memory, which stores the corresponding DMA Tag and Unit ID for each possible PCIe Tag.
Since, this memory can be updated multiple times in each cycle, the N_LOOP_OP is used, which allows parallel memory update.

PCIe Tag values are assigned to DMA Tag-ID values in two different ways depending on the unit settings.
The two architectures are described in the diagrams below.

.. _ptc_tag_manager_diag_assign:

.. image:: doc/ptc_tag_manager.svg
      :align: center
      :width: 100 %
      :alt:

#. Auto-assign

    In this mode the unit generates the PCIe Tags itself and passes them to the upstream transactions to be propagated to PCIe.
    The unit is responsible for releasing of the PCIe Tags for repeated usage depending on the downstream transactions.

.. _ptc_tag_manager_diag_no_assign:

.. image:: doc/ptc_tag_manager_no_assign.svg
      :align: center
      :width: 100 %
      :alt:

#. No Auto-assign

    In this mode the PCIe Tags are assigned to the upstream transactions by the PCIe IP core and passed by to the Tag Manager.
    In upstream, this unit is only responsible for checking number of available credits (space in downstream Storage FIFO).
    The transaction DMA Tag and ID is stored in the DMA Trans FIFOX Multi, where they wait for the corresponding PCIe Tag value passed from the IP core.

    In downstream the Tag Manager must detect when a PCIe Tag has been freed.
    A situation may occur, when the PCIe IP core releases a PCIe Tag and immidiately assigns it to a new transaction.
    The re-assigned PCIe Tag value can then reach the output of the PCIe Tag FIFOX Multi before the last part of the completion, to which it was assigned before (now released in the IP core but not in the Tag Manager).
    At that point, the Tag Manager must wait for the completion to pass before it can write a new mapping value to the N_LOOP_OP.
    For this reason, there is the Tag Assign Valid Reg Array.
    All values on the PCIe Tag FIFOX Multi are checked for having a '0' (non-valid) value in this array.
    If not, they (and all after them) must wait.

    In order to separate the complex logic on the PCIe Tag FIFOX Multi from the N_LOOP_OP operator logic, there is a register.
    To make this possible, the number of the PCIe Tag FIFOX Multi output interfaces is doubled, to be able to calculate the current cycle or the previous cycle again, depending on the result of the previous cycle.
