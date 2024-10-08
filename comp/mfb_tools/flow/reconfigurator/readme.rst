.. _mfb_reconfigurator:

MFB Reconfigurator
------------------

MFB Reconfigurator reconfigures a MFB bus interface from an arbitrary configuration to another arbitrary configuration.
This includes changing of ``ITEM_WIDTH``, ``BLOCK_SIZE``, ``REGION_SIZE`` and number of ``REGIONS``.

.. warning::

   All of the MFB parameteres (bot RX and TX) are required to be powers of 2.

Architecture
^^^^^^^^^^^^

.. _mfb_reconfigurator_diag:

.. image:: doc/mfb_reconfigurator.svg
      :align: center
      :width: 100 %
      :alt:

MFB Reconfigurator does not perform all the required transformations at once.
Instead it consists of components, which modify partial attributes of the MFB bus.
These components are connected to a pipeline to form a full power MFB Reconfigurator.

The components included in the architecture are as follows:

#. MFB Item Reconfigurator

    Is cappable of dividing Items into smaller Items to increase their number *or* joining multiple Items in one Block to decrease their number.

    .. vhdl:autoentity:: MFB_ITEM_RECONFIGURATOR

#. MFB Block Reconfigurator

    Division of Blocks into smaller Blocks ---
    the division is only done between Items; the component cannot split Items ---
    *or* joining of multiple Blocks within the same Region into bigger Blocks.

    .. vhdl:autoentity:: MFB_BLOCK_RECONFIGURATOR


#. MFB Region Reconfigurator

    Division of Regions into smaller Regions ---
    the division is only done between Blocks; the component cannot split Blocks ---
    *or* joining of multiple Regions within the word into bigger Regions.

    .. vhdl:autoentity:: MFB_REGION_RECONFIGURATOR

#. :ref:`MFB Transformer<mfb_transformer>`

It is important to realize, that the components cannot be placed in the MFB Reconfigurator in an arbitrary order.
In fact, as you can see in the diagram above, all of them appart from the MFB Transformer are required to be present **twice**.
One of the 2 copies is needed when division is being done; the other when joining is done.
The means, that **there is allways one of these 2 copies, which is not needed, and is reduced to simple straight RX-to-TX connection**.
For example: when the ``ITEM_WIDTH`` is being lowered, the first copy of Item Reconfigurator is used to divide Items into smaller Items, while the second copy is not needed.
When the ``ITEM_WIDTH`` is being increased, it is the other way around.
If the respective MFB parameter is not changing at all, **neither of the 2 copies are needed and both are reduced to straight conenctions**.
(If the RX MFB configuration is the same as the TX MFB configuration, the whole component is reduced to straight signal connections.)

The reason for this are the constraints, which each of the components has in order to work.
For example:
Let's say you have a MFB bus with 2 MFB Regions, 2 MFB Blocks each, 2 MFB Items each, 8 bits wide each (configuration ``(2,2,2,8)``).
And you want to reconfigure this but into a single MFB Item 128 bits wide ``(1,1,1,128)``.
Since the original bus was only 2*2*2*8 = 64 bits wide, you will need MFB Transformer to increase the word size.
At the same time you cannot perform *any* transformations *before* the word is resized, because neither Items Reconfigurator, nor Block Reconfigurator, nor Region Reconfigurator can create an Item / BLock / Region, which is wider than the whole current word.
This means, that the first 3 components will actualy be removed and the pipeline will start with the MFB Transformer.

Constraints and side-effects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The MFB Reconfigurator has a few constraints and side-effects concerning secondary MFB bus characteristics.

First there are side-effects caused by the very nature of the MFB bus:

If you are increasing the value ``ITEM_WIDTH``, you are reducing the resolution of the ``EOF_POS`` value.
This in turn means that you are reducing the resolution of the frame length information.
In that case, Item Reconfigurator round the value of ``EOF_POS`` **up**, which will lead to invalid data appearing at the end of each previously unaligned frame.
(e.g.: If there is a frame with the size of 1 MFB Item and we are doubling the ``ITEM_WIDTH``, then the output frame will also have the size of 1 MFB Item, but it will be a larger MFB Item and only the beginig will contain valid data.)

Data shifting
=============

Some reconfigurations will require shifting of frame data within the data word.
Data shifting is the most resource-consuming action of the MFB Reconfigurator.
It also raises the component latency and, in case of a complicated MFB configuration, may lead to timing problems.
Data shifting in the MFB Reconfigurator occurs when either of these two operations are required:

#. Blocks are being merged together (``BLOCK_SIZE * ITEM_WIDTH`` is being increased).

#. Reginos are being merged together (``REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH`` is being increased).

In these two cases, a situation may occur, when multiple ``SOFs`` or ``EOFs`` occur in the same Region after the reconfiguration.
This is not allowed on the MFB bus and data shifting is thus required.
The user can prevent this by declaring, that such situation will not occur on the data bus using generics ``FRAMES_OVER_TX_BLOCK`` and ``FRAMES_OVER_TX_REGION`` respectively.

When data shifting is required, the MFB Reconfigurator **does not support shared Regions for TX MFB**.
(TX MFB interface will not contain any Regions with data from 2 different frames.)
This is done in sake of logic complexity and implementation difficulty reduction.
When data is being shifted, each output data block is dependent on all previous input data blocks.
To support shared output Regions, the logic would also have to check for presence of double ``SOF`` or ``EOF`` in the output Region, which would add dependency on all othee *output* Blocks in the same Region.
