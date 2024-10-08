.. _mi_bus:

MI bus specification
--------------------

MI (Memory Interface) bus realizes software access to firmware components. These components (usually some control, state or statistics registers) can be either configured by **write** requests, or  their current data can be determined by **read** requests. These components are accessed by their addresses that are sent along with the requests. The default width used in this project is 32 bits for both, data and addresses. That is why the name MI32 is often used for this bus.

MI bus description
^^^^^^^^^^^^^^^^^^

MI bus has these 8 ports + 1 port optional divided into two channels (*the port directions in example are valid for slave MI components*):

.. code-block:: vhdl

    -- ===========================================================================
    -- Ports of MI bus request channel (master to slave):
    -- ===========================================================================
    ADDR : in  std_logic_vector(ADDR_WIDTH-1 downto 0);   -- ADDRess
    DWR  : in  std_logic_vector(DATA_WIDTH-1 downto 0);   -- Data WRite
    MWR  : in  std_logic_vector(META_WIDTH-1 downto 0);   -- Metadata WRite (optional)
    BE   : in  std_logic_vector(DATA_WIDTH/8-1 downto 0); -- Byte Enable
    WR   : in  std_logic;                                 -- WRite
    RD   : in  std_logic;                                 -- ReaD
    ARDY : out std_logic;                                 -- Address ReaDY
    -- ===========================================================================
    -- Ports of MI bus response channel (slave to master):
    -- ===========================================================================
    DRD  : out std_logic_vector(DATA_WIDTH-1 downto 0);   -- Data ReaD
    DRDY : out std_logic;                                 -- Data ReaDY

Address and data widths are determined by respective generic parameters. It is not surprising, that ``ADDR_WIDTH`` states the width of addresses and can be any positive integer, while ``DATA_WIDTH`` states the width of the transferred data and it's value can only be a multiple of 8. The ``META_WIDTH`` states the width of the transferred metadata.

Through the ``ADDR`` port a slave component recieves addresses of target recipients. Target recipients can be addressed individually by their indices (indexes for Americans and such) - they are not influenced by the width of stored data. For example, their addresses can be 0, 1, 2, etc. This is shown on the left side of the picture below. But this approach is not commonly used in our project. In vast majority of cases, addresses of our components are mapped to an address space (of PCI for example). That means each following address is incremented by the number of stored items of data, which is usually one byte (can be more, but never less). This mapped addressing is shown on the right side of the picture below. Let's say the data in the memory is stored in bytes, so each byte has a different address. The width of data stored in these registers is 32 bits, so each register can store four bytes of data, that is four addresses. Therefore in this example, the first register stores four bytes of data with addresses 0, 1, 2 and 3. However, only address of the first byte is sent with a request, so ``ADDR`` will carry value 0. The next four bytes of data will have ``ADDR`` equal to 4, the next will have 8 and so on.

.. image:: docs/mi_addresses_indexed_mapped.svg
    :align: center
    :width: 50 %

These addresses are only valid when a request is being sent, either read or write. If neither of these is active, address can be arbitrary. When multiple slave components are connected to the MI, they must have a defined disjointed address space and incomming requests must be distributed by address decoders (like the *MI_SPLITTER_PLUS_GEN*). That means the slave component recieves only requests that are meant for it and no final address checking is necessary.

``DWR`` carries data to be written into the slave component stated by the address. These data are only valid when a write request is issued (``WR`` is asserted). Please note that the written data can be recieved by slave components in different order, then in which they were sent, as each path to the slave component might have different latency. But data sent to one component will be recieved in order.

``MWR`` is used for the optional transfer of metadata (user-defined) from the master to the slave component. Metadata port is valid with each request (``WR`` or ``RD`` is asserted).

As ``WR`` signals a request to write, ``RD`` signals a request to read. If ``WR`` or ``RD`` is asserted, then ports: ``ADDR``, ``DWR``, ``MWR`` and ``BE`` must have valid values. The valid values of these ports must not change until the request is accepted. Also, ``WR`` and ``RD`` can not be asserted at the same time. The ``ARDY`` indicates whether the slave component is able to accept the request. The request is received when the ``ARDY`` is asserted in the same cycle as ``WR`` or ``RD``. The behavior of the MI bus with a request sent to an undefined address space is not defined and can cause a critical error.

Data comming to master as a response to a read request come from port ``DRD``. These data can be ready at the output even before the read request, so with incoming read request, they can be immediately read. But the slave component can take theoretically as long as it wants to get the data ready. ``DRDY`` validates the data that are being read (``DRD``). The requesting (master) component accepts the read data only when ``DRDY`` is asserted. It is essential for the requesting component to recieve as many responses (asserted ``DRDY`` signals) as it sent read requests **in the same order** as in which they were sent. It is also essential not to assert ``DRDY`` before accepting a read request.

``BE`` is there to define which bytes of the transferred data (``DWR`` or ``DRD``) are valid and should be worked with and which bytes should be ignored. Each bit validates one byte of the data, that is why it is ``DATA_WIDTH/8`` bits wide. Usually, it is used in write transactions, but it may also be used in read transactions.

A few timing diagrams
^^^^^^^^^^^^^^^^^^^^^

to make sure you really understand, how the MI bus works. The optional ``MWR`` signal is not used in these examples.

**A) Simple write transaction & the ARDY occurrences**

.. image:: docs/wave_simple_write.svg
    :align: center
    :width: 100 %
    :alt: A simple write transaction and ARDY

In the first clock cycle, when ``WR`` and ``ARDY`` are both active, data D0 with byte enable B0 are sent to the slave component with the address A0. That is why there are new data (along with address and byte enable, which always go together in write request) in the next clock cycle. Then in the following clock cycle, the ``WR`` is inactive (as is ``RD``), so the slave component can set ``ARDY`` arbitrarily according to its current state.

After the divider, ``WR`` is asserted and so is ``ARDY``, so the data D2 are transferred. In the next clock cycle, new data D3 are ready to by transferred as ``WR`` is active, but now ``ARDY`` is inactive for the next three clock cycles, meaning that the slave component is not ready to accept a write request (nor a read request). After those three clock cycles of inactive ``ARDY``, it is then asserted and data D3 are transferred.

**B) Simple read transaction & the ARDY occurrences**

.. image:: docs/wave_simple_read.svg
    :align: center
    :width: 100 %
    :alt: A simple read transaction and ARDY

This timing diagram is in principle very similar to the previous one. At first, there are two read requests addressed to A0 and A1. slave component/s are ready to immediately respond in this example, so ``DRDY`` is always active when ``ARDY`` is (*rather we recommend* ``DRDY`` *delay of one clock cycle for better timing*). As long as ``RD`` is active, read requests are being generated (2 clock cycles). Then RD deasserts, causing ``DRDY`` to deassert as well.

After the divider, ``RD`` asserts and so does ``ARDY`` (and ``DRDY``) for one clock cycle. Then the slave component signals that it can not accept any more requests by deasserting ``ARDY`` (and ``DRDY`` as well, because it has no read request to respond to). The request does not change until it is accepted (i.e. when ``ARDY`` is asserted again).

**C) Simple read transaction & the DRDY occurrences**

.. image:: docs/wave_adv_read.svg
    :align: center
    :width: 100 %
    :alt: A simple read transaction and DRDY

This diagram focuses on the ``DRDY`` signal. First, there is a simple transaction, a read request with immediate response. Two clock cycles later, when ``RD`` asserts once again, the request is sent but no response is recieved yet. Response comes in the next clock cycle, when ``DRDY`` is asserted. At the same time, new request is issued, because the last one was accepted with ``ARDY`` being asserted.

After that, ``ARDY`` is asserted for four clock cycles along with ``RD``, which means that four read requests are sent. It also means that four responses must be recieved. Because the data in responses are not addressed (or anyhow else identified), the master component expects them to be returned in the same order as it requested them. But there is no time limit for when the responses must be recieved. You can notice this in the diagram. Regardless of when the responses come, they always come in the same order as in which requests were sent. First, data were requested from address A0, so the first response is D0, then data D1 respond to request addressed to A1 and so on.

**D) Combined write and read transactions**

.. image:: docs/wave_rd_wr_combo.svg
    :align: center
    :width: 100 %
    :alt: Read and write requests combined

In this diagram, there is a couple of combinations of read and write transactions to show how they can interact. First comes a read request which is accepted and immediately responded to (as ``DRDY`` is asserted), followed by a write request that is also accepted. Then there is no request for one clock cycle. Two read requests and two write requests follow to show that it is possible to recieve a response in the same clock cycle as a write request is being sent. A response (D2) comes as an answer to the first of these read requests (addressed as A2) one clock cycle later. Next comes one write request followed by another one. With that second write request (addressed as A5) comes a response (D3) to the other read request (addressed as A3).

There are more examples of possible combinations of transactions on the MI. Four read requests are sent and only two responeses are recieved by the end of these four clock cycles. In the following clock cycle, a write request is sent with ``ARDY`` inactive, so it stays the same till the next clock cycle, and at the same time, third response (D8) is recieved. Then in the next clock cycle there is only a write request and in the one after that, there is a write request along with the fourth response (D9).

**E) The byte enable occurrence**

.. image:: docs/wave_be_enh.svg
    :align: center
    :width: 100 %
    :alt: Byte enable in transaction

This diagram aims to show possible utilization of ``BE``. Addresses and data are in hexadecimal format and ``ADDR_WIDTH`` and ``DATA_WIDTH`` are both 16. In the first part of the diagram (before the divider), all requests are sent to a slave component with the address ``1234``. First comes a write request with ``BE = "11"``, saying both bytes of sent data are valid. The component accepts the data, then a read request is issued with ``BE = "10"``, so only the higher byte of data is read. The lower byte of ``DRD`` is not valid, hence it has value ``98XX``, ``98`` being the previously written data and ``XX`` being the invalid ("don't care") data. A write reques follows in the next clock cycle, with ``BE = "10"``. That means the higher byte of ``DWR`` is valid and the lower is not. ``54XX`` then overwrites the current data, so the newly stored data are ``5476``, which are read in the following read request with ``BE = "11"``.

Behind the divider, the slave component of the requests has address ``4321``. **This is a component that clears its stored data after each read request.** First transaction is a write request with ``BE = "11"``. Then a read request is issued with ``BE = "10"``, so the higher byte of the stored data will be read (and then cleared) while the lower byte will be ignored. That is why the ``DRD`` has value ``67XX``. Now the current data stored at this component are ``0089``. The next write request overwrites the lower byte as ``BE = "01"``, so now the stored data are ``0045``. This value is read in the next clock cycle with ``BE = "11"``. Then after the read, the stored data are ``0000``.
