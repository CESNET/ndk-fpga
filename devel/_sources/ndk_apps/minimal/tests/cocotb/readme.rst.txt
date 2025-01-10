=====================
Top-level simulations
=====================

The top-level simulations (TLS) are suitable for:

-  software testing without access to real acceleration card
-  whole design compile and basic functionality check
-  address space debugging
-  resets, clocks, clock domain crossings check

Basics
======

What simulation includes / excludes
-----------------------------------

The TLS doesn’t simulate IP cores but emulates their I/O signals. The
primary effort is to emulate the Ethernet and PCIe I/O and DMA for the most used FPGA families
(Xilinx US+, Intel P-TILE, Intel E-TILE, ...).

Common tips for cocotb
----------------------

-  Use ``sys.stderr`` stream for ModelSim / Questa to achieve instant
   display of log:

   .. code:: python

      logging.basicConfig(stream=sys.stderr, force=True)

-  Verbose messages for all loggers except some:

   .. code:: python

      logging.getLogger().setLevel(logging.INFO)
      logging.getLogger("cocotbext.nfb.ext.grpc.server").setLevel(logging.WARNING)

gRPC example
============

This variant enables the usage of external processes and is intended for
manual interaction. The TLS doesn’t contain any real test cases. Instead, it
starts the gRPC server, runs for a specified simulation time (e.g., 10ms), and
expects the user to execute an application that uses the acceleration
card through the ``libnfb`` gRPC extension. The application then generates
I/O read and write requests and the simulator translates them to the bus
interface and back.

A feature in ``libnfb-ext-grpc`` enables simple handling of DMA requests
from the simulated design. If the ``dma_vas`` tag is present in the device
string, the library opens a reverse stream. As soon as the DMA request
arrives in the process, ``libnfb-ext-grpc`` copies data from/to the virtual
address space of the process. Just use the virtual address for
descriptor values. There are no boundary checks and the request can
potentially harm the process, which probably gets killed by ``SIGSEGV``
signal in the case of an error.

The simple DMA request handling is most suitable for a DPDK application;
see the section below.

Prerequisites
-------------

libnfb-ext-grpc.so from the libnfb-ext-grpc package (RPM)

Running
-------

1. Prepare a Python environment and install packages

   .. code:: shell

      . ./prepare.sh

2. Install specific dependencies for the gRPC-based simulation

   .. code:: shell

      pip install .[grpc]

3. Run the simulation

   .. code:: shell

      make COCOTB_MODULE=cocotb_grpc

4. Wait until this message appears in the console

   ``gRPC server started, listening on 50051. Device string: libnfb-ext-grpc.so:grpc:localhost:50051``

5. Run your software application and specify the device string

   .. code:: shell

      $ nfb-eth -ri0 -d libnfb-ext-grpc.so:grpc:localhost:50051

DPDK usage
----------

DPDK needs to be executed with the ``--vdev`` argument:

.. code:: shell

   sudo dpdk-testpmd --vdev=eth_vdev_nfb,dev=libnfb-ext-grpc.so:grpc+dma_vas:localhost:50051,queue_driver=native --iova-mode=va -- -i

The ``queue_driver=native`` is currently the only supported mode, for which the
``--iova-mode=va`` is essential. The ``dma_vas`` tag also
must be stated in the device string:
``libnfb-ext-grpc.so:grpc+dma_vas:localhost:50051``.

Do not forget to alloc hugepages.

Tips
----

Concurrent processes
^^^^^^^^^^^^^^^^^^^^

The simulation environment can handle requests from multiple running
applications at once. For example: start the ``dpdk-testpmd`` in
interactive mode, enable MACs with ``nfb-eth -e1`` and then type
``start`` in the DPDK app prompt. Be aware that only one application should use
the ``dma_vas`` tag in the device string at a time.

*There is an issue with nfb locks: nfb_comp_lock / nfb_comp_unlock is not
implemented. Two processes mixing requests on one lock-aware component
will probably break its function.*

Locally build libnfb-ext-grpc.so
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the gRPC client library is not in the standard system path (``/usr/lib``),
use the full path in the device parameter:

.. code:: shell

   nfb-info -d /home/joe/ndk-sw/cmake-build/ext/libnfb-ext-grpc/libnfb-ext-grpc.so:grpc:localhost:50051

Remote access to TLS
^^^^^^^^^^^^^^^^^^^^

Listen on all IP addresses:

``NfbDmaThreadedGrpcServer(ram, dev, addr='0.0.0.0')``

and run the application on another machine with the ``target_addr:port`` string in the device parameter.

