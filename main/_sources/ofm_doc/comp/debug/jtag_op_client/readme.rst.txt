.. _jtag_op_client:

JTAG-over-protocol Client
-------------------------

This component is used for software communication with internal debug hardware present on Intel FPGAs.
It acts as MI wrapper of the *JTAG-over-protocol IP* core and provides the capability of debugging card designs via e. g. SignalTap over PCIe without the need of connecting a JTAG cable.
The debugging is done via a running instance of ``etherlink`` application which translates the traffic between JTAG server (communicating with SignalTap) and nfb driver.

Address space size
^^^^^^^^^^^^^^^^^^

Size of the *JTAG-over-protocol IP* address space depends on the configuration given while generating the IP core.
The total memory occupied by the component consists of three distinct memory blocks for each subpart (as mentioned in the `documentation of the IP core`_).

- Minimum size is ``0x1800`` (``3 * 0x0800``) items for memory depth of 2048 items or less -> address width = 13 bits.
- Default size is ``0x4000`` (``3 * 0x1000`` + padding) items for memory depth of 4096 items -> address width = 14 bits.
- Maximum size is ``0xc000`` (``3 * 0x4000``) items for memory depth of 16384 items -> address width = 16 bits.


Debugging - HW part
^^^^^^^^^^^^^^^^^^^

1. instantiate JTAG_OP_CLIENT component
    - while building design on top of NDK
        - the component is already present in the design on address ``0x00010000``
        - the address space provided is sufficiently large (``0x00010000``)
    - while building without the use of NDK
        - component folder is located under the OFM repository at ``<ofm path>/comp/debug/jtag_op_client``
        - also add the component to the top-level ``DevTree.tcl`` file for gaining sw access to the component

2. create *.stp* file
    - use Quartus Prime SignalTap Logic Analyzer software to add debug logic to your design
    - debug logic can alternatively be added to the design via corresponding IP core instantiations directly in source code
    - without debug logic present in the design, JTAG chain ends up being broken (no debug logic to communicate with)

3. enable JTAG_OP_CLIENT
    - the component is disabled by default
    - to enable it, add ``set VIRTUAL_DEBUG_ENABLE true`` to the app_conf.tcl file

4. build design
    - with JTAG_OP_CLIENT component (enabled) and debug logic added

5. configure device
    - upload the design to the target device (NFB card)


Debugging - SW part
^^^^^^^^^^^^^^^^^^^

1. install the etherlink rpm package
    - download the prebuilt rpm package (via the CESNET Copr or from `the app github repository`_ releases) or
    - alternatively, build the app directly from source code via the commands in README.md file
    - (to build the package manually, clone *hak-rpm-pkg* branch from `the app github repository`_ and execute the commands below)

.. code-block:: bash

    # install the prebuilt rpm via Copr
    sudo dnf copr enable @CESNET/nfb-framework
    sudo dnf install remote-debug-for-intel-fpga

.. code-block:: bash

    # build the rpm manually
    git clone https://github.com/CESNET/remote-debug-for-intel-fpga
    cd remote-debug-for-intel-fpga
    git switch hak-rpm-pkg
    cmake . -Bbuild && cd build
    cpack

    # install the package (built or downloaded)
    sudo su
    rpm -i <rpm package name>

.. code-block:: bash

    # build the app from source code (app will be installed to 'usr/local/bin')
    git clone https://github.com/CESNET/remote-debug-for-intel-fpga
    cd remote-debug-for-intel-fpga
    cmake . -Bbuild && cd build
    make
    sudo make install

2. run ``jtag_op_mgmt.py`` script with sudo privileges on the machine hosting the target device
    - the script is located under ``<ofm_path>/comp/debug/jtag_op_client/sw/jtag_op_mgmt.py``
    - the script runs an instance of the ``etherlink`` application (its location is expected under ``/usr/local/bin/etherlink``)
    - after that, it registers the application for communication with the jtag server (running on the same host)
    - check the script options when sw paths different from the default ones are needed (for ``etherlink`` or ``jtagconfig``)
    - the script gets all the information from the Device Tree of the currently loaded design (using ``nfb`` module) and via ``ss`` command (for etherlink port info)

.. note::
    Only one running instance of the application is supported in the current implementation.
    You can list open JTAG connections by issuing ``jtagconfig``.
    Be sure to unregister the JTAG connection after you are done with debugging (run ``jtagconfig --remove <#>`` where <#> is the JTAG-over-protocol option number).


Debugging - DEBUG part
^^^^^^^^^^^^^^^^^^^^^^

1. open the .stp file used for build
    - use Quartus Prime SignalTap Logic Analyzer on the host machine to start debugging the design with .stp file

2. configure the SignalTap logic Analyzer
    - in the JTAG Chain Configuration pane set JTAG-over-protocol as the hardware option and wait until the chain is scanned

3. analyze the results
    - use SignalTap as you were used to and enjoy life without JTAG cables

.. _documentation of the IP core: https://www.intel.com/content/www/us/en/docs/programmable/728673/21-3/jtag-over-protocol-parameters.html
.. _the app github repository: https://github.com/CESNET/remote-debug-for-intel-fpga
