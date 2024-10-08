===============================
HDL Application Runner Platform
===============================

A script for HDL build and verification processes.

Description
-----------

harp is a Python script that provides functionality for HDL synthesis
and verification processes. It supports verification and multiverification and is prepared for
extension with various synthesis and simulation tools.

Features
--------

- Supports multiple commands: ver, multiver (TODO synth and multisynth)
- Configurable via TOML configuration file
- Run with GUI support
- Dry run capability with all combinations stored in Markdown or CSV format
- Logging level configuration for debugging
- Combination dry evaluation
- Integration with QuestaSim for verification

Installation
------------

To use harp, ensure you have Python installed along with the following dependencies:

- tomli
- pydantic
- pandas
- cowsay
- colorama
- argparse

You can install harp using this command (dependencies are installed automatically):

.. code-block:: bash

    pip install .

Usage
-----

To use the script, one must create configuration file. Default name for config file
is "harpproject.toml" in root folder of entity. To create this file, read section
"Enitity configuration". After creating this file, to run verification with defualt settings
just run this command:

Example:

.. code-block:: bash

    harp ver        # command line only or
    harp ver --gui  # with gui

To run multi verification with all combinations:

.. code-block:: bash

    harp multiver   # no gui only

After multi verification finished, if any combination verification failed,
all failed combinations are stored inside "failed_comb.csv" file along with system verilog seed.

To run failed combination, just run:

.. code-block:: bash

    harp --gui --failed-comb ./failed_comb.csv 0  # run first failed combination

For now, one must set random seed manually in "top_level.fdo". Automatic setting
of seed can be added upon request.

For debugging purposes you can store all combinations in markdown file or csv file using
this commands:

.. code-block:: bash

    harp --dry md   # markdown, human readable format
    harp --dry csv  # csv, machine readable format

Another good debugging feature is listing generic settings of one combination:

.. code-block:: bash

    harp --comb regions # Show generics for combination named "regions"

In the case of some errors during combination evaluation, it may useful to increase
logging level:

.. code-block:: bash

    harp multiver --log-level DEBUG

Verification setup
~~~~~~~~~~~~~~~~~~

Generics of entities are passed to QuestaSim through command line and they modify
generics of top level module. For our typical usage, testbench of UVM verification
must be parametrized and parameters must be passed to tests. All tests must have
"uvm_component_registry" macro:

.. code-block:: sv

    typedef uvm_component_registry#(test::ex_test #(MFB_REGIONS, MVB_ITEMS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH), "test::ex_test") type_id;

Testbench may look like this:

.. code-block:: sv

    module testbench #(
        int unsigned MVB_ITEMS,
        int unsigned MVB_ITEM_WIDTH_RAW,
        int unsigned MFB_REGIONS,
        int unsigned MFB_REGION_SIZE,
        int unsigned MFB_BLOCK_SIZE,
        int unsigned MFB_ITEM_WIDTH,
        int unsigned MFB_ALIGNMENT,
        int unsigned MFB_META_WIDTH,
        string DEVICE
    );

    ...

    initial begin
    ...

Full example of setup verification for harp can be found in folder "comp/mvb_tools/flow/mvb2mfb".

Entity configuration
--------------------

Build system
~~~~~~~~~~~~
One can define folders, in which necessary files are contained. This configuration
is optional has default values.

- synth_folder: Synthesis folder containing Makefile (default: "synth")
- ver_folder: Verification folder containing verification .fdo file (default: "uvm")
- ver_fdo_file: Verification FDO file name (default: "top_level.fdo")

Example:

.. code-block:: toml

    [build_system]
    synth_folder = "synth"
    ver_folder = "ver"
    ver_fdo_file = "custom_top_level.fdo"

Generics setting
~~~~~~~~~~~~~~~~

HARP currently supports generics of type int (VHDL - integer, natural), string and boolean.
Each generic can be set to a value from a defined set and it will be set to every value from
that set. Sets can be defined in multiple ways:

- constant,
- list,
- generator.

Constant defines a set with only one value. A set defined by a list is equivalent to a set
defined by an enumeration of values. The generator produces a set that is the image
of a function whose definition scope can be defined by a Python iterable object.

Example:

.. code-block:: toml

    # Constant, creates set [48]
    [setting.mvb]
    DATA_WIDTH = 48

    # List, creates set [48, 64, 256]
    [setting.mvb]
    DATA_WIDTH = {type = "list", value = [48, 64, 256]}

    # Alternative and equivalent list setting
    [setting.mvb.DATA_WIDTH]
    type = "list"
    value = value = [48, 64, 256]

    # Generator, creates set [64, 128, 256]
    [setting.mvb.DATA_WIDTH]
    type = "gen"
    # Definition of function
    value = "lambda x : 2**x"
    # Definition scope of the function
    range = "range(6, 8+1)"

As you might have noticed, individual settings are created as follows:

.. code-block:: toml

    [settings.<setting_name>.<generic_name>]

Setting name must be unique. Also one must create "default" setting, which has two functions:
- Enumaration of available generics of entity
- Default values for generics, which are not modified by a setting.
Default setting must be defined only with constants.

It is important to note that multiple combinations can be created within a single setting.
Within a single setup, the Cartesian product of the sets of values of all generics is performed.

.. code-block:: toml

    # Generator, creates set [64, 128]
    [setting.mvb.ITEM_WIDTH]
    type = "gen"
    value = "lambda x : 2**x"
    range = "range(6, 7+1)"

    # Generator, creates set [1, 2]
    [setting.mvb.ITEMS]
    type = "gen"
    value = "lambda x : 2**x"
    range = "range(0, 1+1)"

In the example above, setting "mvb" will contain combinations:

 ======= ============
  ITEMS   ITEM_WIDTH
 ======= ============
      1           64
      1          128
      2           64
      2          128
 ======= ============

There is also one special type of setting, which contains individual combinations, without
cartesian product performed between sets.

.. code-block:: toml

    # Each column is one combination
    [settings.regions]
    type = "list"
    REGIONS     = [1, 2, 1, 1, 1, 1]
    REGION_SIZE = [8, 8, 1, 2, 2, 4]
    BLOCK_SIZE  = [8, 8, 8, 8, 4, 8]
    ITEM_WIDTH  = [8, 8, 8, 8, 8, 8]

Creating combinations
~~~~~~~~~~~~~~~~~~~~~

Setting combinations are created separately for verification and synthesis. Each combination
must have a name and list of settings to apply. By default, cartesian product is performed
between the settings. It implies, that applied settings must not have overlapping generics.
Combinations are specified in list of tables. Simple verification combination definition
can look like this:

.. code-block:: toml

    [[ver.combinations]]
    name = "Regions"
    description = "This description is totally optional, but may be useful"
    settings = ["regions", "fifox_size"]

When creating synthesis combination, one just replaces "ver" with "synth" in the table creation.

One can also create in a "distributive" way. For example, one wishes to create combinations like this:

- regions
- regions, pipe_on
- regions, output_reg
- regions, special_device

Instead of creating individual combination for each case, this can be written like this:

.. code-block:: toml

    [[ver.combinations]]
    name = "Regions"
    description = "This description is totally optional, but may be useful"
    settings = ["regions", ["", "pipe_on", "output_reg", "special_device"]]

The empty string represents no setting, which enables creating combination with setting "regions".
One can use same principle with empty string for grouping multiple combinations without any common
setting.

Verification can have special random combination. It can be useful, if one manages to create huge
amounts of combinations, which would run almost forever. This combination will select given amount
of combinations randomly. This feature is to be implemented as deemed non essential.

.. code-block:: toml

    [ver.rnd]
    settings = ["regions", "big_setting0", "big_setting1", ...]
    # Select 8 random combinations
    amout = 8

Special directives
~~~~~~~~~~~~~~~~~~

HDL components usually have some restrictions for their generics. Creating exact settings
and combinations without violating those restrictions may difficult. Thus, one can specify
assertions on the generics, which must be true. Combinations which violate those assertions
are filtered out.

.. code-block:: toml

    [generics]
    asserts = [
    """(MVB_ITEM_WIDTH_RAW >= MFB_REGION_SIZE * MFB_BLOCK_SIZE * MFB_ITEM_WIDTH) \
    or (MFB_ALIGNMENT == MFB_REGION_SIZE * MFB_BLOCK_SIZE)""",
    "(MVB_ITEM_WIDTH_RAW % MFB_ITEM_WIDTH) == 0",
    """(MFB_ALIGNMENT <= MFB_REGION_SIZE*MFB_BLOCK_SIZE) and \
    (MFB_ALIGNMENT >= MFB_BLOCK_SIZE)""",
    ]

Example configuration can be found in "comp/mvb_tools/flow/mvb2mfb/harp.toml"

Authors
-------

- Oliver Gurka <oliver.gurka@cesnet.cz>
