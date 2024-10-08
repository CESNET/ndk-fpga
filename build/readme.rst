.. _ofm_build_system:

Build System
==================

This build system has been developed for easier implementation and
simulation of the large projects and individual components as well.
The main idea is based on the uniform definition of components hierarchy,
which is used for sythesis and simulation purposes.
Translation system is mainly implemented using Makefile and Tcl scripts.
The Tcl language is independent of target operation system and it is
supported in the most of tools dedicated for hardware developement.

Hierarchy description in Modules.tcl
------------------------------------

The objective of hierarchy description is to define a structure of
complex projects. Generally, a project is composed of several components
and a component is recursively composed of several subcomponents and
modules. Further, each subcomponent can occure in several instances and
each subcomponent instance can use a different architecture.
The Modules.tcl file describes all direct necessary dependencies (e.g. instantiated
subcomponents or packages) for the component and the source
file of the component itself. Sometimes it may also be appropriate to include
more independent components into one Modules.tcl file as one bundle. In such
cases, it is recomended to include only source files from the same directory
as the Modules.tcl file, exceptionally from direct subdirectories.
file.

For the definition of a component structure two variables are reserved - ``MOD`` and
``COMPONENTS``. The ``MOD`` variable specifies the list of modules (typically
VHDL files in current directory) while the ``COMPONENTS`` variable specifies
the subcomponent list of the component.

Variables in Modules.tcl obtained by the build system
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. role:: tcl(code)
   :language: tcl

- **PACKAGES** defines the list of VHDL files, which serve as packages.
  These packages are usually used at the begining of VHDL files using command
  "use library.package_name.function". Via this build system, packages are translated sooner than other
  VHDL modules and components. During translation, the order of files defined in
  variable is preserved. Common packages used by multiple sources are usually
  included in Modules.tcl for top-level, not in component's Modules.tcl.

- **MOD** variable defines the list of modules (VHDL or Verilog source files),
  which specify the component structure. It's important to preserve
  the order of modules declared in this list. Module used by another module in
  current Modules.tcl scope has to be defined
  sooner in the list.

- **COMPONENTS** defines the list of subcomponents, needed for the component.
  Each item of the list is also the list with following parameters:

    .. code-block:: tcl

        [list ENTITY ENTITY_BASE ARCHGRP]

  - *ENTITY* specifies the entity name. It's used by the Translation System to
    distinguish between several entities in the same directory, although it is not commonly used.

  - *ENTITY_BASE* defines the path to the subcomponent. It's strongly recommended
    to specify this path relatively to another directory (mostly to the root folder of currently used
    git repository), the current ``ENTITY_BASE`` should be used for this purpose. Target path must
    contain the Modules.tcl file, which will be parsed.

  - *ARCHGRP* specifies the architecture (or more architectures) of a subcomponent.
    For example, architecture can be an empty implementation (string ``EMPTY``) or a full implementation (string ``FULL``),
    but the value can also be a list of specific configurations to its subcomponents.

- **SV_LIB** List of dynamic libraries used for SystemVerilog DPI verification.
  If the dynamic library file doesn't exist, the build system requires existing
  Makefile in the same directory and executes make.

.. note::
  Do not include prefix (lib) nor suffix (.dll or .so) in the filename.

Variables ``ENTITY``, ``ENTITY_BASE`` and ``ARCHGRP`` are predefined (provided) by the build system to be used in every Modules.tcl file. Their values are obtained from the respective ``COMPONENT`` list item of the ancestor's Modules.tcl.

.. note::
  Prefer to use :tcl:`lappend MOD "myfile.vhd"` instead of :tcl:`set MOD "$MOD myfile.vhd"`,
  because the ``lappend`` better express the operation and is faster.

.. _extra file properties:

List of properties used in MOD variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For translation, it is often required to specify more of the details about items (files)
present in ``MOD`` and ``PACKAGES`` variables. In this case the translation
system can get a list with property name and value pairs instead of a single item, e.g.:

.. code-block:: tcl

    lappend MOD [list $ENTITY_BASE/myfile.vhd LIBRARY another_lib SIM_MODULE glbl]

- **LIBRARY** specifies another library name than default `work` into which the module will be compiled.

- **TYPE** overrides automatically selected file type which is otherwise based on the file extension. Currently supported types are:

  - *CONSTR_QUARTUS*
  - *CONSTR_VIVADO*
  - *VIVADO_IP_XACT* - automatically used for *xci* files

- **SCOPED_TO_REF** - only for the CONSTR_VIVADO type, calls ``set_property SCOPED_TO_REF`` for the file

- **PROCESSING_ORDER** - only for the CONSTR_VIVADO type, calls ``set_property PROCESSING_ORDER`` for the file

- **USED_IN** - only for the CONSTR_VIVADO type, calls ``set_property USED_IN`` for the file

- **VIVADO_SET_PROPERTY** calls ``set_property {*}$value`` for the file

- **SIM_MODULE** - the file uses another module for simulation, which must be simulated together like this: ``vsim extra_module testbench``

- **SIM_LIB** - the file uses a simulation library which must be loaded like this: ``vsim -L extra_library testbench``

Example of using properties
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: tcl

   lappend MOD [list $ENTITY_BASE/dp_bmem_behav.vhd VIVADO_SET_PROPERTY [list -quiet FILE_TYPE {VHDL}]] ;# set the VHDL98 standard for this file
   lappend MOD [list "$ENTITY_BASE/bus_handshake.xdc" TYPE "CONSTR_VIVADO" SCOPED_TO_REF "ASYNC_BUS_HANDSHAKE" PROCESSING_ORDER "LATE"]

List of properties used in SV_LIBS
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- **MAKE_PARAMS** - value will be passed to ``make`` command as the parameters


Example of using Modules.tcl variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: tcl

    # HFE top level entity
    if {$ENTITY == "HFE_TOP"} {
       if {$ARCHGRP == "FULL"} {
          # This architecture relies on HFE component, which is located
          # in the same directory as current entity and shares this Modules.tcl file.
          lappend COMPONENTS [list HFE $ENTITY_BASE FULL]

          # This file will be compiled to library work
          lappend MOD $ENTITY_BASE/file_to_work.vhd

          # This file will be compiled to library anotherlib
          lappend MOD [list $ENTITY_BASE/file_to_anotherlib.vhd LIBRARY anotherlib]
       }

       if {$ARCHGRP == "EMPTY"} {
          lappend MOD $ENTITY_BASE/hfe_empty.vhd
       }
    }

    # HFE core entity
    if {$ENTITY == "HFE"} {
       if {$ARCHGRP == "FULL"} {
          lappend MOD "$ENTITY_BASE/hfe_pipe.vhd"
          lappend MOD "$ENTITY_BASE/hfe_parser.vhd"
          lappend MOD "$ENTITY_BASE/hfe_full.vhd"
       } elseif {$ARCHGRP == "EMPTY"} {
          lappend MOD "$ENTITY_BASE/hfe_empty.vhd"
       }
    }


Component synthesis
-------------------

Synthesis of the component is typically handled by a simple user-created ``Makefile``.
It can be located anywhere, but the recommendation is to use the ``synth`` subdirectory of the synthesized component.
The ``Makefile`` sets the ``TOP_LEVEL_ENT`` variable and calls the ``comp`` target
from global ``Makefile`` located in ``$OFM_PATH/build/Makefile``, which must be *included*.
After calling ``make`` the synthesis will be performed.

Advanced synthesis configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

User can specify those variables in ``Makefile``:

- TOP_LEVEL_ENT - *required*.
  Name of the synthesized entity.

- TOP_LEVEL_PATH - *optional, default value is ".."*.
  Path to the Modules.tcl with the synthesized entity.

- TOP_LEVEL_ARCHGRP - *optional, default value is "FULL"*.

- CLK_PORTS - *optional, default value is CLK*.
  Name or list of space-separated names of component ports which serves as clock input.

- CLK_PERIOD - *optional, default value is 5.0*.
  One or more space-separated integer or float values. Clock constraints will be generated
  with this value in ns. If there are more CLK ports than period values,
  unspecified periods will be calculated with a simply formula (add 1.0 for each next clock).

- SYNTH - *optional, default value is "vivado"*.
  Synthesis tool can be {vivado, quartus}.
  For lazy users, there is a ``vivado`` / ``quartus`` target in global ``Makefile``,
  which sets this variable and calls ``make`` recursively with the default target.

Example of Makefile for component synthesis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: Makefile

   TOP_LEVEL_ENT=RX_MAC_LITE
   TOP_LEVEL_PATH=../../mac/rx

   SYNTH=quartus

   CLK_PORTS=RX_CLK TX_CLK MI_CLK
   CLK_PERIOD=3.500 2.500 5.000

   .PHONY: all
   all: comp

   include ../../../../../build/Makefile

.. _comp target:

The ``comp`` target in Makefile
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``make comp`` runs the ``comp_$(SYNTH).tcl`` script located in ``$OFM_PATH/build/targets/`` with the synthesis tool.
Script sets some default values for mandatory variables and fetches environment variables listed above.
The script also tries to source ``Vivado.inc.tcl`` / ``Quartust.inc.tcl`` file (if it exists) in a current directory.
This can be useful for overriding some variables, e.g. ``SYNTH_FLAGS`` or ``CONSTR_TEXT``.

User should override the ``CONSTR_TEXT`` variable in this file for example when the ``TOP_LEVEL_ENT`` has very specific clock/constraints requirements.
The constraint file for current synthesis tool is generated from the ``CONSTR_TEXT`` variable at the end of the preparation.
The file is overwritten only when needs to be updated, otherwise is leaved untouched, which is useful for typical ``make`` run: If all sources are unchanged from the last build,
the targed file (synthesised project) is up-to-date and doesn't need to rebuild.

Finally, the script calls default Tcl target (proc ``target_default``) which then passes to ``SynthesizeProject`` procedure documented below.


Chip design synthesis and implementation
----------------------------------------

It is a good practice to split common functionality from application specific functionality:

a) top-level entity of card together with main constraints and build scripts,
b) application entity for end user with minimum build scripts.

In this scheme, the process basically starts at the user Vivado/Quartus.tcl file (the default value of ``SYNTHFILES`` variable in Makefile)
where the user includes a common build script from a top-level entity.
This fills the ``HIERARCHY`` array with varables ``COMPONENTS`` and ``MOD`` and sets up other neccessary values in ``SYNTH_FLAGS`` array.

After Tcl interpreter goes back from common build script, the user tcl should add architecture (implementation) of application entity into the appropriate variables of ``HIERARCHY`` array, either ``MOD`` or ``COMPONENTS``.
User tcl can tune some values of SYNTH_FLAGS as well.

Final step in user tcl file is to call the ``nb_main`` procedure, which passes to SynthesizeProject_ procedure within ``target_default`` similarly as in the `comp target`_.

.. _SynthesizeProject:

SynthesizeProject
-----------------

1. Init phase (SetupDesign)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This creates a project within synthesis tool, sets the FPGA device type and does the necessary project setup before adding any source files.

2. File add phase (AddInputFiles)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this stage, files and components are processed from HIERARCHY array and passed to procedure EvalFile_.
EvalFile is called for each entry in PACKAGES/MOD variables and should instruct the synthesis tool to compile source file including fine-tunnig of additional properties based on `extra file properties`_

3. Synthesis and Implemenation (SynthetizeDesign, ImplementDesign)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Procedures configure rest of parameters of the project and run the main process: the synthesis and the implementation.

4. Final phase (SaveDesign)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this step, the binary programming file is generated.


Other features of the build system
----------------------------------

.. _EvalFile:

EvalFile
~~~~~~~~

EvalFile procedure is specific for each synthesis tool and is being used as callback
when the common code goes through hierarchy of modules. Procedure usually adds
source files into the project and sets additional properties based on `extra file
properties`_.

Batch feature in EvalFile
~~~~~~~~~~~~~~~~~~~~~~~~~

Although the EvalFile procedure receives one file for processing in each call,
it can use the lazy evaluation mechanism, which processes a batch of source
files in one command run. This mechanism is enabled in the simulation environment
(Modelsim.inc.fdo file), where it has significantly positive impact on compilation time.

Source files which have the same compile flags (e.g. same library name or -vhdl2008 parameter)
are stored into the special variable together with the flags instead of being processed (compiled) immediately.
When EvalFile gets a file with a different set of flags, the files stored inside the batch variable must be compiled immediately, the variable is then emptied and the newly evaluated file is inserted into it.
At the end of the AddInputFiles phase, the last batch must be compiled explicitely.

Makefile
~~~~~~~~

There are few mechanisms in the global Makefile which deserve an explanation.

Some targets in the Makefile are aware of unchanged files. If none of the source files
for such target has been modified and the target already exists, it will not be remade.
This is handled by the ``make`` itself, but the build system must supply a list of source files.
The list is generated by executing Tcl target called 'makefile', which goes through entire hierarchy of Modules.tcl,
gathers filenames and writes the list in form of ``target: prerequisites`` into ``$PROJECT.$SYNTH.mk`` file,
which is simply included in the main Makefile. This approach is not so simple and hides some caveats.
Makefile doesn't propagate `target specific variables <https://www.gnu.org/software/make/manual/html_node/Target_002dspecific.html>`_
to global scope and it is unreliable to get prerequisites for generated Makefile.
Hence the generated Makefile is created (by shadowed target with same name) in the first ``make run`` (only for concerned targets)
and the real main target is launched in a recursive run of ``make``.

Environment variables available in ``make`` run aren't exported to subprocess, except variables which are set using the ``export`` keyword.
If the user needs to pass an environment variable into tclsh or synthesis tool, it's better he uses the ``USER_ENV`` variable.
It is a necessity to export user defined variable for targets which needs a generated makefile mentioned above.

There are also targets, which can trigger an user defined procedure in Tcl: ``ttarget_%`` and ``starget_%``.
The user defines a Tcl procedure named for example ``target_myproc``.
Executing ``make ttarget_myproc`` will trigger the `stem <https://www.gnu.org/software/make/manual/html_node/Pattern-Intro.html>`_ target:
either bare tclsh (ttarget) or synthesis tool (starget) is started, the ``$SYNTHFILES`` script
is sourced and if the script includes common ``build/[Vivado|Quartus|...].inc.tcl`` script
and runs nb_main (which is recommended for best integration with build system),
the user defined procedure will be run.

This is also used for generating a source files inside the Tcl from make target.
Common used files are DevTree.dts/dtb/vhd and user_const.vhd.

The (incomplete) list of SYNTH_FLAGS array items
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- PROJ_ONLY *{false, true}*: Only the project file will be created. Neither synthesis nor implementation will be run.
- SYNTH_ONLY *{false, true}*: Only the synthesis will be run, the implementation will be skipped.
- PHASE_SAVE *{true, false}*: Do not generate programming files and archives after implementation.
- DEVICE *{ULTRASCALE, VIRTEX7, STRATIX10, AGILEX}*: Sets the FPGA family. In the `comp target`_ is mapped to specific FPGA.
- FPGA *{xcvu7p-flvb2104-2-i, 1SD280PT2F55E1VG, ...}*: Sets the FPGA part directly.
- SETUP_FLAGS: List of specific flags for entire project:
   - USE_XPM_LIBRARIES: includes XPM_CDC XPM_MEMORY XPM_FIFO in Vivado projects

For other values and their purpose see the Vivado.inc.tcl or Quartus.inc.tcl file in the build directory.
