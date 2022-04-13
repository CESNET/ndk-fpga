Basic logic elements
====================

**AFTER_ONE** - The unit sets all output bits to high if they have a higher index than the first one in the input vector. Example: DI="00100000" => DO="11000000".

**ALU** - ALU implementation based on Xilinx 7-Series DSP slices.

**AND** - Behavioral implementation of generic AND.

**BARREL_SHIFTER** - Generic barrel shifter. You can set data width and shift direction.

**BARREL_SHIFTER_DSP** - Barrel shifter implementation based on Xilinx 7-Series DSP slices.

**BEFORE_ONE** - The unit sets all output bits to high if they have a lower index than the first one in the input vector. Example: DI="00100000" => DO="00011111".

**BIN2HOT** - Behavioral implementation of binary to one-hot converter with enable.

**CARRY_CHAIN** - Generic structural implementation of carry chain. 

**CMP** - Generic implementation of comparator. It contains behavioral variant and also DSP variant based on Xilinx 7-Series DSP slices.

**CNT** - Fast counter with generic width and direction. Fast counter without load.
Solves problem in synthesis of standard counter in Leonardo.

**CNT_DIST** - Array of counters in distributed memory. Useful for saving resources when many and big counters are needed.
Counters are stored in distributed memory and increased (or cleared) sequentialy.
Cannot be used where increasing of counters is needed in one period.

**CNT_MULTI_MEMX** - Statistics counters for multiple channels implemented using SDP_MEMX.

**COUNT** - Generic implementation of counter. It contains behavioral variant and also DSP variant based on Xilinx 7-Series DSP slices.

**DEC1FN** - Decoder 1 from N is a generic component that converts input vector in binary code into the code 1 from N (one-hot).
There is also a variant with an enable signal and a variant with a reverse coding direction (one-hot to binary converter).

**DEMUX** - Behavioral implementation of generic demultiplexer with generic default value for unselected outputs.

**DSP_XOR** - Generic XOR implementation based on Xilinx DSP48E2 slice.

**EDGE_DETECT** - Behavioral implementation of rising edge detector. One cycle pulse on output when rising edge was detected on input.

**ENC** - Behavioral implementation of generic encoder (one-hot to binary converter). With some optimalizations for Xilinx FPGAs.

**FIRST_ONE** - Behavioral implementation of generic detector of first one in input vector. Output vector one-hot encoded.

**GEN_NOR** - Behavioral implementation of generic NOR. With some optimalizations for Xilinx FPGAs (use of fast carry chain wires).

**LAST_ONE** - Behavioral implementation of generic detector of last one in input vector. Output vector one-hot encoded.

**LFSR_SIMPLE_RANDOM_GEN** - Simple LFSR pseudo-random generator uses Fibonacci implementation of LFSR with XNOR gate.

**MOD** - Behavioral implementation of generic modulo constant block. TODO

**MODULO_LOOKUP** - Behavioral implementation of Modulo look-up table in ROM. Optimized for Xilinx FPGAs only.

**MUL48** - Implementation of generic multiplier based on Xilinx 7-Series DSP slices.

**MUX** - Behavioral implementation of generic multiplexer. It also contains a one-hot variant and an extended registered variant (piped).

**MUX_DSP** - Implementation of generic multiplier based on Xilinx 7-Series DSP slices.

**N_LOOP_OP** - The unit performs multiple parallel read-modify-write operations over an multi-port memory (NP_LUTRAM). Detailed :ref:`documentation can be found here<n_loop_op>`.

**N_LOOP_OP_PRO** - This unit serves the same purpose as the N_LOOP_OP unit, but is based on NP_LUTRAM_PRO. This means, that it requires additional double speed CLK2 and has lesser chip resource usage.
Expert knowledge is required to use this component!

**N_ONE** - Detector of a variable number (N) of ones in the input vector. The value of N is set by the input binary signal. 

**N_TO_M_HANDSHAKE** - Connects N sources and M destination using shared (SRC_RDY, DST_RDY) handshake.
Data is only transfered when all sources and all destinations are ready.

**OR** - Behavioral implementation of generic OR.

**PIPE_DSP** - Implementation of N one detector
 
**PIPE_TREE_ADDER** - Creates a tree of adders with registers in between to add multiple values together.
Tries to use as simple adders as the set latency allows. It has a valid bit for each input.

**SHIFTER** - Behavioral implementation of left or right block-by-block shifter.

**SQUARER** - The unit is used for calculation square (n^2** of input vector.

**SR_SYNC_LATCH** - Synchronous SR latch whose forbidden state has been removed. Latches data of variable length. Detailed documentation can be found :ref:`here<sr_sync_latch>`

**SUM_ONE** - Behavioral implementation of generic counter of ones in input vector.

**XOR48** - Parallel bitwise XOR implementation based on Xilinx 7-Series DSP slices.

.. toctree::
   :maxdepth: 1
   :hidden:
          
   comp/base/logic/n_loop_op/readme
   comp/base/logic/sr_sync_latch/readme
..  comp/base/logic/<something>
..  Add more references here...


