.. _barrel_shifter:

Barrel Shifter
==============

A high-performance parameterized barrel shifter component for digital logic designs,
implementing fast multi-bit shift and rotate operations in constant time. Supports
configurable data widths, shift directions (left/right).


We present the results of several tests for different implementations of Barrel Shifter.
Tests have been done with Vivado 2025.1 (AMD/Xilinx).


.. note::

    These implementations (V0, V1, V2, V3, V4) are not 100% tested. They have been used only for resource elaboration.
    Implementation of barrel_shifter in git is tested.



.. code-block:: VHDL
   :caption: V0 - Implements barrel shifting by computing block indices with modulo arithmetic for each output block via a multiplexer process.

    architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
        constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
    begin

        multiplexors: for i in 0 to BLOCKS-1 generate
            process (DATA_IN, SEL)
                variable sel_aux : integer;
                variable sel_blk : integer;
            begin
                if (SHIFT_LEFT) then
                    sel_aux := conv_integer('0'&SEL);
                else
                    sel_aux := conv_integer('0'&(0-SEL));
                end if;

                sel_blk := ((BLOCKS-sel_aux+i) mod BLOCKS);

                DATA_OUT((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH) <= DATA_IN((sel_blk+1)*BLOCK_WIDTH-1 downto sel_blk*BLOCK_WIDTH);
            end process;
        end generate;

    end architecture;


.. code-block:: VHDL
   :caption: V1 - Uses conditional generation and arithmetic to precompute source block indices per output block, avoiding repeated modulo operations.

    architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
        constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
        signal sel_blk : integer range 0 to BLOCKS-1;
    begin

        sel_int_gen : if (BLOCKS > 1) generate
            sel_int <= to_integer(unsigned(SEL));
        else generate
            sel_int <= 0;
        end generate;

        multiplexors: for i in 0 to BLOCKS-1 generate
            signal sel_int : integer range 0 to BLOCKS-1;
        begin

            shift_sel_gen : if (SHIFT_LEFT) generate
                sel_blk <= i + sel_int when sel_int <= (BLOCKS -i) else sel_int - (BLOCKS -i);
            else generate
                sel_blk <=  (BLOCKS-1 -i) - sel_int when sel_int < i else i - sel_int;
            end generate;

            DATA_OUT((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH) <= DATA_IN((sel_blk+1)*BLOCK_WIDTH-1 downto sel_blk*BLOCK_WIDTH);
        end generate;

    end architecture;


.. code-block:: VHDL
    :caption: V2 - Duplicates input data and selects output via direct slicing on the extended vector, avoiding block-wise indexing.

    architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
        constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
        signal data_in_tmp  : std_logic_vector(2*DATA_WIDTH-1 downto 0);
        signal sel_int : integer range 0 to BLOCKS-1;
    begin

        data_in_tmp <= DATA_IN & DATA_IN;

        sel_int_gen : if (BLOCKS > 1) generate
            sel_int <= to_integer(unsigned(SEL));
        else generate
            sel_int <= 0;
        end generate;

        shift_sel_gen : if (SHIFT_LEFT) generate
            DATA_OUT <= data_in_tmp(DATA_WIDTH   -1 + (sel_int*BLOCK_WIDTH) downto          0 + (sel_int*BLOCK_WIDTH));
        else generate
            DATA_OUT <= data_in_tmp(DATA_WIDTH*2 -1 - (sel_int*BLOCK_WIDTH) downto DATA_WIDTH - (sel_int*BLOCK_WIDTH));
        end generate;
    end architecture;


.. code-block:: VHDL
   :caption: V3 - Leverages VHDL’s built-in rol/ror shift operators for concise rotation implementation.

    architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
        constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
        signal sel_int : integer range 0 to BLOCKS-1;
    begin

        sel_int_gen : if (BLOCKS > 1) generate
            sel_int <= to_integer(unsigned(SEL));
        else generate
            sel_int <= 0;
        end generate;

        shift_sel_gen : if (SHIFT_LEFT) generate
            DATA_OUT <= DATA_IN rol (sel_int*BLOCK_WIDTH);
        else generate
            DATA_OUT <= DATA_IN ror (sel_int*BLOCK_WIDTH);
        end generate;
    end architecture;


.. code-block:: VHDL
   :caption: V4 - Uses shift_left/shift_right from numeric_std on an extended input vector to implement logical shifts.

    architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
        constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
        signal data_in_tmp   : unsigned(2*DATA_WIDTH-1 downto 0);
        signal data_out_tmp  : unsigned(2*DATA_WIDTH-1 downto 0);
        signal sel_int : integer range 0 to BLOCKS-1;
    begin

        data_in_tmp <= unsigned(DATA_IN & DATA_IN);

        sel_int_gen : if (BLOCKS > 1) generate
            sel_int <= to_integer(unsigned(SEL));
        else generate
            sel_int <= 0;
        end generate;

        shift_sel_gen : if (SHIFT_LEFT) generate
            data_out_tmp <= IEEE.numeric_std.shift_left(data_in_tmp, sel_int*BLOCK_WIDTH);
            DATA_OUT <= std_logic_vector(data_out_tmp(DATA_WIDTH*2-1 downto DATA_WIDTH));
        else generate
            data_out_tmp <= IEEE.numeric_std.shift_right(data_in_tmp, sel_int*BLOCK_WIDTH);
            DATA_OUT <= std_logic_vector(data_out_tmp(DATA_WIDTH-1 downto 0));
        end generate;
    end architecture;

.. list-table:: Barrel Shifter Implementation Comparison
   :header-rows: 1
   :align: center

   * - BLOCKS
       BLOCK_WIDTH
     - IMPLEMENTATION
     - LUT
     - MUX
     - TIME
   * - 8|8
     - V0
     - 128
     - 0
     - /
   * - 8|8
     - V1
     - 128
     - 0
     - /
   * - 8|8
     - V2
     - 96
     - 0
     - 0.62ns
   * - 8|8
     - V3
     - 96
     - 0
     - 0.67ns
   * - 8|8
     - V4
     - 96
     - 0
     - 0.63ns
   * - 64|16
     - V0
     - 1700
     - 10000
     - 1.44ns
   * - 64|16
     - V1
     - 4876
     - 400
     - 1.29ns
   * - 64|16
     - V2
     - 3847
     - 180
     - 1.54ns
   * - 64|16
     - V3
     - 4855
     - 0
     - 1.88ns
   * - 64|16
     - V4
     - 1920
     - 0
     - 0.95ns
   * - 64|10
     - V0
     - 23000
     - 5000
     - /
   * - 64|10
     - V1
     - 2088
     - 0
     - /
   * - 64|10
     - V2
     - 14000
     - 2000
     - 1.54ns
   * - 64|10
     - V3
     - 4855
     - 0
     - 1.87ns
   * - 64|10
     - V4
     - 1920
     - 0
     - 0.95ns
   * - 100|10
     - V0
     - 26000
     - 5000
     - 6.94ns
   * - 100|10
     - V1
     - 47000
     - 12000
     - 3.28ns
   * - 100|10
     - V2
     - 14000
     - 2000
     - 1.75ns
   * - 100|10
     - V3
     - 9257
     - 0
     - 3.51ns
   * - 100|10
     - V4
     - 4053
     - 0
     - 0.956ns
   * - 10|16
     - V0
     - 2075
     - 10
     - 5.19ns
   * - 10|16
     - V1
     - 320
     - 0
     - 0.71ns
   * - 10|16
     - V2
     - 351
     - 0
     - 0.71ns
   * - 10|16
     - V3
     - 320
     - 0
     - 0.69ns
   * - 10|16
     - V4
     - 352
     - 0
     - 0.72ns
   * - 100|16
     - V0
     - 30000
     - 13000
     - 5.93ns
   * - 100|16
     - V1
     - 47000
     - 30000
     - 2.31ns
   * - 100|16
     - V2
     - 12000
     - 5000
     - 1.27ns
   * - 100|16
     - V3
     - 13000
     - 32
     - 1.91ns
   * - 100|16
     - V4
     - 6000
     - 0
     - 1.25ns
   * - 512|8
     - V0
     - 445000
     - 25000
     - 2.13ns
   * - 512|8
     - V1
     - 65000
     - 30000
     - 1.40ns
   * - 512|8
     - V2
     - 65000
     - 40000
     - 1.39ns
   * - 512|8
     - V3
     - 37000
     - 0
     - 2.44ns
   * - 512|8
     - V4
     - 18000
     - 0
     - 1.42ns
   * - 253|32
     - V0
     - 84000
     - 50000
     - 6.65ns
   * - 253|32
     - V1
     - 595000
     - 30000
     - 2.35ns
   * - 253|32
     - V2
     - 90000
     - 58
     - 1.37ns
   * - 253|32
     - V3
     - 81000
     - 0
     - 2.24ns
   * - 253|32
     - V4
     - 32000
     - 0
     - 1.32ns


.. vhdl:autoentity:: BARREL_SHIFTER_GEN


.. vhdl:autoentity:: BARREL_SHIFTER_GEN_PIPED

