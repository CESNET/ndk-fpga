--!
--! \file  dp_bram_xilinx_func.vhd
--! \brief Dual port BRAM for Xilinx devices, functions
--! \author Pavel Benáček <benacek@cesnet.cz>
--! \author Jan Kučera <jan.kucera@cesnet.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;


--! \brief Dual port BRAM for Xilinx functions, package declaration
package dp_bram_xilinx_pkg is

    --! Next functions returns values according description of BRAM_TDP_MACRO, which
    --! could be found in UG768 (Xilinx 7 Series FPGA and Zynq-7000 All Programmable SoC
    --! Libraries Guide for HDL Designs).

    --! Returns portion of data per BRAM.
    function bramv7_data_width_portion (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer;

    --! Returns BRAM address width with respect to the selected BRAM type and data width.
    function bramv7_addr_width (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer;

    --! Returns BRAM write enable width with respect to the selected BRAM type and data width.
    function bramv7_we_width (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer;

    --! Returns the number of BRAMs which are needed for keeping of one word with respect
    --! to the selected BRAM type and data width.
    function bramv7_on_word (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer;

    --! Returns the number of BRAM rows.
    function bramv7_row_count (BRAM_TYPE: integer; DATA_WIDTH: integer; ADDRESS_WIDTH: integer) return integer;

end package;


--! \brief Dual port BRAM for Xilinx functions, package definition
package body dp_bram_xilinx_pkg is

    --! Next functions returns values according description of BRAM_TDP_MACRO, which
    --! could be found in UG768 (Xilinx 7 Series FPGA and Zynq-7000 All Programmable SoC
    --! Libraries Guide for HDL Designs.

    --! Returns portion of data per BRAM.
    function bramv7_data_width_portion (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer is
    begin
        if (DATA_WIDTH > 0 and DATA_WIDTH <= 36) then
            --! BRAM could be use with data width as configured.
            return DATA_WIDTH;
        else
            --! Next decision depends on selected BRAM type. Use maximal possible configuration
            --! with respect to actual. BRAM type match maximal possible used data width.
            return BRAM_TYPE;
        end if;
    end function;

    --! Returns BRAM address width with respect to the selected BRAM type and data width.
    function bramv7_addr_width (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer is
    begin

        --! Return the BRAM address width with respect to data width variable.
        if (DATA_WIDTH = 1) then
            if (BRAM_TYPE = 18) then
                return 14;
            else
                return 15;
            end if;
        elsif (DATA_WIDTH = 2) then
            if (BRAM_TYPE = 18) then
                return 13;
            else
                return 14;
            end if;
        elsif (DATA_WIDTH >= 3 and DATA_WIDTH <= 4) then
            if (BRAM_TYPE = 18) then
                return 12;
            else
                return 13;
            end if;
        elsif (DATA_WIDTH >= 5 and DATA_WIDTH <= 9) then
            if (BRAM_TYPE = 18) then
                return 11;
            else
                return 12;
            end if;
        elsif (DATA_WIDTH >= 10 and DATA_WIDTH <= 18) then
            if (BRAM_TYPE = 18) then
                return 10;
            else
                return 11;
            end if;
        else
            --! We need to use more BRAMs for one word. Return BRAM address bus width of maximal
            --! possible data width with respect to the selected BRAM type.
            if (BRAM_TYPE = 18) then
                return 11;
            else
                return 10;
            end if;
        end if;
    end function;

    --! Returns BRAM write enable width with respect to the selected BRAM type and data width.
    function bramv7_we_width (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer is
    begin

        --! Return the BRAM WE width with respect to data width and BRAM type.
        if (DATA_WIDTH > 0 and DATA_WIDTH <= 9) then
            return 1;
        elsif (DATA_WIDTH >= 10 and DATA_WIDTH <= 18) then
            return 2;
        else
            return 4;
        end if;

    end function;

    --! Returns the number of BRAMs which are needed for keeping of one word with respect
    --! to the selected BRAM type and data width.
    function bramv7_on_word (BRAM_TYPE: integer; DATA_WIDTH: integer) return integer is
        variable intcount : integer;
        variable rest     : integer;
    begin
        --! Normalize the data width to ONE BRAM (modulo operation).
        if (BRAM_TYPE = 18) then
            --! Maximal BRAM width is 18.
            rest := DATA_WIDTH mod 18;
        else
            --! Maximal BRAM width is 36.
            rest := DATA_WIDTH mod 36;
        end if;

        --! Get the number of BRAMs, which will be totaly used.
        if (BRAM_TYPE = 18) then
            intcount := DATA_WIDTH/18;
        else
            intcount := DATA_WIDTH/36;
        end if;

        --! Return the corrected number of used BRAMS.
        if (rest = 0) then
            --! We are effectivly using all BRAMs.
            return intcount;
        else
            --! We have to correct a used number of BRAMS.
            --! We need one more BRAM because rest is not null.
            return intcount+1;
        end if;
    end function;

    --! Returns the number of BRAM rows.
    function bramv7_row_count (BRAM_TYPE: integer; DATA_WIDTH: integer; ADDRESS_WIDTH: integer) return integer is
        variable bmem_addr_width : integer;
    begin
        --! Get the BRAM data width (all BRAMs will have this address width)
        bmem_addr_width := BRAMV7_ADDR_WIDTH(BRAM_TYPE, DATA_WIDTH);

        --! Return the rest of generic address width and consumed BRAM address width
        if (ADDRESS_WIDTH > bmem_addr_width) then
            --! We need more than one row.
            return 2**(ADDRESS_WIDTH-bmem_addr_width);
        else
            --! We need only one row,
            return 1;
        end if;
    end function;

end package body;
