--!
--! \file dp_bmem_V7_arch.vhd
--! \brief Dual port BRAM for Virtex 7 architecture, architecture declaration
--! \author Pavel Benáček <benacek@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! TDP macro
library unimacro;
use unimacro.vcomponents.all;

--! Math package
use work.math_pack.all;

--! Use DP_BMEM functions
use work.dp_bmem_v7_pkg.all;

--! \brief Architecture of dual port Virtex7 BRAM declaration
architecture FULL of DP_BRAM_V7 is

    -- -------------------------------------------
    -- Constants
    -- -------------------------------------------
    --! A number of rows of the BRAM
    constant ROW_NUMBER           : integer := GET_BMEM_ROW_COUNT(BRAM_TYPE,DATA_WIDTH,ADDRESS_WIDTH);
    --! A number of bits stored into one BRAM
    constant BRAM_DATA_WIDTH      : integer := GET_BMEM_DATA_WIDTH_PORTION(BRAM_TYPE,DATA_WIDTH);
    --! A number of BRAMs on one word
    constant BRAM_ON_WORD         : integer := GET_BMEM_ON_WORD(BRAM_TYPE,DATA_WIDTH);
    --! Get width of the BMEM address bus
    constant BRAM_ADDRESS_WIDTH   : integer := GET_BMEM_ADDR_WIDTH(BRAM_TYPE,DATA_WIDTH);
    --! A number of bits to address the row
    constant ROW_ADDRESS_WIDTH    : integer := log2(ROW_NUMBER);
    --! Size of WEA vector with respect to data width and bram type
    constant BRAM_WE_WIDHT        : integer := GET_BMEM_WE_WIDTH(BRAM_TYPE,DATA_WIDTH);

    -- -------------------------------------------
    -- Data types
    -- -------------------------------------------

    -- Type definitions for easiser data connection
    --! Memory itself consists of row types (std_logic_vector)
    type t_mem_data is array (0 to ROW_NUMBER-1) of std_logic_vector(DATA_WIDTH-1 downto 0);

    --! Memory itself consists of row types(std_logic_vector)
    type t_mem_we is array (0 to ROW_NUMBER-1) of std_logic_vector(BRAM_WE_WIDHT-1 downto 0);

    --! Memory itself consists of row types(std_logic)
    type t_mem_en is array (0 to ROW_NUMBER-1) of std_logic;

    -- -------------------------------------------
    -- Port A signals
    -- -------------------------------------------
    --! Pipe enable signal for port A
    signal pipe_ena_in            : std_logic;
    --! Register for row address delay
    signal reg_row_address_a      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
    --! Enable signal fof address delay register
    signal reg_row_address_a_en   : std_logic;
    --! Validity signal for readed data
    signal reg_data_a_vld         : std_logic;

    --! Address in BRAM
    signal porta_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
    --! Row address
    signal porta_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);

    --! Output data bus
    signal porta_data_out      : t_mem_data;
    --! Write enable bus
    signal porta_we            : t_mem_we;
    --! Memory Enable bus
    signal porta_en            : t_mem_en;

    -- -------------------------------------------
    -- Port B signals
    -- -------------------------------------------
    --! Pipe enable signal for port B
    signal pipe_enb_in            : std_logic;
    --! Register for row address delay
    signal reg_row_address_b      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
    --! Enable signal fof address delay register
    signal reg_row_address_b_en   : std_logic;
    --! Validity signal for readed data
    signal reg_data_b_vld         : std_logic;

    --! Address in BRAM
    signal portb_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
    --! Row address
    signal portb_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);

    --! Output data bus
    signal portb_data_out      : t_mem_data;
    --! Write enable bus
    signal portb_we            : t_mem_we;
    --! Memory Enable bus
    signal portb_en            : t_mem_en;
begin

    -- -------------------------------------------
    -- Port A handling
    -- -------------------------------------------
    -- Deal with addresses
    porta_one_row_gen: if(ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
        -- Our address space fits into one row memory. Crucial parameter is
        -- also data width (we have one row, we are addresing only the part
        -- of the BRAM but we need more BRAMs to store and load the word)

        --! BRAM address composition
        process (ADDRA)
        begin
            -- Default signal value
            porta_bram_address                            <= (others => '0');
            -- Store the portion of the address
            porta_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRA;
        end process;

        --! Row address - it is still the same
        porta_row_address <= (others => '0');
    end generate;

    porta_more_row_gen: if(ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
        -- Our address space fits into memory with more ROWs. Crucial parameter is
        -- also data width -> this width defines the BRAM address width. So, we
        -- are able to count a number of rows of the final memory.

        --! Set the address portion for the BRAM, rest is used as the row address
        porta_bram_address <= ADDRA(BRAM_ADDRESS_WIDTH-1 downto 0);
        porta_row_address  <= ADDRA(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
    end generate;

    -- Deal with the output and pipeline signals
    porta_out_no_reg_gen: if(ENABLE_OUT_REG = false) generate

        --! Deal with data output
        DOA      <= porta_data_out(conv_integer(UNSIGNED(reg_row_address_a)));
        DOA_DV   <= reg_data_a_vld;

        --! Enable pipeline by default
        pipe_ena_in <= '1';
    end generate;

    porta_out_reg_gen: if(ENABLE_OUT_REG = true) generate
        --! \brief Output register for port A
        porta_out_regp : process (CLKA)
        begin
            if (CLKA = '1' and CLKA'event) then
                if (RSTA = '1') then
                    -- Reset only the validity signal
                    DOA_DV <= '0';
                else
                    if (PIPE_ENA = '1') then
                        DOA    <= porta_data_out(conv_integer(UNSIGNED(reg_row_address_a)));
                        DOA_DV <= reg_data_a_vld;
                    end if;
                end if;
            end if;
        end process;

        --! Use the PIPE_ENA signal from input
        pipe_ena_in <= PIPE_ENA;
    end generate;

    --! \brief Delay register for selected row
    row_addra_regp : process (CLKA)
    begin
        if (CLKA = '1' and CLKA'event) then
            if (pipe_ena_in = '1') then
                reg_row_address_a <= porta_row_address;
            end if;
        end if;
    end process;

    --! \brief Data validity register - delay REA signal
    porta_data_vld_regp : process (CLKA)
    begin
        if (CLKA = '1' and CLKA'event) then
            if (RSTA = '1') then
                reg_data_a_vld <= '0';
            else
                if (pipe_ena_in = '1') then
                    reg_data_a_vld <= REA;
                end if;
            end if;
        end if;
    end process;

    --! \brief Read and write signal generation for BRAM
    porta_rw_en_genp : process (REA,WEA,porta_row_address)
    begin
        --! Default signal values
        def_sig_val : for i in 0 to ROW_NUMBER-1 loop
            porta_en(i) <= '0';
            porta_we(i) <= (others => '0');
        end loop;

        if (REA = '1' or WEA = '1') then
            -- We are requesting read operation (selected row is stored
            -- row delay register)
            porta_en(conv_integer(UNSIGNED(porta_row_address))) <= '1';

            -- Write is enabled
            if (WEA = '1') then
                porta_we(conv_integer(UNSIGNED(porta_row_address))) <= (others => '1');
            end if;
        end if;
    end process;

    -- -------------------------------------------
    -- Port B handling
    -- -------------------------------------------
    -- Deal with addresses
    portb_one_row_gen: if(ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
        -- Our address space fits into one row memory. Crucial parameter is
        -- also data width (we have one row, we are addresing only the part
        -- of the BRAM but we need more BRAMs to store and load the word)

        --! BRAM address composition
        process (ADDRB)
        begin
            -- Default signal value
            portb_bram_address                            <= (others => '0');
            -- Store the portion of the address
            portb_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRB;
        end process;

        --! Row address - it is still the same
        portb_row_address <= (others => '0');
    end generate;

    portb_more_row_gen: if(ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
        -- Our address space fits into memory with more ROWs. Crucial parameter is
        -- also data width -> this width defines the BRAM address width. So, we
        -- are able to count a number of rows of the final memory.

        --! Set the address portion for the BRAM, rest is used as the row address
        portb_bram_address <= ADDRB(BRAM_ADDRESS_WIDTH-1 downto 0);
        portb_row_address  <= ADDRB(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
    end generate;

    -- Deal with the output and pipeline signals
    portb_out_no_reg_gen: if(ENABLE_OUT_REG = false) generate

        --! Deal with data output
        DOB      <= portb_data_out(conv_integer(UNSIGNED(reg_row_address_b)));
        DOB_DV   <= reg_data_b_vld;

        --! Enable pipeline by default
        pipe_enb_in <= '1';
    end generate;

    portb_out_reg_gen: if(ENABLE_OUT_REG = true) generate
        --! \brief Output register for port B
        portb_out_regp : process (CLKB)
        begin
            if (CLKB = '1' and CLKB'event) then
                if (RSTB = '1') then
                    -- Reset only the validity signal
                    DOB_DV <= '0';
                else
                    if (PIPE_ENB = '1') then
                        DOB    <= portb_data_out(conv_integer(UNSIGNED(reg_row_address_b)));
                        DOB_DV <= reg_data_b_vld;
                    end if;
                end if;
            end if;
        end process;

        --! Use the PIPE_ENB signal from input
        pipe_enb_in <= PIPE_ENB;
    end generate;

    --! \brief Delay register for selected row
    row_addrb_regp : process (CLKB)
    begin
        if (CLKB = '1' and CLKB'event) then
            if (pipe_enb_in = '1') then
                reg_row_address_b <= portb_row_address;
            end if;
        end if;
    end process;

    --! \brief Data validity register - delay REB signal
    portb_data_vld_regp : process (CLKB)
    begin
        if (CLKB = '1' and CLKB'event) then
            if (RSTB = '1') then
                reg_data_b_vld <= '0';
            else
                if (pipe_enb_in = '1') then
                    reg_data_b_vld <= REB;
                end if;
            end if;
        end if;
    end process;

    --! \brief Read and write signal generation for BRAM
    portb_rw_en_genp : process (REB,WEB,portb_row_address)
    begin
        --! Default signal values
        def_sig_val : for i in 0 to ROW_NUMBER-1 loop
            portb_en(i) <= '0';
            portb_we(i) <= (others => '0');
        end loop;

        if (REB = '1' or WEB = '1') then
            -- We are requesting read operation (selected row is stored
            -- row delay register)
            portb_en(conv_integer(UNSIGNED(portb_row_address))) <= '1';

            -- Write is enabled
            if (WEB = '1') then
                portb_we(conv_integer(UNSIGNED(portb_row_address))) <= (others => '1');
            end if;
        end if;
    end process;

    -- -----------------------------------------------------
    -- BRAM entity map
    -- -----------------------------------------------------
    -- Now ... for all rows and number of BRAMs per word ...
    row_mem_gen: for i in 0 to ROW_NUMBER-1 generate
        bmem_per_word_gen: for j in 0 to BRAM_ON_WORD-1 generate

            -- Rule for other BRAMs than last (we are using whole data bus)
            other_bram_gen: if(j /= BRAM_ON_WORD-1) generate
                --! BRAM_TDP_MACRO for 7series Xilinx FPGA, more information
                --! in Xilinx 7 Series Library guide for HDL Designs (UG768)
                bram_dp_i: component bram_tdp_macro
                generic map (
                    BRAM_SIZE           => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
                    DEVICE              => DEVICE,                        -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                    DOA_REG             => 0,                             -- Optional port A output register (0 or 1)
                    DOB_REG             => 0,                             -- Optional port B output register (0 or 1)
                    INIT_A              => X"000000000",                  -- Initial values on A output port
                    INIT_B              => X"000000000",                  -- Initial values on B output port
                    INIT_FILE           => "NONE",
                    READ_WIDTH_A        => BRAM_DATA_WIDTH,
                    -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    READ_WIDTH_B        => BRAM_DATA_WIDTH,
                    -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    SIM_COLLISION_CHECK => "NONE",                        -- Collision check enable "ALL", "WARNING_ONLY",
                    -- "GENERATE_X_ONLY" or "NONE"
                    SRVAL_A             => X"000000000",
                    -- Set/Reset value for A port output
                    SRVAL_B             => X"000000000",
                    -- Set/Reset value for B port output
                    WRITE_MODE_A        => WRITE_MODE_A,                  -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                    WRITE_MODE_B        => WRITE_MODE_B,                  -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                    WRITE_WIDTH_A       => BRAM_DATA_WIDTH,               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    WRITE_WIDTH_B       => BRAM_DATA_WIDTH                -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                )
                port map (
                    -- Output data
                    DOA    => porta_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                    DOB    => portb_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                    -- Address input
                    ADDRA  => porta_bram_address,
                    ADDRB  => portb_bram_address,
                    -- Clock
                    CLKA   => CLKA,
                    CLKB   => CLKB,
                    -- Input data
                    DIA    => DIA((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                    DIB    => DIB((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                    -- Enable signal
                    ENA    => porta_en(i),
                    ENB    => portb_en(i),
                    -- Output register enable
                    REGCEA => '1',
                    REGCEB => '1',
                    -- Reset port
                    RSTA   => RSTA,
                    RSTB   => RSTB,
                    -- Byte-wide write enable
                    WEA    => porta_we(i),
                    WEB    => portb_we(i)
                );
            end generate;

            -- We need to know, if we map last BRAM
            last_bram_gen: if(j = BRAM_ON_WORD-1) generate
                constant LAST_DATA_WIDTH : integer := DATA_WIDTH-(BRAM_DATA_WIDTH*j);
                signal   tmp_dia         : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
                signal   tmp_dib         : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
                signal   tmp_doa         : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
                signal   tmp_dob         : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            begin
                tmp_dia(last_data_width-1 downto 0)               <= DIA(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
                tmp_dia(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');
                tmp_dib(last_data_width-1 downto 0)               <= DIB(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
                tmp_dib(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');

                porta_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_doa(last_data_width-1 downto 0);
                portb_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_dob(last_data_width-1 downto 0);
                --! BRAM_TDP_MACRO for 7series Xilinx FPGA, more information
                --! in Xilinx 7 Series Library guide for HDL Designs (UG768)
                bram_dp_i: component bram_tdp_macro
                generic map (
                    BRAM_SIZE           => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
                    DEVICE              => DEVICE,                        -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                    DOA_REG             => 0,                             -- Optional port A output register (0 or 1)
                    DOB_REG             => 0,                             -- Optional port B output register (0 or 1)
                    INIT_A              => X"000000000",                  -- Initial values on A output port
                    INIT_B              => X"000000000",                  -- Initial values on B output pORT
                    INIT_FILE           => "NONE",
                    READ_WIDTH_A        => BRAM_DATA_WIDTH,
                    -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    READ_WIDTH_B        => BRAM_DATA_WIDTH,
                    -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    SIM_COLLISION_CHECK => "NONE",                        -- Collision check enable "ALL", "WARNING_ONLY",
                    -- "GENERATE_X_ONLY" or "NONE"
                    SRVAL_A             => X"000000000",
                    -- Set/Reset value for A port output
                    SRVAL_B             => X"000000000",
                    -- Set/Reset value for B port output
                    WRITE_MODE_A        => WRITE_MODE_A,                  -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                    WRITE_MODE_B        => WRITE_MODE_B,                  -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                    WRITE_WIDTH_A       => BRAM_DATA_WIDTH,               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                    WRITE_WIDTH_B       => BRAM_DATA_WIDTH                -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                )
                port map (
                    -- Output data
                    DOA    => tmp_doa,
                    DOB    => tmp_dob,
                    -- Address input
                    ADDRA  => porta_bram_address,
                    ADDRB  => portb_bram_address,
                    -- CLock
                    CLKA   => CLKA,
                    CLKB   => CLKB,
                    -- Input data
                    DIA    => tmp_dia,
                    DIB    => tmp_dib,
                    -- Enable signal
                    ENA    => porta_en(i),
                    ENB    => portb_en(i),
                    -- Output register enable
                    REGCEA => '1',
                    REGCEB => '1',
                    -- Reset port
                    RSTA   => RSTA,
                    RSTB   => RSTB,
                    -- Byte-wide write enable
                    WEA    => porta_we(i),
                    WEB    => portb_we(i)
                );
            end generate;
        end generate;
    end generate;
end architecture;
