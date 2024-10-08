--!
--! \file dp_bram_xilinx_arch.vhd
--! \brief Dual port BRAM for Xilinx devices, architecture
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library UNIMACRO;
use UNIMACRO.vcomponents.all;

library XPM;
use XPM.vcomponents.all;

library work;
use work.math_pack.all;
use work.DP_BRAM_XILINX_PKG.all;

--! \brief Architecture of dual port Xilinx BRAM
architecture FULL of DP_BRAM_XILINX is

   --! Boolean to integer conversion function
   function bool2int(b: boolean) return integer is
   begin if (b) then return 1; else return 0; end if; end function;

   --! Validity signal for readed data.
   signal reg_data_a_vld  : std_logic;
   signal reg_data_b_vld  : std_logic;

   --! Auxiliary signal for debugging uninitaliazed data
   signal debug_item_vldA : std_logic := '1';
   signal debug_item_vldB : std_logic := '1';

begin

-- pragma translate_off
-- pragma synthesis_off
   --! Support for DEBUG_ASSERT_UNINITIALIZED in simulations.
   assert_gen: if DEBUG_ASSERT_UNINITIALIZED generate
      dbg_init_control: process(CLKA, CLKB)
         variable debug_item_written: std_logic_vector(2**ADDRESS_WIDTH-1 downto 0);
      begin
         if CLKA'event and CLKA = '1' then
            if RSTA = '1' then
               debug_item_written := (others => '0');
            elsif PIPE_ENA = '1' and WEA = '1' then
               debug_item_written(conv_integer(ADDRA)) := '1';
            end if;
            debug_item_vldA <= debug_item_written(conv_integer(ADDRA));
         end if;

         if CLKB'event and CLKB = '1' then
            if RSTB = '1' then
               debug_item_written := (others => '0');
            elsif PIPE_ENB = '1' and WEB = '1' then
               debug_item_written(conv_integer(ADDRB)) := '1';
            end if;
            debug_item_vldB <= debug_item_written(conv_integer(ADDRB));
         end if;
      end process;
      assert debug_item_vldA = '1' or reg_data_a_vld = '0' or RSTA /= '0' or not CLKA'event or CLKA = '0' report "Reading uninitialized item from DP_BRAM_XILINX on port A!" severity error;
      assert debug_item_vldB = '1' or reg_data_b_vld = '0' or RSTB /= '0' or not CLKB'event or CLKB = '0' report "Reading uninitialized item from DP_BRAM_XILINX on port B!" severity error;
   end generate;
-- pragma synthesis_on
-- pragma translate_on

   --! Code for non ULTRASCALE devices.
   --! Based on BRAM_TDP_MACRO, for more details see UG768 (Xilinx 7 Series FPGA
   --! and Zynq-7000 All Programmable SoC Libraries Guide for HDL Designs).
   nonus_gen : if DEVICE /= "ULTRASCALE" generate

      --! Constants -----------------------------------------------------------
      --! The number of rows of the BRAM.
      constant ROW_NUMBER           : integer := BRAMV7_ROW_COUNT(BRAM_TYPE, DATA_WIDTH, ADDRESS_WIDTH);
      --! The number of bits stored into one BRAM.
      constant BRAM_DATA_WIDTH      : integer := BRAMV7_DATA_WIDTH_PORTION(BRAM_TYPE, DATA_WIDTH);
      --! The number of BRAMs on one word.
      constant BRAM_ON_WORD         : integer := BRAMV7_ON_WORD(BRAM_TYPE, DATA_WIDTH);
      --! Width of the BMEM address bus.
      constant BRAM_ADDRESS_WIDTH   : integer := BRAMV7_ADDR_WIDTH(BRAM_TYPE, DATA_WIDTH);
      --! The number of bits to address the row.
      constant ROW_ADDRESS_WIDTH    : integer := log2(ROW_NUMBER);
      --! Size of WEA vector with respect to data width and bram type.
      constant BRAM_WE_WIDTH        : integer := BRAMV7_WE_WIDTH(BRAM_TYPE, DATA_WIDTH);

      --! Data types (type definitions for easier data connection) ------------
      --! Memory itself consists of row types (std_logic_vector)
      type T_MEM_DATA is array (0 to ROW_NUMBER-1) of std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Memory itself consists of row types (std_logic_vector)
      type T_MEM_WE is array (0 to ROW_NUMBER-1) of std_logic_vector(BRAM_WE_WIDTH-1 downto 0);
      --! Memory itself consists of row types (std_logic)
      type T_MEM_EN is array (0 to ROW_NUMBER-1) of std_logic;

      --! Port A & B signals --------------------------------------------------
      --! Pipe enable signal.
      signal pipe_ena_in            : std_logic;
      signal pipe_enb_in            : std_logic;
      --! Register for row address delay.
      signal reg_row_address_a      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      signal reg_row_address_b      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      --! Enable signal for address delay register.
      signal reg_row_address_a_en   : std_logic;
      signal reg_row_address_b_en   : std_logic;
      --! Address in BRAM
      signal portA_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
      signal portB_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
      --! Row address
      signal portA_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      signal portB_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      --! Output data bus
      signal portA_data_out         : T_MEM_DATA;
      signal portB_data_out         : T_MEM_DATA;
      --! Write enable bus
      signal portA_we               : T_MEM_WE;
      signal portB_we               : T_MEM_WE;
      --! Memory Enable bus
      signal portA_en               : T_MEM_EN;
      signal portB_en               : T_MEM_EN;

   begin

      --! One row addressing for port A
      norowsa_gen: if (ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
         portA_row_address <= (others => '0'); --! Row address, still the same
         process (ADDRA)
         begin
            --! Set the portion of the address, rest is zeroed
            portA_bram_address <= (others => '0');
            portA_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRA;
         end process;
      end generate;

      --! One row addressing for port B
      norowsb_gen: if (ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
         portB_row_address <= (others => '0'); --! Row address, still the same
         process (ADDRB)
         begin
            --! Set the portion of the address, rest is zeroed
            portB_bram_address <= (others => '0');
            portB_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRB;
         end process;
      end generate;

      --! More rows addressing for port A
      rowsa_gen: if (ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
         --! Set the address portion for the BRAM, rest is used as the row address
         portA_bram_address <= ADDRA(BRAM_ADDRESS_WIDTH-1 downto 0);
         portA_row_address <= ADDRA(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
      end generate;

      --! More rows addressing for port B
      rowsb_gen: if (ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
         --! Set the address portion for the BRAM, rest is used as the row address
         portB_bram_address <= ADDRB(BRAM_ADDRESS_WIDTH-1 downto 0);
         portB_row_address <= ADDRB(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
      end generate;

      --! No output register for port A
      doa_noreg_gen: if (ENABLE_OUT_REG = false) generate
         pipe_ena_in <= '1'; --! Enable pipeline by default
         DOA_DV <= reg_data_a_vld; --! Deal with data output
         DOA <= portA_data_out(conv_integer(unsigned(reg_row_address_a))) when (debug_item_vldA = '1') else (others => 'U');
      end generate;

      --! No output register for port B
      dob_noreg_gen: if (ENABLE_OUT_REG = false) generate
         pipe_enb_in <= '1'; --! Enable pipeline by default
         DOB_DV <= reg_data_b_vld; --! Deal with data output
         DOB <= portB_data_out(conv_integer(unsigned(reg_row_address_b))) when (debug_item_vldB = '1') else (others => 'U');
      end generate;

      --! Output register for port A
      doa_reg_gen: if (ENABLE_OUT_REG = true) generate
         pipe_ena_in <= PIPE_ENA; --! Use the PIPE_ENA signal from input
         doa_reg_p: process(CLKA)
         begin
            if (CLKA = '1' and CLKA'event) then
               if (RSTA = '1') then
                  DOA_DV <= '0';
               else
                  if (PIPE_ENA = '1') then
                     if (debug_item_vldA = '1') then
                        DOA <= portA_data_out(conv_integer(unsigned(reg_row_address_a)));
                     else
                        DOA <= (others => 'U');
                     end if;
                     DOA_DV <= reg_data_a_vld;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      --! Output register for port B
      dob_reg_gen: if (ENABLE_OUT_REG = true) generate
         pipe_enb_in <= PIPE_ENB; --! Use the PIPE_ENB signal from input
         dob_reg_p: process(CLKB)
         begin
            if (CLKB = '1' and CLKB'event) then
               if (RSTB = '1') then
                  DOB_DV <= '0';
               else
                  if (PIPE_ENB = '1') then
                     if (debug_item_vldB = '1') then
                        DOB <= portB_data_out(conv_integer(unsigned(reg_row_address_b)));
                     else
                        DOB <= (others => 'U');
                     end if;
                     DOB_DV <= reg_data_b_vld;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      --! Delay register for selected row of port A
      raddra_p: process(CLKA)
      begin
         if (CLKA = '1' and CLKA'event) then
            if (pipe_ena_in = '1') then
               reg_row_address_a <= portA_row_address;
            end if;
         end if;
      end process;

      --! Delay register for selected row of port B
      raddrb_p: process(CLKB)
      begin
         if (CLKB = '1' and CLKB'event) then
            if (pipe_enb_in = '1') then
               reg_row_address_b <= portB_row_address;
            end if;
         end if;
      end process;

      --! Data validity register for port A
      vlda_p: process(CLKA)
      begin
         if (CLKA = '1' and CLKA'event) then
            if (RSTA = '1') then
               reg_data_a_vld <= '0';
            elsif (pipe_ena_in = '1') then
               reg_data_a_vld <= REA;
            end if;
         end if;
      end process;

      --! Data validity register for port B
      vldb_p: process(CLKB)
      begin
         if (CLKB = '1' and CLKB'event) then
            if (RSTB = '1') then
               reg_data_b_vld <= '0';
            elsif (pipe_enb_in = '1') then
               reg_data_b_vld <= REB;
            end if;
         end if;
      end process;

      --! Read and write signal generation for port A
      rwa_p: process(REA, WEA, portA_row_address)
      begin
         --! Default signal values
         for i in 0 to ROW_NUMBER-1 loop portA_en(i) <= '0'; portA_we(i) <= (others => '0'); end loop;
         --! We are requesting read operation (selected row is stored in row delay register)
         portA_en(conv_integer(unsigned(portA_row_address))) <= REA or WEA;
         --! Set write enable in requested row
         portA_we(conv_integer(unsigned(portA_row_address))) <= (others => WEA);
      end process;

      --! Read and write signal generation for port B
      rwb_p: process(REB, WEB, portB_row_address)
      begin
         --! Default signal values
         for i in 0 to ROW_NUMBER-1 loop portB_en(i) <= '0'; portB_we(i) <= (others => '0'); end loop;
         --! We are requesting read operation (selected row is stored in row delay register)
         portB_en(conv_integer(unsigned(portB_row_address))) <= REB or WEB;
         --! Set write enable in requested row
         portB_we(conv_integer(unsigned(portB_row_address))) <= (others => WEB);
      end process;

      --! BRAM MACRO instantiation, for all rows and all BRAMs per word
      row_gen: for i in 0 to ROW_NUMBER-1 generate
         word_gen: for j in 0 to BRAM_ON_WORD-1 generate

            --! Rule for other BRAMs than last (we are using whole data bus)
            other_gen: if (j /= BRAM_ON_WORD-1) generate
               macro_i: BRAM_TDP_MACRO
               generic map (
                  BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", --! Target BRAM, "18Kb" or "36Kb"
                  DEVICE => DEVICE, --! Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                  DOA_REG => 0, --! Optional port A output register (0 or 1)
                  DOB_REG => 0, --! Optional port B output register (0 or 1)
                  INIT_A => X"000000000", --! Initial values on A output port
                  INIT_B => X"000000000", --! Initial values on B output port
                  INIT_FILE => "NONE",
                  READ_WIDTH_A => BRAM_DATA_WIDTH, --! Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  READ_WIDTH_B => BRAM_DATA_WIDTH, --! Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  SIM_COLLISION_CHECK => "NONE", --! Collision check enable "ALL", "WARNING_ONLY", "GENERATE_X_ONLY" or "NONE"
                  SRVAL_A => X"000000000", --! Set/Reset value for A port output
                  SRVAL_B => X"000000000", --! Set/Reset value for B port output
                  WRITE_MODE_A => WRITE_MODE_A, --! "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                  WRITE_MODE_B => WRITE_MODE_B, --! "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                  WRITE_WIDTH_A => BRAM_DATA_WIDTH, --! Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  WRITE_WIDTH_B => BRAM_DATA_WIDTH  --! Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               ) port map (
                  --! Clocks
                  CLKA => CLKA,
                  CLKB => CLKB,
                  --! Output registers synchronous resets
                  RSTA => RSTA,
                  RSTB => RSTB,
                  --! Port enable signals
                  ENA => portA_en(i),
                  ENB => portB_en(i),
                  --! Byte-wide write enable
                  WEA => portA_we(i),
                  WEB => portB_we(i),
                  --! Address input
                  ADDRA => portA_bram_address,
                  ADDRB => portB_bram_address,
                  --! Input data
                  DIA => DIA((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  DIB => DIB((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  --! Output data
                  DOA => portA_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  DOB => portB_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  --! Output register enable
                  REGCEA => '1',
                  REGCEB => '1'
               );
            end generate;

            --! Last BRAM in the row
            last_gen: if (j = BRAM_ON_WORD-1) generate
               constant last_data_width: integer := DATA_WIDTH-(BRAM_DATA_WIDTH*j);
               signal tmp_dia: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
               signal tmp_dib: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
               signal tmp_doa: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
               signal tmp_dob: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            begin
               tmp_dia(last_data_width-1 downto 0) <= DIA(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
               tmp_dia(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');
               tmp_dib(last_data_width-1 downto 0) <= DIB(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
               tmp_dib(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');
               portA_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_doa(last_data_width-1 downto 0);
               portB_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_dob(last_data_width-1 downto 0);

               macro_i: BRAM_TDP_MACRO
               generic map (
                  BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
                  DEVICE => DEVICE, -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                  DOA_REG => 0, -- Optional port A output register (0 or 1)
                  DOB_REG => 0, -- Optional port B output register (0 or 1)
                  INIT_A => X"000000000", -- Initial values on A output port
                  INIT_B => X"000000000", -- Initial values on B output port
                  INIT_FILE => "NONE",
                  READ_WIDTH_A => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  READ_WIDTH_B => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  SIM_COLLISION_CHECK => "NONE", -- Collision check enable "ALL", "WARNING_ONLY", "GENERATE_X_ONLY" or "NONE"
                  SRVAL_A => X"000000000", -- Set/Reset value for A port output
                  SRVAL_B => X"000000000", -- Set/Reset value for B port output
                  WRITE_MODE_A => WRITE_MODE_A, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                  WRITE_MODE_B => WRITE_MODE_B, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
                  WRITE_WIDTH_A => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  WRITE_WIDTH_B => BRAM_DATA_WIDTH  -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               ) port map (
                  --! Clocks
                  CLKA => CLKA,
                  CLKB => CLKB,
                  --! Output registers synchronous resets
                  RSTA => RSTA,
                  RSTB => RSTB,
                  --! Enable signal
                  ENA => portA_en(i),
                  ENB => portB_en(i),
                  --! Byte-wide write enable
                  WEA => portA_we(i),
                  WEB => portB_we(i),
                  --! Address input
                  ADDRA => portA_bram_address,
                  ADDRB => portB_bram_address,
                  --! Input data
                  DIA => tmp_dia,
                  DIB => tmp_dib,
                  --! Output data
                  DOA => tmp_doa,
                  DOB => tmp_dob,
                  --! Output register enable
                  REGCEA => '1',
                  REGCEB => '1'
               );
            end generate;
         end generate;
      end generate;
   end generate;

   --! Code for ULTRASCALE devices.
   --! Based on XPM_MEMORY_TDPRAM macro, for more details
   --! see UG974 (UltraScale Architecture Libraries Guide).
   us_gen : if DEVICE = "ULTRASCALE" generate

      --! Deleyed validity signal for readed data.
      signal reg_data_a_vld_d  : std_logic;
      signal reg_data_b_vld_d  : std_logic;

   begin

      macro_i: xpm_memory_tdpram
      generic map (
         --! Global generics
         MEMORY_SIZE => 2**ADDRESS_WIDTH*DATA_WIDTH, -- Total memory array size, in bits.
         MEMORY_PRIMITIVE => "block", -- Memory primitive type to map to: "auto", "distributed", "block" or "ultra"
         CLOCKING_MODE => CLOCKING_MODE, -- Clocking Mode: "common_clock", "independent_clock".
         MEMORY_INIT_FILE => "none", -- File name for memory content initialization: "none" or "<filename>.mem".
         MEMORY_INIT_PARAM => "0", -- Initialize the contents of the memory using a parameter.
         USE_MEM_INIT => 1, -- Enable the generation of INFO message.
         WAKEUP_TIME => "disable_sleep", -- Memory sleep control: "disable_sleep" or "use_sleep_pin", only for URAM.
         MESSAGE_CONTROL => 0, -- Module messaging control: 0 (disable dynamic assertions), 1 (enable it).
         ECC_MODE => "no_ecc", -- ECC mode cotrol: "no_ecc", "encode_only", "decode_only" or "both_encode_and_decode", only for URAM.
         AUTO_SLEEP_TIME => 0, -- Autosleep control: 0 (disabled), do not change, only for URAM.
         USE_EMBEDDED_CONSTRAINT => 0, -- Specify "0" (disable) or "1" to enable the set_false_path constraint
            -- addition between CLKA of Distributed RAM and DOUBTB_REG on CLKB. Only of DISTMEM.
         MEMORY_OPTIMIZATION => "true", -- Specify "true" to enable the optimization of unused memory or bits in the memory.

         --! Port A module generics
         WRITE_DATA_WIDTH_A => DATA_WIDTH, -- Width of the port [A|B] write data port, DIN[A|B].
         READ_DATA_WIDTH_A => DATA_WIDTH, -- Width of the port [A|B] output data port, DOUT[A|B].
         BYTE_WRITE_WIDTH_A => DATA_WIDTH, -- Width of each byte to enable byte-wide write; 8, 9, or WRITE_DATA_WIDTH_[A|B].
         ADDR_WIDTH_A => ADDRESS_WIDTH, -- Width of the port [A|B] address port, ADDR[A|B].
         READ_RESET_VALUE_A => "0", -- Initial and reset value of final register stage in port [A|B] output data path.
         READ_LATENCY_A => 1 + bool2int(ENABLE_OUT_REG), -- Number of register stages in the port [A|B] read data path; >= 1.
         WRITE_MODE_A => WRITE_MODE_A, -- Write mode behavior for port [A|B] output data port. Only for [U|B]RAM.

         WRITE_DATA_WIDTH_B => DATA_WIDTH, -- Width of the port [A|B] write data port, DIN[A|B].
         READ_DATA_WIDTH_B => DATA_WIDTH, -- Width of the port [A|B] output data port, DOUT[A|B].
         BYTE_WRITE_WIDTH_B => DATA_WIDTH, -- Width of each byte to enable byte-wide write; 8, 9, or WRITE_DATA_WIDTH_[A|B].
         ADDR_WIDTH_B => ADDRESS_WIDTH, -- Width of the port [A|B] address port, ADDR[A|B].
         READ_RESET_VALUE_B => "0", -- Initial and reset value of final register stage in port [A|B] output data path.
         READ_LATENCY_B => 1 + bool2int(ENABLE_OUT_REG), -- Number of register stages in the port [A|B] read data path; >= 1.
         WRITE_MODE_B => WRITE_MODE_B -- Write mode behavior for port [A|B] output data port. Only for [U|B]RAM.
      ) port map (
         -- Common module ports
         SLEEP => '0',

         -- Port A module ports
         CLKA => CLKA,
         RSTA => RSTA,
         ENA => PIPE_ENA,
         REGCEA => PIPE_ENA,
         WEA(0) => WEA,
         ADDRA => ADDRA,
         DINA => DIA,
         INJECTSBITERRA => '0',
         INJECTDBITERRA => '0',
         DOUTA => DOA,
         SBITERRA => open,
         DBITERRA => open,

         -- Port B module ports
         CLKB => CLKB,
         RSTB => RSTB,
         ENB => PIPE_ENB,
         REGCEB => PIPE_ENB,
         WEB(0) => WEB,
         ADDRB => ADDRB,
         dinb => DIB,
         INJECTSBITERRB => '0',
         INJECTDBITERRB => '0',
         DOUTB => DOB,
         SBITERRB => open,
         DBITERRB => open
      );

      --! Data validity registers for port A
      vlda_p: process(CLKA)
      begin
         if (CLKA = '1' and CLKA'event) then
            if (RSTA = '1') then
               reg_data_a_vld <= '0';
               reg_data_a_vld_d <= '0';
            elsif (PIPE_ENA = '1') then
               reg_data_a_vld <= REA;
               reg_data_a_vld_d <= reg_data_a_vld;
            end if;
         end if;
      end process;

      --! Data validity registers for port B
      vldb_p: process(CLKB)
      begin
         if (CLKB = '1' and CLKB'event) then
            if (RSTB = '1') then
               reg_data_b_vld <= '0';
               reg_data_b_vld_d <= '0';
            elsif (PIPE_ENB = '1') then
               reg_data_b_vld <= REB;
               reg_data_b_vld_d <= reg_data_b_vld;
            end if;
         end if;
      end process;

      --! Validity output connection
      DOA_DV <= reg_data_a_vld_d when (ENABLE_OUT_REG) else reg_data_a_vld;
      DOB_DV <= reg_data_b_vld_d when (ENABLE_OUT_REG) else reg_data_b_vld;

   end generate;

end architecture;
