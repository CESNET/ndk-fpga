--!
--! \file dp_bram_xilinx_arch.vhd
--! \brief Single port BRAM for Xilinx devices, architecture
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
use work.SP_BRAM_XILINX_PKG.all;

--! \brief Architecture of single port Xilinx BRAM
architecture FULL of SP_BRAM_XILINX is

   --! Boolean to integer conversion function
   function bool2int(b: boolean) return integer is
   begin if (b) then return 1; else return 0; end if; end function;

   --! Validity signal for readed data.
   signal reg_data_vld  : std_logic;

   --! Auxiliary signal for debugging uninitaliazed data
   signal debug_item_vld : std_logic := '1';

begin

-- pragma translate_off
-- pragma synthesis_off
   --! Support for DEBUG_ASSERT_UNINITIALIZED in simulations.
   assert_gen: if DEBUG_ASSERT_UNINITIALIZED generate
      dbg_init_control: process(CLK)
         variable debug_item_written: std_logic_vector(2**ADDRESS_WIDTH-1 downto 0);
      begin
         if CLK'event and CLK = '1' then
            if RST = '1' then
               debug_item_written := (others => '0');
            elsif PIPE_EN = '1' and WE = '1' then
               debug_item_written(conv_integer(ADDR)) := '1';
            end if;
            debug_item_vld <= debug_item_written(conv_integer(ADDR));
         end if;
      end process;
      assert debug_item_vld = '1' or reg_data_vld = '0' or RST /= '0' or not CLK'event or CLK = '0' report "Reading uninitialized item from SP_BRAM_XILINX!" severity error;
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

      --! Port signals --------------------------------------------------------
      --! Pipe enable signal.
      signal pipe_en_in           : std_logic;
      --! Register for row address delay.
      signal reg_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      --! Enable signal for address delay register.
      signal reg_row_address_en   : std_logic;
      --! Address in BRAM
      signal port_bram_address    : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
      --! Row address
      signal port_row_address     : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);
      --! Output data bus
      signal port_data_out        : T_MEM_DATA;
      --! Write enable bus
      signal port_we              : T_MEM_WE;
      --! Memory Enable bus
      signal port_en              : T_MEM_EN;

   begin

      --! One row addressing
      norows_gen: if (ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
         port_row_address <= (others => '0'); --! Row address, still the same
         process (ADDR)
         begin
            --! Set the portion of the address, rest is zeroed
            port_bram_address <= (others => '0');
            port_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDR;
         end process;
      end generate;

      --! More rows addressing
      rows_gen: if (ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
         --! Set the address portion for the BRAM, rest is used as the row address
         port_bram_address <= ADDR(BRAM_ADDRESS_WIDTH-1 downto 0);
         port_row_address <= ADDR(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
      end generate;

      --! No output register
      do_noreg_gen: if (ENABLE_OUT_REG = false) generate
         pipe_en_in <= '1'; --! Enable pipeline by default
         DO_DV <= reg_data_vld; --! Deal with data output
         DO <= port_data_out(conv_integer(unsigned(reg_row_address))) when (debug_item_vld = '1') else (others => 'U');
      end generate;

      --! Output register
      do_reg_gen: if (ENABLE_OUT_REG = true) generate
         pipe_en_in <= PIPE_EN; --! Use the PIPE_ENA signal from input
         do_reg_p: process(CLK)
         begin
            if (CLK = '1' and CLK'event) then
               if (RST = '1') then
                  DO_DV <= '0';
               else
                  if (PIPE_EN = '1') then
                     if (debug_item_vld = '1') then
                        DO <= port_data_out(conv_integer(unsigned(reg_row_address)));
                     else
                        DO <= (others => 'U');
                     end if;
                     DO_DV <= reg_data_vld;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      --! Delay register for selected row
      raddr_p: process(CLK)
      begin
         if (CLK = '1' and CLK'event) then
            if (pipe_en_in = '1') then
               reg_row_address <= port_row_address;
            end if;
         end if;
      end process;

      --! Data validity register
      vld_p: process(CLK)
      begin
         if (CLK = '1' and CLK'event) then
            if (RST = '1') then
               reg_data_vld <= '0';
            elsif (pipe_en_in = '1') then
               reg_data_vld <= RE;
            end if;
         end if;
      end process;

      --! Read and write signal generation
      rw_p: process(RE, WE, port_row_address)
      begin
         --! Default signal values
         for i in 0 to ROW_NUMBER-1 loop port_en(i) <= '0'; port_we(i) <= (others => '0'); end loop;
         --! We are requesting read operation (selected row is stored in row delay register)
         port_en(conv_integer(unsigned(port_row_address))) <= RE or WE;
         --! Set write enable in requested row
         port_we(conv_integer(unsigned(port_row_address))) <= (others => WE);
      end process;

      --! BRAM MACRO instantiation, for all rows and all BRAMs per word
      row_gen: for i in 0 to ROW_NUMBER-1 generate
         word_gen: for j in 0 to BRAM_ON_WORD-1 generate

            --! Rule for other BRAMs than last (we are using whole data bus)
            other_gen: if (j /= BRAM_ON_WORD-1) generate
               macro_i: BRAM_SINGLE_MACRO
               generic map (
                  BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
                  DEVICE => DEVICE, -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                  DO_REG => 0, -- Optional output register (0 or 1)
                  INIT => X"000000000", -- Initial values on output
                  INIT_FILE => "NONE",
                  READ_WIDTH => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  SRVAL => X"000000000", -- Set/Reset value for output
                  WRITE_WIDTH => BRAM_DATA_WIDTH -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               ) port map (
                  --! Clocks
                  CLK => CLK,
                  --! Output registers synchronous resets
                  RST => RST,
                  --! Port enable signals
                  EN => port_en(i),
                  --! Byte-wide write enable
                  WE => port_we(i),
                  --! Address input
                  ADDR => port_bram_address,
                  --! Input data
                  DI => DI((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  --! Output data
                  DO => port_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
                  --! Output register enable
                  REGCE => '1'
               );
            end generate;

            --! Last BRAM in the row
            last_gen: if (j = BRAM_ON_WORD-1) generate
               constant last_data_width: integer := DATA_WIDTH-(BRAM_DATA_WIDTH*j);
               signal tmp_di: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
               signal tmp_do: std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            begin
               tmp_di(last_data_width-1 downto 0) <= DI(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
               tmp_di(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');
               port_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_do(last_data_width-1 downto 0);

               macro_i: BRAM_SINGLE_MACRO
               generic map (
                  BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
                  DEVICE => DEVICE, -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
                  DO_REG => 0, -- Optional output register (0 or 1)
                  INIT => X"000000000", -- Initial values on output
                  INIT_FILE => "NONE",
                  READ_WIDTH => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
                  SRVAL => X"000000000", -- Set/Reset value for output
                  WRITE_WIDTH => BRAM_DATA_WIDTH -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               ) port map (
                  --! Clocks
                  CLK => CLK,
                  --! Output registers synchronous resets
                  RST => RST,
                  --Enable signal
                  EN => port_en(i),
                  --! Byte-wide write enable
                  WE => port_we(i),
                  -- Address input
                  ADDR => port_bram_address,
                  -- Input data
                  DI => tmp_di,
                  -- Output data
                  DO => tmp_do,
                  -- Output register enable
                  REGCE => '1'
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
      signal reg_data_vld_d  : std_logic;

   begin

      macro_i: xpm_memory_spram
      generic map (
         --! Global generics
         MEMORY_SIZE => 2**ADDRESS_WIDTH*DATA_WIDTH, -- Total memory array size, in bits.
         MEMORY_PRIMITIVE => "block", -- Memory primitive type to map to: "auto", "distributed", "block" or "ultra"
         MEMORY_INIT_FILE => "none", -- File name for memory content initialization: "none" or "<filename>.mem".
         MEMORY_INIT_PARAM => "0", -- Initialize the contents of the memory using a parameter.
         USE_MEM_INIT => 1, -- Enable the generation of INFO message.
         WAKEUP_TIME => "disable_sleep", -- Memory sleep control: "disable_sleep" or "use_sleep_pin", only for URAM.
         MESSAGE_CONTROL => 0, -- Module messaging control: 0 (disable dynamic assertions), 1 (enable it).
         ECC_MODE => "no_ecc", -- ECC mode cotrol: "no_ecc", "encode_only", "decode_only" or "both_encode_and_decode", only for URAM.
         AUTO_SLEEP_TIME => 0, -- Autosleep control: 0 (disabled), do not change, only for URAM.
         MEMORY_OPTIMIZATION => "true", -- Specify "true" to enable the optimization of unused memory or bits in the memory.

         --! Port A module generics
         WRITE_DATA_WIDTH_A => DATA_WIDTH, -- Width of the port [A|B] write data port, DIN[A|B].
         READ_DATA_WIDTH_A => DATA_WIDTH, -- Width of the port [A|B] output data port, DOUT[A|B].
         BYTE_WRITE_WIDTH_A => DATA_WIDTH, -- Width of each byte to enable byte-wide write; 8, 9, or WRITE_DATA_WIDTH_[A|B].
         ADDR_WIDTH_A => ADDRESS_WIDTH, -- Width of the port [A|B] address port, ADDR[A|B].
         READ_RESET_VALUE_A => "0", -- Initial and reset value of final register stage in port [A|B] output data path.
         READ_LATENCY_A => 1 + bool2int(ENABLE_OUT_REG) -- Number of register stages in the port [A|B] read data path; >= 1.
      ) port map (
         -- Common module ports
         SLEEP => '0',

         -- Port A module ports
         CLKA => CLK,
         RSTA => RST,
         ENA => PIPE_EN,
         REGCEA => PIPE_EN,
         WEA(0) => WE,
         ADDRA => ADDR,
         DINA => DI,
         INJECTSBITERRA => '0',
         INJECTDBITERRA => '0',
         DOUTA => DO,
         SBITERRA => open,
         DBITERRA => open
      );

      --! Data validity registers
      vld_p: process(CLK)
      begin
         if (CLK = '1' and CLK'event) then
            if (RST = '1') then
               reg_data_vld <= '0';
               reg_data_vld_d <= '0';
            elsif (PIPE_EN = '1') then
               reg_data_vld <= RE;
               reg_data_vld_d <= reg_data_vld;
            end if;
         end if;
      end process;

      --! Validity output connection
      DO_DV <= reg_data_vld_d when (ENABLE_OUT_REG) else reg_data_vld;

   end generate;

end architecture;
