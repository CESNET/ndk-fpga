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
library UNIMACRO;
use UNIMACRO.vcomponents.all;

--! Math package
use work.math_pack.all;

--! Use DP_BMEM functions
use work.DP_BMEM_V7_PKG.all;

--! \brief Architecture of dual port Virtex7 BRAM declaration
architecture FULL of DP_BRAM_V7 is

   -- -------------------------------------------
   -- Constants
   -- -------------------------------------------
   --! A number of rows of the BRAM
   constant ROW_NUMBER        : integer := GET_BMEM_ROW_COUNT(BRAM_TYPE,DATA_WIDTH,ADDRESS_WIDTH);
   --! A number of bits stored into one BRAM
   constant BRAM_DATA_WIDTH   : integer := GET_BMEM_DATA_WIDTH_PORTION(BRAM_TYPE,DATA_WIDTH);
   --! A number of BRAMs on one word
   constant BRAM_ON_WORD      : integer := GET_BMEM_ON_WORD(BRAM_TYPE,DATA_WIDTH);
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
   type T_MEM_DATA is array (0 to ROW_NUMBER-1) of std_logic_vector(DATA_WIDTH-1 downto 0);

   --! Memory itself consists of row types(std_logic_vector)
   type T_MEM_WE is array (0 to ROW_NUMBER-1) of std_logic_vector(BRAM_WE_WIDHT-1 downto 0);

   --! Memory itself consists of row types(std_logic)
   type T_MEM_EN is array (0 to ROW_NUMBER-1) of std_logic;

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
   signal portA_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
   --! Row address
   signal portA_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);

   --! Output data bus
   signal portA_data_out      : T_MEM_DATA;
   --! Write enable bus
   signal portA_we            : T_MEM_WE;
   --! Memory Enable bus
   signal portA_en            : T_MEM_EN;

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
   signal portB_bram_address     : std_logic_vector(BRAM_ADDRESS_WIDTH-1 downto 0);
   --! Row address
   signal portB_row_address      : std_logic_vector(ROW_ADDRESS_WIDTH-1 downto 0);

   --! Output data bus
   signal portB_data_out      : T_MEM_DATA;
   --! Write enable bus
   signal portB_we            : T_MEM_WE;
   --! Memory Enable bus
   signal portB_en            : T_MEM_EN;

   signal debug_item_vldA : std_logic := '1';
   signal debug_item_vldB : std_logic := '1';

begin

   -- -------------------------------------------
   -- Port A handling
   -- -------------------------------------------
   -- Deal with addresses
   PORTA_ONE_ROW_GEN:if(ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
      --Our address space fits into one row memory. Crucial parameter is
      --also data width (we have one row, we are addresing only the part
      --of the BRAM but we need more BRAMs to store and load the word)

      --! BRAM address composition
      process(ADDRA)
      begin
         --Default signal value
         portA_bram_address <= (others => '0');
         --Store the portion of the address
         portA_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRA;
      end process;

      --! Row address - it is still the same
      portA_row_address <= (others=>'0');
   end generate;

   PORTA_MORE_ROW_GEN:if(ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
      --Our address space fits into memory with more ROWs. Crucial parameter is
      --also data width -> this width defines the BRAM address width. So, we
      --are able to count a number of rows of the final memory.

      --! Set the address portion for the BRAM, rest is used as the row address
      portA_bram_address <= ADDRA(BRAM_ADDRESS_WIDTH-1 downto 0);
      portA_row_address <= ADDRA(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
   end generate;

   --Deal with the output and pipeline signals
   PORTA_OUT_NO_REG_GEN:if(ENABLE_OUT_REG = false) generate

      --! Deal with data output
      DOA      <= portA_data_out(conv_integer(UNSIGNED(reg_row_address_a))) when debug_item_vldA='1' else (others => 'U');
      DOA_DV   <= reg_data_a_vld;

      --! Enable pipeline by default
      pipe_ena_in <= '1';
   end generate;

   PORTA_OUT_REG_GEN:if(ENABLE_OUT_REG = true) generate
      --! \brief Output register for port A
      PORTA_OUT_REGP:process(CLKA)
      begin
         if(CLKA = '1' and CLKA'event)then
            if(RSTA = '1')then
               --Reset only the validity signal
               DOA_DV <= '0';
            else
               if(PIPE_ENA = '1')then
                  if debug_item_vldA='1' then
                     DOA <= portA_data_out(conv_integer(UNSIGNED(reg_row_address_a)));
                  else
                     DOA <= (others => 'U');
                  end if;
                  DOA_DV <= reg_data_a_vld;
               end if;
            end if;
         end if;
      end process;

      --! Use the PIPE_ENA signal from input
      pipe_ena_in <= PIPE_ENA;
   end generate;

   --! \brief Delay register for selected row
   ROW_ADDRA_REGP:process(CLKA)
   begin
      if(CLKA = '1' and CLKA'event)then
         if(pipe_ena_in = '1')then
            reg_row_address_a <= portA_row_address;
         end if;
      end if;
   end process;

   --! \brief Data validity register - delay REA signal
   PORTA_DATA_VLD_REGP:process(CLKA)
   begin
      if(CLKA = '1' and CLKA'event)then
         if(RSTA = '1')then
            reg_data_a_vld <= '0';
         else
            if(pipe_ena_in = '1')then
               reg_data_a_vld <= REA;
            end if;
         end if;
      end if;
   end process;

   --! \brief Read and write signal generation for BRAM
   PORTA_RW_EN_GENP:process(REA,WEA,portA_row_address)
   begin
      --! Default signal values
      DEF_SIG_VAL:for i in 0 to ROW_NUMBER-1 loop
         portA_en(i) <= '0';
         portA_we(i) <= (others=>'0');
      end loop;

      if(REA = '1' or WEA = '1')then
         --We are requesting read operation (selected row is stored
         --row delay register)
         portA_en(conv_integer(UNSIGNED(portA_row_address))) <= '1';

         --Write is enabled
         if(WEA = '1')then
            portA_we(conv_integer(UNSIGNED(portA_row_address))) <= (others=>'1');
         end if;
      end if;
   end process;

   -- -------------------------------------------
   -- Port B handling
   -- -------------------------------------------
   -- Deal with addresses
   PORTB_ONE_ROW_GEN:if(ADDRESS_WIDTH <= BRAM_ADDRESS_WIDTH) generate
      --Our address space fits into one row memory. Crucial parameter is
      --also data width (we have one row, we are addresing only the part
      --of the BRAM but we need more BRAMs to store and load the word)

      --! BRAM address composition
      process(ADDRB)
      begin
         --Default signal value
         portB_bram_address <= (others => '0');
         --Store the portion of the address
         portB_bram_address(ADDRESS_WIDTH-1  downto 0) <= ADDRB;
      end process;

      --! Row address - it is still the same
      portB_row_address <= (others=>'0');
   end generate;

   PORTB_MORE_ROW_GEN:if(ADDRESS_WIDTH > BRAM_ADDRESS_WIDTH) generate
      --Our address space fits into memory with more ROWs. Crucial parameter is
      --also data width -> this width defines the BRAM address width. So, we
      --are able to count a number of rows of the final memory.

      --! Set the address portion for the BRAM, rest is used as the row address
      portB_bram_address <= ADDRB(BRAM_ADDRESS_WIDTH-1 downto 0);
      portB_row_address <= ADDRB(ADDRESS_WIDTH-1 downto BRAM_ADDRESS_WIDTH);
   end generate;

   --Deal with the output and pipeline signals
   PORTB_OUT_NO_REG_GEN:if(ENABLE_OUT_REG = false) generate

      --! Deal with data output
      DOB      <= portB_data_out(conv_integer(UNSIGNED(reg_row_address_b))) when debug_item_vldB='1' else (others => 'U');
      DOB_DV   <= reg_data_b_vld;

      --! Enable pipeline by default
      pipe_enb_in <= '1';
   end generate;

   PORTB_OUT_REG_GEN:if(ENABLE_OUT_REG = true) generate
      --! \brief Output register for port B
      PORTB_OUT_REGP:process(CLKB)
      begin
         if(CLKB = '1' and CLKB'event)then
            if(RSTB = '1')then
               --Reset only the validity signal
               DOB_DV <= '0';
            else
               if(PIPE_ENB = '1')then
                  if debug_item_vldB='1' then
                     DOB <= portB_data_out(conv_integer(UNSIGNED(reg_row_address_b)));
                  else
                     DOB <= (others => 'U');
                  end if;
                  DOB_DV <= reg_data_b_vld;
               end if;
            end if;
         end if;
      end process;

      --! Use the PIPE_ENB signal from input
      pipe_enb_in <= PIPE_ENB;
   end generate;

   --! \brief Delay register for selected row
   ROW_ADDRB_REGP:process(CLKB)
   begin
      if(CLKB = '1' and CLKB'event)then
         if(pipe_enb_in = '1')then
            reg_row_address_b <= portB_row_address;
         end if;
      end if;
   end process;

   --! \brief Data validity register - delay REB signal
   PORTB_DATA_VLD_REGP:process(CLKB)
   begin
      if(CLKB = '1' and CLKB'event)then
         if(RSTB = '1')then
            reg_data_b_vld <= '0';
         else
            if(pipe_enb_in = '1')then
               reg_data_b_vld <= REB;
            end if;
         end if;
      end if;
   end process;

   --! \brief Read and write signal generation for BRAM
   PORTB_RW_EN_GENP:process(REB,WEB,portB_row_address)
   begin
      --! Default signal values
      DEF_SIG_VAL:for i in 0 to ROW_NUMBER-1 loop
         portB_en(i) <= '0';
         portB_we(i) <= (others=>'0');
      end loop;

      if(REB = '1' or WEB = '1')then
         --We are requesting read operation (selected row is stored
         --row delay register)
         portB_en(conv_integer(UNSIGNED(portB_row_address))) <= '1';

         --Write is enabled
         if(WEB = '1')then
            portB_we(conv_integer(UNSIGNED(portB_row_address))) <= (others=>'1');
         end if;
      end if;
   end process;

   -- -----------------------------------------------------
   -- BRAM entity map
   -- -----------------------------------------------------
   --Now ... for all rows and number of BRAMs per word ...
   ROW_MEM_GEN:for i in 0 to ROW_NUMBER-1 generate
      BMEM_PER_WORD_GEN:for j in 0 to BRAM_ON_WORD-1 generate

         --Rule for other BRAMs than last (we are using whole data bus)
         OTHER_BRAM_GEN:if(j /= BRAM_ON_WORD-1) generate
            --! BRAM_TDP_MACRO for 7series Xilinx FPGA, more information
            --! in Xilinx 7 Series Library guide for HDL Designs (UG768)
            BRAM_DP_I:BRAM_TDP_MACRO
            generic map(
               BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
               DEVICE => DEVICE, -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
               DOA_REG => 0, -- Optional port A output register (0 or 1)
               DOB_REG => 0, -- Optional port B output register (0 or 1)
               INIT_A => X"000000000", -- Initial values on A output port
               INIT_B => X"000000000", -- Initial values on B output port
               INIT_FILE => "NONE",
               READ_WIDTH_A => BRAM_DATA_WIDTH,
               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               READ_WIDTH_B => BRAM_DATA_WIDTH,
               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               SIM_COLLISION_CHECK => "NONE", -- Collision check enable "ALL", "WARNING_ONLY",
               -- "GENERATE_X_ONLY" or "NONE"
               SRVAL_A => X"000000000",
               -- Set/Reset value for A port output
               SRVAL_B => X"000000000",
               -- Set/Reset value for B port output
               WRITE_MODE_A => WRITE_MODE_A, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
               WRITE_MODE_B => WRITE_MODE_B, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
               WRITE_WIDTH_A => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               WRITE_WIDTH_B => BRAM_DATA_WIDTH  -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
            )
            port map (
               -- Output data
               DOA => portA_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
               DOB => portB_data_out(i)((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
               -- Address input
               ADDRA => portA_bram_address,
               ADDRB => portB_bram_address,
               -- Clock
               CLKA => CLKA,
               CLKB => CLKB,
               -- Input data
               DIA => DIA((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
               DIB => DIB((j+1)*BRAM_DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j),
               -- Enable signal
               ENA => portA_en(i),
               ENB => portB_en(i),
               -- Output register enable
               REGCEA => '1',
               REGCEB => '1',
               -- Reset port
               RSTA => RSTA,
               RSTB => RSTB,
               --Byte-wide write enable
               WEA => portA_we(i),
               WEB => portB_we(i)
            );
         end generate;

         --We need to know, if we map last BRAM
         LAST_BRAM_GEN:if(j = BRAM_ON_WORD-1) generate
            constant last_data_width : integer := DATA_WIDTH-(BRAM_DATA_WIDTH*j);
            signal tmp_dia : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            signal tmp_dib : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            signal tmp_doa : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
            signal tmp_dob : std_logic_vector(BRAM_DATA_WIDTH-1 downto 0);
         begin
            tmp_dia(last_data_width-1 downto 0) <= DIA(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
            tmp_dia(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');
            tmp_dib(last_data_width-1 downto 0) <= DIB(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j);
            tmp_dib(BRAM_DATA_WIDTH-1 downto last_data_width) <= (others => '0');

            portA_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_doa(last_data_width-1 downto 0);
            portB_data_out(i)(DATA_WIDTH-1 downto BRAM_DATA_WIDTH*j) <= tmp_dob(last_data_width-1 downto 0);
            --! BRAM_TDP_MACRO for 7series Xilinx FPGA, more information
            --! in Xilinx 7 Series Library guide for HDL Designs (UG768)
            BRAM_DP_I:BRAM_TDP_MACRO
            generic map(
               BRAM_SIZE => integer'image(BRAM_TYPE)&"Kb", -- Target BRAM, "18Kb" or "36Kb"
               DEVICE => DEVICE, -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
               DOA_REG => 0, -- Optional port A output register (0 or 1)
               DOB_REG => 0, -- Optional port B output register (0 or 1)
               INIT_A => X"000000000", -- Initial values on A output port
               INIT_B => X"000000000", -- Initial values on B output pORT
               INIT_FILE => "NONE",
               READ_WIDTH_A => BRAM_DATA_WIDTH,
               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               READ_WIDTH_B => BRAM_DATA_WIDTH,
               -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               SIM_COLLISION_CHECK => "NONE", -- Collision check enable "ALL", "WARNING_ONLY",
               -- "GENERATE_X_ONLY" or "NONE"
               SRVAL_A => X"000000000",
               -- Set/Reset value for A port output
               SRVAL_B => X"000000000",
               -- Set/Reset value for B port output
               WRITE_MODE_A => WRITE_MODE_A, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
               WRITE_MODE_B => WRITE_MODE_B, -- "WRITE_FIRST", "READ_FIRST" or "NO_CHANGE"
               WRITE_WIDTH_A => BRAM_DATA_WIDTH, -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
               WRITE_WIDTH_B => BRAM_DATA_WIDTH  -- Valid values are 1-36 (19-36 only valid when BRAM_SIZE="36Kb")
            )
            port map (
               -- Output data
               DOA => tmp_doa,
               DOB => tmp_dob,
               -- Address input
               ADDRA => portA_bram_address,
               ADDRB => portB_bram_address,
               -- CLock
               CLKA => CLKA,
               CLKB => CLKB,
               -- Input data
               DIA => tmp_dia,
               DIB => tmp_dib,
               --Enable signal
               ENA => portA_en(i),
               ENB => portB_en(i),
               -- Output register enable
               REGCEA => '1',
               REGCEB => '1',
               -- Reset port
               RSTA => RSTA,
               RSTB => RSTB,
               -- Byte-wide write enable
               WEA => portA_we(i),
               WEB => portB_we(i)
            );
         end generate;
      end generate;
   end generate;


-- pragma translate_off
-- pragma synthesis_off
   -- Debuging -----------------------------------------------------------------
   dbg_init_control : process(CLKA,CLKB)
      variable debug_item_written  : std_logic_vector(2**ADDRESS_WIDTH-1 downto 0);
   begin
      if CLKA'event and CLKA='1' then
         if RSTA='1' then
            debug_item_written := (others => '0');
         elsif  PIPE_ENA='1' and WEA='1' then
            debug_item_written(conv_integer(ADDRA)) := '1';
         end if;
         debug_item_vldA <= debug_item_written(conv_integer(ADDRA));
      end if;
      if CLKB'event and CLKB='1' then
         if RSTB='1' then
            debug_item_written := (others => '0');
         elsif  PIPE_ENB='1' and WEB='1' then
            debug_item_written(conv_integer(ADDRB)) := '1';
         end if;
         debug_item_vldB <= debug_item_written(conv_integer(ADDRB));
      end if;
   end process;
   assert_gen : if DEBUG_ASSERT_UNINITIALIZED generate
      assert debug_item_vldA='1' or reg_data_a_vld='0' or RSTA/='0' or not CLKA'event or CLKA='0' report "Reading uninitialized item from DP_BMEM_V7 on port A!" severity error;
      assert debug_item_vldB='1' or reg_data_b_vld='0' or RSTB/='0' or not CLKB'event or CLKB='0' report "Reading uninitialized item from DP_BMEM_V7 on port B!" severity error;
   end generate;
-- pragma synthesis_on
-- pragma translate_on

end architecture FULL;
