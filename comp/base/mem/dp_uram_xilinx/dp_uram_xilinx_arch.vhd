
--
-- DP_URAM_XILINX.vhd:
-- True dual port UltraRAM instantiation component
-- Copyright (C) 2004 CESNET
-- Author(s): Kamil Vojanec <xvojan00!stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- pragma translate_off
library XPM;
use XPM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture DP_URAM_XILINX_arch of DP_URAM_XILINX is

   component xpm_memory_tdpram
      generic (

        -- Common module generics
        MEMORY_SIZE             : integer := 2048           ;
        MEMORY_PRIMITIVE        : string  := "auto"         ;
        CLOCKING_MODE           : string  := "common_clock" ;
        ECC_MODE                : string  := "no_ecc"       ;
        MEMORY_INIT_FILE        : string  := "none"         ;
        MEMORY_INIT_PARAM       : string  := ""             ;
        USE_MEM_INIT            : integer := 1              ;
        WAKEUP_TIME             : string  := "disable_sleep";
        AUTO_SLEEP_TIME         : integer := 0              ;
        MESSAGE_CONTROL         : integer := 0              ;
        USE_EMBEDDED_CONSTRAINT : integer := 0              ;
        MEMORY_OPTIMIZATION     : string  := "true";
        CASCADE_HEIGHT          : integer := 0               ;
        SIM_ASSERT_CHK          : integer := 0               ;

        -- Port A module generics
        WRITE_DATA_WIDTH_A : integer := 32          ;
        READ_DATA_WIDTH_A  : integer := 32          ;
        BYTE_WRITE_WIDTH_A : integer := 32          ;
        ADDR_WIDTH_A       : integer := 6           ;
        READ_RESET_VALUE_A : string  := "0"         ;
        READ_LATENCY_A     : integer := 2           ;
        WRITE_MODE_A       : string  := "no_change" ;
        RST_MODE_A         : string  := "SYNC"      ;

        -- Port B module generics
        WRITE_DATA_WIDTH_B : integer := 32         ;
        READ_DATA_WIDTH_B  : integer := 32         ;
        BYTE_WRITE_WIDTH_B : integer := 32         ;
        ADDR_WIDTH_B       : integer := 6          ;
        READ_RESET_VALUE_B : string  := "0"        ;
        READ_LATENCY_B     : integer := 2          ;
        WRITE_MODE_B       : string  := "no_change";
        RST_MODE_B         : string  := "SYNC"

      );
      port (

        -- Common module ports
        sleep          : in  std_logic;

        -- Port A module ports
        clka           : in  std_logic;
        rsta           : in  std_logic;
        ena            : in  std_logic;
        regcea         : in  std_logic;
        wea            : in  std_logic_vector((WRITE_DATA_WIDTH_A/BYTE_WRITE_WIDTH_A)-1 downto 0);
        addra          : in  std_logic_vector(ADDR_WIDTH_A-1 downto 0);
        dina           : in  std_logic_vector(WRITE_DATA_WIDTH_A-1 downto 0);
        injectsbiterra : in  std_logic;
        injectdbiterra : in  std_logic;
        douta          : out std_logic_vector(READ_DATA_WIDTH_A-1 downto 0);
        sbiterra       : out std_logic;
        dbiterra       : out std_logic;

        -- Port B module ports
        clkb           : in  std_logic;
        rstb           : in  std_logic;
        enb            : in  std_logic;
        regceb         : in  std_logic;
        web            : in  std_logic_vector((WRITE_DATA_WIDTH_B/BYTE_WRITE_WIDTH_B)-1 downto 0);
        addrb          : in  std_logic_vector(ADDR_WIDTH_B-1 downto 0);
        dinb           : in  std_logic_vector(WRITE_DATA_WIDTH_B-1 downto 0);
        injectsbiterrb : in  std_logic;
        injectdbiterrb : in  std_logic;
        doutb          : out std_logic_vector(READ_DATA_WIDTH_B-1 downto 0);
        sbiterrb       : out std_logic;
        dbiterrb       : out std_logic
      );
    end component;

   -- Function converts boolean value to either 0 or 1
   function bool2int(b:boolean) return integer is
   begin
      if(b) then return 1;
      else return 0;
      end if;
   end function;

   -- Define constants for instantiation template
   constant READ_LATENCY : integer := 1 + ADDITIONAL_REG + bool2int(INTERNAL_OUT_REG);
   constant C_AWIDTH : integer := ADDRESS_WIDTH;
   constant C_DWIDTH : integer := DATA_WIDTH;
   -- Constant C_NBPIPE : integer := READ_LATENCY-1; -- Eliminates clock latency problem.


   -- Additional signals for behavioral instantiation
   -- Internal Signals
   signal out_mema : std_logic_vector(C_DWIDTH-1 downto 0);
   signal out_memb : std_logic_vector(C_DWIDTH-1 downto 0);

   -- Registers for data validity signals
   signal reg_data_a_vld : std_logic_vector(READ_LATENCY-1 downto 0);     --Data valid registers
   signal reg_data_b_vld : std_logic_vector(READ_LATENCY-1 downto 0);

   signal debug_item_vldA : std_logic := '1';
   signal debug_item_vldB : std_logic := '1';



   begin
      -- Generate reports of reading from uninitialized memory
      assert_gen : if DEBUG_ASSERT_UNINITIALIZED = true generate
         dbg_assertA : process(CLK)
         variable debug_item_written : std_logic_vector(2**ADDRESS_WIDTH-1 downto 0);
         begin
            if CLK'event and CLK = '1' then
               if RSTA = '1' then
                  debug_item_written := (others => '0');
               elsif PIPE_ENA = '1' and WEA = '1' then
                  debug_item_written(to_integer(unsigned(ADDRA))) := '1';
               end if;
               debug_item_vldA <= debug_item_written(to_integer(unsigned(ADDRA)));

               if RSTB = '1' then
                  debug_item_written := (others => '0');
               elsif PIPE_ENB = '1' and WEB = '1' then
                  debug_item_written(to_integer(unsigned(ADDRB))) := '1';
               end if;
               debug_item_vldB <= debug_item_written(to_integer(unsigned(ADDRB)));
            end if;
         end process;
         assert debug_item_vldA = '1' or reg_data_a_vld(READ_LATENCY-1) = '0' or RSTA /= '0' or not CLK'event or CLK = '0' report "Reading uninitialized data on DP_URAM_XILINX port A" severity error;
         assert debug_item_vldB = '1' or reg_data_b_vld(READ_LATENCY-1) = '0' or RSTB /= '0' or not CLK'event or CLK = '0' report "Reading uninitialized data on DP_URAM_XILINX port B" severity error;
      end generate;

      -- Genrate UltraRAM using XPM macro
      macro : if (DEVICE = "ULTRASCALE") generate

         macro_inst : xpm_memory_tdpram
            generic map (
            --! Common memory genercis
            MEMORY_SIZE          => 2**ADDRESS_WIDTH*DATA_WIDTH,  --Positive integer
            MEMORY_PRIMITIVE     => "ultra", --string "auto", "distributed, "block" "ultra"
            CLOCKING_MODE        => "common_clock", --string "common_clock" or "independent_clock"
            MEMORY_INIT_FILE     => "none", --string "none: or "<filename>.mem"
            MEMORY_INIT_PARAM    => "", --string
            USE_MEM_INIT         => 1, --integer 0,1
            WAKEUP_TIME          => "disable_sleep", --string "disable_sleep" or "use_sleep_pin"
            MESSAGE_CONTROL      => 0, --integer
            ECC_MODE             => "no_ecc", --string
            AUTO_SLEEP_TIME      => 0, --do not change
            USE_EMBEDDED_CONSTRAINT=> 0, --integer
            MEMORY_OPTIMIZATION  => "true", --string "true" or "false"

            --Port A module generics
            WRITE_DATA_WIDTH_A   => DATA_WIDTH,--Positive integer
            READ_DATA_WIDTH_A    => DATA_WIDTH, --positive integer
            BYTE_WRITE_WIDTH_A   => DATA_WIDTH, --positive integer 8,9 or WRITE_DATA_WIDTH_A
            ADDR_WIDTH_A         => ADDRESS_WIDTH,  --positive integer
            READ_RESET_VALUE_A   => "0",--string
            READ_LATENCY_A       => READ_LATENCY, --non negative integer
            WRITE_MODE_A         => "NO_CHANGE", -- Do not change. UltraRAM does not support different write modes on true dual port units

            --Port B module generics
            WRITE_DATA_WIDTH_B   => DATA_WIDTH, --Positive integer
            READ_DATA_WIDTH_B    => DATA_WIDTH, --positive integer
            BYTE_WRITE_WIDTH_B   => DATA_WIDTH, --positive integer 8,9 or WRITE_DATA_WIDTH_A
            ADDR_WIDTH_B         => ADDRESS_WIDTH,  --positive integer
            READ_RESET_VALUE_B   => "0",--string
            READ_LATENCY_B       => READ_LATENCY, --non negative integer
            WRITE_MODE_B         => "NO_CHANGE" -- DO not change. UltraRam does not support different write modes on true dual port units
            )
            port map(
            --common module ports
            SLEEP                => '0',
            --port A ports
            CLKA                 => CLK,
            RSTA                 => RSTA,
            ENA                  => PIPE_ENA,
            REGCEA               => PIPE_ENA,
            WEA(0)               => WEA,
            ADDRA                => ADDRA,
            DINA                 => DIA,
            INJECTSBITERRA       => '0',
            INJECTDBITERRA       => '0',
            DOUTA                => out_mema,
            SBITERRA             => open,
            DBITERRA             => open,
            --port B ports
            CLKB                 => CLK,
            RSTB                 => RSTB,
            ENB                  => PIPE_ENB,
            REGCEB               => PIPE_ENB,
            WEB(0)               => WEB,
            ADDRB                => ADDRB,
            DINB                 => DIB,
            INJECTSBITERRB       => '0',
            INJECTDBITERRB       => '0',
            DOUTB                => out_memb,
            SBITERRB             => open,
            DBITERRB             => open
            );

      end generate;


      -- Instantiate behavioral memory
      beh : if (DEVICE = "BEHAVIORAL") generate
         -- Types for memory instantiation
         type mem_t is array(natural range<>) of std_logic_vector(C_DWIDTH-1 downto 0);
         type pipe_data_t is array(natural range<>) of std_logic_vector(C_DWIDTH-1 downto 0);

         -- Memory variable
         shared variable mem : mem_t(2**C_AWIDTH-1 downto 0);                -- Memory Declaration
         -- Memory register for port A
         signal memrega : std_logic_vector(C_DWIDTH-1 downto 0);
         -- Pipeline for memory for port A
         signal mem_pipe_rega : pipe_data_t(READ_LATENCY-1 downto 0);
         -- Memory register for port B
         signal memregb : std_logic_vector(C_DWIDTH-1 downto 0);
         -- Pipeline for memory for port B
         signal mem_pipe_regb : pipe_data_t(READ_LATENCY-1 downto 0);    -- Pipelines for memory

         -- Specify memory type for behavioral instantiation
         attribute ram_style : string;
         attribute ram_style of mem : variable is "ultra";
      begin

      -- Port A:
      -- RAM : Read has one latency, Write has one latency as well.
      process(CLK)
      begin
         if(CLK'event and CLK='1')then
            if(PIPE_ENA = '1') then
               if(WEA = '1') then
                  mem(to_integer(unsigned(ADDRA))) := DIA;
               else
                  memrega <= mem(to_integer(unsigned(ADDRA)));
               end if;
            end if;
         end if;
      end process;

      -- RAM output data goes through a pipeline.
      process(CLK, memrega)
      begin
         mem_pipe_rega(0) <= memrega;
         if(CLK'event and CLK = '1') then
            for i in 0 to READ_LATENCY-2 loop
               if(PIPE_ENA = '1') then
                  mem_pipe_rega(i+1) <= mem_pipe_rega(i);
               end if;
            end loop;
         end if;
      end process;

      -- Port B:
      -- RAM : Read has one latency, Write has one latency as well.
      process(CLK)
      begin
         if(CLK'event and CLK='1')then
            if(PIPE_ENB = '1') then
               if(WEB = '1') then
                  mem(to_integer(unsigned(ADDRB))) := DIB;
               else
                  memregb <= mem(to_integer(unsigned(ADDRB)));
               end if;
            end if;
         end if;
      end process;

      -- RAM output data goes through a pipeline.
      process(CLK, memregb)
      begin
         mem_pipe_regb(0) <= memregb;
         if(CLK'event and CLK = '1') then
            for i in 0 to READ_LATENCY-2 loop
               if(PIPE_ENB = '1') then
                  mem_pipe_regb(i+1) <= mem_pipe_regb(i);
               end if;
            end loop;
         end if;
      end process;

      -- Assign output signals
      out_mema <= mem_pipe_rega(READ_LATENCY-1);
      out_memb <= mem_pipe_regb(READ_LATENCY-1);

   end generate;

   -- Generate output register
   out_reg_gen : if (EXTERNAL_OUT_REG = true) generate
      out_reg_a : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if PIPE_ENA = '1' then
               if(debug_item_vldA = '1') then
                  DOA <= out_mema;
               else
                  DOA <= (others => 'U');
               end if;
            end if;
         end if;
      end process;

      -- Data valid output registers
      dv_out_reg_a : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RSTA = '1' then
               DOA_DV <= '0';
            elsif PIPE_ENA = '1' then
               DOA_DV <= reg_data_a_vld(READ_LATENCY-1);
            end if;
         end if;
      end process;

      -- Output register for port B
      out_reg_b : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if PIPE_ENB = '1' then
               if(debug_item_vldB = '1') then
                  DOB <= out_memb;
               else
                  DOB <= (others => 'U');
               end if;
            end if;
         end if;
      end process;

      -- Data valid register for port B
      dv_out_reg_b : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RSTB = '1' then
               DOB_DV <= '0';
            elsif PIPE_ENB ='1' then
               DOB_DV <= reg_data_b_vld(READ_LATENCY-1);
            end if;
         end if;
      end process;
   end generate;

   -- Output register disable
   disable_out_reg : if (EXTERNAL_OUT_REG = false) generate
      DOA <= out_mema when debug_item_vldA = '1' else (others => 'U');
      DOB <= out_memb when debug_item_vldB = '1' else (others => 'U');
      DOA_DV <= reg_data_a_vld(READ_LATENCY-1);
      DOB_DV <= reg_data_b_vld(READ_LATENCY-1);
   end generate;

   --Data valid register for port A
   vld_a : process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         if(RSTA = '1') then
            reg_data_a_vld <= (others =>'0');
         elsif (PIPE_ENA = '1') then
            for i in 0 to READ_LATENCY-2 loop
               reg_data_a_vld(i+1) <= reg_data_a_vld(i);
            end loop;
            reg_data_a_vld(0) <= REA;
         end if;
      end if;
   end process;

   --Data valid register for port B
   vld_b : process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         if(RSTB = '1') then
            reg_data_b_vld <= (others => '0');
         elsif (PIPE_ENB = '1') then
            for i in 0 to READ_LATENCY-2 loop
               reg_data_b_vld(i+1) <= reg_data_b_vld(i);
            end loop;
            reg_data_b_vld(0) <= REB;
         end if;
      end if;
   end process;



end architecture DP_URAM_XILINX_arch;
