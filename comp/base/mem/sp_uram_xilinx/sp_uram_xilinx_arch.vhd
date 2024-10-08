
--
-- SP_URAM_XILINX.vhd: Architecture for single port UltraRAM
-- Copyright (C) 2018 CESNET
-- Author(s): Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
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
use xpm.vcomponents.all;
-- pragma translate_on
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SP_URAM_XILINX_arch of SP_URAM_XILINX is

component xpm_memory_spram
  generic (

    -- Common module generics
    MEMORY_SIZE         : integer := 2048            ;
    MEMORY_PRIMITIVE    : string  := "auto"          ;
    ECC_MODE            : string  := "no_ecc"        ;
    MEMORY_INIT_FILE    : string  := "none"          ;
    MEMORY_INIT_PARAM   : string  := ""              ;
    USE_MEM_INIT        : integer := 1               ;
    WAKEUP_TIME         : string  := "disable_sleep" ;
    AUTO_SLEEP_TIME     : integer := 0               ;
    MESSAGE_CONTROL     : integer := 0               ;
    MEMORY_OPTIMIZATION : string  := "false" ;

    -- Port A module generics
    WRITE_DATA_WIDTH_A  : integer := 32           ;
    READ_DATA_WIDTH_A   : integer := 32           ;
    BYTE_WRITE_WIDTH_A  : integer := 32           ;
    ADDR_WIDTH_A        : integer := 6            ;
    READ_RESET_VALUE_A  : string  := "0"          ;
    READ_LATENCY_A      : integer := 2            ;
    WRITE_MODE_A        : string  := "read_first"

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
    dbiterra       : out std_logic
  );
end component;

-- Function converts boolean value to either 0 or 1 (integer)
function bool2int(b:boolean) return integer is
begin
   if(b) then return 1;
   else return 0;
   end if;
end function;


-- Constants definition
constant READ_LATENCY : integer := 1 + ADDITIONAL_REG + bool2int(INTERNAL_OUT_REG);
constant C_AWIDTH : integer := ADDRESS_WIDTH;
constant C_DWIDTH : integer := DATA_WIDTH;
--constant C_NBPIPE : integer := READ_LATENCY-1;


signal out_mem : std_logic_vector(C_DWIDTH-1 downto 0);

-- Internal Signals

signal reg_data_vld : std_logic_vector(READ_LATENCY-1 downto 0);
signal debug_item_vld : std_logic := '1';

begin
   -- Generate uninitialized memory reports
   assert_gen : if DEBUG_ASSERT_UNINITIALIZED = true generate
      dbg_assertA : process(CLK)
      variable debug_item_written : std_logic_vector(2**ADDRESS_WIDTH-1 downto 0);
      begin
         if CLK'event and CLK = '1' then
            if RST = '1' then
               debug_item_written := (others => '0');
            elsif PIPE_EN = '1' and WE = '1' then
               debug_item_written(to_integer(unsigned(ADDR))) := '1';
            end if;
            debug_item_vld <= debug_item_written(to_integer(unsigned(ADDR)));
         end if;
      end process;
      assert debug_item_vld = '1' or reg_data_vld(READ_LATENCY-1) = '0' or RST /= '0' or not CLK'event or CLK = '0' report "Reading uninitialized data on DP_URAM_XILINX port A" severity error;
   end generate;

-- Macro instantiation
macro_gen : if (DEVICE = "ULTRASCALE") generate
   macro_mem_inst: xpm_memory_spram
   generic map(
      MEMORY_SIZE          => 2**ADDRESS_WIDTH*DATA_WIDTH,
      MEMORY_PRIMITIVE     => "ultra",
      MEMORY_INIT_FILE     => "none",
      MEMORY_INIT_PARAM    => "",
      USE_MEM_INIT         => 1,
      WAKEUP_TIME          => "disable_sleep",
      MESSAGE_CONTROL      => 0,
      ECC_MODE             => "no_ecc",
      AUTO_SLEEP_TIME      => 0,
      MEMORY_OPTIMIZATION  => "true",

      WRITE_DATA_WIDTH_A   => DATA_WIDTH,
      READ_DATA_WIDTH_A    => DATA_WIDTH,
      BYTE_WRITE_WIDTH_A   => DATA_WIDTH,
      ADDR_WIDTH_A         => ADDRESS_WIDTH,
      READ_RESET_VALUE_A   => "0",
      READ_LATENCY_A       => READ_LATENCY,
      WRITE_MODE_A         => WRITE_MODE
   )
   port map(
      sleep          => '0',
      clka           => CLK,
      rsta           => RST,
      ena            => PIPE_EN,
      regcea         => PIPE_EN,
      wea(0)         => WE,
      addra          => ADDR,
      dina           => DI,
      injectsbiterra => '0',
      injectdbiterra => '0',
      douta          => out_mem,
      sbiterra       => open,
      dbiterra       => open
   );
end generate;

-- Generate componenet using behavioral description
beh_gen : if (DEVICE = "BEHAVIORAL") generate
   type mem_t is array(natural range<>) of std_logic_vector(C_DWIDTH-1 downto 0);
   type pipe_data_t is array(natural range<>) of std_logic_vector(C_DWIDTH-1 downto 0);

   signal mem : mem_t(2**C_AWIDTH-1 downto 0);                -- Memory Declaration
   signal memreg : std_logic_vector(C_DWIDTH-1 downto 0);
   signal mem_pipe_reg : pipe_data_t(READ_LATENCY-1 downto 0);    -- Pipelines for memory
   attribute ram_style : string;
   attribute ram_style of mem : signal is "ultra";
   begin
   -- No change mode
   no_chg : if (WRITE_MODE = "NO_CHANGE") generate
      process(CLK)
      begin
        if(CLK'event and CLK='1')then
          if(PIPE_EN = '1') then
            if(WE = '1') then
              mem(to_integer(unsigned(ADDR))) <= DI;
            else
              memreg <= mem(to_integer(unsigned(ADDR)));
            end if;
          end if;
        end if;
      end process;
   end generate; --NO_CHANGE

   -- Write first mode
   write_first_mode : if(WRITE_MODE = "WRITE_FIRST") generate
   -- RAM : Read has one latency, Write has one latency as well.
      process(CLK)
      begin
         if(CLK'event and CLK='1')then
            if(PIPE_EN = '1') then
               if(WE = '1') then
                  mem(to_integer(unsigned(ADDR))) <= DI;
                  memreg <= DI;
               else
                  memreg <= mem(to_integer(unsigned(ADDR)));
               end if;
            end if;
         end if;
      end process;
   end generate;-- WRITE_FIRST

   -- Read first mode
   read_first_gen : if (WRITE_MODE = "READ_FIRST") generate
   -- RAM : Read has one latency, Write has one latency as well.
      process(CLK)
      begin
         if(CLK'event and CLK='1')then
            if(PIPE_EN = '1') then
               if(WE = '1') then
                  mem(to_integer(unsigned(ADDR))) <= DI;
               end if;
               memreg <= mem(to_integer(unsigned(ADDR)));
            end if;
         end if;
      end process;
   end generate; -- READ_FIRST

   -- Generate pipeline delay
   process(CLK, memreg)
   begin
      mem_pipe_reg(0) <= memreg;
      if(CLK'event and CLK = '1') then
         for i in 0 to READ_LATENCY-2 loop
            if(PIPE_EN = '1') then
               mem_pipe_reg(i+1) <= mem_pipe_reg(i);
            end if;
         end loop;
      end if;
   end process;

   out_mem <= mem_pipe_reg(READ_LATENCY-1);

end generate;
   --Data valid register
   vld : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if(rst = '1') then
            reg_data_vld <= (others => '0');
         elsif (PIPE_EN = '1') then
            for i in 0 to READ_LATENCY-2 loop
                reg_data_vld(i+1) <= reg_data_vld(i);
             end loop;
             reg_data_vld(0) <= RE;
          end if;
       end if;
    end process;

  -- Generate output register
   out_reg_gen : if (EXTERNAL_OUT_REG = true) generate
     -- Final output register gives user the option to add a reset and
     -- an additional enable signal just for the data ouptut

      process(CLK)
      begin
         if(CLK'event and CLK = '1') then
            if(PIPE_EN = '1') then
               if debug_item_vld = '1' then
                  DO <= out_mem;
               else
                  DO <= (others => 'U');
               end if;
            end if;
         end if;
      end process;

      -- Data valid output register
      dv_out_reg : process(CLK)
      begin
         if(CLK'event and CLK = '1') then
            if(RST = '1') then
               DO_DV <= '0';
            elsif(PIPE_EN = '1') then
               DO_DV <= reg_data_vld(READ_LATENCY-1);
            end if;
         end if;
      end process;
   end generate;

     -- Assign signals when output register is disabled
   disable_out_reg : if(EXTERNAL_OUT_REG = false) generate
      DO_DV <= reg_data_vld(READ_LATENCY-1);
      DO <= out_mem when debug_item_vld = '1' else (others => 'U');
   end generate;


end architecture SP_URAM_XILINX_arch;
