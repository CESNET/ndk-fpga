-- sdp_memx.vhd: SDP_MEMX
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Michal Szabo <xszabo11@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- SDP_MEMX is component capable of implementing memeory into different
-- memory types, such as LUT memeory, BRAMs and UltraRAMs. It also has
-- automatic mode that based on DATA_WIDTH and ITEMS decides which memory
-- type should be used. Data output delay can be 1 CLK cycle if OUTPUT_REG
-- is False or 2 CLK cycles if True. Output registers are enabled with
-- RD_PIPE_EN together at the same time.

entity SDP_MEMX is
   generic(
      -- Data word width in bits.
      DATA_WIDTH          : natural := 8;
      -- FIFO depth, number of data words
      ITEMS               : natural := 16;
      -- Select memory implementation. Options:
      -- "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32),
      -- "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32),
      -- "URAM"  - effective when ITEMS*DATA_WIDTH >= 288000
      --           and DATA_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+)),
      -- "AUTO"  - effective implementation dependent on ITEMS and DEVICE.
      RAM_TYPE            : string  := "AUTO";
      -- Defines what architecture is FIFO implemented on Options:
      -- "ULTRASCALE" (Xilinx)
      -- "7SERIES"    (Xilinx)
      -- "ARRIA10"    (Intel)
      -- "STRATIX10"  (Intel)
      -- "AGILEX"     (Intel)
      DEVICE              : string  := "ULTRASCALE";
      -- Swithes one extra output register on/off.
      OUTPUT_REG          : boolean := True
   );
  port(
      CLK    : in  std_logic;
      RESET  : in  std_logic;
      -- =======================================================================
      --  WRITE INTERFACE
      -- =======================================================================
      WR_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);   --Write data
      WR_ADDR     : in  std_logic_vector((log2(ITEMS))-1 downto 0);--Write address
      WR_EN       : in  std_logic;                                 --Write enable
      -- =======================================================================
      --  READ INTERFACE
      -- =======================================================================
      RD_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);   --Read data
      RD_ADDR     : in  std_logic_vector((log2(ITEMS))-1 downto 0);--Read address
      RD_PIPE_EN  : in  std_logic                                  --Read enable
  );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of SDP_MEMX is

   -- Set of 2 data output registers used with LUT memory impementation.
   -- (These registers are built in BRAM memory implementation.)
   signal lut_mem_reg      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal lut_mem_out      : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- This function is the AUTO mode of RAM_TYPE. If RAM_TYPE is specified,
   -- specific RAM_TYPE will be used. If AUTO is selected, it will choose the
   -- best implementation according to the size of the memory and plaform used.
   -- If the DEVICE and ITEMS don't fit, BRAM will be used defaultly.

   function auto_ram_type(DATA_WIDTH,ITEMS:natural; RAM_TYPE,DEVICE:string)
                           return string is
   begin
      if (RAM_TYPE = "LUT") then
         return "LUT";
      elsif (RAM_TYPE = "BRAM") then
         return "BRAM";
      elsif (RAM_TYPE = "URAM" AND DEVICE = "ULTRASCALE") then
         return "URAM";
      elsif (RAM_TYPE = "AUTO") then
         if (DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES") then
            if (ITEMS <= 64) then
               return "LUT";
            elsif ((ITEMS * DATA_WIDTH) >= 288000 AND DATA_WIDTH >= 72 AND DEVICE = "ULTRASCALE") then
               return "URAM";
            else
               return "BRAM";
            end if;
         elsif (DEVICE = "ARRIA10" OR DEVICE = "STRATIX10" OR DEVICE = "AGILEX") then
            if (ITEMS <= 32) then
               return "LUT";
            else
               return "BRAM";
            end if;
         else
            report "Wrong RAM_TYPE settings. BRAM memory used!";
            return "BRAM";
         end if;
      else
         report "Wrong RAM_TYPE settings. BRAM memory used!";
         return "BRAM";
      end if;
   end function;

begin

   -- -------------------------------------------------------------------------
   --                   BRAM MEMOMRY GENERATION
   -- -------------------------------------------------------------------------

   bram_g : if auto_ram_type(DATA_WIDTH,ITEMS,RAM_TYPE,DEVICE) = "BRAM"  generate
      bram_i : entity work.SDP_BRAM_BEHAV
         generic map(
            DATA_WIDTH  => DATA_WIDTH,
            ITEMS       => ITEMS,
            OUTPUT_REG  => OUTPUT_REG  -- 2 or 1 output registers setting
         )
         port map(
            --WRITE INTERFACE
            WR_CLK      => CLK,
            WR_ADDR     => WR_ADDR,
            WR_EN       => WR_EN,
            WR_DIN      => WR_DATA,
            --READ INTERFACE
            RD_CLK      => CLK,           -- Input and output CLKs are same
            RD_RST      => RESET,
            RD_CE       => RD_PIPE_EN,
            RD_REG_CE   => RD_PIPE_EN,
            RD_ADDR     => RD_ADDR,
            RD_EN       => RD_PIPE_EN,
            RD_DOUT     => RD_DATA,
            RD_DOUT_VLD => open
         );
   end generate;

   -- -------------------------------------------------------------------------
   --                   LUT MEMEORY GENERATION
   -- -------------------------------------------------------------------------

   logic_g : if auto_ram_type(DATA_WIDTH,ITEMS,RAM_TYPE,DEVICE) = "LUT" generate
      sdp_lutram_i : entity work.GEN_LUTRAM
      generic map (
         DATA_WIDTH         => DATA_WIDTH,
         ITEMS              => ITEMS,
         RD_PORTS           => 1,
         RD_LATENCY         => 0,
         WRITE_USE_RD_ADDR0 => False,
         MLAB_CONSTR_RDW_DC => True,
         DEVICE             => DEVICE
      )
      port map (
         CLK     => CLK,
         WR_EN   => WR_EN,
         WR_ADDR => WR_ADDR,
         WR_DATA => WR_DATA,
         RD_ADDR => RD_ADDR,
         RD_DATA => lut_mem_out
      );

      logic_r_g : if OUTPUT_REG = True generate
         lut_mem_reg_p :process (CLK)  -- 2 output registers with LUT memory
         begin
            if (rising_edge(CLK)) then
               if (RD_PIPE_EN = '1') then
                  lut_mem_reg <= lut_mem_out;
                  RD_DATA     <= lut_mem_reg;
               end if;
            end if;
         end process;
      end generate;

      logic_nr_g : if OUTPUT_REG = False generate
         lut_mem_reg <= lut_mem_out;

         lut_mem_reg_p :process (CLK)  -- 1 output register with LUT memory
         begin
            if (rising_edge(CLK)) then
               if (RD_PIPE_EN = '1') then
                  RD_DATA <= lut_mem_reg;
               end if;
            end if;
         end process;
      end generate;

   end generate;

   -- -------------------------------------------------------------------------
   --                      ULTRA-RAM MEMORY GENERATION
   -- -------------------------------------------------------------------------

   uram_g : if auto_ram_type(DATA_WIDTH,ITEMS,RAM_TYPE,DEVICE) = "URAM" generate
      -- Ultra RAM is only on UltraScale devices
      uram_i : entity work.SDP_URAM_XILINX
      generic map(
         DEVICE           => DEVICE,
         DATA_WIDTH       => DATA_WIDTH,
         ADDRESS_WIDTH    => log2(ITEMS),
         WRITE_MODE       => "READ_FIRST",
         ADDITIONAL_REG   => 0,
         EXTERNAL_OUT_REG => false,
         INTERNAL_OUT_REG => OUTPUT_REG
      )
      port map(
         CLK     => CLK,
         WEA     => WR_EN,
         ADDRA   => WR_ADDR,
         DIA     => WR_DATA,
         RSTB    => '0',
         REB     => '1',
         PIPE_EN => RD_PIPE_EN,
         ADDRB   => RD_ADDR,
         DOB     => RD_DATA,
         DOB_DV  => open
      );
   end generate;

end architecture;
