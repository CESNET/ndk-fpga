-- fifox.vhd: Universal FIFO memory
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Michal Szabo <xszabo11@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- Delay: WR and DI have no delay, FULL, DO and EMPTY is pre calculated and has no delay.
-- STATUS has no delay, it reflects actual state of FIFOX, AFULL/AEMPTY have no delay
-- because are STATUS dependant. Written data takes at least 2 CLK before
-- they can be read.

-- A universal ``FIFO``, capable of implementation in multiple types of memories.
-- Both ``DATA_WIDTH`` and ``ITEMS`` may be set to any value; however ``ITEMS``
-- has an implicit lower limit of ``2`` that will be automatically used if required.
--
-- This component is capable of automatic choice of implementation based on the
-- required size and capabilities of selected ``DEVICE``.
--
-- Delay: None of ``WR``, ``DI``, ``FULL``, ``DO``, ``EMPTY``, ``STATUS``,
-- ``AFULL``, or ``AEMPTY`` has any delay; however, written data takes at least
-- two clock cycles before it can be read.
--
-- .. vhdl:autogenerics:: FIFOX
--
-- .. vhdl:enum:: FIFOX_RAM_TYPE
--
--    Represents the type of memory implementation used by ``FIFOX``. Should be
--    chosen based on the target FPGA and required size of the ``FIFOX``
--
--    Note: this type is for documentation only; string representations of the
--    values of this type are actually used instead.
--
--    .. vhdl:enumval:: LUT
--
--        Recommended when :vhdl:genconstant:`ITEMS <FIFOX.ITEMS>` ≤ 64 (
--        respectively ≤ 32 on Intel FPGAs)
--
--    .. vhdl:enumval:: BRAM
--
--        Recommended when :vhdl:genconstant:`ITEMS <FIFOX.ITEMS>` > 64 (
--        respectively > 32 on Intel FPGAs). Check out :vhdl:entity:`example1`
--
--    .. vhdl:enumval:: URAM
--
--        .. important:: Xilinx Ultrascale(+) only!
--
--        Recommended when :vhdl:genconstant:`DATA_WIDTH <FIFOX.DATA_WIDTH>` ≥ 72
--        and :vhdl:genconstant:`ITEMS <FIFOX.ITEMS>` *
--        :vhdl:genconstant:`DATA_WIDTH <FIFOX.DATA_WIDTH>` ≥ ``288 000``
--
--    .. vhdl:enumval:: SHIFT
--
--        Recommended when :vhdl:genconstant:`ITEMS <FIFOX.ITEMS>` ≤ 16.
--
--    .. vhdl:enumval:: AUTO
--
--        Choose an implementation automatically based on
--        :vhdl:genconstant:`ITEMS <FIFOX.ITEMS>` and
--        :vhdl:genconstant:`DEVICE <FIFOX.DEVICE>`.
entity FIFOX is
   generic(
      -- Data word width in bits.
      DATA_WIDTH          : natural := 16;
      -- FIFO depth in number of data words
      ITEMS               : natural := 16;
      -- See :vhdl:type:`FIFOX_RAM_TYPE`
      RAM_TYPE            : string  := "AUTO";
      -- Defines what architecture the FIFO is implemented on
      --
      -- Options:
      --
      -- - "ULTRASCALE" (Xilinx)
      -- - "7SERIES"    (Xilinx)
      -- - "ARRIA10"    (Intel)
      -- - "STRATIX10"  (Intel)
      -- - "AGILEX"     (Intel)
      DEVICE              : string  := "ULTRASCALE";
      -- Determines how few data words must be left free for
      -- :vhdl:portsignal:`AFULL <fifox.afull>` to be triggered.
      --
      -- (``currently_stored >= (`` :vhdl:genconstant:`ITEMS <fifox.items>` ``- ALMOST_FULL_OFFSET)``
      ALMOST_FULL_OFFSET  : natural := 0;
      -- Determines how few data words must be stored for
      -- :vhdl:portsignal:`AEMPTY <fifox.aempty>` to be triggered.
      --
      -- ( ``currently_stored <= ALMOST_EMPTY_OFFSET`` )
      ALMOST_EMPTY_OFFSET : natural := 0;
      -- Disables the FIFO implementation and replaces it with straight wires.
      FAKE_FIFO           : boolean := false
   );
  port(
      CLK    : in  std_logic;
      RESET  : in  std_logic;

      -- =======================================================================
      --  WRITE INTERFACE
      -- =======================================================================

      DI     : in  std_logic_vector(DATA_WIDTH-1 downto 0);       -- Data input
      WR     : in  std_logic;                                     -- Write enable
      FULL   : out std_logic;                                     -- Full flag
      AFULL  : out std_logic;                                     -- Almost full flag
      STATUS : out std_logic_vector(MAX(log2(ITEMS),1) downto 0); -- Items in memory

      -- =======================================================================
      --  READ INTERFACE
      -- =======================================================================

      DO     : out std_logic_vector(DATA_WIDTH-1 downto 0);       -- Data output
      RD     : in  std_logic;                                     -- Data on DO were read
      EMPTY  : out std_logic;                                     -- Empty flag
      AEMPTY : out std_logic                                      -- Almost empty flag
  );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of FIFOX is

   function correct_items
      return natural is
   begin
      if ITEMS < 2 then
         return 2;
      else
         return ITEMS;
      end if;
   end function;

   -- Number to be used as true ITEMS
   constant ITEMS_INTER    : natural := correct_items;
   --Address bus width
   constant ADDR_WIDTH     : integer := log2(ITEMS_INTER);
   -- Number of items in memory when almost full is triggered.
   constant AFULL_CAPACITY : integer := ITEMS_INTER - ALMOST_FULL_OFFSET;
   -- Set of 2 data output registers used with LUT memory impementation.
   -- (These registers are built in BRAM memory implementation.)
   signal lut_mem_reg      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal lut_mem_out      : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- Data output register used with Ultra-RAM memory implementation.
   signal uram_mem_out     : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal sh_mem_reg      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sh_mem_out      : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- Input and output address bus registers. addr_xxx_cnt is actual
   -- register used for address incrementation. addr_xxx_reg is
   -- register used to slow down the adress by one clock cycle.
   signal addr_in_cnt      : unsigned(ADDR_WIDTH-1 downto 0);
   signal addr_out_cnt     : unsigned(ADDR_WIDTH-1 downto 0);
   signal addr_in_reg      : unsigned(ADDR_WIDTH-1 downto 0);
   signal addr_out_reg     : unsigned(ADDR_WIDTH-1 downto 0);

   -- Write and read enable signals
   signal wr_en            : std_logic;
   signal rd_en            : std_logic;
   signal true_read        : std_logic;
   signal true_write       : std_logic;

   -- Registers for EMPTY flag
   signal empty_comp       : std_logic;
   signal empty_reg        : std_logic;
   -- Adress counter incerement signals
   signal inc_in_cnt       : std_logic;
   signal inc_out_cnt      : std_logic;
   -- Registers that show when adress top limit is reached.
   signal max_in           : std_logic;
   signal max_out          : std_logic;
   -- RD registers
   signal rd_ce            : std_logic;
   signal rd_reg_ce        : std_logic;

   signal sh_reg_rd        : std_logic;
   -- FULL register signal
   signal full_comp        : std_logic;
   --STATUS signal
   signal status_reg       : unsigned(MAX(log2(ITEMS_INTER),0) downto 0);
   -- vld is high when valid data is present on DO when one item FIFO is used
   signal vld              : std_logic;

   -- This function is the AUTO mode of RAM_TYPE. If RAM_TYPE is specified,
   -- specific RAM_TYPE will be used. If AUTO is selected, it will choose the
   -- best implementation according to the size of the FIFO and plaform used.
   -- If the DEVICE and ITEMS_INTER don't fit, BRAM will be used defaultly.

   function auto_ram_type(DATA_WIDTH,ITEMS_INTER:natural; RAM_TYPE,DEVICE:string)
      return string is
   begin
      if (RAM_TYPE = "LUT") then
         return "LUT";
      elsif (RAM_TYPE = "BRAM") then
         return "BRAM";
      elsif (RAM_TYPE = "URAM" AND DEVICE = "ULTRASCALE") then
         return "URAM";
      elsif (RAM_TYPE = "SHIFT" ) then
         return "SHIFT";
      elsif (RAM_TYPE = "AUTO") then
         if (DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES") then
            if (ITEMS_INTER <= 16) then
               return "SHIFT";
            elsif (ITEMS_INTER <= 64) then
               return "LUT";
            elsif ((ITEMS_INTER * DATA_WIDTH) >= 288000 AND DATA_WIDTH >= 72 AND DEVICE = "ULTRASCALE") then
               return "URAM";
            else
               return "BRAM";
            end if;
         elsif (DEVICE = "ARRIA10" OR DEVICE = "STRATIX10" OR DEVICE = "AGILEX") then
            if (ITEMS_INTER <= 32) then
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

   constant RAM_TYPE_SELECTED : string := auto_ram_type(DATA_WIDTH,ITEMS_INTER,RAM_TYPE,DEVICE);

   -- Enable signals have high fanout for data size higher than 1000
   -- Vivado optimize this situation with clock buffer while implementation but this solution
   -- is terrible for timing so we need set max limit of fanout of this signals.
   attribute keep : string;
   attribute max_fanout : integer;

   attribute keep of rd_ce : signal is "true";
   attribute keep of rd_reg_ce : signal is "true";
   attribute max_fanout of rd_ce  : signal is 300;
   attribute max_fanout of rd_reg_ce  : signal is 300;

begin

   real_fifo_g : if not FAKE_FIFO generate

      -- -------------------------------------------------------------------------
      --                   BRAM MEMOMRY GENERATION
      -- -------------------------------------------------------------------------

      bram_g : if RAM_TYPE_SELECTED = "BRAM"  generate
         bram_i : entity work.SDP_BRAM_BEHAV
            generic map(
               DATA_WIDTH  => DATA_WIDTH,
               ITEMS       => ITEMS_INTER,
               OUTPUT_REG  => True           -- Output register always enabled
            )
            port map(
               --WRITE INTERFACE
               WR_CLK      => CLK,
               WR_ADDR     => std_logic_vector(addr_in_reg),
               WR_EN       => wr_en,
               WR_DIN      => DI,
               --READ INTERFACE
               RD_CLK      => CLK,           -- Input and output CLKs are same
               RD_RST      => RESET,
               RD_CE       => rd_ce,         -- Output registers enable signal
               RD_REG_CE   => rd_reg_ce,     -- is accessible
               RD_ADDR     => std_logic_vector(addr_out_reg),
               RD_EN       => '1',           -- Data valid signal always generated
               RD_DOUT     => DO,
               RD_DOUT_VLD => open
            );
      end generate;

      -- -------------------------------------------------------------------------
      --                   LUT MEMEORY GENERATION
      -- -------------------------------------------------------------------------

      logic_g : if RAM_TYPE_SELECTED = "LUT" generate
         sdp_lutram_i : entity work.GEN_LUTRAM
         generic map (
            DATA_WIDTH         => DATA_WIDTH,
            ITEMS              => ITEMS_INTER,
            RD_PORTS           => 1,
            RD_LATENCY         => 0,
            WRITE_USE_RD_ADDR0 => False,
            MLAB_CONSTR_RDW_DC => False,
            DEVICE             => DEVICE
         )
         port map (
            CLK     => CLK,
            WR_EN   => wr_en,
            WR_ADDR => std_logic_vector(addr_in_reg),
            WR_DATA => DI,
            RD_ADDR => std_logic_vector(addr_out_reg),
            RD_DATA => lut_mem_reg
         );

         lut_mem_reg_p :process (CLK)  -- First LUT memory data output register
         begin
            if (rising_edge(CLK)) then
               if (rd_ce = '1') then
                  lut_mem_out <= lut_mem_reg;
               end if;
            end if;
         end process;

         lut_mem_out_p :process (CLK)  -- Second LUT memory data output register
         begin
            if (rising_edge(CLK)) then
               if (rd_reg_ce = '1') then
                  DO <= lut_mem_out;
               end if;
            end if;
         end process;

      end generate;

      -- -------------------------------------------------------------------------
      --                      ULTRA-RAM MEMORY GENERATION
      -- -------------------------------------------------------------------------

      uram_g : if RAM_TYPE_SELECTED = "URAM" generate
         -- Ultra RAM is only on UltraScale devices
         uram_i : entity work.SDP_URAM_XILINX
         generic map(
            DEVICE           => DEVICE,
            DATA_WIDTH       => DATA_WIDTH,
            ADDRESS_WIDTH    => log2(ITEMS_INTER),
            WRITE_MODE       => "READ_FIRST",
            ADDITIONAL_REG   => 0,
            EXTERNAL_OUT_REG => false,
            INTERNAL_OUT_REG => false
         )
         port map(
            CLK     => CLK,
            WEA     => wr_en,
            ADDRA   => std_logic_vector(addr_in_reg),
            DIA     => DI,
            RSTB    => '0',
            REB     => rd_ce,
            PIPE_EN => rd_ce,
            ADDRB   => std_logic_vector(addr_out_reg),
            DOB     => uram_mem_out,
            DOB_DV  => open
         );

         -- Ultra-RAM respond to read request a clock cycle later. When not using
         -- its pipeline, we need to put one more register in the way, so the
         -- data on the output is 2 clock ticks away.

         uram_mem_reg :process (CLK)
         begin
            if (rising_edge(CLK)) then
               if (rd_reg_ce = '1') then
                  DO <= uram_mem_out;
               end if;
            end if;
         end process;

      end generate;

      -- -------------------------------------------------------------------------
      --                      FULL FLAG GENERATOR
      -- -------------------------------------------------------------------------
      -- FULL signal is activated when ammount of items in memory equals the
      -- number of ITEMS_INTER maximum or is greater (because FULL is one CLK cycle
      -- slower).

      full_flag_gen : process (status_reg,wr_en,rd_en)
      begin
         if ((wr_en='0' AND rd_en='0' AND status_reg=ITEMS_INTER)OR(wr_en='1' AND rd_en='0' AND status_reg=ITEMS_INTER - 1)) then
            full_comp <= '1';
         else
            full_comp <= '0';
         end if;
      end process;

      full_flag_reg : process (CLK)
      begin
      if (rising_edge(CLK)) then
            if (RESET = '1') then
               FULL <= '0';
            else
               FULL <= full_comp;
            end if;
         end if;
      end process;

      -- -------------------------------------------------------------------------
      --                      EMPTY FLAG REGISTERS
      -- -------------------------------------------------------------------------

      empty_comp_reg :process (CLK) -- First EMPTY register
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  empty_reg <= '1';
               elsif (rd_ce = '1') then
                  empty_reg <= empty_comp;
               end if;
            end if;
         end process;

      empty_p :process (CLK)        -- Second EMPTY register
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  EMPTY <= '1';
               elsif (rd_reg_ce = '1') then
                  EMPTY <= empty_reg;
               end if;
            end if;
         end process;

      -- -------------------------------------------------------------------------
      --                      STATUS COUNTER
      -- -------------------------------------------------------------------------

      status_gen_inc_dec : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               status_reg <= (others => '0');
            elsif (wr_en = '1' AND rd_en = '0') then
               status_reg <= status_reg + 1;
            elsif (rd_en = '1' AND wr_en = '0') then
               status_reg <= status_reg - 1;
            else
               status_reg <= status_reg;
            end if;
      end if;
      end process;

      STATUS <= std_logic_vector(status_reg);

      -- -------------------------------------------------------------------------
      --                      ALMOST FULL GENERATOR
      -- -------------------------------------------------------------------------

      AFULL <= '1' when status_reg >= AFULL_CAPACITY else '0';

      -- -------------------------------------------------------------------------
      --                      ALMOST EMPTY GENERATOR
      -- -------------------------------------------------------------------------

      AEMPTY <= '1' when status_reg <= ALMOST_EMPTY_OFFSET  else '0';

      -- -------------------------------------------------------------------------
      --                      GENERAL CONTROL UNIT
      -- -------------------------------------------------------------------------

      wr_en <= WR AND NOT FULL;
      rd_en <= RD AND NOT EMPTY;
      rd_reg_ce <= RD OR EMPTY;
      rd_ce <= rd_reg_ce OR empty_reg;

      non_shift_fifo_g : if (RAM_TYPE_SELECTED /= "SHIFT") generate
         -- -------------------------------------------------------------------------
         --                      FIFO WRITE ADDRESS COUNTER
         -- -------------------------------------------------------------------------

         -- Input address register is inceremented when given command inc_in_cnt
         -- comming from control unit. If addres reaches maximum, it is set to 0.
         -- Data protection is handled by FULL and EMPTY systems.

         cnt_in : process (CLK) -- Input address incrementation
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  addr_in_cnt <= to_unsigned(1,ADDR_WIDTH);
               elsif (inc_in_cnt = '1') then
                  if (max_in = '1') then
                     addr_in_cnt <= (others => '0');
                  else
                     addr_in_cnt <= addr_in_cnt + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_in_reg : process (CLK) -- Inout address register
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  addr_in_reg <= (others => '0');
               elsif(inc_in_cnt = '1') then
                  addr_in_reg <= addr_in_cnt;
               end if;
            end if;
         end process;

         max_in <= '1' when (addr_in_cnt = (ITEMS_INTER-1)) else '0';

         -- -------------------------------------------------------------------------
         --                      FIFO READ ADDRESS COUNTER
         -- -------------------------------------------------------------------------

         -- Output address register is inceremented when given command inc_out_cnt
         -- comming from control unit. If addres reaches maximum, it is set to 0.
         -- Data protection is handled by FULL and EMPTY systems.

         cnt_out_out : process (CLK) -- Output address incrementation
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  addr_out_cnt <= to_unsigned(1,ADDR_WIDTH);
               elsif (inc_out_cnt = '1') then
                  if (max_out = '1') then
                     addr_out_cnt <= (others => '0');
                  else
                     addr_out_cnt <= addr_out_cnt + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_out : process (CLK) -- Output address register
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  addr_out_reg <= (others => '0');
               elsif(inc_out_cnt = '1') then
                  addr_out_reg <= addr_out_cnt;
               end if;
            end if;
         end process;


         max_out <= '1' when (addr_out_cnt = (ITEMS_INTER-1)) else '0';

         -- -------------------------------------------------------------------------
         --                    NON-SHIFT EMPTY FLAG GENERATOR
         -- -------------------------------------------------------------------------

         -- When the difference between output and inpur address registes is 0,
         -- output address has reached the input address and memory is EMPTY.
         -- Because data on output is regisred twice, EMPTY signal is registered
         -- the same way.

         empty_flag_gen : process (addr_in_cnt, addr_out_cnt)
         begin
            if (addr_out_cnt = addr_in_cnt) then
               empty_comp <= '1';
            else
               empty_comp <= '0';
            end if;
         end process;

         -- -------------------------------------------------------------------------
         --                     NON-SHIFT CONTROL UNIT
         -- -------------------------------------------------------------------------

         inc_in_cnt <= wr_en;
         inc_out_cnt <= rd_ce AND NOT empty_comp;

      end generate non_shift_fifo_g;

         -- ----------------------------------------------------------------------
         --                    SHIFT MEMORY GENERATION
         -- ----------------------------------------------------------------------

      sh_mem_g : if (RAM_TYPE_SELECTED = "SHIFT") generate
         sh_mem_i : entity work.SH_REG_BASE_DYNAMIC
            generic map(
               DATA_WIDTH => DATA_WIDTH,
               NUM_BITS   => ITEMS_INTER,
               INIT_TYPE  => 0,
               OPT        => "VIVADO"
            )
            port map(
               -- CLOCK SOURCE
               CLK        => CLK,
               CE         => wr_en,
               ADDR       => std_logic_vector(addr_out_reg),
               DIN        => DI,
               DOUT       => sh_mem_reg
            );

         sh_mem_reg_p :process (CLK)  -- First SHIFT memory data output register
            begin
               if (rising_edge(CLK)) then
                  if (rd_ce = '1') then
                     sh_mem_out <= sh_mem_reg;
                  end if;
               end if;
            end process;

         sh_mem_out_p :process (CLK)  -- Second SHIFT memory data output register
            begin
               if (rising_edge(CLK)) then
                  if (rd_reg_ce = '1') then
                     DO <= sh_mem_out;
                  end if;
               end if;
         end process;

         -- ----------------------------------------------------------------------
         --                    SHIFT MEM EMPTY FLAG GENERATOR
         -- ----------------------------------------------------------------------

         empty_comp <= '1' when addr_out_reg = ITEMS_INTER-1 else '0';

         -- ----------------------------------------------------------------------
         --                    SHIFT MEM OUTPUT ADDRESS COUNTER
         -- ----------------------------------------------------------------------

         -- This output adress generator returns numbers between 0 and [ITEMS_INTER],
         -- according to wr_en and sh_reg_rd signals. while begins at ITEMS_INTER,
         -- one abowe that is 0 and the continues onward.

         adrr_stat_gen_inc_dec : process (CLK)
         begin
            if (rising_edge(CLK)) then
               if (RESET = '1') then
                  addr_out_reg <= to_unsigned(ITEMS_INTER-1,log2(ITEMS_INTER));
               elsif (wr_en = '1' AND sh_reg_rd = '0') then
                  if (addr_out_reg = ITEMS_INTER-1) then
                     addr_out_reg <= (others => '0');
                  else
                     addr_out_reg <= addr_out_reg + 1;
                  end if;
               elsif (sh_reg_rd = '1' AND wr_en = '0') then
                  if (addr_out_reg = 0) then
                     addr_out_reg <= to_unsigned(ITEMS_INTER-1,log2(ITEMS_INTER));
                  else
                     addr_out_reg <= addr_out_reg - 1;
                  end if;
               else
                  addr_out_reg <= addr_out_reg;
               end if;
            end if;
         end process;

         -- ----------------------------------------------------------------------
         --                    SHIFT MEM CONTROL UNIT
         -- ----------------------------------------------------------------------

         sh_reg_rd <= rd_ce AND NOT empty_comp;

      end generate sh_mem_g;
   end generate; -- end of real fifo

   fake_fifo_g : if FAKE_FIFO generate
      DO     <= DI;
      FULL   <= not RD;
      AFULL  <= not RD;
      STATUS <= (others => '0');
      EMPTY  <= not WR;
      AEMPTY <= not WR;
   end generate; -- end of fake fifo

end architecture;
