-- n_loop_op_pro.vhd : N loop operator pro
--!
--! \file
--! \brief N loop operator pro
--! \author Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- -----------------------------------------------------------------------------
--                               Description
-- -----------------------------------------------------------------------------
-- This unit serves the same purpose as the N_LOOP_OP unit on which it is based
-- on except that it uses NP_DSTMEM_PRO and not the NP_DISTMEM as an inner memory.
-- This means, that it requires additional double speed CLK2 and has lesser chip
-- resource usage.
-- However the NP_DISTMEM_PRO memory has an increased read latency (2 CLK cycles)
-- and so does this unit (in both the OP interface and the READ interface).
--------
-- For usage and behaiour example see the description of the original N_LOOP_OP.
-------

-- -----------------------------------------------------------------------------
--                            Entity declaration
-- -----------------------------------------------------------------------------

entity N_LOOP_OP_PRO is
generic (
   -- Data width
   DATA_WIDTH     : integer := 16;
   -- Number of items to select from
   ITEMS          : integer := 32;
   -- Enable immediate reset of all data in the memory to RESET_VAL by the RESET signal (leads to worse timing)
   QUICK_RESET_EN : boolean := false;
   -- Items value after reset
   RESET_VAL      : integer := 0;

   -- Number of independent read interfaces
   READ_PORTS     : integer := 2;

   -- Number of intependent user-defined operator units
   OPERATORS      : integer := 4;
   -- Number of different operations
   OPERATIONS     : integer := 5;

   -- Target device
   -- "7SERIES", "ULTRASCALE"
   DEVICE         : string  := "7SERIES"
);
port (

   -- =====================================================
   -- clock & reset
   -- =====================================================
   CLK            : in  std_logic;
   -- Clock with the same source as the CLK and double frequency
   CLK2           : in  std_logic;
   -- !! MUST BE SYNCHRONISED ON rising_edge(CLK) !!
   RESET          : in  std_logic;

   -- =====================================================
   -- Interface for operations ordering per operator
   -- =====================================================

   -- desired item address for each operator unit
   OP_ITEM_SEL    : in  slv_array_t(OPERATORS-1 downto 0)(log2(ITEMS)-1 downto 0);
   -- desired operations for each operator unit (can be used for operation metadata informations)
   OP_OPERATIONS  : in  slv_array_t(OPERATORS-1 downto 0)(OPERATIONS-1 downto 0);

   -- =====================================================
   -- Input interface for user operator units
   --
   -- (1 CLK latency from )
   -- =====================================================

   -- chosen item's address
   OP_IN_SEL      : out slv_array_t(OPERATORS-1 downto 0)(log2(ITEMS)-1 downto 0);
   -- mask of OP_IN interfaces with the same OP_IN_SEL (helps to identify the source interfaces of this operator unit)
   OP_IN_SRC      : out slv_array_t(OPERATORS-1 downto 0)(OPERATORS-1 downto 0);
   -- chosen operations
   -- (  if multiple UP_IN_SEL have the same value, than the OP_IN_OPS of the first of them is equal to OR )
   -- (                  of OP_OPERATIONS on these interfaces, while the other OP_IN_OPS are 0             )
   OP_IN_OPS      : out slv_array_t(OPERATORS-1 downto 0)(OPERATIONS-1 downto 0);
   -- selected input data for operation
   OP_IN_DATA     : out slv_array_t(OPERATORS-1 downto 0)(DATA_WIDTH-1 downto 0);

   -- =====================================================
   -- Output interface for user operator units
   --
   -- (0 latency, operators must be combination logic only)
   -- =====================================================

   -- data after operations execution
   OP_OUT_DATA    : in  slv_array_t(OPERATORS-1 downto 0)(DATA_WIDTH-1 downto 0);

   -- =====================================================
   -- Interface for independent data reading
   -- =====================================================

   -- item select
   READ_ADDR      : in  slv_array_t(READ_PORTS-1 downto 0)(log2(ITEMS)-1 downto 0);
   -- read item (1 CLK latency from READ_ADDR)
   READ_DATA      : out slv_array_t(READ_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0)

);
end entity N_LOOP_OP_PRO;

architecture full of N_LOOP_OP_PRO is

   ---------------------------------------------------
   -- constants
   ---------------------------------------------------

   constant RESET_VAL_VEC : std_logic_vector(DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(RESET_VAL,DATA_WIDTH));

   ---------------------------------------------------

   ---------------------------------------------------
   -- memory interface
   ---------------------------------------------------

   signal mem_in_we     : std_logic_vector(OPERATORS-1 downto 0);
   signal mem_in_addr   : slv_array_t(OPERATORS-1 downto 0)(log2(ITEMS)-1 downto 0);
   signal mem_in_data   : slv_array_t(OPERATORS-1 downto 0)(DATA_WIDTH-1 downto 0);

   signal mem_out_addr  : slv_array_t(READ_PORTS+OPERATORS-1 downto 0)(log2(ITEMS)-1 downto 0);
   signal mem_out_data  : slv_array_t(READ_PORTS+OPERATORS-1 downto 0)(DATA_WIDTH-1 downto 0);

   signal read_addr_reg0: slv_array_t(0 to READ_PORTS-1)(log2(ITEMS)-1 downto 0);
   signal read_addr_reg1: slv_array_t(0 to READ_PORTS-1)(log2(ITEMS)-1 downto 0);

   ---------------------------------------------------

   ---------------------------------------------------
   -- data registers
   ---------------------------------------------------

   signal reg_1_op_in_src : slv_array_t(OPERATORS-1 downto 0)(OPERATORS-1 downto 0);
   signal reg_1_addr      : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg_1_op        : slv_array_t(0 to OPERATORS-1)(0 to OPERATIONS-1);
   signal reg_1_vld       : std_logic_vector(0 to OPERATORS-1);

   signal reg0_vld        : std_logic_vector(0 to OPERATORS-1);
   signal reg0_d_sel      : slv_array_t(0 to OPERATORS-1)(3-1 downto 0); -- data input select ("000" - reg0; "001" - reg1; "010" - reg2; "011" - reg3; "100" - reg4; other - invalid)
   signal reg0_d_sel_a    : slv_array_t(0 to OPERATORS-1)(log2(OPERATORS)-1 downto 0);
   signal reg0_addr       : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg0_op         : slv_array_t(0 to OPERATORS-1)(0 to OPERATIONS-1);

   signal reg1_data       : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
   signal reg1_addr       : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg1_vld        : std_logic_vector(0 to OPERATORS-1);

   signal reg2_data       : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
   signal reg2_addr       : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg2_vld        : std_logic_vector(0 to OPERATORS-1);

   signal reg3_data       : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
   signal reg3_addr       : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg3_vld        : std_logic_vector(0 to OPERATORS-1);

   signal reg4_data       : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
   signal reg4_addr       : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
   signal reg4_vld        : std_logic_vector(0 to OPERATORS-1);

   ---------------------------------------------------

   ---------------------------------------------------
   -- data init
   ---------------------------------------------------

   signal init_val  : std_logic_vector(0 to ITEMS-1);

   ---------------------------------------------------

begin

   ---------------------------------------------------
   -- DATA INIT
   ---------------------------------------------------

   data_init_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            if (reg1_vld(i)='1') then
               init_val(to_integer(unsigned(reg1_addr(i)))) <= '0';
            end if;
         end loop;

         if (RESET='1') then
            init_val <= (others => '1');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- MULTIPORT MEMORY FOR DATA
   ---------------------------------------------------

   mem_i : entity work.NP_LUTRAM_PRO
   generic map(
    DATA_WIDTH => DATA_WIDTH,
    ITEMS      => ITEMS,
    WRITE_PORTS=> OPERATORS,
    READ_PORTS => READ_PORTS+OPERATORS,
    DEVICE     => DEVICE
   )
   port map(
    WCLK       => CLK,
    WCLKN      => CLK2,
    WRESET     => RESET,

    WE         => mem_in_we,
    ADDRA      => mem_in_addr,
    DI         => mem_in_data,

    ADDRB      => mem_out_addr,
    DOB        => mem_out_data
   );

   ---------------------------------------------------

   ---------------------------------------------------
   -- DATA_READ
   ---------------------------------------------------

   read_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to READ_PORTS-1 loop
            read_addr_reg0(i) <= READ_ADDR(i);
            read_addr_reg1(i) <= read_addr_reg0(i);
         end loop;
      end if;
   end process;

   mem_read_pr : process (all)
   begin
      -- operators read
      for i in READ_PORTS to READ_PORTS+OPERATORS-1 loop
         mem_out_addr(i) <= OP_ITEM_SEL(i-READ_PORTS);
      end loop;

      -- port read
      for i in 0 to READ_PORTS-1 loop
         mem_out_addr(i) <= READ_ADDR(i);

         READ_DATA(i)    <= mem_out_data(i);

         if (QUICK_RESET_EN=true and init_val(to_integer(unsigned(read_addr_reg1(i))))='1') then
            READ_DATA(i) <= RESET_VAL_VEC;
         end if;

         for e in 0 to OPERATORS-1 loop
            if (reg4_addr(e)=read_addr_reg1(i) and reg4_vld(e)='1') then
               READ_DATA(i) <= reg4_data(e);
            end if;
         end loop;

         for e in 0 to OPERATORS-1 loop
            if (reg3_addr(e)=read_addr_reg1(i) and reg3_vld(e)='1') then
               READ_DATA(i) <= reg3_data(e);
            end if;
         end loop;

         for e in 0 to OPERATORS-1 loop
            if (reg2_addr(e)=read_addr_reg1(i) and reg2_vld(e)='1') then
               READ_DATA(i) <= reg2_data(e);
            end if;
         end loop;

         for e in 0 to OPERATORS-1 loop
            if (reg1_addr(e)=read_addr_reg1(i) and reg1_vld(e)='1') then
               READ_DATA(i) <= reg1_data(e);
            end if;
         end loop;

      end loop;

   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg-1 SETTING
   ---------------------------------------------------

   reg_1_pr : process (RESET,CLK)
      variable ops : slv_array_t(0 to OPERATORS-1)(0 to OPERATIONS-1);
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg_1_addr(i) <= OP_ITEM_SEL(i);

            -- get operations
            ops(i) := OP_OPERATIONS(i);

            -- join operations
            for e in i+1 to OPERATORS-1 loop
               if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                  ops(i) := ops(i) or OP_OPERATIONS(e);
               end if;
            end loop;

            -- zero out operations
            for e in 0 to i-1 loop
               if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                  ops(i) := (others => '0');
               end if;
            end loop;

            -- save operations and valid
            reg_1_op(i)  <= ops(i);
            reg_1_vld(i) <= (or ops(i));

         end loop;

         if (RESET='1') then
            reg_1_op  <= (others => (others => '0'));
            reg_1_vld <= (others =>'0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg0 SETTING
   ---------------------------------------------------

   reg0_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg0_vld(i)  <= reg_1_vld(i);
            reg0_addr(i) <= reg_1_addr(i);
            reg0_op(i)   <= reg_1_op(i);

            -- save data select
            reg0_d_sel(i)   <= "000";
            reg0_d_sel_a(i) <= (others => '0');

            -- overwrite with reg4
            for e in OPERATORS-1 downto 0 loop
               if (reg_1_addr(i)=reg3_addr(e) and reg3_vld(e)='1') then
                  reg0_d_sel(i)   <= "100";
                  reg0_d_sel_a(i) <= std_logic_vector(to_unsigned(e,log2(OPERATORS)));
               end if;
            end loop;

            -- overwrite with reg3
            for e in OPERATORS-1 downto 0 loop
               if (reg_1_addr(i)=reg2_addr(e) and reg2_vld(e)='1') then
                  reg0_d_sel(i)   <= "011";
                  reg0_d_sel_a(i) <= std_logic_vector(to_unsigned(e,log2(OPERATORS)));
               end if;
            end loop;

            -- overwrite with reg2
            for e in OPERATORS-1 downto 0 loop
               if (reg_1_addr(i)=reg1_addr(e) and reg1_vld(e)='1') then
                  reg0_d_sel(i)   <= "010";
                  reg0_d_sel_a(i) <= std_logic_vector(to_unsigned(e,log2(OPERATORS)));
               end if;
            end loop;

            -- overwrite with reg1
            for e in OPERATORS-1 downto 0 loop
               if (reg_1_addr(i)=reg0_addr(e) and reg0_vld(e)='1') then
                  reg0_d_sel(i)   <= "001";
                  reg0_d_sel_a(i) <= std_logic_vector(to_unsigned(e,log2(OPERATORS)));
               end if;
            end loop;

         end loop;

         if (RESET='1') then
            reg0_op  <= (others => (others => '0'));
            reg0_vld <= (others => '0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- OPERATOR INPUT GENERATIONS
   ---------------------------------------------------


   op_in_to_downto_gen : for i in 0 to OPERATORS-1 generate
      OP_IN_SEL(i) <= reg0_addr(i);
      OP_IN_OPS(i) <= reg0_op(i);
   end generate;

   op_in_data_pr : process (all)
   begin
      for i in 0 to OPERATORS-1 loop
         if    (reg0_d_sel(i)="000") then
            OP_IN_DATA(i) <= mem_out_data(i+READ_PORTS) when QUICK_RESET_EN=false or init_val(to_integer(unsigned(reg0_addr(i))))='0' else RESET_VAL_VEC;
         elsif (reg0_d_sel(i)="001") then
            OP_IN_DATA(i) <= reg1_data(to_integer(unsigned(reg0_d_sel_a(i))));
         elsif (reg0_d_sel(i)="010") then
            OP_IN_DATA(i) <= reg2_data(to_integer(unsigned(reg0_d_sel_a(i))));
         elsif (reg0_d_sel(i)="011") then
            OP_IN_DATA(i) <= reg3_data(to_integer(unsigned(reg0_d_sel_a(i))));
         elsif (reg0_d_sel(i)="100") then
            OP_IN_DATA(i) <= reg4_data(to_integer(unsigned(reg0_d_sel_a(i))));
         else
            OP_IN_DATA(i) <= (others => '1'); -- invalid option
         end if;
      end loop;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg1 SETTING
   ---------------------------------------------------

   reg1_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg1_data(i) <= OP_OUT_DATA(i);
            reg1_vld(i)  <= '0';
            for e in i to OPERATORS-1 loop
                if (reg0_vld(e)='1' and reg0_addr(i)=reg0_addr(e)) then
                    reg1_vld(i) <= '1';
                end if;
            end loop;
            reg1_addr(i) <= reg0_addr(i);
         end loop;

         if (RESET='1') then
            reg1_vld <= (others =>'0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg2 SETTING
   ---------------------------------------------------

   reg2_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg2_data(i) <= reg1_data(i);
            reg2_vld(i)  <= reg1_vld(i);
            reg2_addr(i) <= reg1_addr(i);
         end loop;

         if (RESET='1') then
            reg2_vld <= (others =>'0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg3 SETTING
   ---------------------------------------------------

   reg3_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg3_data(i) <= reg2_data(i);
            reg3_vld(i)  <= reg2_vld(i);
            reg3_addr(i) <= reg2_addr(i);
         end loop;

         if (RESET='1') then
            reg3_vld <= (others =>'0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- reg4 SETTING
   ---------------------------------------------------

   reg4_pr : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         for i in 0 to OPERATORS-1 loop
            -- save data
            reg4_data(i) <= reg3_data(i);
            reg4_vld(i)  <= reg3_vld(i);
            reg4_addr(i) <= reg3_addr(i);
         end loop;

         if (RESET='1') then
            reg4_vld <= (others =>'0');
         end if;
      end if;
   end process;

   ---------------------------------------------------

   ---------------------------------------------------
   -- DATA WRITE
   ---------------------------------------------------

   mem_in_gen : for i in 0 to OPERATORS-1 generate
      mem_in_we(i)   <= reg1_vld(i);
      mem_in_data(i) <= reg1_data(i);
      mem_in_addr(i) <= reg1_addr(i);
   end generate;

   ---------------------------------------------------

   ---------------------------------------------------
   -- OP_IN_SRC setting
   ---------------------------------------------------

   op_in_src_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then

         reg_1_op_in_src <= (others => (others => '0'));
         for i in OPERATORS-1 downto 0 loop
            -- Set when any operation requested
            -- on any port with index higher
            -- or equal to this one.
            for e in OPERATORS-1 downto i loop
               if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                  if ((or OP_OPERATIONS(e))='1') then
                     reg_1_op_in_src(i)(e) <= '1';
                  end if;
               end if;
            end loop;
            -- Reset when the operations will actually be
            -- propagated to a port with lower index (higher priority).
            for e in i-1 downto 0 loop
               if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                  reg_1_op_in_src(i) <= (others => '0');
               end if;
            end loop;
         end loop;

         OP_IN_SRC <= reg_1_op_in_src;

         if (RESET='1') then
            reg_1_op_in_src <= (others => (others => '0'));
            OP_IN_SRC       <= (others => (others => '0'));
         end if;
      end if;
   end process;

   ---------------------------------------------------

end full;
