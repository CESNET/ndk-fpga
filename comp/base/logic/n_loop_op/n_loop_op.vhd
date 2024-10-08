-- n_loop_op.vhd : N loop operator
--
-- N loop operator
-- author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
-- date: 2020
--
-- License
--
-- Copyright (C) 2018 CESNET
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- -----------------------------------------------------------------------------
--                               Description
-- -----------------------------------------------------------------------------
-- This unit serves as a too for operating with large array of addressable registers,
-- where multiple different operations need to be done over registers on multiple
-- different addresses at once.
-- The main purpouse of the unit is the elimination of timing problems associated
-- with creating an operation loop over a large register field at the cost of 1 CLK
-- latency.
-- The unit alows multiple operations on the same address. The result of such operations
-- is defined by the user.
-- This unit uses NP_DISTMEM multiport memory internaly. Each OPERATOR unit adds 1 read
-- 1 write port. Try to keep the number of OPERATORS and READ PORTS to a minimum
-- for the sake of resource consumption.
-- To correctly execute operations, the user needs to create one asynchronous operator unit
-- for each IP_IN / OP_OUT interface. These units will have identical structure and should
-- be completely independent.
-- For usage example see "comp/pcie/axi2mfb/comp/tag_manager"
-- or "comp/400g/crossbar_sched_DPDK/comp/desc_fifo" (uses old interface,
-- but is a better example).
--
-- example:
--    ptr_arr : slv_array_t (256-1 downto 0)(10-1 downto 0); -- array of 256 pointers
--  The default value of each pointer is 0.
--  There are 4 interfaces, where each can order to decrement or increment any of
--  the pointers.
--  There is also an interface, which can issue an order to set an pointer to
--  a specific value.
--  Lastly there are 4 independent interfaces, which need to be able to read a pointer
--  value, but don't make any changes.
--
--  The solution is to use this unit with the following set of generics:
--    DATA_WIDTH  => 10
--    ITEMS       => 256
--    RESET_VALUE => 0
--    OPERATORS   => 4+1 -- there are up to 5 different pointers, which will be operated
--    OPERATIONS  => 3   -- increment, decrement, set
--    DEVICE      => "DEVICE" -- target device
--
-- behavior:
--  (here shown with 2 OPERATORS, 3 OPERATIONS and 1 READ PORT)
--  (the operations 0bXXX in this example are ("add 3" & "add 1" & "substract 2"))
--  (the initial values are 123 for item 42 and 666 for item 0)
--
--                    -----    -----    -----    -----    -----    -----
-- CLK              __|   |____|   |____|   |____|   |____|   |____|
-- ~~~~~~~~~~
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~
--                  -\ /------\ /---------------------------------------
-- OP_ITEM_SEL(0)     X   42   X  0
--                  -/ \------/ \---------------------------------------
--
--                  -\ /------\ /---------------------------------------
-- OP_OPERATIONS(0)   X 0b001  X  0b000
--                  -/ \------/ \---------------------------------------
-- ~~~~~~~~~~
-- ~~~~~~~~~~
--                  -\ /---------------\ /------------------------------
-- OP_ITEM_SEL(1)     X        42       X  0
--                  -/ \---------------/ \------------------------------
--
--                  -\ /---------------\ /------------------------------
-- OP_OPERATIONS(1)   X       0b100     X  0b000
--                  -/ \---------------/ \------------------------------
-- ~~~~~~~~~~
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~
--                  ----------\ /------\ /------------------------------
-- OP_IN_SEL(0)                X   42   X  0
--                  ----------/ \------/ \------------------------------
--
--                  ----------\ /!!!!!!\ /------\ /---------------------
-- OP_IN_SRC(0)                X  0b11  X  0b01  X  0b11
--                  ----------/ \!!!!!!/ \------/ \---------------------
--
--                  ----------\ /!!!!!!\ /------------------------------
-- OP_IN_OPS(0)                X 0b101  X  0b000
--                  ----------/ \!!!!!!/ \------------------------------
--
--                  ----------\ /------\ /------------------------------
-- OP_IN_DATA(0)               X  123   X  666
--                  ----------/ \------/ \------------------------------
--                          123 + 3 - 2 = 124
--                  ----------\ /------\ /------------------------------
-- OP_OUT_DATA(0)              X  124   X  666
--                  ----------/ \------/ \------------------------------
-- ~~~~~~~~~~
-- ~~~~~~~~~~
--                  ----------\ /---------------\ /---------------------
-- OP_IN_SEL(1)                X        42       X  0
--                  ----------/ \---------------/ \---------------------
--
--                  ----------\ /!!!!!!\ /!!!!!!\ /---------------------
-- OP_IN_SRC(1)                X  0b11  X  0b10  X  0b00
--                  ----------/ \!!!!!!/ \!!!!!!/ \---------------------
--
--                  ----------\ /!!!!!!\ /!!!!!!\ /---------------------
-- OP_IN_OPS(1)                X 0b000  X 0b100  X  0b000
--                  ----------/ \!!!!!!/ \!!!!!!/ \---------------------
--
--                  ----------\ /------\ /------\ /---------------------
-- OP_IN_DATA(1)               X  123   X  124   X  666
--                  ----------/ \------/ \------/ \---------------------
--                                     124 + 3 = 127
--                  ----------\ /------\ /------\ /---------------------
-- OP_OUT_DATA(1)              X  123   X  127   X  666
--                  ----------/ \------/ \------/ \---------------------
-- ~~~~~~~~~~
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~
--                  -\ /------------------------------------------------
-- READ_ADDR(0)       X   42
--                  -/ \------------------------------------------------
--
--                  ----------\ /------\ /------\ /---------------------
-- READ_DATA(0)                X  123   X  124   X  127
--                  ----------/ \------/ \------/ \---------------------
--

-- -----------------------------------------------------------------------------
--                            Entity declaration
-- -----------------------------------------------------------------------------

entity N_LOOP_OP is
generic (
    -- Data width
    DATA_WIDTH         : integer := 16;
    -- Number of items to select from
    ITEMS              : integer := 32;
    -- Enable immediate reset of all data in the memory to RESET_VAL by the RESET signal.
    -- Warning: Leads to worse timing!
    QUICK_RESET_EN     : boolean := false;
    -- Items value after reset (only when QUICK_RESET is enabled)
    RESET_VAL          : integer := 0;

    -- Number of independent read interfaces
    READ_PORTS         : integer := 2;

    -- Number of intependent user-defined operator units
    OPERATORS          : integer := 4;
    -- Number of different operations
    OPERATIONS         : integer := 5;

    -- Metadata width
    META_WIDTH         : integer := 1;

    -- Use register array
    -- With this option set to True the GEN_REG_ARRAY is used to implement
    -- the inner memory instead of the NP_LUTRAM.
    -- This is effective when DATA_WIDTH is very low (8 bits or less).
    USE_REG_ARRAY      : boolean := false;

    -- Target device
    -- "7SERIES", "ULTRASCALE"
    DEVICE             : string  := "7SERIES"
);
port (

    -- =====================================================
    -- clock & reset
    -- =====================================================
    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- =====================================================
    -- Interface for operations ordering per operator
    -- =====================================================

    -- desired item address for each operator unit
    OP_ITEM_SEL    : in  slv_array_t(OPERATORS-1 downto 0)(log2(ITEMS)-1 downto 0);
    -- desired operations for each operator unit (can be used for operation metadata informations)
    OP_OPERATIONS  : in  slv_array_t(OPERATORS-1 downto 0)(OPERATIONS-1 downto 0);
    -- operator metadata
    OP_META        : in  slv_array_t(OPERATORS-1 downto 0)(META_WIDTH-1 downto 0) := (others => (others => '0'));

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
    -- operator metadata
    OP_IN_META     : out slv_array_t(OPERATORS-1 downto 0)(META_WIDTH-1 downto 0);

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
end entity N_LOOP_OP;

architecture full of N_LOOP_OP is

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

    signal read_addr_reg : slv_array_t(0 to READ_PORTS-1)(log2(ITEMS)-1 downto 0);
    signal read_data_reg : slv_array_t(0 to READ_PORTS-1)(DATA_WIDTH-1 downto 0);

    signal read_addr_eq_reg1_reg : slv_array_t(0 to READ_PORTS-1)(0 to OPERATORS-1);
    signal read_addr_eq_reg2_reg : slv_array_t(0 to READ_PORTS-1)(0 to OPERATORS-1);

    ---------------------------------------------------

    ---------------------------------------------------
    -- data registers
    ---------------------------------------------------

    signal reg0_data   : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
    signal reg0_vld    : std_logic_vector(0 to OPERATORS-1);
    signal reg0_d_sel  : slv_array_t(0 to OPERATORS-1)(2-1 downto 0); -- data input select ("00" - reg0; "01" - reg1; "10" - reg2; "11" - invalid)
    signal reg0_d_sel_a: slv_array_t(0 to OPERATORS-1)(log2(OPERATORS)-1 downto 0);
    signal reg0_addr   : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
    signal reg0_op     : slv_array_t(0 to OPERATORS-1)(0 to OPERATIONS-1);
    signal reg0_meta   : slv_array_t(0 to OPERATORS-1)(META_WIDTH-1 downto 0);

    signal reg1_data   : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
    signal reg1_addr   : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
    signal reg1_vld    : std_logic_vector(0 to OPERATORS-1);

    signal reg2_data   : slv_array_t(0 to OPERATORS-1)(DATA_WIDTH-1 downto 0);
    signal reg2_addr   : slv_array_t(0 to OPERATORS-1)(log2(ITEMS)-1 downto 0);
    signal reg2_vld    : std_logic_vector(0 to OPERATORS-1);

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
                if (reg0_vld(i)='1') then
                    init_val(to_integer(unsigned(reg0_addr(i)))) <= '0';
                end if;
            end loop;

            if (RESET='1') then
                init_val <= (others => '1');
            end if;
        end if;
    end process;

    ---------------------------------------------------

    np_lutram_gen : if (USE_REG_ARRAY=false) generate

        ---------------------------------------------------
        -- MULTIPORT MEMORY FOR DATA
        ---------------------------------------------------

        mem_i : entity work.NP_LUTRAM
        generic map (
            DATA_WIDTH => DATA_WIDTH,
            ITEMS      => ITEMS,
            WRITE_PORTS=> OPERATORS,
            READ_PORTS => READ_PORTS+OPERATORS,
            DEVICE     => DEVICE
        )
        port map (
            WCLK       => CLK,

            WE         => mem_in_we,
            ADDRA      => mem_in_addr,
            DI         => mem_in_data,

            ADDRB      => mem_out_addr,
            DOB        => mem_out_data
        );

        ---------------------------------------------------

    end generate;

    reg_array_gen : if (USE_REG_ARRAY=true) generate
        signal tmp_mem_out_data_vec : std_logic_vector((READ_PORTS+OPERATORS)*DATA_WIDTH-1 downto 0);
    begin

        ---------------------------------------------------
        -- REGISTER ARRAY FOR DATA
        ---------------------------------------------------

        mem_i : entity work.GEN_REG_ARRAY
        generic map (
            DATA_WIDTH => DATA_WIDTH,
            ITEMS      => ITEMS,
            WR_PORTS   => OPERATORS,
            RD_PORTS   => READ_PORTS+OPERATORS,
            RD_LATENCY => 0,
            OUTPUT_REG => false,
            DEVICE     => DEVICE
        )
        port map (
            CLK        => CLK,
            RESET      => '0',

            WR_EN      => mem_in_we,
            WR_ADDR    => slv_array_ser(mem_in_addr),
            WR_DATA    => slv_array_ser(mem_in_data),

            RD_ADDR    => slv_array_ser(mem_out_addr),
            RD_DATA    => tmp_mem_out_data_vec
        );

        mem_out_data <= slv_array_downto_deser(tmp_mem_out_data_vec,READ_PORTS+OPERATORS);

        ---------------------------------------------------

    end generate;

    ---------------------------------------------------
    -- DATA_READ
    ---------------------------------------------------

    read_reg_pr : process (RESET,CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to READ_PORTS-1 loop
                read_addr_reg(i) <= READ_ADDR(i);
                read_data_reg(i) <= mem_out_data(i);
            end loop;
            if (QUICK_RESET_EN and RESET='1') then
                read_data_reg <= (others => RESET_VAL_VEC);
            end if;
        end if;
    end process;

    read_addr_comp_reg : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to READ_PORTS-1 loop
                for e in 0 to OPERATORS-1 loop
                    read_addr_eq_reg1_reg(i)(e) <= '1' when READ_ADDR(i)=reg0_addr(e) else '0';
                    read_addr_eq_reg2_reg(i)(e) <= '1' when READ_ADDR(i)=reg1_addr(e) else '0';
                end loop;
            end loop;
        end if;
    end process;

    mem_read_pr : process (OP_ITEM_SEL,READ_ADDR,mem_out_data,reg1_data,reg1_vld,reg2_data,reg2_vld,init_val,read_data_reg,read_addr_reg,read_addr_eq_reg1_reg,read_addr_eq_reg2_reg)
    begin
        -- operators read
        for i in READ_PORTS to READ_PORTS+OPERATORS-1 loop
            mem_out_addr(i) <= OP_ITEM_SEL(i-READ_PORTS);
        end loop;

        -- port read
        for i in 0 to READ_PORTS-1 loop
            mem_out_addr(i) <= READ_ADDR(i);

            READ_DATA(i)    <= read_data_reg(i);

            for e in OPERATORS-1 downto 0 loop
                if (read_addr_eq_reg2_reg(i)(e)='1' and reg2_vld(e)='1') then
                    READ_DATA(i) <= reg2_data(e);
                end if;
            end loop;

            for e in OPERATORS-1 downto 0 loop
                if (read_addr_eq_reg1_reg(i)(e)='1' and reg1_vld(e)='1') then
                    READ_DATA(i) <= reg1_data(e);
                end if;
            end loop;

            if (QUICK_RESET_EN=true and init_val(to_integer(unsigned(read_addr_reg(i))))='1') then
                READ_DATA(i) <= RESET_VAL_VEC;
            end if;

        end loop;

    end process;

    ---------------------------------------------------

    ---------------------------------------------------
    -- reg0 SETTING
    ---------------------------------------------------

    reg0_pr : process (RESET,CLK)
        variable ops : slv_array_t(0 to OPERATORS-1)(0 to OPERATIONS-1);
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to OPERATORS-1 loop
                -- save data
                reg0_data(i) <= mem_out_data(i+READ_PORTS) when QUICK_RESET_EN=false or init_val(to_integer(unsigned(OP_ITEM_SEL(i))))='0' else RESET_VAL_VEC;
                reg0_addr(i) <= OP_ITEM_SEL(i);
                reg0_meta(i) <= OP_META(i);

                -- get operations
                ops(i)    := OP_OPERATIONS(i);

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
                reg0_op(i)  <= ops(i);
                reg0_vld(i) <= (or ops(i));

                -- save data select
                reg0_d_sel(i)   <= "00";
                reg0_d_sel_a(i) <= (others => '0');

                -- overwrite with reg2
                for e in OPERATORS-1 downto 0 loop
                    if (OP_ITEM_SEL(i)=reg1_addr(e) and reg1_vld(e)='1') then
                        reg0_d_sel(i)   <= "10";
                        reg0_d_sel_a(i) <= std_logic_vector(to_unsigned(e,log2(OPERATORS)));
                    end if;
                end loop;

                -- overwrite with reg1
                for e in OPERATORS-1 downto 0 loop
                    if (OP_ITEM_SEL(i)=reg0_addr(e) and reg0_vld(e)='1') then
                        reg0_d_sel(i)   <= "01";
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
        OP_IN_SEL (i) <= reg0_addr(i);
        OP_IN_OPS (i) <= reg0_op  (i);
        OP_IN_META(i) <= reg0_meta(i);
    end generate;

    op_in_data_pr : process (reg0_data,reg0_addr,reg1_data,reg1_addr,reg2_data,reg2_addr,reg0_d_sel,reg0_d_sel_a)
    begin
        for i in 0 to OPERATORS-1 loop
            if    (reg0_d_sel(i)="00") then
                OP_IN_DATA(i) <= reg0_data(i);
            elsif (reg0_d_sel(i)="01") then
                OP_IN_DATA(i) <= reg1_data(to_integer(unsigned(reg0_d_sel_a(i))));
            elsif (reg0_d_sel(i)="10") then
                OP_IN_DATA(i) <= reg2_data(to_integer(unsigned(reg0_d_sel_a(i))));
            else
                OP_IN_DATA(i) <= (others => '0'); -- invalid option
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

            OP_IN_SRC <= (others => (others => '0'));
            for i in OPERATORS-1 downto 0 loop
                -- Set when any operation requested
                -- on any port with index higher
                -- or equal to this one.
                for e in OPERATORS-1 downto i loop
                    if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                        if ((or OP_OPERATIONS(e))='1') then
                            OP_IN_SRC(i)(e) <= '1';
                        end if;
                    end if;
                end loop;
                -- Reset when the operations will actually be
                -- propagated to a port with lower index (higher priority).
                for e in i-1 downto 0 loop
                    if (OP_ITEM_SEL(i)=OP_ITEM_SEL(e)) then
                        OP_IN_SRC(i) <= (others => '0');
                    end if;
                end loop;
            end loop;

            if (RESET='1') then
                OP_IN_SRC <= (others => (others => '0'));
            end if;
        end if;
    end process;

    ---------------------------------------------------

end full;
