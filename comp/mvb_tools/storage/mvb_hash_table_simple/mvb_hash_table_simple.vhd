-- mvb_hash_table_simple.vhd
-- Copyright (C) 2024 CESNET z. s. p. o
-- Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- MVB_HASH_TABLE_SIMPLE is a component used for storing and retrieving data
-- from two SDP MEMX memory modules using toeplitz and simple xor hash functions.
-- MI32 bus is used for storing data, MVB bus for retrieving data.
--
-- MI32 is also used to send commands for functions such as storing data, reading
-- the configuration of the component, clearing tables and so on. Commands are
-- sent via the MI_ADDR port, accompanied by data necessary for the requested action
-- sent via the MI_DATA port.
--
-- General commands:
--      0x00 - write command from MI_DWR to the command register.
--      0x04 - write data from MI_DWR to the address shift register.
--      0x08 - write data from MI_DWR to the data shift register.
--      0x0C - write from data shift register to chosen table (see Command register commands)
--             to an address from the address register.
--      0x10 - write data from MI_DWR to hash key configuration shift register.
--
-- Command register commands (bit indexes):
--      0x00 - choose table0 (toeplitz) for writting operations
--      0x01 - choose table1 (simple xor) for writting operations
--      0x02 - clear both tables
--
-- Read interface of the MI32 bus is used for reading table configuration. It can be accessed by setting MI_RD to 1 and choosing data via MI_ADDR port.
--
-- Read interface commands and returned data:
--      0x00 - MVB_ITEMS
--      0x04 - MVB_KEY_WIDTH
--      0x08 - DATA_OUT_WIDTH
--      0x0C - HASH_WIDTH
--      0x10 - HASH_KEY_WIDTH
--      0x14 - TABLE_CAPACITY
--
entity MVB_HASH_TABLE_SIMPLE is
generic (
    TABLE_CAPACITY    : natural := 256;
    MVB_ITEMS         : natural := 4;
    MVB_KEY_WIDTH     : natural := 8;
    DATA_OUT_WIDTH    : natural := 8;
    MI_WIDTH          : natural := 32;
    HASH_KEY_WIDTH    : natural := 32;
    DEVICE            : string  := "STRATIX10"
);
port (
    CLK               : in  std_logic;
    RST               : in  std_logic;

    -- ===========================================================================
    -- PORTS OF INPUT MVB BUS
    -- ===========================================================================
    RX_MVB_KEY        : in  std_logic_vector(MVB_ITEMS*MVB_KEY_WIDTH-1 downto 0);
    RX_MVB_VLD        : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY    : in  std_logic;
    RX_MVB_DST_RDY    : out std_logic;

    -- ===========================================================================
    -- PORTS OF OUTPUT MVB BUS
    -- ===========================================================================
    TX_MVB_DATA       : out std_logic_vector(MVB_ITEMS*DATA_OUT_WIDTH-1 downto 0);
    TX_MVB_MATCH      : out std_logic_vector(MVB_ITEMS-1 downto 0);
    TX_MVB_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);
    TX_MVB_SRC_RDY    : out std_logic;
    TX_MVB_DST_RDY    : in  std_logic;

    -- ===========================================================================
    -- PORTS OF MI BUS
    -- ===========================================================================
    MI_ADDR           : in  std_logic_vector(MI_WIDTH-1 downto 0);
    MI_DWR            : in  std_logic_vector(MI_WIDTH-1 downto 0);
    MI_BE             : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
    MI_WR             : in  std_logic;
    MI_RD             : in  std_logic;
    MI_ARDY           : out std_logic;
    MI_DRD            : out std_logic_vector(MI_WIDTH-1 downto 0);
    MI_DRDY           : out std_logic
);
end entity;

architecture FULL of MVB_HASH_TABLE_SIMPLE is

    -- ===========================================================================
    -- DECLARATION OF CONTROL SIGNALS
    -- ===========================================================================
    constant TABLE_ITEM_WIDTH  : natural := MVB_KEY_WIDTH+DATA_OUT_WIDTH+1;
    constant DATA_WR_REG_WIDTH : natural := div_roundup(TABLE_ITEM_WIDTH,MI_WIDTH)*MI_WIDTH;
    constant HASH_WIDTH        : natural := log2(TABLE_CAPACITY);
    signal mvb_key_local       : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal mi_addr_local       : unsigned(8-1 downto 0);
    signal t_hash_out          : slv_array_t(MVB_ITEMS-1 downto 0)(HASH_WIDTH-1 downto 0);
    signal t_mi_wr_en          : std_logic;
    signal t_rd_data           : slv_array_t(MVB_ITEMS-1 downto 0)(TABLE_ITEM_WIDTH-1 downto 0);
    signal t_wr_addr           : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal t_wr_data           : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal t_wr_en             : std_logic;
    signal x_hash_out          : slv_array_t(MVB_ITEMS-1 downto 0)(HASH_WIDTH-1 downto 0);
    signal x_mi_wr_en          : std_logic;
    signal x_rd_data           : slv_array_t(MVB_ITEMS-1 downto 0)(TABLE_ITEM_WIDTH-1 downto 0);
    signal x_wr_addr           : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal x_wr_data           : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal x_wr_en             : std_logic;
    signal clear_wr_en         : std_logic;
    signal clear_wr_en_vld     : std_logic;
    signal clear_wr_addr       : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal clear_wr_data       : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal cap_cnt             : unsigned(HASH_WIDTH-1 downto 0);
    signal ardy_en             : std_logic;
    signal mi_wr_addr          : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal mi_wr_data          : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal cmd_reg             : std_logic_vector(2-1 downto 0);
    signal mi_wr_data_reg      : std_logic_vector(DATA_WR_REG_WIDTH-1 downto 0);
    signal table_choice        : std_logic;
    signal hash_key            : std_logic_vector(HASH_KEY_WIDTH-1 downto 0);
    signal src_rdy_reg         : std_logic_vector(3-1 downto 0);
    signal mvb_vld_reg         : slv_array_t(MVB_ITEMS-1 downto 0)(3-1 downto 0);
    signal prev_mvb_key_reg    : slv_array_t(MVB_ITEMS-1 downto 0)(2*MVB_KEY_WIDTH-1 downto 0);
    signal prev_mvb_key        : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal mvb_key_t           : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal mvb_key_x           : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal mvb_data_t          : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal mvb_data_x          : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal prev_mvb_key_t_cmp  : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal prev_mvb_key_x_cmp  : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal match_t             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal match_x             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal out_data_sig        : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal out_match_sig       : std_logic_vector(MVB_ITEMS-1 downto 0);

    -- ===========================================================================
    -- DEFINITION OF HASH FUNCTIONS
    -- ===========================================================================
    function f_toeplitz_hash(din : std_logic_vector; key : std_logic_vector) return std_logic_vector is
        variable v_hash      : std_logic_vector(HASH_WIDTH-1 downto 0);
        variable v_key_slice : std_logic_vector(HASH_WIDTH-1 downto 0);
        variable v_key_hash  : std_logic_vector(HASH_WIDTH-1 downto 0);
    begin
        v_hash := (others => '0');

        --report "THASH: din=" & to_hstring(din) & "h";
        --report "THASH: key=" & to_hstring(key) & "h";
        for i in din'length-1 downto 0 loop
            v_key_slice := key((key'length-(din'length-1-i)-1) downto (key'length-HASH_WIDTH-(din'length-1-i)));
            v_key_hash := (others => '0');
            if (din(i) = '1') then
                v_key_hash := v_key_slice;
            end if;
            v_hash := v_hash xor v_key_hash;
        end loop;
        --report "THASH: hash=" & to_hstring(v_hash) & "h";

        return v_hash;
    end;

    function f_simple_xor_hash(din : std_logic_vector; key : std_logic_vector) return std_logic_vector is
        variable v_hash : std_logic_vector(HASH_WIDTH-1 downto 0);
    begin
        v_hash := din(HASH_WIDTH-1 downto 0) xor key(HASH_WIDTH-1 downto 0);

        return v_hash;
    end;

    begin

    mvb_key_local_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_key_local(g) <= RX_MVB_KEY((g+1)*MVB_KEY_WIDTH-1 downto g*MVB_KEY_WIDTH);
    end generate;

    mi_addr_local <= unsigned(MI_ADDR(mi_addr_local'length-1 downto 0));

    -- ===========================================================================
    -- SETTING HASH KEY AND RUNNING HASH FUNCTIONS
    -- ===========================================================================
    hash_functions_g: for g in 0 to MVB_ITEMS-1 generate
        t_hash_out(g) <= f_toeplitz_hash(mvb_key_local(g), hash_key)(HASH_WIDTH-1 downto 0);
        x_hash_out(g) <= f_simple_xor_hash(mvb_key_local(g), hash_key)(HASH_WIDTH-1 downto 0);
    end generate;

    -- ===========================================================================
    -- SDP_MEMX MEMORY MODULES
    -- ===========================================================================
    toeplitz_hash_table_g: for g in 0 to MVB_ITEMS-1 generate
        toeplitz_hash_table_i: entity work.SDP_MEMX
        generic map (
            DATA_WIDTH   => MVB_KEY_WIDTH + DATA_OUT_WIDTH + 1,
            ITEMS        => TABLE_CAPACITY,
            DEVICE       => DEVICE,
            RAM_TYPE     => "AUTO",
            OUTPUT_REG   => True
        )
        port map (
            CLK          => CLK,
            RESET        => RST,
            RD_ADDR      => t_hash_out(g),
            RD_DATA      => t_rd_data(g),
            RD_PIPE_EN   => TX_MVB_DST_RDY,
            WR_ADDR      => t_wr_addr,
            WR_DATA      => t_wr_data,
            WR_EN        => t_wr_en
        );
    end generate;

    simple_xor_hash_table_g: for g in 0 to MVB_ITEMS-1 generate
        simple_xor_hash_table_i: entity work.SDP_MEMX
        generic map (
            DATA_WIDTH   => MVB_KEY_WIDTH + DATA_OUT_WIDTH + 1,
            ITEMS        => TABLE_CAPACITY,
            DEVICE       => DEVICE,
            RAM_TYPE     => "AUTO",
            OUTPUT_REG   => True
        )
        port map (
            CLK          => CLK,
            RESET        => RST,
            RD_ADDR      => x_hash_out(g),
            RD_DATA      => x_rd_data(g),
            RD_PIPE_EN   => TX_MVB_DST_RDY,
            WR_ADDR      => x_wr_addr,
            WR_DATA      => x_wr_data,
            WR_EN        => x_wr_en
        );
    end generate;

    -- ===========================================================================
    -- MI COMMAND REGISTER
    -- ===========================================================================
    mi_cmd_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"00")) then
                cmd_reg <= MI_DWR(2-1 downto 0);
            end if;

            if (clear_wr_en_vld = '0') then
                cmd_reg(1)  <= '0';
            end if;

            if (RST = '1') then
                cmd_reg <= (others => '0');
            end if;
        end if;
    end process;

    table_choice <= cmd_reg(0);
    clear_wr_en  <= cmd_reg(1);

    -- ===========================================================================
    -- MI ADDRESS REGISTER
    -- ===========================================================================
    mi_addr_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"04")) then
                mi_wr_addr <= MI_DWR(mi_wr_addr'length-1 downto 0);
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- MI DATA REGISTER
    -- ===========================================================================
    mi_data_reg_p: process(CLK)
        variable be_dwr : std_logic_vector(MI_DWR'LENGTH-1 downto 0);
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"08")) then
                mi_wr_data_reg <= MI_DWR & mi_wr_data_reg(mi_wr_data_reg'high downto mi_wr_data_reg'low + MI_DWR'LENGTH);
            end if;

            if (RST = '1') then
                mi_wr_data_reg <= (others => '0');
            end if;
        end if;
    end process;

    mi_wr_data <= mi_wr_data_reg(mi_wr_data'length-1 downto 0);

    -- ===========================================================================
    -- MI WRITE ENABLE REGISTER
    -- ===========================================================================
    mi_write_en_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"0C")) then
                t_mi_wr_en <= not table_choice;
                x_mi_wr_en <= table_choice;
            else
                t_mi_wr_en <= '0';
                x_mi_wr_en <= '0';
            end if;

            if (RST = '1') then
                t_mi_wr_en <= '0';
                x_mi_wr_en <= '0';
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- HASH KEY CONFIGURATION REGISTER
    -- ===========================================================================
    hash_key_config_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"10")) then
                hash_key <= MI_DWR & hash_key(hash_key'high downto hash_key'low + MI_DWR'LENGTH);
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- CLEAR TABLE
    -- ===========================================================================
    clear_table_p: process(CLK)
    begin
        if rising_edge(CLK) then
            clear_wr_en_vld <= '1';
            clear_wr_addr   <= std_logic_vector(cap_cnt);

            if (clear_wr_en = '1') then
                if (cap_cnt = TABLE_CAPACITY-1) then
                    clear_wr_en_vld <= '0';
                    ardy_en         <= '1';
                else
                    ardy_en         <= '0';
                end if;

            else
                ardy_en             <= '1';
            end if;

            if (RST = '1') then
                clear_wr_en_vld     <= '0';
                ardy_en             <= '1';
            end if;
        end if;
    end process;

    clear_wr_data <= (others => '0');

    clear_table_cntr_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if (clear_wr_en = '1') then
                cap_cnt <= cap_cnt + 1;
            else
                cap_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- CONFIGURATION READOUT
    -- ===========================================================================
    capacity_readout_p: process(CLK)
    begin
        if rising_edge(CLK) then
            case mi_addr_local is
                when X"00"      => MI_DRD <= std_logic_vector(to_unsigned(MVB_ITEMS, MI_DRD'LENGTH));
                when X"04"      => MI_DRD <= std_logic_vector(to_unsigned(MVB_KEY_WIDTH, MI_DRD'LENGTH));
                when X"08"      => MI_DRD <= std_logic_vector(to_unsigned(DATA_OUT_WIDTH, MI_DRD'LENGTH));
                when X"0C"      => MI_DRD <= std_logic_vector(to_unsigned(HASH_WIDTH, MI_DRD'LENGTH));
                when X"10"      => MI_DRD <= std_logic_vector(to_unsigned(HASH_KEY_WIDTH, MI_DRD'LENGTH));
                when X"14"      => MI_DRD <= std_logic_vector(to_unsigned(TABLE_CAPACITY, MI_DRD'LENGTH));
                when others => NULL;
            end case;

            MI_DRDY <= MI_RD;

            if (RST = '1') then
                MI_DRDY <= '0';
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- MVB KEY COMPARATOR
    -- ===========================================================================
    mvb_key_comparator_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_key_t(g) <= t_rd_data(g)(TABLE_ITEM_WIDTH-1 downto DATA_OUT_WIDTH+1);
        mvb_key_x(g) <= x_rd_data(g)(TABLE_ITEM_WIDTH-1 downto DATA_OUT_WIDTH+1);

        mvb_data_t(g) <= t_rd_data(g)(DATA_OUT_WIDTH downto 1);
        mvb_data_x(g) <= x_rd_data(g)(DATA_OUT_WIDTH downto 1);

        prev_mvb_key_t_cmp(g) <= '1' when (mvb_key_t(g) = prev_mvb_key(g)) else '0';
        prev_mvb_key_x_cmp(g) <= '1' when (mvb_key_x(g) = prev_mvb_key(g)) else '0';

        match_t(g) <= t_rd_data(g)(0) and prev_mvb_key_t_cmp(g);
        match_x(g) <= x_rd_data(g)(0) and prev_mvb_key_x_cmp(g);

        out_data_sig(g)  <= mvb_data_t(g) when (match_t(g) = '1') else mvb_data_x(g);
        out_match_sig(g) <= match_t(g) or match_x(g);

        mvb_key_comparator_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    TX_MVB_DATA((g+1)*DATA_OUT_WIDTH-1 downto g*DATA_OUT_WIDTH) <= out_data_sig(g);
                    TX_MVB_MATCH(g) <= out_match_sig(g);
                end if;
            end if;
        end process;
    end generate;

    -- ===========================================================================
    -- PREVIOUS MVB KEY SHIFT REGISTERS
    -- ===========================================================================
    prev_mvb_key_shift_reg_g: for g in 0 to MVB_ITEMS-1 generate
        prev_mvb_key_shift_reg_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    prev_mvb_key_reg(g) <= prev_mvb_key_reg(g)(prev_mvb_key_reg(g)'high - MVB_KEY_WIDTH downto prev_mvb_key_reg(g)'low) & mvb_key_local(g);
                end if;
            end if;
        end process;

        prev_mvb_key(g) <= prev_mvb_key_reg(g)(prev_mvb_key_reg(g)'high downto prev_mvb_key_reg(g)'high - MVB_KEY_WIDTH + 1);
    end generate;

    -- ===========================================================================
    -- TX_MVB_SRC_RDY SHIFT REGISTERS
    -- ===========================================================================
    src_rdy_shift_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_MVB_DST_RDY = '1') then
                src_rdy_reg <= src_rdy_reg(src_rdy_reg'high - 1 downto src_rdy_reg'low) & RX_MVB_SRC_RDY;
            end if;

            if (RST = '1') then
                src_rdy_reg <= (others => '0');
            end if;
        end if;
    end process;

    TX_MVB_SRC_RDY <= src_rdy_reg(src_rdy_reg'high);

    -- ===========================================================================
    -- MVB VLD SIGNAL SHIFT REGISTERS
    -- ===========================================================================
    mvb_vld_shift_reg_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_vld_shift_reg_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    mvb_vld_reg(g) <= mvb_vld_reg(g)(mvb_vld_reg(g)'high - 1 downto mvb_vld_reg(g)'low) & RX_MVB_VLD(g);
                end if;

                if (RST = '1') then
                    mvb_vld_reg(g) <= (others => '0');
                end if;
            end if;
        end process;

        TX_MVB_VLD(g)  <= mvb_vld_reg(g)(mvb_vld_reg(g)'high);
    end generate;

    -- ===========================================================================
    -- OUTPUT SIGNALS
    -- ===========================================================================
    RX_MVB_DST_RDY       <= TX_MVB_DST_RDY when (MI_WR = '0' and MI_RD = '0' and clear_wr_en = '0') else '0';

    MI_ARDY              <= (MI_WR or MI_RD) and ardy_en;

    t_wr_en              <= t_mi_wr_en or clear_wr_en;
    t_wr_addr            <= clear_wr_addr when clear_wr_en = '1' else mi_wr_addr;
    t_wr_data            <= clear_wr_data when clear_wr_en = '1' else mi_wr_data;

    x_wr_en              <= x_mi_wr_en or clear_wr_en;
    x_wr_addr            <= clear_wr_addr when clear_wr_en = '1' else mi_wr_addr;
    x_wr_data            <= clear_wr_data when clear_wr_en = '1' else mi_wr_data;

end architecture;
