-- controller.vhd: SWITCH_CONTROLLER component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.proto_match_pack.all;

entity SWITCH_CONTROLLER is
    generic (
        -- Configuration array object.
        CONFIG                : config_array_t := CONFIG_NONE;
        -- Number of match-action tables per port.
        NUM_MATS_PER_PORT     : natural        := tsel(CONFIG(0).match_num_fields = 0, 0, CONFIG'length);
        -- Max capacity of the match-action tables.
        CONFIG_MAX_ITEMS      : natural        := config_array_get_max(CONFIG, MAT_CONFIG_ITEMS);
        -- Max address width in bits.
        CONFIG_MAX_ADDR_WIDTH : natural        := log2(CONFIG_MAX_ITEMS);
        -- Max data vector width in bits.
        CONFIG_MAX_DATA_WIDTH : natural        := config_array_get_max(CONFIG, MAT_CONFIG_MATCH_WIDTH);
        -- Number of output actions.
        CONFIG_NUM_ACTIONS    : natural        := 16;
        -- Width of output actions in bits.
        CONFIG_ACTION_WIDTH   : natural        := log2(CONFIG_NUM_ACTIONS);
        -- Number of input/output ports.
        CONFIG_NUM_PORTS      : natural        := CONFIG_NUM_ACTIONS;
        -- Enable read from match-action tables.
        MAT_READ_ENABLE       : boolean        := true;
        -- MI data bus width in bits.
        MI_DATA_WIDTH         : natural        := 32;
        -- MI address bus width in bits.
        MI_ADDR_WIDTH         : natural        := 32;
        -- Blocks traffic if not enabled (configurable via CSR).
        MI_ENABLE_AXI         : boolean        := true;
        -- Target device.
        DEVICE                : string         := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =========================================================================
        -- MI CONTROL INTERFACE
        -- =========================================================================
        MI_DWR           : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR          : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        MI_RD            : in  std_logic;
        MI_WR            : in  std_logic;
        MI_BE            : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0); -- not supported
        MI_DRD           : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ARDY          : out std_logic;
        MI_DRDY          : out std_logic;

        -- =========================================================================
        -- MATCH-ACTION TABLES READ/WRITE INTERFACE
        -- =========================================================================
        MAT_READ_ADDR    : out std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_READ_EN      : out std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT-1 downto 0);
        MAT_READ_RDY     : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT-1 downto 0);
        MAT_READ_VLD     : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT-1 downto 0);
        MAT_READ_DATA    : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT*CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_READ_MASK    : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT*CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_READ_ACTION  : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT*CONFIG_ACTION_WIDTH-1 downto 0);

        MAT_WRITE_ADDR   : out std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_WRITE_EN     : out std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT-1 downto 0);
        MAT_WRITE_RDY    : in  std_logic_vector(CONFIG_NUM_PORTS*NUM_MATS_PER_PORT-1 downto 0);
        MAT_WRITE_DATA   : out std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_MASK   : out std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_ACTION : out std_logic_vector(CONFIG_ACTION_WIDTH-1 downto 0);

        -- =========================================================================
        -- FLOW CONTROL INTERFACE
        -- =========================================================================
        -- Blocks traffic if not enabled (only functional in combination with MI_ENABLE_AXI generic).
        AXI_ENABLE       : out std_logic
    );
end entity;

architecture FULL of SWITCH_CONTROLLER is

    -- Function to get number of all match-action tables' configuration registers.
    function config_get_num_mat_cfg_regs (
        config_array : config_array_t;
        empty        : boolean
    ) return natural is
        variable num_regs : natural := 0;
    begin
        if (not empty) then
            for i in 0 to config_array'length-1 loop
                num_regs := num_regs + 2 + config_array(i).match_num_fields*3;
            end loop;
        end if;
        return num_regs;
    end function;

    -- Function to store the match-action tables' configuration in MI-addressable registers.
    function config_get_mat_cfg_regs (
        cfg   : config_array_t;
        empty : boolean;
        width : natural
    ) return slv_array_t is
        constant COUNT : natural := config_get_num_mat_cfg_regs(cfg, empty);
        variable regs  : slv_array_t(COUNT-1 downto 0)(MI_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
        variable idx   : natural := 0;
    begin
        if (not empty) then
            for i in 0 to cfg'length-1 loop
                regs(idx) := std_logic_vector(to_unsigned(cfg(i).match_num_fields, width)); idx := idx+1;
                regs(idx) := std_logic_vector(to_unsigned(cfg(i).match_items, width)); idx := idx+1;
                for j in 0 to cfg(i).match_num_fields-1 loop
                    regs(idx) := std_logic_vector(to_unsigned(cfg(i).match_protocols(j), width)); idx := idx+1;
                    regs(idx) := std_logic_vector(to_unsigned(cfg(i).match_range_highs(j), width)); idx := idx+1;
                    regs(idx) := std_logic_vector(to_unsigned(cfg(i).match_range_lows(j), width)); idx := idx+1;
                end loop;
            end loop;
        end if;
        return regs;
    end function;

    constant VERSION                   : natural := 1;

    -- ADDRESS SPACE
    --   META registers
    constant REG_IDX_NUM_META_REGS     : natural := 0;
    constant REG_IDX_NUM_DATA_REGS     : natural := 1;
    constant REG_IDX_VERSION           : natural := 2;
    constant REG_IDX_NUM_ACTIONS       : natural := 3;
    constant REG_IDX_NUM_PORTS         : natural := 4;
    constant REG_IDX_NUM_MATS_PER_PORT : natural := 5;
    constant NUM_META_INFO_REGS        : natural := 6;
    constant NUM_META_MAT_CFG_REGS     : natural := config_get_num_mat_cfg_regs(CONFIG, NUM_MATS_PER_PORT = 0);
    constant NUM_META_REGS             : natural := NUM_META_INFO_REGS + NUM_META_MAT_CFG_REGS;

    --   CONTROL & STATUS register (CSR)
    constant REG_IDX_CSR               : natural := NUM_META_REGS;
    --     CSR fields
    constant CSR_IDX_ACTIVATE          : natural := 0;
    constant CSR_IDX_CONFIGURE         : natural := 1;
    constant CSR_IDX_SOFT_RESET        : natural := 2;
    constant CSR_IDX_WRITE             : natural := 3;
    constant CSR_IDX_READ              : natural := 4;
    constant CSR_NUM_FIELDS            : natural := 5;
    --     CSR capabilities
    constant CSR_CAP_READ              : natural := 31;

    --   DATA IN registers
    constant NUM_DATA_REGS             : natural := div_roundup(CONFIG_MAX_DATA_WIDTH, MI_DATA_WIDTH);
    constant REG_IDX_ADDR              : natural := 0;
    constant REG_IDX_DATA_IN_0         : natural := 1;
    constant REG_IDX_MASK_IN_0         : natural := 1 + NUM_DATA_REGS;
    constant REG_IDX_ACTION_IN         : natural := 1 + NUM_DATA_REGS*2;
    constant NUM_DATA_IN_REGS          : natural := 2 + NUM_DATA_REGS*2;

    --   DATA OUT registers
    constant REG_IDX_DATA_OUT_0        : natural := 0;
    constant REG_IDX_MASK_OUT_0        : natural := 0 + NUM_DATA_REGS;
    constant REG_IDX_ACTION_OUT        : natural := 0 + NUM_DATA_REGS*2;
    constant NUM_DATA_OUT_REGS         : natural := 1 + NUM_DATA_REGS*2;

    constant NUM_REGS                  : natural := NUM_META_REGS + 1 + NUM_DATA_IN_REGS + NUM_DATA_OUT_REGS;

    constant META_MAT_CFG_REGS_ARR     : slv_array_t(NUM_META_MAT_CFG_REGS-1 downto 0)(MI_DATA_WIDTH-1 downto 0) := config_get_mat_cfg_regs(CONFIG, NUM_MATS_PER_PORT = 0, MI_DATA_WIDTH);
    constant META_INFO_REGS_ARR        : slv_array_t(NUM_META_INFO_REGS   -1 downto 0)(MI_DATA_WIDTH-1 downto 0) := (
        REG_IDX_NUM_META_REGS     => std_logic_vector(to_unsigned(NUM_META_REGS, MI_DATA_WIDTH)),
        REG_IDX_NUM_DATA_REGS     => std_logic_vector(to_unsigned(NUM_DATA_REGS, MI_DATA_WIDTH)),
        REG_IDX_VERSION           => std_logic_vector(to_unsigned(VERSION, MI_DATA_WIDTH)),
        REG_IDX_NUM_ACTIONS       => std_logic_vector(to_unsigned(CONFIG_NUM_ACTIONS, MI_DATA_WIDTH)),
        REG_IDX_NUM_PORTS         => std_logic_vector(to_unsigned(CONFIG_NUM_PORTS, MI_DATA_WIDTH)),
        REG_IDX_NUM_MATS_PER_PORT => std_logic_vector(to_unsigned(NUM_MATS_PER_PORT, MI_DATA_WIDTH))
    );

    signal s_csr_requests              : std_logic_vector(CSR_NUM_FIELDS-1 downto 0);
    signal s_cs_reg                    : std_logic_vector(MI_DATA_WIDTH-1 downto 0) := (
                                                                                        CSR_CAP_READ => tsel(MAT_READ_ENABLE, '1', '0'),
                                                                                        others       => '0'
                                                                                       );

    signal s_data_in_regs_arr           : slv_array_t(NUM_DATA_IN_REGS-1 downto 0)(MI_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    alias  s_addr_in_reg                : std_logic_vector                        (MI_DATA_WIDTH-1 downto 0) is s_data_in_regs_arr(REG_IDX_ADDR);
    alias  s_data_in_reg                : slv_array_t(NUM_DATA_REGS   -1 downto 0)(MI_DATA_WIDTH-1 downto 0) is s_data_in_regs_arr(REG_IDX_MASK_IN_0-1 downto REG_IDX_DATA_IN_0);
    alias  s_mask_in_reg                : slv_array_t(NUM_DATA_REGS   -1 downto 0)(MI_DATA_WIDTH-1 downto 0) is s_data_in_regs_arr(REG_IDX_ACTION_IN-1 downto REG_IDX_MASK_IN_0);
    alias  s_action_in_reg              : std_logic_vector                        (MI_DATA_WIDTH-1 downto 0) is s_data_in_regs_arr(NUM_DATA_IN_REGS -1);

    signal s_data_out_regs_arr          : slv_array_t(NUM_DATA_OUT_REGS-1 downto 0)(MI_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    alias  s_data_out_reg               : slv_array_t(NUM_DATA_REGS    -1 downto 0)(MI_DATA_WIDTH-1 downto 0) is s_data_out_regs_arr(REG_IDX_MASK_OUT_0-1 downto REG_IDX_DATA_OUT_0);
    alias  s_mask_out_reg               : slv_array_t(NUM_DATA_REGS    -1 downto 0)(MI_DATA_WIDTH-1 downto 0) is s_data_out_regs_arr(REG_IDX_ACTION_OUT-1 downto REG_IDX_MASK_OUT_0);
    alias  s_action_out_reg             : std_logic_vector                         (MI_DATA_WIDTH-1 downto 0) is s_data_out_regs_arr(NUM_DATA_OUT_REGS -1);

    constant NUM_MATS                     : natural := CONFIG_NUM_PORTS*NUM_MATS_PER_PORT;
    signal   s_mat_ops_busy               : slv_array_t(NUM_MATS-1 downto 0)(2-1 downto 0);
    signal   s_mat_read_rdy               : std_logic_vector(NUM_MATS-1 downto 0);
    signal   s_mat_read_in_progress       : std_logic := '0';
    signal   s_mat_en                     : std_logic_vector(NUM_MATS-1 downto 0);
    alias    s_mat_addr                   : std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0) is s_addr_in_reg(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
    alias    s_mat_sel                    : std_logic_vector(max(1,log2(NUM_MATS))-1 downto 0) is s_addr_in_reg(MI_DATA_WIDTH-1 downto MI_DATA_WIDTH-max(1,log2(NUM_MATS)));

    signal s_regs_rst                   : std_logic;
    signal s_regs_en                    : std_logic_vector(NUM_REGS-1 downto 0);
    alias  s_regs_addr                  : std_logic_vector(log2(NUM_REGS)-1 downto 0) is MI_ADDR(log2(NUM_REGS)+2-1 downto 2);

begin

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;

    mi_drd_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => MI_DATA_WIDTH,
        MUX_WIDTH  => NUM_REGS
    )
    port map (
        DATA_IN  => slv_array_ser(s_data_out_regs_arr) & slv_array_ser(s_data_in_regs_arr) & s_cs_reg & slv_array_ser(meta_mat_cfg_regs_arr) & slv_array_ser(meta_info_regs_arr),
        SEL      => s_regs_addr,
        DATA_OUT => MI_DRD
    );

    mi_addr_dec_i : entity work.DEC1FN_ENABLE
    generic map (
        ITEMS => NUM_REGS
    )
    port map (
        ADDR   => s_regs_addr,
        ENABLE => MI_WR,
        DO     => s_regs_en
    );

    s_csr_requests <= MI_DWR(CSR_NUM_FIELDS-1 downto 0) and (CSR_NUM_FIELDS-1 downto 0 => s_regs_en(REG_IDX_CSR));
    s_regs_rst     <= RESET or s_csr_requests(CSR_IDX_SOFT_RESET);
    csr_mode_flags_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_regs_rst or s_csr_requests(CSR_IDX_ACTIVATE)) then
                s_cs_reg(CSR_IDX_ACTIVATE)  <= '1';
                s_cs_reg(CSR_IDX_CONFIGURE) <= '0';
            elsif (s_csr_requests(CSR_IDX_CONFIGURE)) then
                s_cs_reg(CSR_IDX_ACTIVATE)  <= '0';
                s_cs_reg(CSR_IDX_CONFIGURE) <= '1';
            end if;
        end if;
    end process;
    csr_op_flags_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => 2,
        MUX_WIDTH  => NUM_MATS
    )
    port map (
        DATA_IN  => slv_array_ser(s_mat_ops_busy),
        SEL      => s_mat_sel,
        DATA_OUT => s_cs_reg(CSR_IDX_READ downto CSR_IDX_WRITE)
    );
    mi_enable_axi_g : if MI_ENABLE_AXI generate
        AXI_ENABLE <= s_cs_reg(CSR_IDX_ACTIVATE);
    else generate
        AXI_ENABLE <= '1';
    end generate;

    data_in_regs_g : for i in 0 to NUM_DATA_IN_REGS-1 generate
        constant REG_IDX_G : natural := NUM_META_REGS + 1 + i;
    begin
        data_in_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_regs_rst) then
                    s_data_in_regs_arr(i) <= (others => '0');
                elsif (s_regs_en(REG_IDX_G)) then
                    s_data_in_regs_arr(i) <= MI_DWR;
                end if;
            end if;
        end process;
    end generate;

    data_out_regs_g : if MAT_READ_ENABLE generate
        constant MAT_READ_VEC_WIDTH          : natural := CONFIG_MAX_DATA_WIDTH*2 + CONFIG_ACTION_WIDTH + 1;
        signal   s_mat_read_data_arr         : slv_array_t(NUM_MATS-1 downto 0)(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        signal   s_mat_read_mask_arr         : slv_array_t(NUM_MATS-1 downto 0)(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        signal   s_mat_read_action_arr       : slv_array_t(NUM_MATS-1 downto 0)(CONFIG_ACTION_WIDTH-1 downto 0);
        signal   s_mat_read_vec_arr          : slv_array_t(NUM_MATS-1 downto 0)(MAT_READ_VEC_WIDTH-1 downto 0);
        signal   s_mat_read_vec_mux          : std_logic_vector(MAT_READ_VEC_WIDTH-1 downto 0);
        signal   s_mat_read_vld_mux          : std_logic;
        signal   s_mat_read_data_mux         : std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        signal   s_mat_read_mask_mux         : std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        signal   s_mat_read_action_mux       : std_logic_vector(CONFIG_ACTION_WIDTH-1 downto 0);
    begin
        s_mat_read_data_arr   <= slv_array_deser(MAT_READ_DATA, NUM_MATS);
        s_mat_read_mask_arr   <= slv_array_deser(MAT_READ_MASK, NUM_MATS);
        s_mat_read_action_arr <= slv_array_deser(MAT_READ_ACTION, NUM_MATS);
        mat_read_vec_arr_g : for i in 0 to NUM_MATS-1 generate
            s_mat_read_vec_arr(i) <= MAT_READ_VLD(i) & s_mat_read_data_arr(i) & s_mat_read_mask_arr(i) & s_mat_read_action_arr(i);
        end generate;
        mat_read_vec_mux_i : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => MAT_READ_VEC_WIDTH,
            MUX_WIDTH  => NUM_MATS
        )
        port map (
            DATA_IN  => slv_array_ser(s_mat_read_vec_arr),
            SEL      => s_mat_sel,
            DATA_OUT => s_mat_read_vec_mux
        );
        (s_mat_read_vld_mux, s_mat_read_data_mux, s_mat_read_mask_mux, s_mat_read_action_mux) <= s_mat_read_vec_mux;

        data_out_regs_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_regs_rst) then
                    s_data_out_regs_arr <= (others => (others => '0'));
                elsif (s_mat_read_vld_mux) then
                    s_data_out_reg   <= slv_array_deser(resize(s_mat_read_data_mux, NUM_DATA_REGS*MI_DATA_WIDTH), NUM_DATA_REGS);
                    s_mask_out_reg   <= slv_array_deser(resize(s_mat_read_mask_mux, NUM_DATA_REGS*MI_DATA_WIDTH), NUM_DATA_REGS);
                    s_action_out_reg <= resize(s_mat_read_action_mux, MI_DATA_WIDTH);
                end if;
            end if;
        end process;

        mat_read_in_progress_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_regs_rst or s_mat_read_vld_mux) then
                    s_mat_read_in_progress <= '0';
                elsif (or MAT_READ_EN) then
                    s_mat_read_in_progress <= '1';
                end if;
            end if;
        end process;
    end generate;

    s_mat_read_rdy <= MAT_READ_RDY and (NUM_MATS-1 downto 0 => not s_mat_read_in_progress);
    mat_ops_rdy_g : for i in 0 to NUM_MATS-1 generate
        s_mat_ops_busy(i) <= not s_mat_read_rdy(i) & not MAT_WRITE_RDY(i);
    end generate;

    mat_en_dec_i : entity work.DEC1FN
    generic map (
        ITEMS => NUM_MATS
    )
    port map (
        ADDR => s_mat_sel,
        DO   => s_mat_en
    );

    MAT_READ_ADDR <= s_mat_addr;
    MAT_READ_EN   <= s_mat_en and (NUM_MATS-1 downto 0 => s_csr_requests(CSR_IDX_READ)) and s_mat_read_rdy;

    MAT_WRITE_ADDR   <= s_mat_addr;
    MAT_WRITE_EN     <= s_mat_en and (NUM_MATS-1 downto 0 => s_csr_requests(CSR_IDX_WRITE)) and MAT_WRITE_RDY;
    MAT_WRITE_DATA   <= slv_array_ser(s_data_in_reg)(CONFIG_MAX_DATA_WIDTH-1 downto 0);
    MAT_WRITE_MASK   <= slv_array_ser(s_mask_in_reg)(CONFIG_MAX_DATA_WIDTH-1 downto 0);
    MAT_WRITE_ACTION <= s_action_in_reg(CONFIG_ACTION_WIDTH-1 downto 0);

end architecture;
