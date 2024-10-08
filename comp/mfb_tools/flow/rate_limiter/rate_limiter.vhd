-- rate_limiter_full.vhd: Rate Limiter component
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RATE_LIMITER is
    generic(
        -- MI Data word width (in bits)
        MI_DATA_WIDTH   : natural := 32;
        -- MI Address word width (in bits)
        MI_ADDR_WIDTH   : natural := 32;
        -- Number of MFB regions (rx and tx)
        MFB_REGIONS     : natural := 1;
        -- MFB region size (in number of blocks)
        MFB_REGION_SIZE : natural := 8;
        -- MFB block size (in number of items)
        MFB_BLOCK_SIZE  : natural := 8;
        -- MFB item width (in bits)
        MFB_ITEM_WIDTH  : natural := 8;
        -- MFB metadata width (in bits)
        MFB_META_WIDTH  : natural := 0;
        -- Default section length (in number of clock cycles)
        -- Maximum: 2**MI_DATA_WIDTH
        SECTION_LENGTH  : natural := 1000;
        -- Default interval length (in number of sections)
        -- Maximum: 2**MI_DATA_WIDTH
        INTERVAL_LENGTH : natural := 40;
        -- Maximum number of intervals (different speed registers)
        INTERVAL_COUNT  : natural := 32;
        -- Default output speed (in bytes per section or packets per section)
        OUTPUT_SPEED    : natural := 62500;
        -- Operating frequency in MHz (used in SW for calculation of output speed)
        FREQUENCY       : natural := 200;
        -- Target device
        DEVICE          : string  := "AGILEX"
    );
    port(
        -- Clock and Reset
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- MI configuration interface
        MI_DWR         : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR        : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        MI_RD          : in  std_logic;
        MI_WR          : in  std_logic;
        MI_BE          : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        MI_DRD         : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ARDY        : out std_logic;
        MI_DRDY        : out std_logic;

        -- MFB input interface
        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- MFB output interface
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of RATE_LIMITER is

    constant MI_CONFIG_REGS          : integer := 5 + INTERVAL_COUNT;
    constant MI_REG_DATA_WIDTH       : integer := max(8, MI_DATA_WIDTH);
    constant MI_REG_ADDR_WIDTH       : integer := log2(MI_CONFIG_REGS);
    constant MI_REG_ADDR_OFFSET      : integer := log2(MI_REG_DATA_WIDTH/8);

    constant MI_STATUS_REG_POS       : integer := 0;
    constant MI_SEC_LEN_REG_POS      : integer := 1;
    constant MI_INT_LEN_REG_POS      : integer := 2;
    constant MI_FIRST_SPEED_REG_POS  : integer := 5;

    constant SR_IDLE_FLAG            : integer := 0;
    constant SR_CONF_FLAG            : integer := 1;
    constant SR_RUN_FLAG             : integer := 2;
    constant SR_WRITE_AUX_FLAGS_FLAG : integer := 3;
    constant SR_SPEED_PTR_RST_FLAG   : integer := 4;
    constant SR_SHAPING_TYPE_FLAG    : integer := 5;

    constant MI_STATUS_REG_INIT      : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := (SR_IDLE_FLAG => '1', others => '0');
    constant MI_SEC_LEN_REG_INIT     : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(SECTION_LENGTH, MI_REG_DATA_WIDTH));
    constant MI_INT_LEN_REG_INIT     : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(INTERVAL_LENGTH, MI_REG_DATA_WIDTH));
    constant MI_SPEED_REGS_COUNT     : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(INTERVAL_COUNT, MI_REG_DATA_WIDTH));
    constant MI_FREQ_REG             : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(FREQUENCY, MI_REG_DATA_WIDTH));
    constant MI_SPEED_REG_INIT       : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(OUTPUT_SPEED, MI_REG_DATA_WIDTH));

    signal mi_regs_addr              : std_logic_vector(MI_REG_ADDR_WIDTH-1 downto 0);
    signal mi_regs_en                : std_logic_vector(MI_CONFIG_REGS-1 downto 0);
    signal mi_regs_drd               : std_logic_vector(MI_CONFIG_REGS*MI_REG_DATA_WIDTH-1 downto 0);
    signal mi_regs_do                : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal mi_regs_dwr               : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);

    signal mi_status_reg             : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := MI_STATUS_REG_INIT;
    signal mi_status_reg_write_flag  : std_logic;

    signal mi_sec_len_reg            : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := MI_SEC_LEN_REG_INIT;
    signal mi_int_len_reg            : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0) := MI_INT_LEN_REG_INIT;
    signal mi_speed_regs             : slv_array_t(INTERVAL_COUNT-1 downto 0)(MI_REG_DATA_WIDTH-1 downto 0);
    signal mi_speed_regs_read        : slv_array_t(INTERVAL_COUNT-1 downto 0)(MI_REG_DATA_WIDTH-1 downto 0);
    signal mi_speed_regs_vld_reg     : std_logic_vector(INTERVAL_COUNT-1 downto 0) := (0 => '1', others => '0');
    signal mi_speed_regs_ptr         : std_logic_vector(max(1, log2(INTERVAL_COUNT))-1 downto 0);
    signal mi_speed_regs_vld_ptr     : std_logic_vector(max(1, log2(INTERVAL_COUNT))-1 downto 0);

    type mode is (IDLE, CONF, RUN);
    signal p_state                   : mode := IDLE;
    signal n_state                   : mode;
    signal write_ctrl_flag           : std_logic;
    signal write_aux_flag            : std_logic;
    signal start_conf_flag           : std_logic;
    signal stop_conf_flag            : std_logic;
    signal start_run_flag            : std_logic;
    signal stop_run_flag             : std_logic;
    signal reset_ptr_flag            : std_logic;
    signal limit_byte_flag           : std_logic;
    signal limit_pkts_flag           : std_logic;

    -- ------------------------------------------------------------------------
    -- MFB PACKET PROCESSING
    -- ------------------------------------------------------------------------

    constant MFB_SPEED_METER_BYTES_LATENCY : integer := 3;
    constant MFB_SPEED_METER_PKTS_LATENCY  : integer := 1;
    constant LATENCY_RESERVE_BYTES         : integer := MFB_SPEED_METER_BYTES_LATENCY*RX_MFB_DATA'length/8;
    constant LATENCY_RESERVE_PKTS          : integer := MFB_SPEED_METER_PKTS_LATENCY*MFB_REGIONS;

    signal start_shaping             : std_logic;
    signal next_speed_req            : std_logic;
    signal next_speed_vld            : std_logic;
    signal next_speed_vld_vec        : std_logic_vector(1-1 downto 0);
    signal sec_len_cnt               : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal int_len_cnt               : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal end_of_sec                : std_logic;
    signal new_section               : std_logic;
    signal end_of_int                : std_logic;

    signal active_speed              : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal bytes_in_sec              : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal eofs_in_sec               : std_logic_vector(MI_REG_DATA_WIDTH-1 downto 0);
    signal last_eof                  : std_logic;
    signal any_eof                   : std_logic;
    signal bytes_over                : std_logic;
    signal packets_over              : std_logic;
    signal limit_bytes               : std_logic;
    signal limit_reached             : std_logic;
    signal rx_mfb_src_rdy_masked     : std_logic;
    signal mfb_rx_src_rdy_shaped     : std_logic;
    signal mfb_tx_dst_rdy_shaped     : std_logic;

    signal rx_mfb_eof_last           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof_rest           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof_rest_reg       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof_masked         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_last           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_rest           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_rest_reg       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_mask           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_masked         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_before_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_mask_auto      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_pos_deser      : slv_array_t(MFB_REGIONS-1 downto 0)(max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal rx_mfb_eof_pos_deser      : slv_array_t(MFB_REGIONS-1 downto 0)(max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal send_last_eof             : std_logic;
    signal send_last_eof_reg         : std_logic;
    signal send_rest                 : std_logic;
begin

    -- ------------------------------------------------------------------------
    -- CONFIGURATION
    -- ------------------------------------------------------------------------

    -- register address decoding
    mi_regs_addr <= MI_ADDR(MI_REG_ADDR_OFFSET+MI_REG_ADDR_WIDTH-1 downto MI_REG_ADDR_OFFSET);
    mi_regs_addr_dec_p: process (mi_regs_addr)
    begin
        mi_regs_en <= (others => '0');
        mi_regs_en(to_integer(unsigned(mi_regs_addr))) <= '1';
    end process;

    -- MI_ARDY and MI_DRDY logic
    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;

    -- speed regs read value (MSB replaced with valid flag)
    mi_speed_regs_read_g: for i in 0 to INTERVAL_COUNT-1 generate
        mi_speed_regs_read(i) <= mi_speed_regs_vld_reg(i) & mi_speed_regs(i)(MI_DATA_WIDTH-2 downto 0);
    end generate;

    -- MI_DRD mux
    mi_regs_drd <= slv_array_ser(mi_speed_regs_read) & MI_FREQ_REG &  MI_SPEED_REGS_COUNT & mi_int_len_reg & mi_sec_len_reg & mi_status_reg;
    mi_regs_drd_mux_i: entity work.GEN_MUX
    generic map (
        DATA_WIDTH => MI_REG_DATA_WIDTH,
        MUX_WIDTH  => MI_CONFIG_REGS
    )
    port map (
        DATA_IN  => mi_regs_drd,
        SEL      => mi_regs_addr,
        DATA_OUT => mi_regs_do
    );
    MI_DRD <= mi_regs_do;

    -- byte enable logic
    mi_regs_dwr_g: for i in 0 to MI_REG_DATA_WIDTH/8-1 generate
        mi_regs_dwr((i+1)*8-1 downto i*8) <= MI_DWR((i+1)*8-1 downto i*8) when MI_BE(i) = '1' else
                                             mi_regs_do((i+1)*8-1 downto i*8);
    end generate;

    -- mode register
    fsm_mode_reg_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                p_state <= IDLE;
            else
                p_state <= n_state;
            end if;
        end if;
    end process;

    -- mode n_state and output signals logic
    fsm_mode_n_state_logic_p: process (p_state, start_conf_flag, start_run_flag, stop_conf_flag, stop_run_flag)
    begin
        n_state <= p_state;
        start_shaping <= '0';
        case p_state is
            when IDLE =>
                if (start_conf_flag = '1') then
                    n_state <= CONF;
                elsif (start_run_flag = '1') then
                    n_state <= RUN;
                    start_shaping <= '1';
                end if;
            when CONF =>
                if (stop_conf_flag = '1') then
                    if (start_run_flag = '1') then
                        n_state <= RUN;
                        start_shaping <= '1';
                    else
                        n_state <= IDLE;
                    end if;
                end if;
            when RUN =>
                if (start_conf_flag = '1') then
                    n_state <= CONF;
                elsif (stop_run_flag = '1') then
                    n_state <= IDLE;
                end if;
            when others =>
                null;
        end case;
    end process;

    -- differentiate between state control flags and auxiliary flags
    write_ctrl_flag <= mi_status_reg_write_flag and not MI_DWR(SR_WRITE_AUX_FLAGS_FLAG);
    write_aux_flag  <= mi_status_reg_write_flag and     MI_DWR(SR_WRITE_AUX_FLAGS_FLAG);
    -- state control flags
    start_conf_flag <= write_ctrl_flag          and     MI_DWR(SR_CONF_FLAG);
    stop_conf_flag  <= write_ctrl_flag          and not MI_DWR(SR_CONF_FLAG);
    start_run_flag  <= write_ctrl_flag          and     MI_DWR(SR_RUN_FLAG);
    stop_run_flag   <= write_ctrl_flag          and not MI_DWR(SR_RUN_FLAG);
    -- auxiliary flags
    reset_ptr_flag  <= write_aux_flag           and     MI_DWR(SR_SPEED_PTR_RST_FLAG);
    limit_byte_flag <= write_aux_flag           and not MI_DWR(SR_SHAPING_TYPE_FLAG);
    limit_pkts_flag <= write_aux_flag           and     MI_DWR(SR_SHAPING_TYPE_FLAG);

    -- status register
    mi_status_reg_write_flag <= mi_regs_en(MI_STATUS_REG_POS) and MI_WR and MI_BE(0);
    mi_status_reg_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                mi_status_reg <= MI_STATUS_REG_INIT;
            else
                -- indicate current state of the component
                if (n_state = CONF) then
                    mi_status_reg(SR_IDLE_FLAG) <= '0';
                    mi_status_reg(SR_CONF_FLAG) <= '1';
                    mi_status_reg(SR_RUN_FLAG)  <= '0';
                elsif (n_state = RUN) then
                    mi_status_reg(SR_IDLE_FLAG) <= '0';
                    mi_status_reg(SR_CONF_FLAG) <= '0';
                    mi_status_reg(SR_RUN_FLAG)  <= '1';
                else
                    mi_status_reg(SR_IDLE_FLAG) <= '1';
                    mi_status_reg(SR_CONF_FLAG) <= '0';
                    mi_status_reg(SR_RUN_FLAG)  <= '0';
                end if;

                -- indicate traffic limiting choice
                if (limit_byte_flag = '1') then
                    mi_status_reg(SR_SHAPING_TYPE_FLAG) <= '0';
                elsif (limit_pkts_flag = '1') then
                    mi_status_reg(SR_SHAPING_TYPE_FLAG) <= '1';
                end if;
            end if;
        end if;
    end process;

    -- section length register
    mi_sec_len_reg_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') or (p_state = IDLE) then
                mi_sec_len_reg <= MI_SEC_LEN_REG_INIT;
            elsif (p_state = CONF and mi_regs_en(MI_SEC_LEN_REG_POS) = '1' and MI_WR = '1') then
                mi_sec_len_reg <= mi_regs_dwr;
            end if;
        end if;
    end process;

    -- interval length register
    mi_int_len_reg_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') or (p_state = IDLE) then
                mi_int_len_reg <= MI_INT_LEN_REG_INIT;
            elsif (p_state = CONF and mi_regs_en(MI_INT_LEN_REG_POS) = '1' and MI_WR = '1') then
                mi_int_len_reg <= mi_regs_dwr;
            end if;
        end if;
    end process;

    -- speed registers
    mi_speed_reg_first_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') or (start_conf_flag = '1') or (p_state = IDLE) then
                mi_speed_regs(0)         <= MI_SPEED_REG_INIT;
                mi_speed_regs_vld_reg(0) <= '1'; -- The first Speed register is always valid
            elsif (p_state = CONF) and (mi_regs_en(MI_FIRST_SPEED_REG_POS) = '1') and (MI_WR = '1') then
                mi_speed_regs(0)         <= mi_regs_dwr;
            end if;
        end if;
    end process;

    mi_speed_regs_g: for i in 1 to INTERVAL_COUNT-1 generate
        mi_speed_regs_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') or (start_conf_flag = '1') or (p_state = IDLE) then
                    mi_speed_regs(i)         <= (others => '0');
                    mi_speed_regs_vld_reg(i) <= '0';
                elsif (p_state = CONF and mi_regs_en(MI_CONFIG_REGS-INTERVAL_COUNT+i) = '1' and MI_WR = '1') then
                    mi_speed_regs(i)         <= mi_regs_dwr;
                    mi_speed_regs_vld_reg(i) <= '1';
                end if;
            end if;
        end process;
    end generate;

    -- speed registers pointer
    mi_speed_regs_ptr_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                mi_speed_regs_ptr <= (others => '0');
            elsif (p_state = CONF or (p_state = IDLE and reset_ptr_flag = '1') or (next_speed_req = '1' and next_speed_vld = '0')) then
                mi_speed_regs_ptr <= (others => '0');
            elsif (next_speed_req = '1' and next_speed_vld = '1') then
                mi_speed_regs_ptr <= mi_speed_regs_vld_ptr;
            end if;
        end if;
    end process;

    mi_speed_regs_vld_ptr <= std_logic_vector(unsigned(mi_speed_regs_ptr) + 1);

    mi_speed_regs_vld_mux_i: entity work.GEN_MUX
    generic map (
        DATA_WIDTH => 1,
        MUX_WIDTH  => INTERVAL_COUNT
    )
    port map (
        DATA_IN  => mi_speed_regs_vld_reg,
        SEL      => mi_speed_regs_vld_ptr,
        DATA_OUT => next_speed_vld_vec
    );

    next_speed_vld <= next_speed_vld_vec(0);

    mi_speed_regs_mux_i: entity work.GEN_MUX
    generic map (
        DATA_WIDTH => MI_REG_DATA_WIDTH,
        MUX_WIDTH  => INTERVAL_COUNT
    )
    port map (
        DATA_IN  => slv_array_ser(mi_speed_regs),
        SEL      => mi_speed_regs_ptr,
        DATA_OUT => active_speed
    );

    -- ------------------------------------------------------------------------
    -- MFB PACKET PROCESSING
    -- ------------------------------------------------------------------------

    end_of_sec     <= '1' when sec_len_cnt = std_logic_vector(unsigned(mi_sec_len_reg) - 1) else '0';
    end_of_int     <= '1' when int_len_cnt = std_logic_vector(unsigned(mi_int_len_reg) - 1) else '0';
    next_speed_req <= end_of_int and end_of_sec;

    -- section length counter
    sec_len_cnt_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                sec_len_cnt <= (others => '0');
            elsif (start_shaping = '1' or end_of_sec = '1') then
                sec_len_cnt <= (others => '0');
            elsif (p_state = RUN) then
                sec_len_cnt <= std_logic_vector(unsigned(sec_len_cnt) + 1);
            end if;
        end if;
    end process;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                new_section <= '0';
            else
                new_section <= end_of_sec;
            end if;
        end if;
    end process;

    -- interval length counter
    int_len_cnt_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                int_len_cnt <= (others => '0');
            elsif (start_shaping = '1' or next_speed_req = '1') then
                int_len_cnt <= (others => '0');
            elsif (p_state = RUN and end_of_sec = '1') then
                int_len_cnt <= std_logic_vector(unsigned(int_len_cnt) + 1);
            end if;
        end if;
    end process;

    -- speed_meter component
    -- bytes_in_sec latency = 3 clock cycles
    -- eofs_in_sec  latency = 1 clock cycle
    speed_meter_i: entity work.MFB_SPEED_METER
    generic map (
        REGIONS         => MFB_REGIONS,
        REGION_SIZE     => MFB_REGION_SIZE,
        BLOCK_SIZE      => MFB_BLOCK_SIZE,
        ITEM_WIDTH      => MFB_ITEM_WIDTH,
        DISABLE_ON_CLR  => false,
        COUNT_PACKETS   => true,
        ADD_ARR_PKTS    => true
    )
    port map (
        CLK           => CLK,
        RST           => RESET,

        RX_SOF_POS    => RX_MFB_SOF_POS,
        RX_EOF_POS    => RX_MFB_EOF_POS,
        RX_SOF        => rx_mfb_sof_masked,
        RX_EOF        => rx_mfb_eof_masked,
        RX_SRC_RDY    => mfb_rx_src_rdy_shaped,
        RX_DST_RDY    => mfb_tx_dst_rdy_shaped,

        CNT_TICKS     => open,
        CNT_TICKS_MAX => open,
        CNT_BYTES     => bytes_in_sec,
        CNT_PKT_SOFS  => open,
        CNT_PKT_EOFS  => eofs_in_sec,
        CNT_CLEAR     => end_of_sec
    );

    -- compare requested and actual speed (in packets per section)
    last_eof     <= '1' when unsigned(active_speed) <= unsigned(eofs_in_sec) + LATENCY_RESERVE_PKTS else '0';
    any_eof      <= (or RX_MFB_EOF) and RX_MFB_SRC_RDY;
    packets_over <= last_eof and any_eof;

    -- first eof present is the last eof sent
    rx_mfb_eof_first_one_i: entity work.FIRST_ONE
    generic map (
        DATA_WIDTH => MFB_REGIONS
    )
    port map (
        DI => RX_MFB_EOF,
        DO => rx_mfb_eof_last
    );

    -- sof and eof masking
    rx_mfb_sof_pos_deser <= slv_array_deser(RX_MFB_SOF_POS, MFB_REGIONS);
    rx_mfb_eof_pos_deser <= slv_array_deser(RX_MFB_EOF_POS, MFB_REGIONS);

    rx_mfb_eof_rest   <= RX_MFB_SRC_RDY and RX_MFB_EOF and not rx_mfb_eof_last;
    rx_mfb_eof_masked <= rx_mfb_eof_rest_reg when send_rest = '1' else RX_MFB_EOF;

    send_rest <= new_section and send_last_eof_reg;

    rx_mfb_sof_mask_g: for i in 0 to MFB_REGIONS-1 generate
        rx_mfb_sof_before_eof(i) <= '1' when unsigned(rx_mfb_eof_pos_deser(i)) >= enlarge_right(unsigned(rx_mfb_sof_pos_deser(i)), log2(MFB_BLOCK_SIZE)) else '0';
        rx_mfb_sof_mask_auto(i)  <= '1' when shift_right(unsigned(rx_mfb_eof_last), i) > 1 else '0';
        rx_mfb_sof_mask(i)       <= rx_mfb_sof_before_eof(i) when rx_mfb_eof_last(i) = '1' else rx_mfb_sof_mask_auto(i);
    end generate;

    rx_mfb_sof_last   <= RX_MFB_SOF and rx_mfb_sof_mask;
    rx_mfb_sof_rest   <= RX_MFB_SRC_RDY and RX_MFB_SOF and not rx_mfb_sof_mask;
    rx_mfb_sof_masked <= rx_mfb_sof_rest_reg when send_rest = '1' else RX_MFB_SOF;

    rx_mfb_rest_regs_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (send_last_eof = '1') then
                rx_mfb_eof_rest_reg <= rx_mfb_eof_rest;
                rx_mfb_sof_rest_reg <= rx_mfb_sof_rest;
            end if;
        end if;
    end process;

    -- control logic for sending masked eof
    send_last_eof <= not limit_bytes and packets_over and TX_MFB_DST_RDY and not send_last_eof_reg;
    send_last_eof_reg_p: process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or send_rest = '1') then -- or p_state /= RUN  ??
                send_last_eof_reg <= '0';
            elsif (send_last_eof = '1') then
                send_last_eof_reg <= '1';
            end if;
        end if;
    end process;

    -- compare requested and actual speed (in bytes per section)
    bytes_over <= '1' when unsigned(active_speed) <= unsigned(bytes_in_sec) + LATENCY_RESERVE_BYTES else '0';

    -- choose between byte limiting and packet limiting
    limit_bytes   <= not mi_status_reg(SR_SHAPING_TYPE_FLAG);
    limit_reached <= bytes_over when limit_bytes = '1' else packets_over;

    -- RX dest and TX src logic
    rx_mfb_src_rdy_masked <= RX_MFB_SRC_RDY when send_rest = '0' else (or rx_mfb_sof_rest_reg) or (or rx_mfb_eof_rest_reg);
    mfb_rx_src_rdy_shaped <= rx_mfb_src_rdy_masked when p_state = RUN and (limit_reached = '0' or send_last_eof = '1') else '0';
    mfb_tx_dst_rdy_shaped <= TX_MFB_DST_RDY when p_state = RUN and limit_reached = '0' else '0';

    TX_MFB_DATA    <= RX_MFB_DATA;
    TX_MFB_META    <= RX_MFB_META;
    TX_MFB_SOF     <= rx_mfb_sof_masked when send_last_eof = '0' else rx_mfb_sof_last;
    TX_MFB_EOF     <= rx_mfb_eof_masked when send_last_eof = '0' else rx_mfb_eof_last;
    TX_MFB_SOF_POS <= RX_MFB_SOF_POS;
    TX_MFB_EOF_POS <= RX_MFB_EOF_POS;
    TX_MFB_SRC_RDY <= RX_MFB_SRC_RDY when p_state = IDLE else mfb_rx_src_rdy_shaped;
    RX_MFB_DST_RDY <= TX_MFB_DST_RDY when p_state = IDLE else mfb_tx_dst_rdy_shaped;

end architecture;
