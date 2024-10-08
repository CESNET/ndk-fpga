-- ctrl_unit.vhd: Control unit
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_CTRL_UNIT is
    generic(
        LEN_WIDTH          : natural := 14;
        INBANDFCS          : boolean := true;
        MAC_COUNT          : natural := 16;
        SM_CNT_TICKS_WIDTH : natural := 24;
        SM_CNT_BYTES_WIDTH : natural := 32;
        DEVICE             : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK                    : in  std_logic;
        RESET                  : in  std_logic;
        -- =====================================================================
        -- MI32 INTERFACE
        -- =====================================================================
        MI_CLK                 : in  std_logic;
        MI_RESET               : in  std_logic;
        MI_DWR                 : in  std_logic_vector(32-1 downto 0);
        MI_ADDR                : in  std_logic_vector(32-1 downto 0);
        MI_RD                  : in  std_logic;
        MI_WR                  : in  std_logic;
        MI_BE                  : in  std_logic_vector(4-1 downto 0);
        MI_DRD                 : out std_logic_vector(32-1 downto 0);
        MI_ARDY                : out std_logic;
        MI_DRDY                : out std_logic;
        -- =====================================================================
        -- OTHERS CONTROL INPUT INTERFACE
        -- =====================================================================
        LINK_STATUS            : in  std_logic; -- link status from adapter
        BUFFER_STATUS          : in  std_logic_vector(2-1 downto 0);
        -- =====================================================================
        -- SPEED METER INTERFACE
        -- =====================================================================

        -- counter of clock ticks
        SM_CNT_TICKS           : in  std_logic_vector(SM_CNT_TICKS_WIDTH-1 downto 0);
        -- maximum value flag of clock ticks counter, when CNT_TICKS_MAX=1 speed test is done
        SM_CNT_TICKS_MAX       : in  std_logic;
        -- counter of valid bytes
        SM_CNT_BYTES           : in  std_logic_vector(SM_CNT_BYTES_WIDTH-1 downto 0);
        -- counter of valid packets
        SM_CNT_PACKETS         : in  std_logic_vector(SM_CNT_BYTES_WIDTH-1 downto 0);
        -- reset all speed meter counters
        SM_CNT_CLEAR           : out std_logic;
        -- =====================================================================
        -- OUTPUT CAM WRITE INTERFACE
        -- =====================================================================
        CAM_WRITE_DATA         : out std_logic_vector(49-1 downto 0);
        CAM_WRITE_ADDR         : out std_logic_vector(log2(MAC_COUNT)-1 downto 0);
        CAM_WRITE_EN           : out std_logic;
        CAM_WRITE_RDY          : in  std_logic;
        -- =====================================================================
        -- OUTPUT CONTROL INTERFACE
        -- =====================================================================
        -- SW reset command.
        CTL_SW_RESET           : out std_logic;
        -- Take snapshot of counter
        CTL_TAKE_SNAPSHOT      : out std_logic;
        -- Read and release snapshot of counters
        CTL_READ_SNAPSHOT      : out std_logic;
        -- Enable of RX MAC LITE
        CTL_ENABLE             : out std_logic;
        -- Mask of error bits
        CTL_ERROR_MASK         : out std_logic_vector(5-1 downto 0);
        -- Maximum lenght of frame. Allowed values are 128 and more.
        CTL_FRAME_LEN_MAX      : out std_logic_vector(LEN_WIDTH-1 downto 0);
        -- Minimum lenght of frame. Is constant.
        CTL_FRAME_LEN_MIN      : out std_logic_vector(LEN_WIDTH-1 downto 0);
        -- Mode of MAC checking.
        CTL_MAC_CHECK_MODE     : out std_logic_vector(2-1 downto 0);
        -- =====================================================================
        -- INPUT OF STATISTICS
        -- =====================================================================
        -- Total number of received frames
        STAT_FRAMES_RECEIVED    : in  std_logic_vector(63 downto 0);
        -- Total number of transmitted frames
        STAT_FRAMES_TRANSMITTED : in  std_logic_vector(63 downto 0);
        -- Total number of discarded frames
        STAT_FRAMES_DISCARDED   : in  std_logic_vector(63 downto 0);
        -- Discarded frames due to buffer overflow
        STAT_BUFFER_OVF         : in  std_logic_vector(63 downto 0);
        -- Total number of received bytes (include CRC bytes)
        STAT_RX_BYTES           : in  std_logic_vector(63 downto 0);
        -- Total number of transmitted
        STAT_TX_BYTES           : in  std_logic_vector(63 downto 0);
        -- Total number of frames with bad CRC
        STAT_CRC_ERR            : in  std_logic_vector(63 downto 0);
        -- Total number of frames over MTU
        STAT_OVER_MTU           : in  std_logic_vector(63 downto 0);
        -- Total number of frames below minimal length
        STAT_BELOW_MIN          : in  std_logic_vector(63 downto 0);
        -- Total amount of received broadcast frames
        STAT_BCAST_FRAMES       : in  std_logic_vector(63 downto 0);
        -- Total amount of received multicast frames
        STAT_MCAST_FRAMES       : in  std_logic_vector(63 downto 0);
        -- Total amount of received "fragment" frames
        STAT_FRAGMENT_FRAMES    : in  std_logic_vector(63 downto 0);
        -- Total amount of received "jabber" frames (frames above 1518 bytes including FCS)
        STAT_JABBER_FRAMES      : in  std_logic_vector(63 downto 0);
        -- Frame length histograms
        STAT_FRAMES_UNDERSIZE   : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_64          : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_65_127      : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_128_255     : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_256_511     : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_512_1023    : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_1024_1518   : in  std_logic_vector(63 downto 0);
        STAT_FRAMES_OVER_1518   : in  std_logic_vector(63 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_CTRL_UNIT is

    constant ADAPTER_SPEED           : std_logic_vector(2 downto 0) := "101";

    -- =====================================================================
    -- base addresses
    -- =====================================================================

    constant TRFC_L_ADDR             : std_logic_vector(7 downto 2) := "000000"; -- 0x00
    constant CFC_L_ADDR              : std_logic_vector(7 downto 2) := "000001"; -- 0x04
    constant DFC_L_ADDR              : std_logic_vector(7 downto 2) := "000010"; -- 0x08
    constant BODFC_L_ADDR            : std_logic_vector(7 downto 2) := "000011"; -- 0x0C
    constant TRFC_H_ADDR             : std_logic_vector(7 downto 2) := "000100"; -- 0x10
    constant CFC_H_ADDR              : std_logic_vector(7 downto 2) := "000101"; -- 0x14
    constant DFC_H_ADDR              : std_logic_vector(7 downto 2) := "000110"; -- 0x18
    constant BODFC_H_ADDR            : std_logic_vector(7 downto 2) := "000111"; -- 0x1C
    constant IBUF_EN_ADDR            : std_logic_vector(7 downto 2) := "001000"; -- 0x20
    constant ERROR_MASK_ADDR         : std_logic_vector(7 downto 2) := "001001"; -- 0x24
    constant STATUS_ADDR             : std_logic_vector(7 downto 2) := "001010"; -- 0x28
    constant COMMAND_ADDR            : std_logic_vector(7 downto 2) := "001011"; -- 0x2C
    constant MIN_FRAME_LEN_ADDR      : std_logic_vector(7 downto 2) := "001100"; -- 0x30
    constant MAX_FRAME_LEN_ADDR      : std_logic_vector(7 downto 2) := "001101"; -- 0x34
    constant MAC_CHECK_MODE_ADDR     : std_logic_vector(7 downto 2) := "001110"; -- 0x38
    constant OROC_L_ADDR             : std_logic_vector(7 downto 2) := "001111"; -- 0x3C
    constant OROC_H_ADDR             : std_logic_vector(7 downto 2) := "010000"; -- 0x40
    constant SM_CNT_TICKS_ADDR       : std_logic_vector(7 downto 2) := "010001"; -- 0x44
    constant SM_CNT_BYTES_ADDR       : std_logic_vector(7 downto 2) := "010010"; -- 0x48
    constant SM_CNT_PACKETS_ADDR     : std_logic_vector(7 downto 2) := "010011"; -- 0x4C
    constant CAM_BASE_ADDR           : std_logic_vector(7 downto 2) := "100000"; -- 0x80

    -- =====================================================================
    -- RFC2819 counter addresses
    -- =====================================================================

    constant CRC_ERR_L_ADDR          : std_logic_vector(7 downto 2) := "000000";
    constant OVER_MTU_L_ADDR         : std_logic_vector(7 downto 2) := "000001";
    constant BELOW_MIN_L_ADDR        : std_logic_vector(7 downto 2) := "000010";
    constant BCAST_FRAMES_L_ADDR     : std_logic_vector(7 downto 2) := "000011";
    constant MCAST_FRAMES_L_ADDR     : std_logic_vector(7 downto 2) := "000100";
    constant FRAGMENT_FRAMES_L_ADDR  : std_logic_vector(7 downto 2) := "000101";
    constant JABBER_FRAMES_L_ADDR    : std_logic_vector(7 downto 2) := "000110";
    constant TRANS_OCTETS_L_ADDR     : std_logic_vector(7 downto 2) := "000111";
    constant FRAMES_64_L_ADDR        : std_logic_vector(7 downto 2) := "001000";
    constant FRAMES_65_127_L_ADDR    : std_logic_vector(7 downto 2) := "001001";
    constant FRAMES_128_255_L_ADDR   : std_logic_vector(7 downto 2) := "001010";
    constant FRAMES_256_511_L_ADDR   : std_logic_vector(7 downto 2) := "001011";
    constant FRAMES_512_1023_L_ADDR  : std_logic_vector(7 downto 2) := "001100";
    constant FRAMES_1024_1518_L_ADDR : std_logic_vector(7 downto 2) := "001101";
    constant FRAMES_OVER_1518_L_ADDR : std_logic_vector(7 downto 2) := "011100";
    constant FRAMES_UNDERSIZE_L_ADDR : std_logic_vector(7 downto 2) := "011110";

    constant CRC_ERR_H_ADDR          : std_logic_vector(7 downto 2) := "001110";
    constant OVER_MTU_H_ADDR         : std_logic_vector(7 downto 2) := "001111";
    constant BELOW_MIN_H_ADDR        : std_logic_vector(7 downto 2) := "010000";
    constant BCAST_FRAMES_H_ADDR     : std_logic_vector(7 downto 2) := "010001";
    constant MCAST_FRAMES_H_ADDR     : std_logic_vector(7 downto 2) := "010010";
    constant FRAGMENT_FRAMES_H_ADDR  : std_logic_vector(7 downto 2) := "010011";
    constant JABBER_FRAMES_H_ADDR    : std_logic_vector(7 downto 2) := "010100";
    constant TRANS_OCTETS_H_ADDR     : std_logic_vector(7 downto 2) := "010101";
    constant FRAMES_64_H_ADDR        : std_logic_vector(7 downto 2) := "010110";
    constant FRAMES_65_127_H_ADDR    : std_logic_vector(7 downto 2) := "010111";
    constant FRAMES_128_255_H_ADDR   : std_logic_vector(7 downto 2) := "011000";
    constant FRAMES_256_511_H_ADDR   : std_logic_vector(7 downto 2) := "011001";
    constant FRAMES_512_1023_H_ADDR  : std_logic_vector(7 downto 2) := "011010";
    constant FRAMES_1024_1518_H_ADDR : std_logic_vector(7 downto 2) := "011011";
    constant FRAMES_OVER_1518_H_ADDR : std_logic_vector(7 downto 2) := "011101";
    constant FRAMES_UNDERSIZE_H_ADDR : std_logic_vector(7 downto 2) := "011111";

    -- =====================================================================
    -- Command constants
    -- =====================================================================

    constant CMD_SAMPLE              : std_logic_vector(2 downto 0) := "001"; -- 0x01
    constant CMD_RESET               : std_logic_vector(2 downto 0) := "010"; -- 0x02
    constant CMD_SW_BASE_REG         : std_logic_vector(2 downto 0) := "011"; -- 0x03
    constant CMD_SM_CNT_CLEAR        : std_logic_vector(2 downto 0) := "100"; -- 0x04

    -- MI32 slave interface signals
    signal s_mi_dwr                      : std_logic_vector(31 downto 0);
    signal s_mi_addr                     : std_logic_vector(31 downto 0);
    signal s_mi_rd                       : std_logic;
    signal s_mi_rd_reg                   : std_logic;
    signal s_mi_wr                       : std_logic;
    signal s_mi_be                       : std_logic_vector(3 downto 0);
    signal s_mi_drd                      : std_logic_vector(31 downto 0);
    signal s_mi_drd0                     : std_logic_vector(31 downto 0);
    signal s_mi_drd1                     : std_logic_vector(31 downto 0);
    signal s_mi_ardy                     : std_logic;
    signal s_mi_drdy                     : std_logic;

    signal s_mi_sync_dwr                 : std_logic_vector(31 downto 0);
    signal s_mi_sync_addr                : std_logic_vector(31 downto 0);
    signal s_mi_sync_rd                  : std_logic;
    signal s_mi_sync_wr                  : std_logic;
    signal s_mi_sync_be                  : std_logic_vector(3 downto 0);
    signal s_mi_sync_drd                 : std_logic_vector(31 downto 0);
    signal s_mi_sync_ardy                : std_logic;
    signal s_mi_sync_drdy                : std_logic;

    -- CAM writing logic
    signal s_reg_data_wr_l               : std_logic_vector(31 downto 0);
    signal s_reg_data_wr_l_we            : std_logic;
    signal s_reg_data_wr_h               : std_logic_vector(16 downto 0);
    signal s_reg_data_wr_h_we            : std_logic;
    signal s_reg_cam_addr                : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
    signal s_reg_cam_we                  : std_logic;
    signal s_cam_rdy                     : std_logic;

    -- Internal registers
    signal s_reg_enable                  : std_logic;
    signal s_reg_error_mask              : std_logic_vector(4 downto 0);
    signal s_inbandfcs                   : std_logic;
    signal s_mac_count                   : std_logic_vector(4 downto 0);
    signal s_reg_status                  : std_logic_vector(28 downto 0);
    signal s_reg_min_frame_len           : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_reg_max_frame_len           : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_reg_min_frame_len_fix       : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_reg_max_frame_len_fix       : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_reg_mac_check_mode          : std_logic_vector(1 downto 0);
    signal s_sm_cnt_ticks_reg            : std_logic_vector(31 downto 0);
    signal s_sm_cnt_bytes_reg            : std_logic_vector(31 downto 0);
    signal s_sm_cnt_packets_reg          : std_logic_vector(31 downto 0);

    -- Command decoder
    signal s_cmd_sample_sel              : std_logic;
    signal s_cmd_sw_reset_sel            : std_logic;
    signal s_cmd_switch_rfc_sel          : std_logic;
    signal s_cmd_sm_cnt_clear_sel        : std_logic;
    signal s_cmd_switch_rfc              : std_logic;
    signal s_cmd_switch_rfc_reg          : std_logic;
    signal s_cmd_read_snapshot           : std_logic;
    signal s_cmd_read_snapshot_reg       : std_logic;
    signal s_cmd_take_snapshot           : std_logic;
    signal s_cmd_sw_reset                : std_logic;
    signal s_cmd_sm_cnt_clear            : std_logic;

    -- CS signals
    signal s_ibuf_en_cs                  : std_logic;
    signal s_error_mask_cs               : std_logic;
    signal s_status_cs                   : std_logic;
    signal s_cmd_cs                      : std_logic;
    signal s_min_frame_len_cs            : std_logic;
    signal s_max_frame_len_cs            : std_logic;
    signal s_mac_check_mode_cs           : std_logic;
    signal s_cam_cs                      : std_logic;
    signal s_stats_rfc2819_cs            : std_logic;
    signal s_stats_rfc2819_cs_reg        : std_logic;

    -- WE signals
    signal s_reg_enable_we               : std_logic;
    signal s_reg_error_mask_we           : std_logic;
    signal s_reg_status_we               : std_logic;
    signal s_cmd_we                      : std_logic;
    signal s_reg_min_frame_len_we        : std_logic;
    signal s_reg_max_frame_len_we        : std_logic;
    signal s_reg_mac_check_mode_we       : std_logic;
    signal s_cam_we                      : std_logic;

    signal s_cam_re                      : std_logic;
    signal s_cam_re_reg0                 : std_logic;
    signal s_cam_re_reg1                 : std_logic;

    signal s_mx_ctrl_regs_out            : std_logic_vector(32-1 downto 0);
    signal s_mx_base_stat_out            : std_logic_vector(32-1 downto 0);
    signal s_mx_rfc2819_out              : std_logic_vector(32-1 downto 0);

    signal s_reg_sel_register_out        : std_logic;
    signal s_sel_register_out            : std_logic;

begin

    -- =========================================================================
    --  MI32 ASYNC
    -- =========================================================================

    mi_async_i : entity work.MI_ASYNC
    generic map(
        DEVICE => DEVICE
    )
    port map(
        -- Master interface
        CLK_M     => MI_CLK,
        RESET_M   => MI_RESET,
        MI_M_DWR  => MI_DWR,
        MI_M_ADDR => MI_ADDR,
        MI_M_RD   => MI_RD,
        MI_M_WR   => MI_WR,
        MI_M_BE   => MI_BE,
        MI_M_DRD  => MI_DRD,
        MI_M_ARDY => MI_ARDY,
        MI_M_DRDY => MI_DRDY,

        -- Slave interface
        CLK_S     => CLK,
        RESET_S   => RESET,
        MI_S_DWR  => s_mi_sync_dwr,
        MI_S_ADDR => s_mi_sync_addr,
        MI_S_RD   => s_mi_sync_rd,
        MI_S_WR   => s_mi_sync_wr,
        MI_S_BE   => s_mi_sync_be,
        MI_S_DRD  => s_mi_sync_drd,
        MI_S_ARDY => s_mi_sync_ardy,
        MI_S_DRDY => s_mi_sync_drdy
    );

    -- =========================================================================
    --  MI32 PIPE
    -- =========================================================================

    mi_pipe_i : entity work.MI_PIPE
    generic map(
        DEVICE      => DEVICE,
        DATA_WIDTH  => 32,
        ADDR_WIDTH  => 32,
        --PIPE_TYPE   => "REG",
        USE_OUTREG  => True,
        FAKE_PIPE   => False
    )
    port map(
        -- Common interface
        CLK      => CLK,
        RESET    => RESET,

        -- Input MI interface
        IN_DWR   => s_mi_sync_dwr,
        IN_ADDR  => s_mi_sync_addr,
        IN_RD    => s_mi_sync_rd,
        IN_WR    => s_mi_sync_wr,
        IN_BE    => s_mi_sync_be,
        IN_DRD   => s_mi_sync_drd,
        IN_ARDY  => s_mi_sync_ardy,
        IN_DRDY  => s_mi_sync_drdy,

        -- Output MI interface
        OUT_DWR  => s_mi_dwr,
        OUT_ADDR => s_mi_addr,
        OUT_RD   => s_mi_rd,
        OUT_WR   => s_mi_wr,
        OUT_BE   => s_mi_be,
        OUT_DRD  => s_mi_drd,
        OUT_ARDY => s_mi_ardy,
        OUT_DRDY => s_mi_drdy
    );

    -- =========================================================================
    --  CAM WRITE LOGIC
    -- =========================================================================

    -- Write enable for lower part of MAC address
    s_reg_data_wr_l_we <= s_cam_we and not s_mi_addr(2);

    -- Write enable for higher part of MAC address
    s_reg_data_wr_h_we <= s_cam_we and s_mi_addr(2);

    -- Register storing lower part of MAC address
    reg_data_wr_l_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_reg_data_wr_l_we = '1') then
                s_reg_data_wr_l <= s_mi_dwr;
            end if;
        end if;
    end process;

    -- Register storing higher part of MAC address
    reg_data_wr_h_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_reg_data_wr_h_we = '1') then
                s_reg_data_wr_h <= s_mi_dwr(16 downto 0);
            end if;
        end if;
    end process;

    -- Register for storing address where actual MAC is going to be written
    reg_cam_addr_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_reg_data_wr_l_we = '1') then
                s_reg_cam_addr <= s_mi_addr(log2(MAC_COUNT)+2 downto 3);
            end if;
        end if;
    end process;

    CAM_WRITE_ADDR <= s_reg_cam_addr;

    -- Reordering from SW format (little endian) to network format (big endian)
    CAM_WRITE_DATA(48)           <= s_reg_data_wr_h(16);           -- validity bit
    CAM_WRITE_DATA(47 downto 40) <= s_reg_data_wr_l(7  downto 0);  -- LSB
    CAM_WRITE_DATA(39 downto 32) <= s_reg_data_wr_l(15 downto 8);
    CAM_WRITE_DATA(31 downto 24) <= s_reg_data_wr_l(23 downto 16);
    CAM_WRITE_DATA(23 downto 16) <= s_reg_data_wr_l(31 downto 24);
    CAM_WRITE_DATA(15 downto 8)  <= s_reg_data_wr_h(7  downto 0);
    CAM_WRITE_DATA(7  downto 0)  <= s_reg_data_wr_h(15 downto 8);  -- MSB

    -- Register storing cam_we value
    reg_cam_we_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg_cam_we <= s_reg_data_wr_h_we and not s_reg_enable;
        end if;
    end process;

    CAM_WRITE_EN <= s_reg_cam_we;

    -- CAM ready flag
    s_cam_rdy <= (CAM_WRITE_RDY and not s_reg_enable) or s_reg_enable;

    -- =========================================================================
    --  CONTROL REGISTERS
    -- =========================================================================

    reg_enable_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_enable <= '0';
            elsif (s_reg_enable_we = '1') then
                s_reg_enable <= s_mi_dwr(0);
            end if;
        end if;
    end process;
    -- -------------------------------------------------------------------------

    reg_error_mask_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_error_mask <= (others => '1');
            elsif (s_reg_error_mask_we = '1') then
                s_reg_error_mask <= s_mi_dwr(4 downto 0);
            end if;
        end if;
    end process;
    -- -------------------------------------------------------------------------

    s_inbandfcs <= '1' when INBANDFCS else '0';
    s_mac_count <= std_logic_vector(to_unsigned(MAC_COUNT, 5));

    reg_status_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg_status               <= (others => '0');
            s_reg_status(1 downto 0)   <= s_reg_status(1 downto 0) or BUFFER_STATUS(1 downto 0);
            if (CTL_SW_RESET = '1') then
                s_reg_status(1 downto 0) <= (others => '0');
            end if;
            if (s_reg_status_we = '1') then
                s_reg_status(3 downto 2) <= s_mi_dwr(3 downto 2); -- debug bits
            end if;
            s_reg_status(6 downto 4)   <= ADAPTER_SPEED;
            s_reg_status(7)            <= LINK_STATUS;
            s_reg_status(22)           <= s_inbandfcs;
            s_reg_status(27 downto 23) <= s_mac_count;
            s_reg_status(28)           <= SM_CNT_TICKS_MAX;
        end if;
    end process;
    -- -------------------------------------------------------------------------

    reg_min_frame_len_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_min_frame_len <= std_logic_vector(to_unsigned(64,LEN_WIDTH));
            elsif (s_reg_min_frame_len_we = '1') then
                s_reg_min_frame_len <= s_mi_dwr(LEN_WIDTH-1 downto 0);
            end if;
        end if;
    end process;

    frame_len_min_with_crc_g : if INBANDFCS generate
        s_reg_min_frame_len_fix <= s_reg_min_frame_len;
    end generate;

    frame_len_min_without_crc_g : if not INBANDFCS generate
        s_reg_min_frame_len_fix <= std_logic_vector(unsigned(s_reg_min_frame_len) - 4);
    end generate;
    -- -------------------------------------------------------------------------

    reg_max_frame_len_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_max_frame_len <= std_logic_vector(to_unsigned(1526,LEN_WIDTH));
            elsif (s_reg_max_frame_len_we = '1') then
                s_reg_max_frame_len <= s_mi_dwr(LEN_WIDTH-1 downto 0);
            end if;
        end if;
    end process;

    frame_len_max_with_crc_g : if INBANDFCS generate
        s_reg_max_frame_len_fix <= s_reg_max_frame_len;
    end generate;

    frame_len_max_without_crc_g : if not INBANDFCS generate
        s_reg_max_frame_len_fix <= std_logic_vector(unsigned(s_reg_max_frame_len) - 4);
    end generate;
    -- -------------------------------------------------------------------------

    reg_mac_check_mode_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_mac_check_mode <= (others => '0');
            elsif (s_reg_mac_check_mode_we = '1') then
                s_reg_mac_check_mode <= s_mi_dwr(1 downto 0);
            end if;
        end if;
    end process;

    -- =========================================================================
    --  COMMANDS DECODER
    -- =========================================================================

    s_cmd_sample_sel       <= '1' when (s_mi_dwr(2 downto 0) = CMD_SAMPLE) else '0';
    s_cmd_sw_reset_sel     <= '1' when (s_mi_dwr(2 downto 0) = CMD_RESET) else '0';
    s_cmd_switch_rfc_sel   <= '1' when (s_mi_dwr(2 downto 0) = CMD_SW_BASE_REG) else '0';
    s_cmd_sm_cnt_clear_sel <= '1' when (s_mi_dwr(2 downto 0) = CMD_SM_CNT_CLEAR) else '0';

    s_cmd_read_snapshot <= s_cmd_we and s_cmd_sample_sel;
    s_cmd_take_snapshot <= s_cmd_read_snapshot_reg;
    s_cmd_sw_reset      <= s_cmd_we and s_cmd_sw_reset_sel;
    s_cmd_switch_rfc    <= s_cmd_we and s_cmd_switch_rfc_sel;
    s_cmd_sm_cnt_clear  <= s_cmd_we and s_cmd_sm_cnt_clear_sel;

    cmd_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_cmd_switch_rfc_reg    <= s_cmd_switch_rfc;
            s_cmd_read_snapshot_reg <= s_cmd_read_snapshot;
        end if;
    end process;

    -- =========================================================================
    --  CTL OUTPUT REGISTERS
    -- =========================================================================

    ctl_out_regs_p : process (CLK) -- for better timing
    begin
        if (rising_edge(CLK)) then
            CTL_READ_SNAPSHOT  <= s_cmd_read_snapshot;
            CTL_TAKE_SNAPSHOT  <= s_cmd_take_snapshot;
            CTL_SW_RESET       <= s_cmd_sw_reset;
            CTL_ENABLE         <= s_reg_enable;
            CTL_ERROR_MASK     <= s_reg_error_mask;
            CTL_FRAME_LEN_MIN  <= s_reg_min_frame_len_fix;
            CTL_FRAME_LEN_MAX  <= s_reg_max_frame_len_fix;
            CTL_MAC_CHECK_MODE <= s_reg_mac_check_mode;
            SM_CNT_CLEAR       <= s_cmd_sm_cnt_clear;
        end if;
    end process;

    -- =========================================================================
    --  ADDRESS DECODER
    -- =========================================================================

    -- -------------------------------------------------------------------------
    --  CHIP SELECT SIGNALS
    -- -------------------------------------------------------------------------

    -- base chip select
    base_cs_p : process (s_mi_addr(8 downto 2))
    begin
        s_ibuf_en_cs        <= '0';
        s_error_mask_cs     <= '0';
        s_status_cs         <= '0';
        s_cmd_cs            <= '0';
        s_min_frame_len_cs  <= '0';
        s_max_frame_len_cs  <= '0';
        s_mac_check_mode_cs <= '0';
        s_cam_cs            <= '0';

        -- CS signals for particular registers
        case (s_mi_addr(7 downto 2)) is
            when IBUF_EN_ADDR        => s_ibuf_en_cs        <= '1';
            when ERROR_MASK_ADDR     => s_error_mask_cs     <= '1';
            when STATUS_ADDR         => s_status_cs         <= '1';
            when COMMAND_ADDR        => s_cmd_cs            <= '1';
            when MIN_FRAME_LEN_ADDR  => s_min_frame_len_cs  <= '1';
            when MAX_FRAME_LEN_ADDR  => s_max_frame_len_cs  <= '1';
            when MAC_CHECK_MODE_ADDR => s_mac_check_mode_cs <= '1';
            when others => null;
        end case;

        -- CS signal for CAM
        if (s_mi_addr(8 downto log2(MAC_COUNT)+3) = '0' & CAM_BASE_ADDR(7 downto log2(MAC_COUNT)+3)) then
            s_cam_cs <= '1';
        end if;
    end process;

    -- RFC2819 chip select signals
    s_stats_rfc2819_cs <= s_mi_addr(8);

    -- -------------------------------------------------------------------------
    --  WRITE ENABLE SIGNALS
    -- -------------------------------------------------------------------------

    -- WE signals generation
    s_reg_enable_we         <= s_mi_wr and s_ibuf_en_cs;
    s_reg_error_mask_we     <= s_mi_wr and s_error_mask_cs;
    s_reg_status_we         <= s_mi_wr and s_status_cs;
    s_cmd_we                <= s_mi_wr and s_cmd_cs;
    s_reg_min_frame_len_we  <= s_mi_wr and s_min_frame_len_cs;
    s_reg_max_frame_len_we  <= s_mi_wr and s_max_frame_len_cs;
    s_reg_mac_check_mode_we <= s_mi_wr and s_mac_check_mode_cs;
    s_cam_we                <= s_mi_wr and s_cam_cs;
    s_cam_re                <= s_mi_rd and s_cam_cs;

    sm_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_sm_cnt_ticks_reg   <= (others => '0');
            s_sm_cnt_bytes_reg   <= (others => '0');
            s_sm_cnt_packets_reg <= (others => '0');
            s_sm_cnt_ticks_reg(SM_CNT_TICKS_WIDTH-1 downto 0)   <= SM_CNT_TICKS;
            s_sm_cnt_bytes_reg(SM_CNT_BYTES_WIDTH-1 downto 0)   <= SM_CNT_BYTES;
            s_sm_cnt_packets_reg(SM_CNT_BYTES_WIDTH-1 downto 0) <= SM_CNT_PACKETS;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  DATA READ MULTIPLEXORS
    -- -------------------------------------------------------------------------

    -- Multiplexor of control registers
    mx_ctrl_regs_out_p : process (all)
    begin
        case (s_mi_addr(7 downto 2)) is
            when IBUF_EN_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto 1 => '0') & s_reg_enable;
            when ERROR_MASK_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto 5 => '0') & s_reg_error_mask;
            when STATUS_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto 29 => '0') & s_reg_status;
            when MIN_FRAME_LEN_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto LEN_WIDTH => '0') & s_reg_min_frame_len;
            when MAX_FRAME_LEN_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto LEN_WIDTH => '0') & s_reg_max_frame_len;
            when MAC_CHECK_MODE_ADDR =>
                s_mx_ctrl_regs_out <= (31 downto 2 => '0') & s_reg_mac_check_mode;
            when SM_CNT_TICKS_ADDR =>
                s_mx_ctrl_regs_out <= s_sm_cnt_ticks_reg;
            when SM_CNT_BYTES_ADDR =>
                s_mx_ctrl_regs_out <= s_sm_cnt_bytes_reg;
            when SM_CNT_PACKETS_ADDR =>
                s_mx_ctrl_regs_out <= s_sm_cnt_packets_reg;
            when others =>
                s_mx_ctrl_regs_out <= X"DEADCAFE";
        end case;
    end process;

    -- Multiplexor of base statistics
    mx_base_stat_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            case (s_mi_addr(7 downto 2)) is
                when TRFC_L_ADDR  => s_mx_base_stat_out <= STAT_FRAMES_RECEIVED(31 downto 0);
                when CFC_L_ADDR   => s_mx_base_stat_out <= STAT_FRAMES_TRANSMITTED(31 downto 0);
                when DFC_L_ADDR   => s_mx_base_stat_out <= STAT_FRAMES_DISCARDED(31 downto 0);
                when BODFC_L_ADDR => s_mx_base_stat_out <= STAT_BUFFER_OVF(31 downto 0);
                when OROC_L_ADDR  => s_mx_base_stat_out <= STAT_TX_BYTES(31 downto 0);

                when TRFC_H_ADDR  => s_mx_base_stat_out <= STAT_FRAMES_RECEIVED(63 downto 32);
                when CFC_H_ADDR   => s_mx_base_stat_out <= STAT_FRAMES_TRANSMITTED(63 downto 32);
                when DFC_H_ADDR   => s_mx_base_stat_out <= STAT_FRAMES_DISCARDED(63 downto 32);
                when BODFC_H_ADDR => s_mx_base_stat_out <= STAT_BUFFER_OVF(63 downto 32);
                when OROC_H_ADDR  => s_mx_base_stat_out <= STAT_TX_BYTES(63 downto 32);

                when others       => s_mx_base_stat_out <= s_mx_ctrl_regs_out;
            end case;
        end if;
    end process;

    -- Multiplexor of RFC2819 statistics
    mx_rfc2819_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            case (s_mi_addr(7 downto 2)) is
                when CRC_ERR_L_ADDR          => s_mx_rfc2819_out <= STAT_CRC_ERR(31 downto 0);
                when OVER_MTU_L_ADDR         => s_mx_rfc2819_out <= STAT_OVER_MTU(31 downto 0);
                when BELOW_MIN_L_ADDR        => s_mx_rfc2819_out <= STAT_BELOW_MIN(31 downto 0);
                when BCAST_FRAMES_L_ADDR     => s_mx_rfc2819_out <= STAT_BCAST_FRAMES(31 downto 0);
                when MCAST_FRAMES_L_ADDR     => s_mx_rfc2819_out <= STAT_MCAST_FRAMES(31 downto 0);
                when FRAGMENT_FRAMES_L_ADDR  => s_mx_rfc2819_out <= STAT_FRAGMENT_FRAMES(31 downto 0);
                when JABBER_FRAMES_L_ADDR    => s_mx_rfc2819_out <= STAT_JABBER_FRAMES(31 downto 0);
                when TRANS_OCTETS_L_ADDR     => s_mx_rfc2819_out <= STAT_RX_BYTES(31 downto 0);

                when CRC_ERR_H_ADDR          => s_mx_rfc2819_out <= STAT_CRC_ERR(63 downto 32);
                when OVER_MTU_H_ADDR         => s_mx_rfc2819_out <= STAT_OVER_MTU(63 downto 32);
                when BELOW_MIN_H_ADDR        => s_mx_rfc2819_out <= STAT_BELOW_MIN(63 downto 32);
                when BCAST_FRAMES_H_ADDR     => s_mx_rfc2819_out <= STAT_BCAST_FRAMES(63 downto 32);
                when MCAST_FRAMES_H_ADDR     => s_mx_rfc2819_out <= STAT_MCAST_FRAMES(63 downto 32);
                when FRAGMENT_FRAMES_H_ADDR  => s_mx_rfc2819_out <= STAT_FRAGMENT_FRAMES(63 downto 32);
                when JABBER_FRAMES_H_ADDR    => s_mx_rfc2819_out <= STAT_JABBER_FRAMES(63 downto 32);
                when TRANS_OCTETS_H_ADDR     => s_mx_rfc2819_out <= STAT_RX_BYTES(63 downto 32);

                when FRAMES_64_L_ADDR        => s_mx_rfc2819_out <= STAT_FRAMES_64(31 downto 0);
                when FRAMES_65_127_L_ADDR    => s_mx_rfc2819_out <= STAT_FRAMES_65_127(31 downto 0);
                when FRAMES_128_255_L_ADDR   => s_mx_rfc2819_out <= STAT_FRAMES_128_255(31 downto 0);
                when FRAMES_256_511_L_ADDR   => s_mx_rfc2819_out <= STAT_FRAMES_256_511(31 downto 0);
                when FRAMES_512_1023_L_ADDR  => s_mx_rfc2819_out <= STAT_FRAMES_512_1023(31 downto 0);
                when FRAMES_1024_1518_L_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_1024_1518(31 downto 0);
                when FRAMES_OVER_1518_L_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_OVER_1518(31 downto 0);
                when FRAMES_UNDERSIZE_L_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_UNDERSIZE(31 downto 0);

                when FRAMES_64_H_ADDR        => s_mx_rfc2819_out <= STAT_FRAMES_64(63 downto 32);
                when FRAMES_65_127_H_ADDR    => s_mx_rfc2819_out <= STAT_FRAMES_65_127(63 downto 32);
                when FRAMES_128_255_H_ADDR   => s_mx_rfc2819_out <= STAT_FRAMES_128_255(63 downto 32);
                when FRAMES_256_511_H_ADDR   => s_mx_rfc2819_out <= STAT_FRAMES_256_511(63 downto 32);
                when FRAMES_512_1023_H_ADDR  => s_mx_rfc2819_out <= STAT_FRAMES_512_1023(63 downto 32);
                when FRAMES_1024_1518_H_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_1024_1518(63 downto 32);
                when FRAMES_OVER_1518_H_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_OVER_1518(63 downto 32);
                when FRAMES_UNDERSIZE_H_ADDR => s_mx_rfc2819_out <= STAT_FRAMES_UNDERSIZE(63 downto 32);

                when others                  => s_mx_rfc2819_out <= s_mx_ctrl_regs_out;
            end case;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  ADDRESS SPACE SWITCHING
    -- -------------------------------------------------------------------------

    -- Address space switching
    reg_sel_register_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                -- Select base register field by default
                s_reg_sel_register_out <= '0';
            elsif (s_cmd_switch_rfc_reg = '1') then
                -- Select base register field
                s_reg_sel_register_out <= not(s_reg_sel_register_out);
            end if;
        end if;
    end process;

    stats_rfc2819_cs_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_stats_rfc2819_cs_reg <= s_stats_rfc2819_cs;
        end if;
    end process;

    -- Generation of selection signal
    s_sel_register_out <= s_stats_rfc2819_cs_reg or (not s_stats_rfc2819_cs_reg and s_reg_sel_register_out);

    -- -------------------------------------------------------------------------
    --  MI DRD, MI DRDY and MI ARDY
    -- -------------------------------------------------------------------------

    s_mi_ardy <= (s_mi_wr or s_mi_rd) and s_cam_rdy;

    mi_drd_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_sel_register_out = '1') then
                s_mi_drd0 <= s_mx_rfc2819_out;
            else
                s_mi_drd0 <= s_mx_base_stat_out;
            end if;
        end if;
    end process;

    mi_drdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_mi_rd_reg   <= '0';
                s_mi_drdy     <= '0';
                s_cam_re_reg0 <= '0';
                s_cam_re_reg1 <= '0';
            else
                s_mi_rd_reg   <= s_mi_rd and s_cam_rdy;
                s_mi_drdy     <= s_mi_rd_reg;
                s_cam_re_reg0 <= s_cam_re;
                s_cam_re_reg1 <= s_cam_re_reg0;
            end if;
        end if;
    end process;

    s_mi_drd <= s_mi_drd1 when s_cam_re_reg1='1' else s_mi_drd0;

    -- -------------------------------------------------------------------------
    --  MI-readable TCAM copy
    -- -------------------------------------------------------------------------

    tcam_memx_i : entity work.SDP_MEMX
    generic map(
        DATA_WIDTH => 32         ,
        ITEMS      => MAC_COUNT*2,
        RAM_TYPE   => "AUTO"     ,
        DEVICE     => DEVICE     ,
        OUTPUT_REG => true
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        WR_DATA    => s_mi_dwr,
        WR_ADDR    => s_mi_addr(log2(MAC_COUNT*2)+2-1 downto 2),
        WR_EN      => s_cam_we,

        RD_DATA    => s_mi_drd1,
        RD_ADDR    => s_mi_addr(log2(MAC_COUNT*2)+2-1 downto 2),
        RD_PIPE_EN => '1'
    );

end architecture;
