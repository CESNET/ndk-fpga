-- mac_check.vhd: MAC check
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_MAC_CHECK is
    generic(
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        REGIONS     : natural := 4; -- any possitive value
        REGION_SIZE : natural := 8; -- must be power of 2
        BLOCK_SIZE  : natural := 8; -- must be power of 2
        ITEM_WIDTH  : natural := 8; -- must be power of 2
        -- =====================================================================
        -- MAC CHECK CONFIGURATION:
        -- =====================================================================
        MAC_COUNT   : natural := 16; -- any possitive value, max is 16
        DEVICE      : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK                : in  std_logic;
        RESET              : in  std_logic;
        -- =====================================================================
        -- INPUT CONTROL REGISTER INTERFACE
        -- =====================================================================
        MAC_CHECK_MODE     : in  std_logic_vector(2-1 downto 0);
        -- =====================================================================
        -- INPUT MFB DATA INTERFACE
        -- =====================================================================
        RX_DATA            : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS         : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS         : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF             : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF             : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY         : in  std_logic;
        -- =====================================================================
        -- INPUT CAM WRITE INTERFACE
        -- =====================================================================
        CAM_WRITE_DATA     : in  std_logic_vector(49-1 downto 0);
        CAM_WRITE_ADDR     : in  std_logic_vector(log2(MAC_COUNT)-1 downto 0);
        CAM_WRITE_EN       : in  std_logic;
        CAM_WRITE_RDY      : out std_logic;
        -- =====================================================================
        -- OUTPUT MVB MAC STATUS INTERFACE
        -- =====================================================================
        -- MAC status format for each region:
        -- log2(MAC_COUNT)+4-1 downto 4 = MAC hit address
        --                            3 = MAC hit valid
        --                            2 = MAC multicast
        --                            1 = MAC broadcast
        --                            0 = MAC error
        MAC_STATUS         : out std_logic_vector(REGIONS*(log2(MAC_COUNT)+4)-1 downto 0);
        -- valid flag of MAC status signal for each region
        MAC_STATUS_VLD     : out std_logic_vector(REGIONS-1 downto 0);
        -- source ready of MAC status signal
        MAC_STATUS_SRC_RDY : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_MAC_CHECK is

    constant REGION_WIDTH     : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant SOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE));
    constant MAC_STATUS_WIDTH : natural := log2(MAC_COUNT)+4;

    signal s_inc_frame              : std_logic_vector(REGIONS downto 0);

    signal s_eof_reg0               : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg1               : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg2               : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg3               : std_logic_vector(REGIONS-1 downto 0);

    signal s_sof_after_eof          : std_logic_vector(REGIONS-1 downto 0);
    signal s_sof_after_eof_reg0     : std_logic_vector(REGIONS-1 downto 0);
    signal s_sof_after_eof_reg1     : std_logic_vector(REGIONS-1 downto 0);
    signal s_sof_after_eof_reg2     : std_logic_vector(REGIONS-1 downto 0);
    signal s_sof_after_eof_reg3     : std_logic_vector(REGIONS-1 downto 0);

    signal s_src_rdy_reg0           : std_logic;
    signal s_src_rdy_reg1           : std_logic;
    signal s_src_rdy_reg2           : std_logic;
    signal s_src_rdy_reg3           : std_logic;

    signal s_ext_mac_arr            : slv_array_t(REGIONS-1 downto 0)(48-1 downto 0);
    signal s_ext_mac_vld            : std_logic_vector(REGIONS-1 downto 0);
    signal s_ext_mac_vld_reg1       : std_logic_vector(REGIONS-1 downto 0);
    signal s_ext_mac_vld_reg2       : std_logic_vector(REGIONS-1 downto 0);
    signal s_ext_mac_vld_reg3       : std_logic_vector(REGIONS-1 downto 0);

    signal s_cam_match_data_arr     : slv_array_t(REGIONS-1 downto 0)(49-1 downto 0);
    signal s_cam_match_en           : std_logic_vector(REGIONS-1 downto 0);

    signal s_multicast_err          : std_logic_vector(REGIONS-1 downto 0);
    signal s_multicast_err_reg1     : std_logic_vector(REGIONS-1 downto 0);
    signal s_multicast_err_reg2     : std_logic_vector(REGIONS-1 downto 0);
    signal s_multicast_err_reg3     : std_logic_vector(REGIONS-1 downto 0);

    signal s_broadcast_err          : std_logic_vector(REGIONS-1 downto 0);
    signal s_broadcast_err_reg1     : std_logic_vector(REGIONS-1 downto 0);
    signal s_broadcast_err_reg2     : std_logic_vector(REGIONS-1 downto 0);
    signal s_broadcast_err_reg3     : std_logic_vector(REGIONS-1 downto 0);

    signal s_cam_write_rdy          : std_logic_vector(REGIONS-1 downto 0);
    signal s_cam_write_en_masked    : std_logic_vector(REGIONS-1 downto 0);
    signal s_cam_match_out_arr_reg3 : slv_array_t(REGIONS-1 downto 0)(MAC_COUNT-1 downto 0);
    signal s_cam_match_out_vld_reg3 : std_logic_vector(REGIONS-1 downto 0);
    signal s_cam_match_out_hit      : std_logic_vector(REGIONS-1 downto 0);
    signal s_mac_hit_addr_arr_reg3  : slv_array_t(REGIONS-1 downto 0)(log2(MAC_COUNT)-1 downto 0);
    signal s_cam_err                : std_logic_vector(REGIONS-1 downto 0);

    signal s_mac_err                : std_logic_vector(REGIONS-1 downto 0);
    signal s_mac_broadcast          : std_logic_vector(REGIONS-1 downto 0);
    signal s_mac_multicast          : std_logic_vector(REGIONS-1 downto 0);
    signal s_mac_status_arr         : slv_array_t(REGIONS-1 downto 0)(MAC_STATUS_WIDTH-1 downto 0);

    signal s_mac_status_lva         : slv_array_t(REGIONS-1 downto 0)(MAC_STATUS_WIDTH-1 downto 0);
    signal s_mac_status_lva_reg     : std_logic_vector(MAC_STATUS_WIDTH-1 downto 0);
    signal s_mac_status_out_arr     : slv_array_t(REGIONS-1 downto 0)(MAC_STATUS_WIDTH-1 downto 0);

begin

    -- -------------------------------------------------------------------------
    --  FRAME STATE LOGIC
    -- -------------------------------------------------------------------------

    inc_frame_g : for r in 0 to REGIONS-1 generate
        s_inc_frame(r+1) <= (RX_SOF(r) and not RX_EOF(r) and not s_inc_frame(r)) or
                            (RX_SOF(r) and RX_EOF(r) and s_inc_frame(r)) or
                            (not RX_SOF(r) and not RX_EOF(r) and s_inc_frame(r));
    end generate;

    inc_frame_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_frame(0) <= '0';
            elsif (RX_SRC_RDY = '1') then
                s_inc_frame(0) <= s_inc_frame(REGIONS);
            end if;
        end if;
    end process;

    sof_after_eof_g : for r in 0 to REGIONS-1 generate
        s_sof_after_eof(r) <= RX_SOF(r) and RX_EOF(r) and s_inc_frame(r);
    end generate;

    -- synchronization registers: delay for 4 clocks
    eof_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_eof_reg0 <= RX_EOF;
            s_eof_reg1 <= s_eof_reg0;
            s_eof_reg2 <= s_eof_reg1;
            s_eof_reg3 <= s_eof_reg2;

            s_sof_after_eof_reg0 <= s_sof_after_eof;
            s_sof_after_eof_reg1 <= s_sof_after_eof_reg0;
            s_sof_after_eof_reg2 <= s_sof_after_eof_reg1;
            s_sof_after_eof_reg3 <= s_sof_after_eof_reg2;
        end if;
    end process;

    src_rdy_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg0 <= '0';
                s_src_rdy_reg1 <= '0';
                s_src_rdy_reg2 <= '0';
                s_src_rdy_reg3 <= '0';
            else
                s_src_rdy_reg0 <= RX_SRC_RDY;
                s_src_rdy_reg1 <= s_src_rdy_reg0;
                s_src_rdy_reg2 <= s_src_rdy_reg1;
                s_src_rdy_reg3 <= s_src_rdy_reg2;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  MAC ADDRESS EXTRACTION + ERRORS
    -- -------------------------------------------------------------------------

    -- extraction of destination MAC address from Ethernet frames (1 cycle)
    get_mac_g : for r in 0 to REGIONS-1 generate
        get_crc32_i : entity work.RX_MAC_LITE_GET_MAC
        generic map(
            REGION_SIZE => REGION_SIZE,
            BLOCK_SIZE  => BLOCK_SIZE,
            ITEM_WIDTH  => ITEM_WIDTH
        )
        port map(
            -- CLOCK AND RESET
            CLK         => CLK,
            RESET       => RESET,
            -- INPUT DATA INTERFACE
            RX_DATA     => RX_DATA((r+1)*REGION_WIDTH-1 downto r*REGION_WIDTH),
            RX_SOF_POS  => RX_SOF_POS((r+1)*SOF_POS_SIZE-1 downto r*SOF_POS_SIZE),
            RX_SOF      => RX_SOF(r),
            RX_SRC_RDY  => RX_SRC_RDY,
            -- OUTPUT MAC INTERFACE
            MAC_DST     => s_ext_mac_arr(r),
            MAC_DST_VLD => s_ext_mac_vld(r)
        );
    end generate;

    -- try find MAC address in CAM memory
    try_cam_match_g : for r in 0 to REGIONS-1 generate
        s_cam_match_data_arr(r) <= '1' & s_ext_mac_arr(r); -- MSB is SW valid bit
        s_cam_match_en(r)       <= s_ext_mac_vld(r);
    end generate;

    mac_cast_err_g : for r in 0 to REGIONS-1 generate
        -- Possible multicast error occurence
        s_multicast_err(r) <= not s_ext_mac_arr(r)(0);
        -- Possible broadcast error occurence
        s_broadcast_err(r) <= nand s_ext_mac_arr(r);
    end generate;

    -- synchronization registers: delay for 3 clocks
    errors_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_multicast_err_reg1 <= s_multicast_err;
            s_multicast_err_reg2 <= s_multicast_err_reg1;
            s_multicast_err_reg3 <= s_multicast_err_reg2;
            s_broadcast_err_reg1 <= s_broadcast_err;
            s_broadcast_err_reg2 <= s_broadcast_err_reg1;
            s_broadcast_err_reg3 <= s_broadcast_err_reg2;
        end if;
    end process;

    ext_mac_vld_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_ext_mac_vld_reg1 <= (others => '0');
                s_ext_mac_vld_reg2 <= (others => '0');
                s_ext_mac_vld_reg3 <= (others => '0');
            else
                s_ext_mac_vld_reg1 <= s_ext_mac_vld;
                s_ext_mac_vld_reg2 <= s_ext_mac_vld_reg1;
                s_ext_mac_vld_reg3 <= s_ext_mac_vld_reg2;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  MAC ADDRESS CAM MEMORY + MAC ERROR
    -- -------------------------------------------------------------------------

    -- CAM memory
    tcam_g : for r in 0 to REGIONS-1 generate
        cam_write_en_masked_p : process (s_cam_write_rdy,CAM_WRITE_EN)
            variable v_mask_bit : std_logic;
        begin
            v_mask_bit := '1';
            for i in 0 to REGIONS-1 loop
                if (i /= r) then
                    v_mask_bit := v_mask_bit and s_cam_write_rdy(i);
                end if;
            end loop;
            s_cam_write_en_masked(r) <= CAM_WRITE_EN and v_mask_bit;
        end process;

        tcam_i : entity work.TCAM2
        generic map(
            DATA_WIDTH         => 49,
            ITEMS              => MAC_COUNT,
            RESOURCES_SAVING   => 0,
            WRITE_BEFORE_MATCH => false,
            READ_FROM_TCAM     => false,
            OUTPUT_READ_REGS   => false,
            DEVICE             => DEVICE
        )
        port map(
            CLK            => CLK,
            RST            => RESET,
            READ_ADDR      => (others => '0'),
            READ_EN        => '0',
            READ_RDY       => open,
            READ_DATA      => open,
            READ_MASK      => open,
            READ_DATA_VLD  => open,
            WRITE_DATA     => CAM_WRITE_DATA,
            WRITE_MASK     => (others => '1'),
            WRITE_ADDR     => CAM_WRITE_ADDR,
            WRITE_EN       => s_cam_write_en_masked(r),
            WRITE_RDY      => s_cam_write_rdy(r),
            MATCH_DATA     => s_cam_match_data_arr(r),
            MATCH_EN       => s_cam_match_en(r),
            MATCH_RDY      => open,
            MATCH_OUT_HIT  => s_cam_match_out_hit(r),
            MATCH_OUT_ADDR => s_cam_match_out_arr_reg3(r),
            MATCH_OUT_VLD  => s_cam_match_out_vld_reg3(r) -- latency is 3 cycles
        );

        s_cam_err(r) <= (not s_cam_match_out_vld_reg3(r)) or (not s_cam_match_out_hit(r));

        hot2bin_i : entity work.DEC1FN2B
        generic map(
            ITEMS => MAC_COUNT
        )
        port map(
            ENABLE => s_cam_match_out_vld_reg3(r),
            DI     => s_cam_match_out_arr_reg3(r),
            ADDR   => s_mac_hit_addr_arr_reg3(r)
        );
    end generate;

    -- All the CAMs should be ready for write at the same time
    CAM_WRITE_RDY <= and s_cam_write_rdy;

    -- Multiplexor between different MAC check modes
    mux_mac_err_g : for r in 0 to REGIONS-1 generate
        mux_mac_err_p : process (all)
        begin
            case (MAC_CHECK_MODE) is
                when "00"   => s_mac_err(r) <= '0';
                when "01"   => s_mac_err(r) <= s_cam_err(r);
                when "10"   => s_mac_err(r) <= s_cam_err(r) and s_broadcast_err_reg3(r);
                when "11"   => s_mac_err(r) <= s_cam_err(r) and s_broadcast_err_reg3(r) and s_multicast_err_reg3(r);
                when others => s_mac_err(r) <= '0';
            end case;
        end process;
    end generate;

    -- -------------------------------------------------------------------------
    --  MAC STATUS SIGNAL WITH DISTRIBUTION
    -- -------------------------------------------------------------------------

    -- Create MAC status signal
    mac_status_g : for r in 0 to REGIONS-1 generate
        s_mac_broadcast(r)  <= not s_broadcast_err_reg3(r);
        s_mac_multicast(r)  <= not s_multicast_err_reg3(r);
        s_mac_status_arr(r) <= s_mac_hit_addr_arr_reg3(r) & s_cam_match_out_hit(r) & s_mac_multicast(r) & s_mac_broadcast(r) & s_mac_err(r);
    end generate;

    -- distribution last valid MAC status
    s_mac_status_lva(0) <= s_mac_status_arr(0) when (s_ext_mac_vld_reg3(0) = '1') else s_mac_status_lva_reg;
    mac_status_lva_g : for r in 1 to REGIONS-1 generate
        s_mac_status_lva(r) <= s_mac_status_arr(r) when (s_ext_mac_vld_reg3(r) = '1') else s_mac_status_lva(r-1);
    end generate;

    -- last valid register of MAC status
    mac_status_lva_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_src_rdy_reg3 = '1') then
                s_mac_status_lva_reg <= s_mac_status_lva(REGIONS-1);
            end if;
        end if;
    end process;

    -- correct sync to EOF
    s_mac_status_out_arr(0) <= s_mac_status_lva_reg when (s_sof_after_eof_reg3(0) = '1') else s_mac_status_lva(0);
    mac_status_out_g : for r in 1 to REGIONS-1 generate
        s_mac_status_out_arr(r) <= s_mac_status_lva(r-1) when (s_sof_after_eof_reg3(r) = '1') else s_mac_status_lva(r);
    end generate;

    -- -------------------------------------------------------------------------
    --  OUTPUT REGISTERS
    -- -------------------------------------------------------------------------

    -- output registers
    mac_status_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            MAC_STATUS     <= slv_array_ser(s_mac_status_out_arr,REGIONS,MAC_STATUS_WIDTH);
            MAC_STATUS_VLD <= s_eof_reg3;
        end if;
    end process;

    -- output source ready register
    mac_status_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                MAC_STATUS_SRC_RDY <= '0';
            else
                MAC_STATUS_SRC_RDY <= s_src_rdy_reg3;
            end if;
        end if;
    end process;

end architecture;
