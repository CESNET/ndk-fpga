-- crc_insert.vhd: TX MAC Lite CRC insertor
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_CRC_INSERT is
    generic(
        -- Number of regions within a data word.
        MFB_REGIONS     : natural := 4;
        -- Region size (in blocks).
        MFB_REGION_SIZE : natural := 8;
        -- Block size (in items).
        MFB_BLOCK_SIZE  : natural := 8;
        -- Item width (in bits), must be 8.
        MFB_ITEM_WIDTH  : natural := 8;
        -- FPGA device name.
        DEVICE          : string := "STRATIX10"
    );
    port(
        -- =====================================================================
        --  CLOCK AND RESET
        -- =====================================================================
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        -- =====================================================================
        --  RX MVB STREAM (with CRC)
        -- =====================================================================
        RX_MVB_CRC_DATA    : in  std_logic_vector(MFB_REGIONS*32-1 downto 0);
        RX_MVB_CRC_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_CRC_SRC_RDY : in  std_logic;
        RX_MVB_CRC_DST_RDY : out std_logic;

        -- =====================================================================
        --  RX MFB STREAM (with free items for CRC insert)
        -- =====================================================================
        RX_MFB_DATA        : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY     : in  std_logic;
        RX_MFB_DST_RDY     : out std_logic;

        -- =====================================================================
        --  TX MFB STREAM
        -- =====================================================================
        TX_MFB_DATA        : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS     : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS     : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF         : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF         : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY     : out std_logic;
        TX_MFB_DST_RDY     : in  std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_CRC_INSERT is

    constant MFB_DATA_W    : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_EOF_POS_W : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    constant CRC_W         : natural := 32;

    signal reg0_mfb_data           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal reg0_mfb_sof_pos        : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal reg0_mfb_eof_pos        : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal reg0_mfb_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal reg0_mfb_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal reg0_mfb_src_rdy        : std_logic;
    signal reg0_mfb_dst_rdy        : std_logic;

    signal crc_fifoxm_wr           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal crc_fifoxm_full         : std_logic;
    signal shake_crc_out           : std_logic_vector(MFB_REGIONS*CRC_W-1 downto 0);
    signal shake_next              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shake_vld               : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shake_vld_n             : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal crc_out_of_sync_dbg     : std_logic;
    signal crc_out_of_sync_dbg_reg : std_logic;

    signal reg0_mfb_eof_pos_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_W-1 downto 0);
    signal crc32_data_arr          : slv_array_t(MFB_REGIONS-1 downto 0)(CRC_W-1 downto 0);
    signal crc32_data_shifted_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(CRC_W-1 downto 0);
    signal crc_accept              : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal crc_offset              : i_array_t(MFB_REGIONS-1 downto 0);

    signal crc_byte_en             : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+4-1 downto 0);
    signal crc_byte_en_reg         : std_logic_vector(4-1 downto 0);

    signal ci_mfb_data_plus_raw    : std_logic_vector(MFB_DATA_W+CRC_W-1 downto 0);
    signal ci_mfb_data_plus_masked : std_logic_vector(MFB_DATA_W+CRC_W-1 downto 0);
    signal ci_mfb_data_plus        : std_logic_vector(MFB_DATA_W+CRC_W-1 downto 0);
    signal ci_mfb_plus_mask_reg    : std_logic_vector(CRC_W-1 downto 0);

    signal ci_mfb_data             : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ci_mfb_sof_pos          : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal ci_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ci_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ci_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ci_mfb_src_rdy          : std_logic;
    signal ci_mfb_dst_rdy          : std_logic;

    signal ci_mfb_eof_pos_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_W-1 downto 0);
    signal ci_mfb_eof_pos_plus_arr : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_W+1-1 downto 0);
    signal ci_mfb_eof_pos_over     : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    signal ci_mfb_eof_pos_val_arr  : slv_array_t(MFB_REGIONS+1-1 downto 0)(MFB_EOF_POS_W-1 downto 0);
    signal ci_mfb_eof_new          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ci_mfb_eof_pos_new_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_W-1 downto 0);
    signal ci_mfb_eof_pos_new      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ci_inc_region           : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    signal ci_mfb_src_rdy_new      : std_logic;

begin

    -- =========================================================================
    --  INPUT MFB REGISTERS
    -- =========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RX_MFB_DST_RDY = '1') then
                reg0_mfb_data    <= RX_MFB_DATA;
                reg0_mfb_sof     <= RX_MFB_SOF;
                reg0_mfb_eof     <= RX_MFB_EOF;
                reg0_mfb_sof_pos <= RX_MFB_SOF_POS;
                reg0_mfb_eof_pos <= RX_MFB_EOF_POS;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                reg0_mfb_src_rdy <= '0';
            elsif (RX_MFB_DST_RDY = '1') then
                reg0_mfb_src_rdy <= RX_MFB_SRC_RDY;
            end if;
        end if;
    end process;

    RX_MFB_DST_RDY <= reg0_mfb_dst_rdy;

    -- =========================================================================
    --  FIFOX MULTI
    -- =========================================================================

    crc_fifoxm_wr <= RX_MVB_CRC_VLD and RX_MVB_CRC_SRC_RDY;
    RX_MVB_CRC_DST_RDY <= not crc_fifoxm_full;

    crc_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => CRC_W,
        ITEMS               => 32,
        WRITE_PORTS         => MFB_REGIONS,
        READ_PORTS          => MFB_REGIONS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        SAFE_READ_MODE      => false
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => RX_MVB_CRC_DATA,
        WR     => crc_fifoxm_wr,
        FULL   => crc_fifoxm_full,
        AFULL  => open,

        DO     => shake_crc_out,
        RD     => shake_next,
        EMPTY  => shake_vld_n,
        AEMPTY => open
    );

    shake_vld <= not shake_vld_n;

    crc_out_of_sync_dbg_p : process (all)
        variable v_crc_index : integer range 0 to MFB_REGIONS;
        variable v_eof_index : integer range 0 to MFB_REGIONS;
    begin
        v_crc_index := 0;
        v_eof_index := 0;
        for i in 0 to MFB_REGIONS-1 loop
            if (shake_vld(i) = '1') then
                v_crc_index := v_crc_index + 1;
            end if;
            if (reg0_mfb_eof(i) = '1') then
                v_eof_index := v_eof_index + 1;
            end if;
        end loop;
        if (v_eof_index > v_crc_index) then
            crc_out_of_sync_dbg <= ci_mfb_src_rdy and ci_mfb_dst_rdy;
        else
            crc_out_of_sync_dbg <= '0';
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            crc_out_of_sync_dbg_reg <= crc_out_of_sync_dbg;
        end if;
    end process;

    assert (not crc_out_of_sync_dbg_reg)
        report "TX_MAC_LITE_CRC_INSERT: CRC32 out of sync!"
        severity error;

    crc_accept_p : process (all)
        variable v_crc_accept : std_logic_vector(MFB_REGIONS-1 downto 0);
        variable v_eof_index  : integer range 0 to MFB_REGIONS;
    begin
        v_eof_index  := 0;
        v_crc_accept := (others => '0');
        for i in 0 to MFB_REGIONS-1 loop
            if (reg0_mfb_eof(i) = '1') then
                v_crc_accept(v_eof_index) := '1';
                v_eof_index := v_eof_index + 1;
            end if;
        end loop;
        crc_accept <= v_crc_accept;
    end process;

    shake_next <= crc_accept and ci_mfb_src_rdy and ci_mfb_dst_rdy;

    -- =========================================================================
    --  CRC INSERT LOGIC
    -- =========================================================================

    reg0_mfb_eof_pos_arr <= slv_array_deser(reg0_mfb_eof_pos,MFB_REGIONS,MFB_EOF_POS_W);
    crc32_data_arr       <= slv_array_deser(shake_crc_out,MFB_REGIONS,CRC_W);

    crc_shift_p : process (all)
        variable v_eof_index : integer range 0 to MFB_REGIONS;
    begin
        v_eof_index := 0;
        for i in 0 to MFB_REGIONS-1 loop
            crc32_data_shifted_arr(i) <= crc32_data_arr(v_eof_index);
            if (reg0_mfb_EOF(i) = '1') then
                v_eof_index := v_eof_index + 1;
            end if;
        end loop;
    end process;

    ci_mfb_data_plus_raw <= X"FFFFFFFF" & reg0_mfb_data;

    ci_mfb_data_plus_masked_p : process (all)
    begin
        ci_mfb_data_plus_masked <= ci_mfb_data_plus_raw;
        for i in 0 to 4-1 loop
            if (crc_byte_en_reg(i) = '1') then
                ci_mfb_data_plus_masked((i+1)*8-1 downto i*8) <= ci_mfb_plus_mask_reg((i+1)*8-1 downto i*8);
            end if;
        end loop;
    end process;

    -- debug only
    crc_offset_g: for i in 0 to MFB_REGIONS-1 generate
        crc_offset(i) <= to_integer(unsigned(reg0_mfb_eof_pos_arr(i))) + i*MFB_REGION_SIZE*MFB_BLOCK_SIZE + 1;
    end generate;

    crc_insert_p : process (all)
        variable v_crc_offset : integer := 0;
        variable v_ci_mfb_data_plus : std_logic_vector(MFB_DATA_W+CRC_W-1 downto 0);
    begin
        v_ci_mfb_data_plus := ci_mfb_data_plus_masked;
        crc_byte_en <= (others => '0');
        for i in 0 to MFB_REGIONS-1 loop
            v_crc_offset := to_integer(unsigned(reg0_mfb_eof_pos_arr(i))) + i*MFB_REGION_SIZE*MFB_BLOCK_SIZE + 1;
            if (reg0_mfb_eof(i) = '1' and ci_mfb_src_rdy = '1') then
                v_ci_mfb_data_plus(v_crc_offset*8+CRC_W-1 downto v_crc_offset*8) := crc32_data_shifted_arr(i);
                crc_byte_en(v_crc_offset+4-1 downto v_crc_offset) <= "1111";
            end if;
        end loop;
        ci_mfb_data_plus <= v_ci_mfb_data_plus;
    end process;

    ci_mfb_plus_mask_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (ci_mfb_dst_rdy = '1') then
                ci_mfb_plus_mask_reg <= ci_mfb_data_plus(MFB_DATA_W+CRC_W-1 downto MFB_DATA_W);
                crc_byte_en_reg <= crc_byte_en(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+4-1 downto MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE);
            end if;
        end if;
    end process;

    ci_mfb_data    <= ci_mfb_data_plus(MFB_DATA_W-1 downto 0);
    ci_mfb_sof     <= reg0_mfb_sof and reg0_mfb_src_rdy;
    ci_mfb_eof     <= reg0_mfb_eof and reg0_mfb_src_rdy;
    ci_mfb_sof_pos <= reg0_mfb_sof_pos;
    ci_mfb_eof_pos <= reg0_mfb_eof_pos;
    ci_mfb_src_rdy <= reg0_mfb_src_rdy;
    reg0_mfb_dst_rdy <= ci_mfb_dst_rdy;

    -- =========================================================================
    --  EOF AND EOF_POS CALCULATION LOGIC
    -- =========================================================================

    ci_mfb_eof_pos_arr <= slv_array_deser(ci_mfb_eof_pos,MFB_REGIONS,MFB_EOF_POS_W);

    ci_mfb_eof_new_g : for i in 0 to MFB_REGIONS-1 generate
        ci_mfb_eof_pos_plus_arr(i)  <= std_logic_vector(unsigned(ci_mfb_eof_pos_arr(i)) + to_unsigned(4,MFB_EOF_POS_W+1));
        ci_mfb_eof_pos_over(i+1)    <= ci_mfb_eof_pos_plus_arr(i)(MFB_EOF_POS_W) and ci_mfb_eof(i);
        ci_mfb_eof_pos_val_arr(i+1) <= ci_mfb_eof_pos_plus_arr(i)(MFB_EOF_POS_W-1 downto 0);

        process (all)
        begin
            ci_mfb_eof_new(i) <= ci_mfb_eof(i);
            ci_mfb_eof_pos_new_arr(i) <= ci_mfb_eof_pos_val_arr(i+1);

            -- EOF in current region overflowed to next region
            if (ci_mfb_eof_pos_over(i+1) = '1') then
                ci_mfb_eof_new(i) <= '0';
            end if;

            -- EOF from previous region overflowed to current region
            if (ci_mfb_eof_pos_over(i) = '1') then
                ci_mfb_eof_new(i) <= '1';
                ci_mfb_eof_pos_new_arr(i) <= ci_mfb_eof_pos_val_arr(i);
            end if;
        end process;
    end generate;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                ci_mfb_eof_pos_over(0) <= '0';
            elsif (ci_mfb_dst_rdy = '1') then
                ci_mfb_eof_pos_over(0) <= ci_mfb_eof_pos_over(MFB_REGIONS);
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (ci_mfb_dst_rdy = '1') then
                ci_mfb_eof_pos_val_arr(0) <= ci_mfb_eof_pos_val_arr(MFB_REGIONS);
            end if;
        end if;
    end process;

    ci_mfb_eof_pos_new <= slv_array_ser(ci_mfb_eof_pos_new_arr,MFB_REGIONS,MFB_EOF_POS_W);

    ci_inc_region_g : for r in 0 to MFB_REGIONS-1 generate
        ci_inc_region(r+1) <= (ci_mfb_sof(r) and not ci_mfb_eof_new(r) and not ci_inc_region(r)) or
            (ci_mfb_sof(r) and ci_mfb_eof_new(r) and ci_inc_region(r)) or
            (not ci_mfb_sof(r) and not ci_mfb_eof_new(r) and ci_inc_region(r));
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                ci_inc_region(0) <= '0';
            elsif (ci_mfb_dst_rdy = '1') then
                ci_inc_region(0) <= ci_inc_region(MFB_REGIONS);
            end if;
        end if;
    end process;

    ci_mfb_src_rdy_new <= ci_inc_region(0) or (or ci_mfb_sof);

    -- =========================================================================
    --  OUTPUT REGISTERS
    -- =========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (ci_mfb_dst_rdy = '1') then
                TX_MFB_DATA    <= ci_mfb_data;
                TX_MFB_SOF     <= ci_mfb_sof;
                TX_MFB_EOF     <= ci_mfb_eof_new;
                TX_MFB_SOF_POS <= ci_mfb_sof_pos;
                TX_MFB_EOF_POS <= ci_mfb_eof_pos_new;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                TX_MFB_SRC_RDY <= '0';
            elsif (ci_mfb_dst_rdy = '1') then
                TX_MFB_SRC_RDY <= ci_mfb_src_rdy_new;
            end if;
        end if;
    end process;

    ci_mfb_dst_rdy <= TX_MFB_DST_RDY;

end architecture;
