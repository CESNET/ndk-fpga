-- tx_lbus.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_ADAPTER_LBUS is
    generic(
        -- REGIONS must be 1
        REGIONS     : natural := 1;
        -- REGION_SIZE must be 8
        REGION_SIZE : natural := 8;
        -- SEGMENTS must be REGION_SIZE/2
        SEGMENTS    : natural := REGION_SIZE/2;
        -- Select correct FPGA device.
        DEVICE      : string  := "ULTRASCALE"
    );
    port(
        -- CLOCK AND RESET
        CLK            : in  std_logic;
        RESET          : in  std_logic;
        -- INPUT MFB (allowed MFB configurations: 1,REGION_SIZE,8,8)
        IN_MFB_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        IN_MFB_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        IN_MFB_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_EOF_POS : in  std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        IN_MFB_SRC_RDY : in  std_logic;
        IN_MFB_DST_RDY : out std_logic;
        -- OUTPUT LBUS
        OUT_LBUS_DATA  : out slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
        OUT_LBUS_MTY   : out slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
        OUT_LBUS_ENA   : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_LBUS_SOP   : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_LBUS_EOP   : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_LBUS_ERR   : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_LBUS_RDY   : in  std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ADAPTER_LBUS is

    constant BYTES : natural := 128/8;

    signal reconf_mfb_data     : std_logic_vector(REGIONS*SEGMENTS*128-1 downto 0);
    signal reconf_mfb_sof      : std_logic_vector(REGIONS-1 downto 0);
    signal reconf_mfb_sof_pos  : std_logic_vector(REGIONS*max(1,log2(SEGMENTS))-1 downto 0);
    signal reconf_mfb_eof      : std_logic_vector(REGIONS-1 downto 0);
    signal reconf_mfb_eof_pos  : std_logic_vector(REGIONS*log2(SEGMENTS*16)-1 downto 0);
    signal reconf_mfb_src_rdy  : std_logic;
    signal reconf_mfb_dst_rdy  : std_logic;

    signal reconf2_mfb_data    : std_logic_vector(REGIONS*SEGMENTS*128-1 downto 0);
    signal reconf2_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal reconf2_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(SEGMENTS))-1 downto 0);
    signal reconf2_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal reconf2_mfb_eof_pos : std_logic_vector(REGIONS*log2(SEGMENTS*16)-1 downto 0);
    signal reconf2_mfb_src_rdy : std_logic;
    signal reconf2_mfb_dst_rdy : std_logic;

    signal align_mfb_data      : std_logic_vector(REGIONS*SEGMENTS*128-1 downto 0);
    signal align_mfb_sof       : std_logic_vector(REGIONS-1 downto 0);
    signal align_mfb_sof_pos   : std_logic_vector(REGIONS*max(1,log2(SEGMENTS))-1 downto 0);
    signal align_mfb_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal align_mfb_eof_pos   : std_logic_vector(REGIONS*log2(SEGMENTS*16)-1 downto 0);
    signal align_mfb_src_rdy   : std_logic;
    signal align_mfb_dst_rdy   : std_logic;
    signal align_mfb_block_vld : std_logic_vector(REGIONS*SEGMENTS-1 downto 0);

    signal lbus_rdy_reg        : std_logic;
    signal lbus_data_comb      : slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
    signal lbus_data_rot       : slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
    signal lbus_sop_comb       : std_logic_vector(SEGMENTS-1 downto 0);
    signal lbus_eop_comb       : std_logic_vector(SEGMENTS-1 downto 0);
    signal lbus_mty_common     : unsigned(4-1 downto 0);
    signal lbus_mty_comb       : slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
    signal lbus_ena_comb       : std_logic_vector(SEGMENTS-1 downto 0);

begin

    -- -------------------------------------------------------------------------
    --  FRAMES REALIGN TO 128b SEGMENTS
    -- -------------------------------------------------------------------------

    mfb_to_lbus_reconf_i : entity work.MFB_TO_LBUS_RECONF
    port map(
        CLK        => CLK,
        RST        => RESET,

        RX_MFB_DATA    => IN_MFB_DATA,
        RX_MFB_SOF     => IN_MFB_SOF(0),
        RX_MFB_EOF     => IN_MFB_EOF(0),
        RX_MFB_SOF_POS => IN_MFB_SOF_POS,
        RX_MFB_EOF_POS => IN_MFB_EOF_POS,
        RX_MFB_SRC_RDY => IN_MFB_SRC_RDY,
        RX_MFB_DST_RDY => IN_MFB_DST_RDY,

        TX_MFB_DATA    => reconf_mfb_data,
        TX_MFB_SOF     => reconf_mfb_sof(0),
        TX_MFB_EOF     => reconf_mfb_eof(0),
        TX_MFB_SOF_POS => reconf_mfb_sof_pos,
        TX_MFB_EOF_POS => reconf_mfb_eof_pos,
        TX_MFB_SRC_RDY => reconf_mfb_src_rdy,
        TX_MFB_DST_RDY => reconf_mfb_dst_rdy
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (reconf_mfb_dst_rdy = '1') then
                reconf2_mfb_data    <= reconf_mfb_data;
                reconf2_mfb_sof     <= reconf_mfb_sof;
                reconf2_mfb_eof     <= reconf_mfb_eof;
                reconf2_mfb_sof_pos <= reconf_mfb_sof_pos;
                reconf2_mfb_eof_pos <= reconf_mfb_eof_pos;
                reconf2_mfb_src_rdy <= reconf_mfb_src_rdy;
            end if;
            if (RESET = '1') then
                reconf2_mfb_src_rdy <= '0';
            end if;
        end if;
    end process;

    mfb_aux_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => SEGMENTS,
        BLOCK_SIZE     => 16,
        ITEM_WIDTH     => 8,
        META_WIDTH     => 2,
        REGION_AUX_EN  => false,
        BLOCK_AUX_EN   => true,
        ITEM_AUX_EN    => false
    )
    port map(
        CLK              => CLK,
        RESET            => RESET,

        RX_DATA          => reconf2_mfb_data,
        RX_META          => (others => '0'),
        RX_SOF           => reconf2_mfb_sof,
        RX_EOF           => reconf2_mfb_eof,
        RX_SOF_POS       => reconf2_mfb_sof_pos,
        RX_EOF_POS       => reconf2_mfb_eof_pos,
        RX_SRC_RDY       => reconf2_mfb_src_rdy,
        RX_DST_RDY       => reconf_mfb_dst_rdy,

        TX_DATA          => align_mfb_data,
        TX_META          => open,
        TX_SOF           => align_mfb_sof,
        TX_EOF           => align_mfb_eof,
        TX_SOF_POS       => align_mfb_sof_pos,
        TX_EOF_POS       => align_mfb_eof_pos,
        TX_SRC_RDY       => align_mfb_src_rdy,
        TX_DST_RDY       => align_mfb_dst_rdy,

        TX_REGION_SHARED => open,
        TX_REGION_VLD    => open,
        TX_BLOCK_VLD     => align_mfb_block_vld,
        TX_ITEM_VLD      => open
    );

    -- -------------------------------------------------------------------------
    --  CONVERSION TO LBUS
    -- -------------------------------------------------------------------------

    align_mfb_dst_rdy <= lbus_rdy_reg;

    process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                lbus_rdy_reg <= '0';
            else
                lbus_rdy_reg <= OUT_LBUS_RDY;
            end if;
        end if;
    end process;

    lbus_data_comb <= slv_array_deser(align_mfb_data,SEGMENTS,128);

    data_rot_g : for s in 0 to SEGMENTS-1 generate
        data_rot_g2 : for i in 0 to BYTES-1 generate
            lbus_data_rot(s)((BYTES-1-i+1)*8-1 downto (BYTES-1-i)*8) <= lbus_data_comb(s)((i+1)*8-1 downto i*8);
        end generate;
    end generate;

    process (all)
    begin
        lbus_sop_comb <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (to_integer(unsigned(align_mfb_sof_pos)) = i) then
                lbus_sop_comb(i) <= align_mfb_sof(0);
            end if;
        end loop;
    end process;

    lbus_mty_common <= (15 - unsigned(align_mfb_eof_pos(align_mfb_eof_pos'length-log2(SEGMENTS)-1 downto 0)));

    process (all)
    begin
        lbus_eop_comb <= (others => '0');
        lbus_mty_comb <= (others => (others => '0'));
        for i in 0 to SEGMENTS-1 loop
            if (to_integer(unsigned(align_mfb_eof_pos(align_mfb_eof_pos'length-1 downto align_mfb_eof_pos'length-log2(SEGMENTS)))) = i) then
                lbus_eop_comb(i) <= align_mfb_eof(0);
                lbus_mty_comb(i) <= std_logic_vector(lbus_mty_common);
            end if;
        end loop;
    end process;

    lbus_ena_comb <= align_mfb_block_vld and align_mfb_src_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- Up to four valid (OUT_LBUS_ENA) cycles might be safely performed
            -- after OUT_LBUS_RDY is negated, then OUT_LBUS_ENA must be in low.
            OUT_LBUS_ENA <= (others => '0');
            if (lbus_rdy_reg = '1') then
                OUT_LBUS_DATA <= lbus_data_rot;
                OUT_LBUS_MTY  <= lbus_mty_comb;
                OUT_LBUS_ENA  <= lbus_ena_comb;
                OUT_LBUS_SOP  <= lbus_sop_comb;
                OUT_LBUS_EOP  <= lbus_eop_comb;
            end if;
            if (RESET = '1') then
                OUT_LBUS_ENA <= (others => '0');
            end if;
        end if;
    end process;

    OUT_LBUS_ERR <= (others => '0');

end architecture;
