-- tx_saxis.vhd: Adapter between MFB and Segmented AXI-Stream
-- Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
--           (C) 2022 CESNET z. s. p. o.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
--            Jakub Cabal <cabal@cesnet.cz>
-- Adapted from component TX_MAC_LITE_ADAPTER_LBUS as Segmented AXI-Stream is
-- very similar to LBUS.
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_ADAPTER_SAXIS is
    generic (
        -- REGIONS must be 1
        REGIONS     : natural := 1;
        -- REGION_SIZE must be 8
        REGION_SIZE : natural := 8;
        -- SEGMENTS must be REGION_SIZE/2
        SEGMENTS    : natural := REGION_SIZE/2;
        -- Select correct FPGA device.
        DEVICE      : string  := "VERSAL"
    );
    port (
        -- CLOCK AND RESET
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- INPUT MFB (allowed MFB configuration: 1,8,8,8)
        IN_MFB_DATA      : in  std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        IN_MFB_SOF       : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_SOF_POS   : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        IN_MFB_EOF       : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_EOF_POS   : in  std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        IN_MFB_SRC_RDY   : in  std_logic;
        IN_MFB_DST_RDY   : out std_logic;
        -- OUTPUT Segmented AXI-Stream
        OUT_SAXIS_DATA   : out slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
        OUT_SAXIS_MTY    : out slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
        OUT_SAXIS_ENA    : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_SAXIS_SOP    : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_SAXIS_EOP    : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_SAXIS_ERR    : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_SAXIS_VALID  : out std_logic;
        OUT_SAXIS_READY  : in  std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ADAPTER_SAXIS is

    -- Checked in the declarative part, before MFB_TO_LBUS_RECONF with its fixed 512b ports is elaborated
    function check_generics return boolean is
    begin
        assert REGIONS = 1
            report "TX_MAC_LITE_ADAPTER_SAXIS: REGIONS generic must be 1. Actual value is: " & natural'image(REGIONS)
            severity failure;
        assert REGION_SIZE = 8
            report "TX_MAC_LITE_ADAPTER_SAXIS: REGION_SIZE generic must be 8. Actual value is: " & natural'image(REGION_SIZE)
            severity failure;
        assert SEGMENTS = REGION_SIZE/2
            report "TX_MAC_LITE_ADAPTER_SAXIS: SEGMENTS generic must be REGION_SIZE/2 (" & natural'image(REGION_SIZE/2) & "). Actual value is: " & natural'image(SEGMENTS)
            severity failure;
        return true;
    end function;

    constant GENERICS_OK : boolean := check_generics;

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

    signal saxis_data_comb      : slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
    signal saxis_sop_comb       : std_logic_vector(SEGMENTS-1 downto 0);
    signal saxis_eop_comb       : std_logic_vector(SEGMENTS-1 downto 0);
    signal saxis_mty_common     : unsigned(4-1 downto 0);
    signal saxis_mty_comb       : slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
    signal saxis_ena_comb       : std_logic_vector(SEGMENTS-1 downto 0);

begin
    -- Currently only 512b bus is supported - intended for 100G wide interface and 200G DCMAC variants.
    -- TODO: Add version of MFB_TO_LBUS_RECONF for 256b and 1024b variant. 256b variant is used for
    --       100G narrow interface and 1024b is used for 400G.

    -- -------------------------------------------------------------------------
    --  FRAMES REALIGN TO 128b SEGMENTS
    -- -------------------------------------------------------------------------

    mfb_to_saxis_reconf_i : entity work.MFB_TO_LBUS_RECONF
    port map (
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
    generic map (
        REGIONS        => REGIONS,
        REGION_SIZE    => SEGMENTS,
        BLOCK_SIZE     => 16,
        ITEM_WIDTH     => 8,
        META_WIDTH     => 2,
        REGION_AUX_EN  => false,
        BLOCK_AUX_EN   => true,
        ITEM_AUX_EN    => false
    )
    port map (
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
    --  CONVERSION TO SEGMENTED AXI-STREAM
    -- -------------------------------------------------------------------------

    -- The output register also loads when it is empty, so OUT_SAXIS_VALID
    -- does not wait for OUT_SAXIS_READY.
    align_mfb_dst_rdy <= OUT_SAXIS_READY or not OUT_SAXIS_VALID;

    -- DCMAC expects byte 0 of each segment in bits 7:0, so no byte rotation is needed (PG369).
    saxis_data_comb <= slv_array_deser(align_mfb_data,SEGMENTS,128);

    process (all)
    begin
        saxis_sop_comb <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (to_integer(unsigned(align_mfb_sof_pos)) = i) then
                saxis_sop_comb(i) <= align_mfb_sof(0);
            end if;
        end loop;
    end process;

    saxis_mty_common <= (15 - unsigned(align_mfb_eof_pos(align_mfb_eof_pos'length-log2(SEGMENTS)-1 downto 0)));

    process (all)
    begin
        saxis_eop_comb <= (others => '0');
        saxis_mty_comb <= (others => (others => '0'));
        for i in 0 to SEGMENTS-1 loop
            if (to_integer(unsigned(align_mfb_eof_pos(align_mfb_eof_pos'length-1 downto align_mfb_eof_pos'length-log2(SEGMENTS)))) = i) then
                saxis_eop_comb(i) <= align_mfb_eof(0);
                saxis_mty_comb(i) <= std_logic_vector(saxis_mty_common);
            end if;
        end loop;
    end process;

    saxis_ena_comb <= align_mfb_block_vld and align_mfb_src_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (align_mfb_dst_rdy = '1') then
                OUT_SAXIS_DATA  <= saxis_data_comb;
                OUT_SAXIS_MTY   <= saxis_mty_comb;
                OUT_SAXIS_ENA   <= saxis_ena_comb;
                OUT_SAXIS_SOP   <= saxis_sop_comb;
                OUT_SAXIS_EOP   <= saxis_eop_comb;
                OUT_SAXIS_VALID <= align_mfb_src_rdy;
            end if;
            if (RESET = '1') then
                OUT_SAXIS_VALID <= '0';
            end if;
        end if;
    end process;

    OUT_SAXIS_ERR <= (others => '0');

end architecture;
