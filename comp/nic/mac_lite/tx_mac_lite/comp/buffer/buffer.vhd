-- buffer.vhd: TX MAC Lite buffer
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_BUFFER is
    generic(
        -- Number of regions within a data word, must be power of 2.
        MFB_REGIONS        : natural := 4;
        -- Region size (in blocks).
        MFB_REGION_SIZE    : natural := 8;
        -- Block size (in items).
        MFB_BLOCK_SIZE     : natural := 8;
        -- Item width (in bits), must be 8.
        MFB_ITEM_WIDTH     : natural := 8;
        -- Width of length signals in bits.
        LENGTH_WIDTH       : natural := 16;
        -- Frame length is counted with CRC.
        FRAME_LEN_WITH_CRC : boolean := False;
        -- Number items of store and forward FIFO.
        FIFO_ITEMS         : natural := 512;
        -- FPGA device name.
        DEVICE             : string := "STRATIX10"
    );
    port(
        -- =====================================================================
        --  CLOCK AND RESET
        -- =====================================================================
        RX_CLK               : in  std_logic;
        TX_CLK               : in  std_logic;
        RX_RESET             : in  std_logic;
        TX_RESET             : in  std_logic;

        -- =====================================================================
        --  RX MFB STREAM (RX_CLK)
        -- =====================================================================
        RX_MFB_DATA          : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS       : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS       : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF           : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF           : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY       : in  std_logic;
        RX_MFB_DST_RDY       : out std_logic;

        -- =====================================================================
        --  TX MFB STREAM (TX_CLK)
        -- =====================================================================
        TX_MFB_DATA          : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY       : out std_logic;
        TX_MFB_DST_RDY       : in  std_logic;

        -- =====================================================================
        --  STATS INCREMENTS OUTPUT (TX_CLK)
        -- =====================================================================
        STAT_FRAME_LENGTH    : out std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
        STAT_FRAME_DISCARDED : out std_logic_vector(MFB_REGIONS-1 downto 0);
        STAT_FRAME_VLD       : out std_logic_vector(MFB_REGIONS-1 downto 0)
    );
end entity;

architecture FULL of TX_MAC_LITE_BUFFER is

    constant ST_ASFIFO_WIDTH : natural := MFB_REGIONS*(LENGTH_WIDTH+1+1);
    constant FRAME_LEN_MIN   : natural := tsel(FRAME_LEN_WITH_CRC,64,60);

    signal fl_mfb_data          : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal fl_mfb_sof_pos       : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal fl_mfb_eof_pos       : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal fl_mfb_sof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fl_mfb_eof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fl_mfb_src_rdy       : std_logic;
    signal fl_mfb_dst_rdy       : std_logic;

    signal fl_mfb_frame_len     : std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
    signal fl_mfb_frame_len_arr : slv_array_t(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal fl_mfb_undersize     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fl_mfb_discard       : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal st_asfifo_di         : std_logic_vector(ST_ASFIFO_WIDTH-1 downto 0);
    signal st_asfifo_wr         : std_logic;
    signal st_asfifo_full       : std_logic;
    signal st_asfifo_do         : std_logic_vector(ST_ASFIFO_WIDTH-1 downto 0);
    signal st_asfifo_empty      : std_logic;

    signal st_frame_length      : std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
    signal st_frame_discarded   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal st_frame_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);

begin

    mfb_frame_len_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS         => MFB_REGIONS,
        REGION_SIZE     => MFB_REGION_SIZE,
        BLOCK_SIZE      => MFB_BLOCK_SIZE,
        ITEM_WIDTH      => MFB_ITEM_WIDTH,
        META_WIDTH      => 1,

        LNG_WIDTH       => LENGTH_WIDTH,
        REG_BITMAP      => "111",
        IMPLEMENTATION  => "parallel"
    )
    port map(
        CLK          => RX_CLK,
        RESET        => RX_RESET,

        RX_DATA      => RX_MFB_DATA,
        RX_META      => (others => '0'),
        RX_SOF_POS   => RX_MFB_SOF_POS,
        RX_EOF_POS   => RX_MFB_EOF_POS,
        RX_SOF       => RX_MFB_SOF,
        RX_EOF       => RX_MFB_EOF,
        RX_SRC_RDY   => RX_MFB_SRC_RDY,
        RX_DST_RDY   => RX_MFB_DST_RDY,

        TX_DATA      => fl_mfb_data,
        TX_META      => open,
        TX_SOF_POS   => fl_mfb_sof_pos,
        TX_EOF_POS   => fl_mfb_eof_pos,
        TX_SOF       => fl_mfb_sof,
        TX_EOF       => fl_mfb_eof,
        TX_COF       => open,
        TX_TEMP_LNG  => open,
        TX_FRAME_LNG => fl_mfb_frame_len,
        TX_SRC_RDY   => fl_mfb_src_rdy,
        TX_DST_RDY   => fl_mfb_dst_rdy
    );

    fl_mfb_frame_len_arr <= slv_array_deser(fl_mfb_frame_len,MFB_REGIONS,LENGTH_WIDTH);

    fl_mfb_discard_g : for r in 0 to MFB_REGIONS-1 generate
        fl_mfb_undersize(r) <= '1' when (unsigned(fl_mfb_frame_len_arr(r)) < FRAME_LEN_MIN) else '0';
        fl_mfb_discard(r)   <= fl_mfb_undersize(r) and fl_mfb_eof(r) and fl_mfb_src_rdy;
    end generate;

    -- =========================================================================
    --  PACKET DISCARD ASFIFO
    -- =========================================================================

    pd_asfifo_i : entity work.MFB_PD_ASFIFO
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        ITEMS       => FIFO_ITEMS,
        DEVICE      => DEVICE
    )
    port map(
        RX_CLK           => RX_CLK,
        RX_RESET         => RX_RESET,

        RX_DATA          => fl_mfb_data,
        RX_SOF_POS       => fl_mfb_sof_pos,
        RX_EOF_POS       => fl_mfb_eof_pos,
        RX_SOF           => fl_mfb_sof,
        RX_EOF           => fl_mfb_eof,
        RX_SRC_RDY       => fl_mfb_src_rdy,
        RX_DST_RDY       => fl_mfb_dst_rdy,

        RX_DISCARD       => fl_mfb_discard,
        RX_FORCE_DISCARD => '0',
        STATUS           => open,

        TX_CLK           => TX_CLK,
        TX_RESET         => TX_RESET,

        TX_DATA          => TX_MFB_DATA,
        TX_SOF_POS       => TX_MFB_SOF_POS,
        TX_EOF_POS       => TX_MFB_EOF_POS,
        TX_SOF           => TX_MFB_SOF,
        TX_EOF           => TX_MFB_EOF,
        TX_SRC_RDY       => TX_MFB_SRC_RDY,
        TX_DST_RDY       => TX_MFB_DST_RDY
    );

    -- =========================================================================
    --  STATISTICS ASFIFO
    -- =========================================================================

    st_asfifo_di <= fl_mfb_frame_len & fl_mfb_undersize & fl_mfb_eof;
    st_asfifo_wr <= (or fl_mfb_eof) and fl_mfb_src_rdy and fl_mfb_dst_rdy;

    assert (not (st_asfifo_wr and st_asfifo_full))
        report "TX_MAC_LITE_BUFFER: Write to full ST_ASFIFO!"
        severity error;

    st_asfifo_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => ST_ASFIFO_WIDTH,
        ITEMS      => FIFO_ITEMS,
        RAM_TYPE   => "BRAM",
        FWFT_MODE  => False,
        OUTPUT_REG => True,
        DEVICE     => DEVICE
    )
    port map(
        WR_CLK    => RX_CLK,
        WR_RST    => RX_RESET,
        WR_DATA   => st_asfifo_di,
        WR_EN     => st_asfifo_wr,
        WR_FULL   => st_asfifo_full, -- for debug only
        WR_AFULL  => open,
        WR_STATUS => open,

        RD_CLK    => TX_CLK,
        RD_RST    => TX_RESET,
        RD_DATA   => st_asfifo_do,
        RD_EN     => '1',
        RD_EMPTY  => st_asfifo_empty,
        RD_AEMPTY => open,
        RD_STATUS => open
    );

    st_frame_length    <= st_asfifo_do(ST_ASFIFO_WIDTH-1 downto 2*MFB_REGIONS);
    st_frame_discarded <= st_asfifo_do(2*MFB_REGIONS-1 downto MFB_REGIONS);
    st_frame_vld       <= st_asfifo_do(MFB_REGIONS-1 downto 0) and not st_asfifo_empty;

    -- =========================================================================
    --  STATISTICS OUTPUT REGISTERS
    -- =========================================================================

    process (TX_CLK)
    begin
        if rising_edge(TX_CLK) then
            STAT_FRAME_LENGTH    <= st_frame_length;
            STAT_FRAME_DISCARDED <= st_frame_discarded;
            STAT_FRAME_VLD       <= st_frame_vld;
        end if;
    end process;

end architecture;
