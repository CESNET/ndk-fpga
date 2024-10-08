-- mfb_frame_extender_datamover.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_FRAME_EXTENDER_DATAMOVER is
    generic(
        REGIONS        : natural := 4;
        REGION_SIZE    : natural := 8;
        BLOCK_SIZE     : natural := 8;
        ITEM_WIDTH     : natural := 8;
        USERMETA_WIDTH : natural := 8;
        FIFO_DEPTH     : natural := 32;
        LEN_WIDTH      : natural := 14;
        DEVICE         : string  := "AGILEX"
    );
    port(
        CLK                 : in  std_logic;
        RESET               : in  std_logic;

        RX_CTRL_INSERT_MOVE : in  slv_array_t(REGIONS*REGION_SIZE-1 downto 0)(log2(REGIONS*REGION_SIZE)-1 downto 0);
        RX_CTRL_INSERT_MASK : in  std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);
        RX_CTRL_INSERT_VLD  : in  std_logic;
        RX_CTRL_USERMETA    : in  std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
        RX_CTRL_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_CTRL_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_CTRL_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_CTRL_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_CTRL_SRC_RDY     : in  std_logic;
        RX_CTRL_DST_RDY     : out std_logic;

        RX_MFB_DATA         : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS      : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS      : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF          : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF          : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SRC_RDY      : in  std_logic;
        RX_MFB_DST_RDY      : out std_logic;

        TX_MFB_DATA         : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_USERMETA     : out std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
        TX_MFB_SOF_POS      : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS      : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF          : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF          : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SRC_RDY      : out std_logic;
        TX_MFB_DST_RDY      : in  std_logic
    );
end entity;

architecture FULL of MFB_FRAME_EXTENDER_DATAMOVER is

    constant WORD_BLOCKS : natural := REGIONS*REGION_SIZE;
    constant BLOCK_WIDTH : natural := BLOCK_SIZE*ITEM_WIDTH;

    signal s_rx_data       : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_rx_valid      : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_rx_dst_rdy    : std_logic;

    signal s_rx_data_reg0  : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_rx_valid_reg0 : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal s_fifox_full    : std_logic;
    signal s_fifox_data    : std_logic_vector(WORD_BLOCKS*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_fifox_rd      : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_fifox_empty   : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_fifox_vld     : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal s_rx_data_arr   : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal s_last_addr     : unsigned(log2(WORD_BLOCKS)-1 downto 0);
    signal s_fifox_rdy     : std_logic;
    signal s_src_rdy       : std_logic;

    signal s_mux_sel_reg0  : slv_array_t(WORD_BLOCKS-1 downto 0)(log2(WORD_BLOCKS)-1 downto 0);
    signal s_data_reg0     : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_usermeta_reg0 : std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
    signal s_sof_pos_reg0  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal s_eof_pos_reg0  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal s_sof_reg0      : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg0      : std_logic_vector(REGIONS-1 downto 0);
    signal s_src_rdy_reg0  : std_logic;

    signal s_muxed_data    : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);

    signal s_data_reg1     : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_usermeta_reg1 : std_logic_vector(REGIONS*USERMETA_WIDTH-1 downto 0);
    signal s_sof_pos_reg1  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal s_eof_pos_reg1  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal s_sof_reg1      : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg1      : std_logic_vector(REGIONS-1 downto 0);
    signal s_src_rdy_reg1  : std_logic;

begin

    -- data block array
    s_rx_data <= slv_array_deser(RX_MFB_DATA, WORD_BLOCKS, BLOCK_SIZE*ITEM_WIDTH);

    -- -------------------------------------------------------------------------
    --  PAYLOAD BLOCK VALID
    -- -------------------------------------------------------------------------

    blk_vld_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS       => REGIONS,
        REGION_SIZE   => REGION_SIZE,
        BLOCK_SIZE    => BLOCK_SIZE,
        ITEM_WIDTH    => ITEM_WIDTH,
        META_WIDTH    => 2,
        REGION_AUX_EN => False,
        BLOCK_AUX_EN  => True,
        ITEM_AUX_EN   => False
    )
    port map(
        CLK              => CLK,
        RESET            => RESET,

        RX_DATA          => RX_MFB_DATA,
        RX_META          => (others => '0'),
        RX_SOF_POS       => RX_MFB_SOF_POS,
        RX_EOF_POS       => RX_MFB_EOF_POS,
        RX_SOF           => RX_MFB_SOF,
        RX_EOF           => RX_MFB_EOF,
        RX_SRC_RDY       => RX_MFB_SRC_RDY,
        RX_DST_RDY       => RX_MFB_DST_RDY,

        TX_DATA          => open,
        TX_META          => open,
        TX_SOF_POS       => open,
        TX_EOF_POS       => open,
        TX_SOF           => open,
        TX_EOF           => open,
        TX_SRC_RDY       => open,
        TX_DST_RDY       => s_rx_dst_rdy,

        TX_REGION_SHARED => open,
        TX_REGION_VLD    => open,
        TX_BLOCK_VLD     => s_rx_valid,
        TX_ITEM_VLD      => open
    );

    -- -------------------------------------------------------------------------
    --  PAYLOAD REGISTERS
    -- -------------------------------------------------------------------------

    process (CLK)
    begin
    if (rising_edge(CLK)) then
        if (s_rx_dst_rdy = '1') then
            s_rx_data_reg0 <= s_rx_data;
        end if;
    end if;
    end process;

    process (CLK)
    begin
    if (rising_edge(CLK)) then
        if (RESET = '1') then
            s_rx_valid_reg0 <= (others => '0');
        elsif (s_rx_dst_rdy = '1') then
            s_rx_valid_reg0 <= s_rx_valid and RX_MFB_SRC_RDY;
        end if;
    end if;
    end process;

    -- -------------------------------------------------------------------------
    --  PAYLOAD FIFOX MULTI
    -- -------------------------------------------------------------------------

    s_rx_dst_rdy <= not s_fifox_full;

    fifox_multi_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => BLOCK_SIZE*ITEM_WIDTH,
        ITEMS               => REGIONS*REGION_SIZE*FIFO_DEPTH,
        WRITE_PORTS         => REGIONS*REGION_SIZE,
        READ_PORTS          => REGIONS*REGION_SIZE,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        SAFE_READ_MODE      => false,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 1
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => slv_array_ser(s_rx_data_reg0),
        WR     => s_rx_valid_reg0,
        FULL   => s_fifox_full,
        AFULL  => open,

        DO     => s_fifox_data,
        RD     => s_fifox_rd,
        EMPTY  => s_fifox_empty,
        AEMPTY => open
    );

    s_fifox_vld <= not s_fifox_empty;

   -- ==========================================================================
   --  0. LOGIC STAGE
   -- ==========================================================================

   -- data block array, only for debug
   s_rx_data_arr <= slv_array_deser(s_fifox_data, WORD_BLOCKS, BLOCK_WIDTH);

   -- control of packet template destination ready
   RX_CTRL_DST_RDY <= (TX_MFB_DST_RDY and RX_CTRL_INSERT_VLD and s_fifox_rdy) or
                      (TX_MFB_DST_RDY and not RX_CTRL_INSERT_VLD) or
                      (not RX_CTRL_SRC_RDY);

   -- control of payload accept
   s_last_addr <= unsigned(RX_CTRL_INSERT_MOVE(REGIONS*REGION_SIZE-1));
   s_fifox_rdy <= s_fifox_vld(to_integer(s_last_addr));
   s_fifox_rd  <= RX_CTRL_INSERT_MASK and RX_CTRL_INSERT_VLD and TX_MFB_DST_RDY and s_fifox_rdy;

   -- control of output source ready
   s_src_rdy <= (RX_CTRL_SRC_RDY and RX_CTRL_INSERT_VLD and s_fifox_rdy) or
                (RX_CTRL_SRC_RDY and not RX_CTRL_INSERT_VLD);

    -- =========================================================================
    --  0. REGISTER STAGE
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                s_mux_sel_reg0  <= RX_CTRL_INSERT_MOVE;
                s_data_reg0     <= s_fifox_data;
                s_usermeta_reg0 <= RX_CTRL_USERMETA;
                s_sof_pos_reg0  <= RX_CTRL_SOF_POS;
                s_eof_pos_reg0  <= RX_CTRL_EOF_POS;
                s_sof_reg0      <= RX_CTRL_SOF;
                s_eof_reg0      <= RX_CTRL_EOF;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg0 <= '0';
            elsif (TX_MFB_DST_RDY = '1') then
                s_src_rdy_reg0 <= s_src_rdy;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  1. LOGIC STAGE
    -- =========================================================================

    block_mux_g : for i in 0 to WORD_BLOCKS-1 generate
        block_mux_i : entity work.GEN_MUX
        generic map(
            DATA_WIDTH => BLOCK_WIDTH,
            MUX_WIDTH  => i+1
        )
        port map(
            DATA_IN  => s_data_reg0((i+1)*BLOCK_WIDTH-1 downto 0),
            SEL      => s_mux_sel_reg0(i)(max(1,log2(i+1))-1 downto 0),
            DATA_OUT => s_muxed_data(i)
        );
    end generate;

   -- ==========================================================================
   --  1. REGISTER STAGE
   -- ==========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                s_data_reg1     <= slv_array_ser(s_muxed_data);
                s_usermeta_reg1 <= s_usermeta_reg0;
                s_sof_pos_reg1  <= s_sof_pos_reg0;
                s_eof_pos_reg1  <= s_eof_pos_reg0;
                s_sof_reg1      <= s_sof_reg0;
                s_eof_reg1      <= s_eof_reg0;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg1 <= '0';
            elsif (TX_MFB_DST_RDY = '1') then
                s_src_rdy_reg1 <= s_src_rdy_reg0;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  TX SIGNALS
    -- =========================================================================

    TX_MFB_DATA     <= s_data_reg1;
    TX_MFB_USERMETA <= s_usermeta_reg1;
    TX_MFB_SOF_POS  <= s_sof_pos_reg1;
    TX_MFB_EOF_POS  <= s_eof_pos_reg1;
    TX_MFB_SOF      <= s_sof_reg1;
    TX_MFB_EOF      <= s_eof_reg1;
    TX_MFB_SRC_RDY  <= s_src_rdy_reg1;

end architecture;
