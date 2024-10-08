-- buffer.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_BUFFER is
    generic(
        REGIONS        : natural := 4;
        REGION_SIZE    : natural := 8;
        BLOCK_SIZE     : natural := 8;
        ITEM_WIDTH     : natural := 8;
        META_WIDTH     : natural := 16;
        META_ALIGN2SOF : boolean := True;
        DFIFO_ITEMS    : natural := 512;
        MFIFO_ITEMS    : natural := 2048;
        MFIFO_RAM_TYPE : string  := "BRAM";
        DEVICE         : string  := "STRATIX10"
    );
   port(
        -- =====================================================================
        -- INPUT INTERFACES
        -- =====================================================================
        -- CLOCK AND RESET
        -- ---------------------------------------------------------------------
        RX_CLK          : in  std_logic;
        RX_RESET        : in  std_logic;

        -- MFB BUS WITH METADATA AND ERROR FLAG (ALIGNED TO EOF)
        -- ---------------------------------------------------------------------
        RX_DATA         : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS      : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS      : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF          : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF          : in  std_logic_vector(REGIONS-1 downto 0);
        RX_ERROR        : in  std_logic_vector(REGIONS-1 downto 0) := (others => '0');
        RX_METADATA     : in  slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
        RX_SRC_RDY      : in  std_logic;

        -- STATISTICS OUTPUT
        -- ---------------------------------------------------------------------
        BUFFER_STATUS   : out std_logic_vector(2-1 downto 0);
        STAT_BUFFER_OVF : out std_logic_vector(REGIONS-1 downto 0);
        STAT_DISCARD    : out std_logic_vector(REGIONS-1 downto 0);
        STAT_METADATA   : out slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
        STAT_VALID      : out std_logic_vector(REGIONS-1 downto 0);

        -- =====================================================================
        -- OUTPUT INTERFACES
        -- =====================================================================
        -- CLOCK AND RESET
        -- ---------------------------------------------------------------------
        TX_CLK          : in  std_logic;
        TX_RESET        : in  std_logic;

        -- MFB BUS
        -- ---------------------------------------------------------------------
        TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic;

        -- MVB BUS
        -- ---------------------------------------------------------------------
        TX_MVB_DATA     : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_BUFFER is

    constant SOF_INDEX_WIDTH : natural := log2(REGIONS);
    constant MBUF_WIDTH      : natural := META_WIDTH;--+SOF_INDEX_WIDTH+1+1;

    type fsm_t is (st_idle, st_last_word, st_overfull);

    signal s_inc_frame          : std_logic_vector(REGIONS downto 0);
    signal s_inc_frame_reg      : std_logic;
    signal s_whole_frame        : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_word_end_ok     : std_logic;
    signal s_rx_rdy2recovery    : std_logic;
    signal s_rx_without_sof     : std_logic;
    signal s_rx_first_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_pos_arr     : slv_array_t(REGIONS-1 downto 0)(max(1,log2(REGION_SIZE))-1 downto 0);
    signal s_rx_eof_pos_arr     : slv_array_t(REGIONS-1 downto 0)(max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal s_full_flag          : std_logic;

    signal fsm_pst              : fsm_t;
    signal fsm_nst              : fsm_t;
    signal s_rx_sof_mod         : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_mod         : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_pos_mod     : slv_array_t(REGIONS-1 downto 0)(max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal s_rx_src_rdy_mod     : std_logic;
    signal s_rx_force_drop      : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_data_reg        : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_rx_sof_pos_reg     : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal s_rx_eof_pos_reg     : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal s_rx_sof_reg         : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_reg         : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_error_reg       : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_metadata_reg    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_rx_src_rdy_reg     : std_logic;
    signal s_whole_frame_reg    : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_force_drop_reg   : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_orig_reg     : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_src_rdy_orig_reg : std_logic;

    signal s_dbuf_rdy           : std_logic;
    signal s_dbuf_full          : std_logic;
    signal s_dbuf_discard       : std_logic_vector(REGIONS-1 downto 0);
    signal s_dbuf_ovf_err_reg   : std_logic;
    signal s_dbuf_afull_reg     : std_logic;
    signal s_dbuf_status        : std_logic_vector(log2(DFIFO_ITEMS) downto 0);

    signal s_mbuf_din           : std_logic_vector(REGIONS*MBUF_WIDTH-1 downto 0);
    signal s_mbuf_vld           : std_logic_vector(REGIONS-1 downto 0);
    signal s_mbuf_src_rdy       : std_logic;
    signal s_mbuf_dst_rdy       : std_logic;
    signal s_mbuf_ovf_err_reg   : std_logic;
    signal s_mbuf_status        : std_logic_vector(log2(MFIFO_ITEMS) downto 0);
    signal s_mbuf_afull         : std_logic;
    signal s_mbuf_afull_reg     : std_logic;
    signal s_mbuf_afull_reg2    : std_logic;
    signal s_mbuf_dout_ser      : std_logic_vector(REGIONS*MBUF_WIDTH-1 downto 0);
    signal s_mbuf_mvb_vld       : std_logic_vector(REGIONS-1 downto 0);
    signal s_mbuf_mvb_src_rdy   : std_logic;
    signal s_mbuf_mvb_dst_rdy   : std_logic;

    signal s_mfb_error     : std_logic_vector(REGIONS-1 downto 0);
    signal s_mfb_error_reg : std_logic;

    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of s_mfb_error : signal is true;
    attribute preserve_for_debug of s_mfb_error_reg : signal is true;

begin

    -- -------------------------------------------------------------------------
    --  FRAME STATE LOGIC
    -- -------------------------------------------------------------------------

    inc_frame_g : for r in 0 to REGIONS-1 generate
        s_inc_frame(r+1) <= (RX_SOF(r) and not RX_EOF(r) and not s_inc_frame(r)) or
                            (RX_SOF(r) and RX_EOF(r) and s_inc_frame(r)) or
                            (not RX_SOF(r) and not RX_EOF(r) and s_inc_frame(r));

        s_mfb_error(r) <= (RX_SOF(r) and not RX_EOF(r) and s_inc_frame(r)) or
                          (not RX_SOF(r) and RX_EOF(r) and not s_inc_frame(r));
    end generate;

    inc_frame_last_reg_p : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_inc_frame(0)  <= '0';
                s_inc_frame_reg <= '0';
                s_mfb_error_reg <= '0';
            elsif (RX_SRC_RDY = '1') then
                s_inc_frame(0)  <= s_inc_frame(REGIONS);
                s_inc_frame_reg <= s_inc_frame(REGIONS); -- register duplication for better timing
                s_mfb_error_reg <= (or s_mfb_error);
            end if;
        end if;
    end process;

    s_whole_frame <= RX_SOF and RX_EOF and not s_inc_frame(REGIONS-1 downto 0);

    -- -------------------------------------------------------------------------
    --  AFTER BUFFER OVERFULL RECOVERY LOGIC
    -- -------------------------------------------------------------------------

    s_rx_word_end_ok  <= (not s_inc_frame(REGIONS) and RX_SRC_RDY) or (not s_inc_frame_reg and not RX_SRC_RDY);
    s_rx_rdy2recovery <= ((RX_SRC_RDY and (or RX_EOF)) or (not RX_SRC_RDY and not s_inc_frame_reg));
    s_rx_without_sof  <= not (or RX_SOF);

    process (all)
    begin
        s_rx_first_eof <= (others => '0');
        for r in 0 to REGIONS-1 loop
            if (RX_EOF(r) = '1') then
                s_rx_first_eof(r) <= RX_SRC_RDY and s_inc_frame_reg;
                exit;
            end if;
        end loop;
    end process;

    s_rx_sof_pos_arr <= slv_array_deser(RX_SOF_POS, REGIONS);
    s_rx_eof_pos_arr <= slv_array_deser(RX_EOF_POS, REGIONS);

    s_full_flag <= s_dbuf_afull_reg or s_mbuf_afull_reg2;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            fsm_pst <= fsm_nst;
            if (RX_RESET = '1') then
                fsm_pst <= st_idle;
            end if;
        end if;
    end process;

    process (all)
    begin
        fsm_nst <= fsm_pst;
        s_rx_sof_mod     <= RX_SOF;
        s_rx_eof_mod     <= RX_EOF;
        s_rx_eof_pos_mod <= s_rx_eof_pos_arr;
        s_rx_src_rdy_mod <= RX_SRC_RDY;
        s_rx_force_drop  <= (others => '0');

        case (fsm_pst) is
            when st_idle =>
                if (s_full_flag = '1') then
                    fsm_nst <= st_last_word;
                end if;

            when st_last_word =>
                s_rx_sof_mod <= RX_SOF and RX_SRC_RDY;
                s_rx_eof_mod <= RX_EOF and RX_SRC_RDY;
                s_rx_src_rdy_mod <= RX_SRC_RDY;
                if (s_rx_word_end_ok = '0') then -- force end is needed
                    -- discard the last SOF if an EOF exists in the last region
                    s_rx_sof_mod(REGIONS-1)     <= (RX_SOF(REGIONS-1) and RX_SRC_RDY) and not (RX_EOF(REGIONS-1) and RX_SRC_RDY);
                    s_rx_eof_mod(REGIONS-1)     <= '1'; -- force end in the last region ...
                    s_rx_eof_pos_mod(REGIONS-1) <= (others => '1'); -- ... and the last byte to truncate the packet at the very end of the word
                    s_rx_force_drop(REGIONS-1)  <= '1'; -- mark the packet to be dropped (valid with EOF)
                    s_rx_src_rdy_mod <= '1';
                end if;
                fsm_nst <= st_overfull;

            when st_overfull =>
                s_rx_force_drop  <= (others => '1');
                s_rx_src_rdy_mod <= '0';
                if (s_rx_rdy2recovery = '1' and s_full_flag = '0') then
                    s_rx_force_drop  <= s_rx_first_eof;
                    s_rx_eof_mod     <= RX_EOF and not s_rx_first_eof; -- discard first the EOF if it ever arrives
                    s_rx_src_rdy_mod <= RX_SRC_RDY and not s_rx_without_sof; -- clear word without any SOF
                    fsm_nst          <= st_idle;
                end if;
        end case;
    end process;

    -- -------------------------------------------------------------------------
    --  REGISTER STAGE
    -- -------------------------------------------------------------------------

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            s_rx_data_reg        <= RX_DATA;
            s_rx_sof_reg         <= s_rx_sof_mod;
            s_rx_sof_pos_reg     <= slv_array_ser(s_rx_sof_pos_arr);
            s_rx_eof_reg         <= s_rx_eof_mod;
            s_rx_eof_orig_reg    <= RX_EOF;
            s_rx_eof_pos_reg     <= slv_array_ser(s_rx_eof_pos_mod);
            s_rx_error_reg       <= RX_ERROR;
            s_rx_metadata_reg    <= RX_METADATA;
            s_rx_force_drop_reg  <= s_rx_force_drop;
            s_whole_frame_reg    <= s_whole_frame;
        end if;
    end process;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_rx_src_rdy_reg      <= '0';
                s_rx_src_rdy_orig_reg <= '0';
            else
                s_rx_src_rdy_reg      <= s_rx_src_rdy_mod;
                s_rx_src_rdy_orig_reg <= RX_SRC_RDY;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  FIFOs CONTROL LOGIC
    -- -------------------------------------------------------------------------

    s_dbuf_full    <= not s_dbuf_rdy;
    s_dbuf_discard <= s_rx_error_reg or s_rx_force_drop_reg;

    buffer_status_reg_p : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            BUFFER_STATUS(0) <= s_mbuf_afull_reg2 and s_rx_src_rdy_orig_reg;
            BUFFER_STATUS(1) <= s_dbuf_full and s_rx_src_rdy_orig_reg;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  STATISTICS OUTPUT
    -- -------------------------------------------------------------------------

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            STAT_BUFFER_OVF <= (s_rx_src_rdy_orig_reg and s_rx_eof_orig_reg) and s_rx_force_drop_reg;
            STAT_DISCARD    <= (s_rx_src_rdy_orig_reg and s_rx_eof_orig_reg) and (s_rx_error_reg or s_rx_force_drop_reg);
            STAT_METADATA   <= s_rx_metadata_reg;
            STAT_VALID      <= s_rx_src_rdy_orig_reg and s_rx_eof_orig_reg;
            if (RX_RESET = '1') then
                STAT_VALID <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  DATA and META BUFFER
    -- -------------------------------------------------------------------------

    dbuf_i : entity work.MFB_PD_ASFIFO_SIMPLE
    generic map(
        MFB_REGIONS     => REGIONS,
        MFB_REGION_SIZE => REGION_SIZE,
        MFB_BLOCK_SIZE  => BLOCK_SIZE,
        MFB_ITEM_WIDTH  => ITEM_WIDTH,
        FIFO_ITEMS      => DFIFO_ITEMS,
        DEVICE          => DEVICE
    )
    port map(
        RX_CLK           => RX_CLK,
        RX_RESET         => RX_RESET,

        RX_DATA          => s_rx_data_reg,
        RX_SOF_POS       => s_rx_sof_pos_reg,
        RX_EOF_POS       => s_rx_eof_pos_reg,
        RX_SOF           => s_rx_sof_reg,
        RX_EOF           => s_rx_eof_reg,
        RX_SRC_RDY       => s_rx_src_rdy_reg,
        RX_DST_RDY       => s_dbuf_rdy,
        RX_DISCARD       => s_dbuf_discard,
        RX_AFULL         => open,
        RX_STATUS        => s_dbuf_status,

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

    process (RX_CLK, TX_RESET)
    begin
        if (TX_RESET = '1') then
            s_dbuf_ovf_err_reg <= '0';
        elsif (rising_edge(RX_CLK)) then
            if (s_dbuf_rdy = '0' and s_rx_src_rdy_reg = '1') then
                s_dbuf_ovf_err_reg <= '1';
            end if;
            if (RX_RESET = '1') then
                s_dbuf_ovf_err_reg <= '0';
            end if;
        end if;
    end process;

    assert (s_dbuf_ovf_err_reg /= '1')
       report "RX_MAC_LITE_BUFFER: Ilegal wite to full dbuf_i FIFO!"
       severity failure;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_dbuf_afull_reg <= '1';
            elsif (unsigned(s_dbuf_status) >= (DFIFO_ITEMS - 8)) then
                s_dbuf_afull_reg <= '1';
            elsif ((unsigned(s_dbuf_status) < (DFIFO_ITEMS/2)) and s_dbuf_rdy = '1') then
                s_dbuf_afull_reg <= '0';
            end if;
        end if;
    end process;

    s_mbuf_din     <= slv_array_ser(s_rx_metadata_reg);
    s_mbuf_vld     <= s_rx_eof_reg and not s_dbuf_discard and s_rx_src_rdy_reg;
    s_mbuf_src_rdy <= or s_mbuf_vld;

    mbuf_i : entity work.MVB_ASFIFOX
    generic map(
        MVB_ITEMS      => REGIONS,
        MVB_ITEM_WIDTH => MBUF_WIDTH,
        FIFO_ITEMS     => MFIFO_ITEMS,
        RAM_TYPE       => MFIFO_RAM_TYPE,
        FWFT_MODE      => True,
        OUTPUT_REG     => True,
        DEVICE         => DEVICE
    )
    port map(
        RX_CLK     => RX_CLK,
        RX_RESET   => RX_RESET,
        RX_DATA    => s_mbuf_din,
        RX_VLD     => s_mbuf_vld,
        RX_SRC_RDY => s_mbuf_src_rdy,
        RX_DST_RDY => s_mbuf_dst_rdy,
        RX_AFULL   => open,
        RX_STATUS  => s_mbuf_status,

        TX_CLK     => TX_CLK,
        TX_RESET   => TX_RESET,
        TX_DATA    => s_mbuf_dout_ser,
        TX_VLD     => s_mbuf_mvb_vld,
        TX_SRC_RDY => s_mbuf_mvb_src_rdy,
        TX_DST_RDY => s_mbuf_mvb_dst_rdy
    );

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (s_mbuf_dst_rdy = '0' and s_mbuf_src_rdy = '1') then
                s_mbuf_ovf_err_reg <= '1';
            end if;
            if (RX_RESET = '1') then
                s_mbuf_ovf_err_reg <= '0';
            end if;
        end if;
    end process;

    assert (s_mbuf_ovf_err_reg /= '1')
       report "RX_MAC_LITE_BUFFER: Ilegal wite to full mbuf_i FIFO!"
       severity failure;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_mbuf_afull <= '1';
            elsif (unsigned(s_mbuf_status) >= (MFIFO_ITEMS-6)) then
                s_mbuf_afull <= '1';
            elsif ((unsigned(s_mbuf_status) < (MFIFO_ITEMS-MFIFO_ITEMS/4)) and s_mbuf_dst_rdy = '1') then
                s_mbuf_afull <= '0';
            end if;
        end if;
    end process;

    mbuf_afull_reg_p : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_mbuf_afull_reg  <= '1';
                s_mbuf_afull_reg2 <= '1';
            else
                s_mbuf_afull_reg  <= s_mbuf_afull;
                s_mbuf_afull_reg2 <= s_mbuf_afull_reg;
            end if;
        end if;
    end process;

    TX_MVB_DATA        <= s_mbuf_dout_ser;
    TX_MVB_VLD         <= s_mbuf_mvb_vld;
    TX_MVB_SRC_RDY     <= s_mbuf_mvb_src_rdy;
    s_mbuf_mvb_dst_rdy <= TX_MVB_DST_RDY;

end architecture;
