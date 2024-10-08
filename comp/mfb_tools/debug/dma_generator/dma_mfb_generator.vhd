-- dma_mfb_generator.vhd: This is the next gen DMA generator.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity DMA_MFB_GENERATOR is
    Generic (
        -- number of regions in a data word
        REGIONS        : natural := 2;
        -- number of blocks in a region
        REGION_SIZE    : natural := 8;
        -- number of items in a block
        BLOCK_SIZE     : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH     : natural := 8;
        -- maximum supported packet MTU in bytes
        PKT_MTU        : natural := 16383;
        -- number of supported DMA channels
        DMA_CHANNELS   : natural := 32;
        -- size of NPP Header (in bytes)
        -- must not be greater than BLOCK_SIZE*ITEM_WIDTH/8
        NPP_HDR_SIZE   : natural := 4;
        -- width of User Header Metadata information
        HDR_META_WIDTH : natural := 12;
        -- enable inserting generated NPP Header
        -- at the start of each MFB frame
        HDR_INS_EN     : boolean := false;
        -- MI_CLK and CLK are the same
        -- set this to True to remove MI asynch conversion
        SAME_CLK       : boolean := false;
        -- MI PIPE enable
        MI_PIPE_EN     : boolean := true;
        -- FPGA device string
        DEVICE         : string  := "STRATIX10"
    );
    Port (
        -- ---------------------------------------------------------------------
        -- MI32 interface
        -- ---------------------------------------------------------------------
        -- Address space: see entity of subcomponent MFB_GENERATOR_MI32
        MI_CLK   : in  std_logic;
        MI_RESET : in  std_logic;
        MI_DWR   : in  std_logic_vector(31 downto 0);
        MI_ADDR  : in  std_logic_vector(31 downto 0);
        MI_BE    : in  std_logic_vector(3 downto 0); -- Not supported!
        MI_RD    : in  std_logic;
        MI_WR    : in  std_logic;
        MI_ARDY  : out std_logic;
        MI_DRD   : out std_logic_vector(31 downto 0);
        MI_DRDY  : out std_logic;

        -- ---------------------------------------------------------------------
        -- MFB+MVB interface to DMA module (to software)
        -- ---------------------------------------------------------------------
        CLK                : in  std_logic;
        RESET              : in  std_logic;
        -- MVB interface with DMA instructions
        INSTR_MVB_LEN      : out std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        INSTR_MVB_CHANNEL  : out std_logic_vector(REGIONS*log2(DMA_CHANNELS)-1 downto 0);
        INSTR_MVB_HDR_META : out std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
        INSTR_MVB_DISCARD  : out std_logic_vector(REGIONS*1-1 downto 0);
        INSTR_MVB_VLD      : out std_logic_vector(REGIONS-1 downto 0);
        INSTR_MVB_SRC_RDY  : out std_logic;
        INSTR_MVB_DST_RDY  : in  std_logic;
        -- MFB interface with data packets
        ETH_MFB_DATA       : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        ETH_MFB_SOF        : out std_logic_vector(REGIONS-1 downto 0);
        ETH_MFB_EOF        : out std_logic_vector(REGIONS-1 downto 0);
        ETH_MFB_SOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        ETH_MFB_EOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        ETH_MFB_SRC_RDY    : out std_logic;
        ETH_MFB_DST_RDY    : in  std_logic
    );
end entity;

architecture FULL of DMA_MFB_GENERATOR is

    constant LENGTH_WIDTH       : natural := log2(PKT_MTU+1);
    constant DMA_CHANNELS_WIDTH : natural := log2(DMA_CHANNELS);

    constant BLOCK_WIDTH  : natural := BLOCK_SIZE*ITEM_WIDTH;
    constant REGION_WIDTH : natural := REGION_SIZE*BLOCK_WIDTH;

    constant USER_HDR_FLAG_INDEX : natural := minimum(10,HDR_META_WIDTH-1);

    signal mi_sync_dwr      : std_logic_vector(32-1 downto 0);
    signal mi_sync_addr     : std_logic_vector(32-1 downto 0);
    signal mi_sync_be       : std_logic_vector(4-1 downto 0);
    signal mi_sync_rd       : std_logic;
    signal mi_sync_wr       : std_logic;
    signal mi_sync_ardy     : std_logic;
    signal mi_sync_drd      : std_logic_vector(32-1 downto 0);
    signal mi_sync_drdy     : std_logic;

    signal mi_pipe_dwr      : std_logic_vector(32-1 downto 0);
    signal mi_pipe_addr     : std_logic_vector(32-1 downto 0);
    signal mi_pipe_be       : std_logic_vector(4-1 downto 0);
    signal mi_pipe_rd       : std_logic;
    signal mi_pipe_wr       : std_logic;
    signal mi_pipe_ardy     : std_logic;
    signal mi_pipe_drd      : std_logic_vector(32-1 downto 0);
    signal mi_pipe_drdy     : std_logic;

    signal mfb_gen_data     : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal mfb_gen_meta     : std_logic_vector(REGIONS*(DMA_CHANNELS_WIDTH+LENGTH_WIDTH)-1 downto 0);
    signal mfb_gen_sof_pos  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal mfb_gen_eof_pos  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal mfb_gen_sof      : std_logic_vector(REGIONS-1 downto 0);
    signal mfb_gen_eof      : std_logic_vector(REGIONS-1 downto 0);
    signal mfb_gen_src_rdy  : std_logic;
    signal mfb_gen_dst_rdy  : std_logic;

    signal mfb_gen_meta_arr : slv_array_t(REGIONS-1 downto 0)(DMA_CHANNELS_WIDTH+LENGTH_WIDTH-1 downto 0);
    signal pkt_len          : slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal dma_meta_hdr_data: slv_array_t(REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0) := (others => (others => '0'));
    signal dma_hdr_data     : slv_array_t(REGIONS-1 downto 0)(NPP_HDR_SIZE*8-1 downto 0);
    signal dma_channel      : slv_array_t(REGIONS-1 downto 0)(DMA_CHANNELS_WIDTH-1 downto 0);
    signal dma_blk_len      : slv_array_t(REGIONS-1 downto 0)(log2(PKT_MTU/8+1)-1 downto 0);

begin

    mi_clk_diff_g : if (not SAME_CLK) generate

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
            MI_S_DWR  => mi_sync_dwr,
            MI_S_ADDR => mi_sync_addr,
            MI_S_RD   => mi_sync_rd,
            MI_S_WR   => mi_sync_wr,
            MI_S_BE   => mi_sync_be,
            MI_S_DRD  => mi_sync_drd,
            MI_S_ARDY => mi_sync_ardy,
            MI_S_DRDY => mi_sync_drdy
        );

    else generate

        mi_sync_dwr  <= MI_DWR;
        mi_sync_addr <= MI_ADDR;
        mi_sync_rd   <= MI_RD;
        mi_sync_wr   <= MI_WR;
        mi_sync_be   <= MI_BE;

        MI_DRD       <= mi_sync_drd;
        MI_ARDY      <= mi_sync_ardy;
        MI_DRDY      <= mi_sync_drdy;

    end generate;

    mi_pipe_i : entity work.MI_PIPE
    generic map(
        DEVICE      => DEVICE,
        DATA_WIDTH  => 32,
        ADDR_WIDTH  => 32,
        PIPE_TYPE   => "REG",
        USE_OUTREG  => True,
        FAKE_PIPE   => (not MI_PIPE_EN)
    )
    port map(
        -- Common interface
        CLK      => CLK,
        RESET    => RESET,

        -- Input MI interface
        IN_DWR   => mi_sync_dwr,
        IN_ADDR  => mi_sync_addr,
        IN_RD    => mi_sync_rd,
        IN_WR    => mi_sync_wr,
        IN_BE    => mi_sync_be,
        IN_DRD   => mi_sync_drd,
        IN_ARDY  => mi_sync_ardy,
        IN_DRDY  => mi_sync_drdy,

        -- Output MI interface
        OUT_DWR  => mi_pipe_dwr,
        OUT_ADDR => mi_pipe_addr,
        OUT_RD   => mi_pipe_rd,
        OUT_WR   => mi_pipe_wr,
        OUT_BE   => mi_pipe_be,
        OUT_DRD  => mi_pipe_drd,
        OUT_ARDY => mi_pipe_ardy,
        OUT_DRDY => mi_pipe_drdy
    );

    mfb_generator_i : entity work.MFB_GENERATOR_MI32
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE,
        ITEM_WIDTH     => ITEM_WIDTH,
        LENGTH_WIDTH   => LENGTH_WIDTH,
        PKT_CNT_WIDTH  => 32,
        CHANNELS_WIDTH => DMA_CHANNELS_WIDTH,
        DEVICE         => DEVICE
    )
    port map(
        CLK            => CLK,
        RST            => RESET,

        MI_DWR         => mi_pipe_dwr,
        MI_ADDR        => mi_pipe_addr,
        MI_BE          => mi_pipe_be,
        MI_RD          => mi_pipe_rd,
        MI_WR          => mi_pipe_wr,
        MI_ARDY        => mi_pipe_ardy,
        MI_DRD         => mi_pipe_drd,
        MI_DRDY        => mi_pipe_drdy,

        TX_MFB_DATA    => mfb_gen_data,
        TX_MFB_META    => mfb_gen_meta,
        TX_MFB_SOF_POS => mfb_gen_sof_pos,
        TX_MFB_EOF_POS => mfb_gen_eof_pos,
        TX_MFB_SOF     => mfb_gen_sof,
        TX_MFB_EOF     => mfb_gen_eof,
        TX_MFB_SRC_RDY => mfb_gen_src_rdy,
        TX_MFB_DST_RDY => mfb_gen_dst_rdy
    );

    mfb_gen_meta_arr <= slv_array_deser(mfb_gen_meta,REGIONS,(DMA_CHANNELS_WIDTH+LENGTH_WIDTH));

    dma_hdr_instr_g : for i in 0 to REGIONS-1 generate
        pkt_len(i)           <= mfb_gen_meta_arr(i)(LENGTH_WIDTH-1 downto 0);
        dma_channel(i)       <= mfb_gen_meta_arr(i)(LENGTH_WIDTH+DMA_CHANNELS_WIDTH-1 downto LENGTH_WIDTH);
        dma_blk_len(i)       <= std_logic_vector(resize(enlarge_right(round_up(resize(unsigned(pkt_len(i)),LENGTH_WIDTH+1),3),-3),log2(PKT_MTU/8+1)));
        dma_meta_hdr_data(i)(USER_HDR_FLAG_INDEX) <= '1';
        dma_hdr_data(i)      <= "0000" & dma_meta_hdr_data(i) & std_logic_vector(resize(unsigned(pkt_len(i)),NPP_HDR_SIZE*8-4-HDR_META_WIDTH));
    end generate;

    mfb_gen_dst_rdy <= INSTR_MVB_DST_RDY and ETH_MFB_DST_RDY;

    mvb_data_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (INSTR_MVB_DST_RDY = '1') then
                INSTR_MVB_LEN      <= slv_array_ser(pkt_len);
                INSTR_MVB_CHANNEL  <= slv_array_ser(dma_channel);
                INSTR_MVB_HDR_META <= slv_array_ser(dma_meta_hdr_data);
                INSTR_MVB_DISCARD  <= (others => '0');
                INSTR_MVB_VLD      <= mfb_gen_sof;
            end if;
        end if;
    end process;

    mvb_vld_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                INSTR_MVB_SRC_RDY <= '0';
            elsif (INSTR_MVB_DST_RDY = '1') then
                INSTR_MVB_SRC_RDY <= mfb_gen_src_rdy and (or mfb_gen_sof) and ETH_MFB_DST_RDY;
            end if;
        end if;
    end process;

    mfb_data_regs_p : process (CLK)
        variable tmp_sof_pos : unsigned(log2(REGION_SIZE)-1 downto 0);
    begin
        if (rising_edge(CLK)) then
            if (ETH_MFB_DST_RDY = '1') then
                ETH_MFB_DATA    <= mfb_gen_data;
                ETH_MFB_SOF     <= mfb_gen_sof;
                ETH_MFB_EOF     <= mfb_gen_eof;
                ETH_MFB_SOF_POS <= mfb_gen_sof_pos;
                ETH_MFB_EOF_POS <= mfb_gen_eof_pos;

                -- If NPP Header insertion is enabled
                if (HDR_INS_EN) then
                    for i in 0 to REGIONS-1 loop
                        tmp_sof_pos := resize(unsigned(mfb_gen_sof_pos((i+1)*max(1,log2(REGION_SIZE))-1 downto i*max(1,log2(REGION_SIZE)))),log2(REGION_SIZE));
                        for e in 0 to REGION_SIZE-1 loop
                            if (mfb_gen_sof(i)='1' and (REGION_SIZE<=1 or tmp_sof_pos=e)) then
                                ETH_MFB_DATA(i*REGION_WIDTH+e*BLOCK_WIDTH+NPP_HDR_SIZE*8-1 downto i*REGION_WIDTH+e*BLOCK_WIDTH) <= dma_hdr_data(i);
                            end if;
                        end loop;
                    end loop;
                end if;
            end if;
        end if;
    end process;

    mfb_vld_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                ETH_MFB_SRC_RDY <= '0';
            elsif (ETH_MFB_DST_RDY = '1') then
                ETH_MFB_SRC_RDY <= mfb_gen_src_rdy and INSTR_MVB_DST_RDY;
            end if;
        end if;
    end process;

end architecture;
