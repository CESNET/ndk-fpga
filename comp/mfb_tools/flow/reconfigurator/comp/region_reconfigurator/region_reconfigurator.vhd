-- region_reconfigurator.vhd: Implementation of MFB region_reconfigurator component
-- Copyright (C) 2020 CESNET
-- Author: Jan Kubalek <kubalek@cesnet.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity MFB_REGION_RECONFIGURATOR is
generic(
    -- =========================================================
    -- MFB Configuration
    --
    -- INEFFICIENCY WARNING (for FRAME_ALIGN == 0):
    -- When TX_REGIONS < RX_REGIONS all TX Frames are generated
    -- with SOF aligned to start of a Region. This might decrease
    -- throughput due to unnessesary gaps.
    -- ==========================================================
    RX_REGIONS            : integer := 2;
    TX_REGIONS            : integer := 1;
    RX_REGION_SIZE        : integer := 1;
    BLOCK_SIZE            : integer := 8;
    ITEM_WIDTH            : integer := 32;
    META_WIDTH            : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Metadata validity mode
    --   - 0 -> with SOF
    --   - 1 -> with EOF
    META_MODE             : integer := 0;

    -- Input FIFO size (in number of MFB words)
    -- Only applies when RX_REGIONS > TX_REGIONS
    FIFO_SIZE             : integer := 32;

    -- Frame alignment mode (Only applies when TX_REGIONS < RX_REGIONS)
    --   - 0 - align to start of Region (requires more resources)
    --   - 1 - align to start of Block (ONLY SUPPORTED WHEN ALL FRAMES ARE BIGGER THAN TX MFB REGION)
    FRAME_ALIGN           : integer := 0;

    -- Target device
    DEVICE                : string := "ULTRASCALE";

    -- Derived parameters
    -- DO NOT CHANGE!
    TX_REGION_SIZE        : integer := RX_REGION_SIZE*RX_REGIONS/TX_REGIONS
);
port(
    -- =============================
    -- Clock and Reset
    -- =============================

    CLK   : in std_logic;
    RESET : in std_logic;

    -- =============================
    -- MFB input interface
    -- =============================

    RX_DATA    : in  std_logic_vector(RX_REGIONS*RX_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_META    : in  std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
    RX_EOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
    RX_SOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
    RX_EOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    -- =============================
    -- MFB output interface
    -- =============================

    TX_DATA    : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_META    : out std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
    TX_SOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
    TX_EOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
    TX_SOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    TX_EOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of MFB_REGION_RECONFIGURATOR is

    constant TX_R_PER_RX_R     : natural := TX_REGIONS/RX_REGIONS;
    constant RX_R_PER_TX_R     : natural := RX_REGIONS/TX_REGIONS;
    constant RX_SOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE));
    constant RX_EOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE*BLOCK_SIZE));
    constant TX_SOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE));
    constant TX_EOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE*BLOCK_SIZE));
    constant BLOCKS            : natural := RX_REGIONS*RX_REGION_SIZE;

    -- ------------------------------------------------------------------------
    -- RX Regions < TX Regions
    -- ------------------------------------------------------------------------

    signal RX_SOF_POS_arr      : slv_array_t(RX_REGIONS-1 downto 0)(RX_SOF_POS_W-1 downto 0);
    signal RX_EOF_POS_arr      : slv_array_t(RX_REGIONS-1 downto 0)(RX_EOF_POS_W-1 downto 0);
    signal RX_META_arr         : slv_array_t(RX_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal RX_SOF_POS_high_arr :   u_array_t(RX_REGIONS-1 downto 0)(log2(TX_R_PER_RX_R)-1 downto 0);
    signal RX_EOF_POS_high_arr :   u_array_t(RX_REGIONS-1 downto 0)(log2(TX_R_PER_RX_R)-1 downto 0);
    signal RX_SOF_POS_low_arr  :   u_array_t(RX_REGIONS-1 downto 0)(log2(TX_REGION_SIZE)-1 downto 0);
    signal RX_EOF_POS_low_arr  :   u_array_t(RX_REGIONS-1 downto 0)(log2(TX_REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal TX_SOF_POS_arr      : slv_array_t(TX_REGIONS-1 downto 0)(TX_SOF_POS_W-1 downto 0);
    signal TX_EOF_POS_arr      : slv_array_t(TX_REGIONS-1 downto 0)(TX_EOF_POS_W-1 downto 0);
    signal TX_META_arr         : slv_array_t(TX_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Regions > TX Regions
    -- ------------------------------------------------------------------------

    signal aux_data      : std_logic_vector(BLOCKS*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal aux_meta      : std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0);
    signal aux_sof       : std_logic_vector(RX_REGIONS-1 downto 0);
    signal aux_eof       : std_logic_vector(RX_REGIONS-1 downto 0);
    signal aux_sof_pos   : std_logic_vector(RX_REGIONS*RX_SOF_POS_W-1 downto 0);
    signal aux_eof_pos   : std_logic_vector(RX_REGIONS*RX_EOF_POS_W-1 downto 0);
    signal aux_src_rdy   : std_logic;
    signal aux_dst_rdy   : std_logic;
    signal aux_block_vld : std_logic_vector(BLOCKS-1 downto 0);

    signal aux_meta_arr         : slv_array_t(RX_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal aux_sof_pos_arr      : slv_array_t(RX_REGIONS-1 downto 0)(RX_SOF_POS_W-1 downto 0);
    signal aux_eof_pos_arr      : slv_array_t(RX_REGIONS-1 downto 0)(RX_EOF_POS_W-1 downto 0);
    signal aux_sof_pos_high_arr :   u_array_t(RX_REGIONS-1 downto 0)(log2(RX_REGION_SIZE)-1 downto 0);
    signal aux_eof_pos_high_arr :   u_array_t(RX_REGIONS-1 downto 0)(log2(RX_REGION_SIZE)-1 downto 0);
    signal aux_eof_pos_low_arr  :   u_array_t(RX_REGIONS-1 downto 0)(log2(BLOCK_SIZE)-1 downto 0);

    --                                      Metadata + MFB Block data + EOF_POS + SOF + EOF
    constant FIFOXM_DATA_WIDTH : natural := META_WIDTH+BLOCK_SIZE*ITEM_WIDTH+log2(BLOCK_SIZE)+1+1;
    signal fifoxm_di    : std_logic_vector(BLOCKS*FIFOXM_DATA_WIDTH-1 downto 0);
    signal fifoxm_wr    : std_logic_vector(BLOCKS-1 downto 0);
    signal fifoxm_full  : std_logic;
    signal fifoxm_do    : std_logic_vector(BLOCKS*FIFOXM_DATA_WIDTH-1 downto 0);
    signal fifoxm_rd    : std_logic_vector(BLOCKS-1 downto 0);
    signal fifoxm_empty : std_logic_vector(BLOCKS-1 downto 0);

    signal fifoxm_di_arr     : slv_array_t     (BLOCKS-1 downto 0)(FIFOXM_DATA_WIDTH-1 downto 0);
    signal fifoxm_di_meta    : slv_array_t     (BLOCKS-1 downto 0)(META_WIDTH-1 downto 0);
    signal fifoxm_di_data    : slv_array_t     (BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal fifoxm_di_eof_pos : slv_array_t     (BLOCKS-1 downto 0)(log2(BLOCK_SIZE)-1 downto 0);
    signal fifoxm_di_sof     : std_logic_vector(BLOCKS-1 downto 0);
    signal fifoxm_di_eof     : std_logic_vector(BLOCKS-1 downto 0);

    signal fifoxm_do_arr     : slv_array_t     (BLOCKS-1 downto 0)(FIFOXM_DATA_WIDTH-1 downto 0);
    signal fifoxm_do_meta    : slv_array_t     (BLOCKS-1 downto 0)(META_WIDTH-1 downto 0);
    signal fifoxm_do_data    : slv_array_t     (BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal fifoxm_do_eof_pos : slv_array_t     (BLOCKS-1 downto 0)(log2(BLOCK_SIZE)-1 downto 0);
    signal fifoxm_do_sof     : std_logic_vector(BLOCKS-1 downto 0);
    signal fifoxm_do_eof     : std_logic_vector(BLOCKS-1 downto 0);

    -- This value can be rounded up to TX_REGION_SIZE up to RX_REGIONS-times
    constant DST_BLOCK_W : natural := log2(RX_REGIONS*BLOCKS+1);
    signal fifoxm_do_dst_block : u_array_t       (BLOCKS-1 downto 0)(DST_BLOCK_W-1 downto 0);
    signal fifoxm_rd_allow     : std_logic_vector(BLOCKS-1 downto 0);

    signal out_reg0_data    : slv_array_t     (BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal out_reg0_meta    : slv_array_t     (BLOCKS-1 downto 0)(META_WIDTH-1 downto 0);
    signal out_reg0_sof     : std_logic_vector(BLOCKS-1 downto 0);
    signal out_reg0_eof     : std_logic_vector(BLOCKS-1 downto 0);
    signal out_reg0_eof_pos : slv_array_t     (BLOCKS-1 downto 0)(log2(BLOCK_SIZE)-1 downto 0);
    signal out_reg0_vld     : std_logic_vector(BLOCKS-1 downto 0);

    signal out_reg1_data    : slv_array_t     (TX_REGIONS-1 downto 0)(TX_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal out_reg1_meta    : slv_array_t     (TX_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal out_reg1_sof     : std_logic_vector(TX_REGIONS-1 downto 0);
    signal out_reg1_eof     : std_logic_vector(TX_REGIONS-1 downto 0);
    signal out_reg1_sof_pos :   u_array_t     (TX_REGIONS-1 downto 0)(log2(RX_R_PER_TX_R)+RX_SOF_POS_W-1 downto 0);
    signal out_reg1_eof_pos :   u_array_t     (TX_REGIONS-1 downto 0)(log2(RX_R_PER_TX_R)+RX_EOF_POS_W-1 downto 0);
    signal out_reg1_src_rdy : std_logic;

    signal out_dst_rdy      : std_logic;

    -- Signals resized to the correct width
    signal out_reg1_sof_pos_res : slv_array_t(TX_REGIONS-1 downto 0)(TX_SOF_POS_W-1 downto 0);
    signal out_reg1_eof_pos_res : slv_array_t(TX_REGIONS-1 downto 0)(TX_EOF_POS_W-1 downto 0);

    -- ------------------------------------------------------------------------

begin

    -- ------------------------------------------------------------------------
    -- Asserts over generics
    -- ------------------------------------------------------------------------

    assert (2**log2(RX_REGIONS) = RX_REGIONS and RX_REGIONS > 0)
        report "MFB_REGION_RECONFIGURATOR: RX_REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_REGIONS) = TX_REGIONS and TX_REGIONS > 0)
        report "MFB_REGION_RECONFIGURATOR: TX_REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_REGION_SIZE) = RX_REGION_SIZE and RX_REGION_SIZE > 0)
        report "MFB_REGION_RECONFIGURATOR: RX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(BLOCK_SIZE) = BLOCK_SIZE and BLOCK_SIZE > 0)
        report "MFB_REGION_RECONFIGURATOR: BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(ITEM_WIDTH) = ITEM_WIDTH and ITEM_WIDTH > 0)
        report "MFB_REGION_RECONFIGURATOR: ITEM_WIDTH must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_REGION_SIZE) = TX_REGION_SIZE and TX_REGION_SIZE > 0)
        report "MFB_REGION_RECONFIGURATOR: TX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;

    -- ------------------------------------------------------------------------

    RX_SOF_POS_arr <= slv_array_deser(RX_SOF_POS,RX_REGIONS);
    RX_EOF_POS_arr <= slv_array_deser(RX_EOF_POS,RX_REGIONS);
    RX_META_arr    <= slv_array_deser(RX_META   ,RX_REGIONS);

    -- ------------------------------------------------------------------------
    -- RX Regions = TX Regions
    -- ------------------------------------------------------------------------

    gen_arch_equal_gen : if (RX_REGIONS = TX_REGIONS) generate
        TX_DATA    <= RX_DATA;
        TX_META    <= RX_META;
        TX_SOF     <= RX_SOF;
        TX_EOF     <= RX_EOF;
        TX_SOF_POS <= RX_SOF_POS;
        TX_EOF_POS <= RX_EOF_POS;
        TX_SRC_RDY <= RX_SRC_RDY;
        RX_DST_RDY <= TX_DST_RDY;
    end generate;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Regions < TX Regions
    -- ------------------------------------------------------------------------

    gen_arch_up_gen : if (RX_REGIONS < TX_REGIONS) generate

        -- Propagate data and control
        TX_DATA    <= RX_DATA;
        TX_SRC_RDY <= RX_SRC_RDY;
        RX_DST_RDY <= TX_DST_RDY;

        -- Reorganize XOF_POSes and Metadata
        xof_resize_gen : for i in 0 to RX_REGIONS-1 generate
            -- Addresses TX Region within RX Region
            RX_SOF_POS_high_arr(i) <= resize_right(unsigned(RX_SOF_POS_arr(i)),RX_SOF_POS_high_arr(i)'length);
            RX_EOF_POS_high_arr(i) <= resize_right(unsigned(RX_EOF_POS_arr(i)),RX_EOF_POS_high_arr(i)'length);
            -- Addresses TX Block within TX Region
            RX_SOF_POS_low_arr (i) <= resize_left (unsigned(RX_SOF_POS_arr(i)),RX_SOF_POS_low_arr (i)'length);
            RX_EOF_POS_low_arr (i) <= resize_left (unsigned(RX_EOF_POS_arr(i)),RX_EOF_POS_low_arr (i)'length);
        end generate;

        -- Set TX XOFs and XOF_POSes and Metadata
        tx_xof_gen : for i in 0 to RX_REGIONS-1 generate
            tx_xof_reg_gen : for e in 0 to TX_R_PER_RX_R-1 generate
                -- Only set for one of the TX Regions
                TX_SOF        (i*TX_R_PER_RX_R+e) <= RX_SOF(i) when RX_SOF_POS_high_arr(i)=e or TX_R_PER_RX_R<2 else '0';
                TX_EOF        (i*TX_R_PER_RX_R+e) <= RX_EOF(i) when RX_EOF_POS_high_arr(i)=e or TX_R_PER_RX_R<2 else '0';
                -- Same for all TX Regions within RX Region
                TX_SOF_POS_arr(i*TX_R_PER_RX_R+e) <= std_logic_vector(resize_left(RX_SOF_POS_low_arr(i),TX_SOF_POS_W));
                TX_EOF_POS_arr(i*TX_R_PER_RX_R+e) <= std_logic_vector(resize_left(RX_EOF_POS_low_arr(i),TX_EOF_POS_W));
                -- Copy Metadata to all new Regions
                TX_META_arr   (i*TX_R_PER_RX_R+e) <= RX_META_arr(i);
            end generate;
        end generate;
        TX_SOF_POS <= slv_array_ser(TX_SOF_POS_arr);
        TX_EOF_POS <= slv_array_ser(TX_EOF_POS_arr);
        TX_META    <= slv_array_ser(TX_META_arr   );

    end generate;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Regions > TX Regions
    -- ------------------------------------------------------------------------

    gen_arch_down_gen : if (RX_REGIONS > TX_REGIONS) generate

        gen_align_0 : if (FRAME_ALIGN = 0) generate

            -- Add valid bits for RX Blocks
            rx_aux_i : entity work.MFB_AUXILIARY_SIGNALS
            generic map(
                REGIONS        => RX_REGIONS    ,
                REGION_SIZE    => RX_REGION_SIZE,
                BLOCK_SIZE     => BLOCK_SIZE    ,
                ITEM_WIDTH     => ITEM_WIDTH    ,
                META_WIDTH     => META_WIDTH    ,
                REGION_AUX_EN  => false         ,
                BLOCK_AUX_EN   => true          ,
                ITEM_AUX_EN    => false
            )
            port map(
                CLK              => CLK  ,
                RESET            => RESET,

                RX_DATA          => RX_DATA   ,
                RX_META          => RX_META   ,
                RX_SOF           => RX_SOF    ,
                RX_EOF           => RX_EOF    ,
                RX_SOF_POS       => RX_SOF_POS,
                RX_EOF_POS       => RX_EOF_POS,
                RX_SRC_RDY       => RX_SRC_RDY,
                RX_DST_RDY       => RX_DST_RDY,

                TX_DATA          => aux_data   ,
                TX_META          => aux_meta   ,
                TX_SOF           => aux_sof    ,
                TX_EOF           => aux_eof    ,
                TX_SOF_POS       => aux_sof_pos,
                TX_EOF_POS       => aux_eof_pos,
                TX_SRC_RDY       => aux_src_rdy,
                TX_DST_RDY       => aux_dst_rdy,

                TX_REGION_SHARED => open         ,
                TX_REGION_VLD    => open         ,
                TX_BLOCK_VLD     => aux_block_vld,
                TX_ITEM_VLD      => open
            );

            -- Reorganize XOF_POSes
            aux_meta_arr    <= slv_array_deser(aux_meta   ,RX_REGIONS);
            aux_sof_pos_arr <= slv_array_deser(aux_sof_pos,RX_REGIONS);
            aux_eof_pos_arr <= slv_array_deser(aux_eof_pos,RX_REGIONS);
            aux_xof_resize_gen : for i in 0 to RX_REGIONS-1 generate
                -- Addresses RX Block within RX Region
                aux_sof_pos_high_arr(i) <= resize_right(unsigned(aux_sof_pos_arr(i)),aux_sof_pos_high_arr(i)'length);
                aux_eof_pos_high_arr(i) <= resize_right(unsigned(aux_eof_pos_arr(i)),aux_eof_pos_high_arr(i)'length);
                -- Addresses Item within RX Block
                aux_eof_pos_low_arr (i) <= resize_left (unsigned(aux_eof_pos_arr(i)),aux_eof_pos_low_arr (i)'length);
            end generate;

            -- Create per-Block input for FIFOX Multi
            fifoxm_di_data <= slv_array_deser(aux_data,BLOCKS);
            fifoxm_input_gen : for i in 0 to RX_REGIONS-1 generate
                fifoxm_input_reg_gen : for e in 0 to RX_REGION_SIZE-1 generate
                    fifoxm_di_meta   (i*RX_REGION_SIZE+e) <= aux_meta_arr(i);
                    fifoxm_di_eof_pos(i*RX_REGION_SIZE+e) <= std_logic_vector(aux_eof_pos_low_arr(i));
                    fifoxm_di_sof    (i*RX_REGION_SIZE+e) <= aux_sof(i) when aux_sof_pos_high_arr(i)=e or RX_REGION_SIZE<2 else '0';
                    fifoxm_di_eof    (i*RX_REGION_SIZE+e) <= aux_eof(i) when aux_eof_pos_high_arr(i)=e or RX_REGION_SIZE<2 else '0';
                    -- Concatenate input block
                    fifoxm_di_arr    (i*RX_REGION_SIZE+e) <= fifoxm_di_meta   (i*RX_REGION_SIZE+e)
                                                            &fifoxm_di_data   (i*RX_REGION_SIZE+e)
                                                            &fifoxm_di_eof_pos(i*RX_REGION_SIZE+e)
                                                            &fifoxm_di_sof    (i*RX_REGION_SIZE+e)
                                                            &fifoxm_di_eof    (i*RX_REGION_SIZE+e);
                end generate;
            end generate;
            fifoxm_di   <= slv_array_ser(fifoxm_di_arr);
            fifoxm_wr   <= aux_block_vld and aux_src_rdy;
            aux_dst_rdy <= not fifoxm_full;

            -- Store data in FIFOX Multi
            rx_fifo_i : entity work.FIFOX_MULTI
            generic map(
                DATA_WIDTH          => FIFOXM_DATA_WIDTH,
                ITEMS               => FIFO_SIZE*BLOCKS ,
                WRITE_PORTS         => BLOCKS           ,
                READ_PORTS          => BLOCKS           ,
                RAM_TYPE            => "AUTO"           ,
                DEVICE              => DEVICE           ,
                ALMOST_FULL_OFFSET  => 0                ,
                ALMOST_EMPTY_OFFSET => 0                ,
                ALLOW_SINGLE_FIFO   => true             ,
                SAFE_READ_MODE      => true
            )
            port map(
                CLK    => CLK  ,
                RESET  => RESET,

                DI     => fifoxm_di   ,
                WR     => fifoxm_wr   ,
                FULL   => fifoxm_full ,
                AFULL  => open        ,

                DO     => fifoxm_do   ,
                RD     => fifoxm_rd   ,
                EMPTY  => fifoxm_empty,
                AEMPTY => open
            );

            -- Deserialize FIFOX Multi output
            fifoxm_do_arr <= slv_array_deser(fifoxm_do,BLOCKS);
            fifoxm_do_gen : for i in 0 to BLOCKS-1 generate
                fifoxm_do_meta   (i) <= fifoxm_do_arr(i)(META_WIDTH+BLOCK_SIZE*ITEM_WIDTH+log2(BLOCK_SIZE)+1+1-1 downto BLOCK_SIZE*ITEM_WIDTH+log2(BLOCK_SIZE)+1+1);
                fifoxm_do_data   (i) <= fifoxm_do_arr(i)(           BLOCK_SIZE*ITEM_WIDTH+log2(BLOCK_SIZE)+1+1-1 downto                       log2(BLOCK_SIZE)+1+1);
                fifoxm_do_eof_pos(i) <= fifoxm_do_arr(i)(                                 log2(BLOCK_SIZE)+1+1-1 downto                                        1+1);
                fifoxm_do_sof    (i) <= fifoxm_do_arr(i)(1);
                fifoxm_do_eof    (i) <= fifoxm_do_arr(i)(0);

                --              '1' when (     read allowed     ) and (block does not go to the next word) and (output is ready) else '0'
                fifoxm_rd(i) <= '1' when (fifoxm_rd_allow(i)='1') and (   fifoxm_do_dst_block(i)<BLOCKS  ) and (out_dst_rdy='1') else '0';
            end generate;

            -- Calculate destination Block address for each FIFOX Multi output
            fifoxm_do_dst_block_gen : process (all)
                variable dst_block : unsigned(DST_BLOCK_W-1 downto 0);
            begin
                fifoxm_do_dst_block <= (others => (others => '0'));
                dst_block := (others => '0');
                for i in 0 to BLOCKS-1 loop
                    if (fifoxm_do_sof(i)='1') then
                        if (FRAME_ALIGN=0) then
                            -- Start new frame in new Region (not efficient)
                            dst_block := round_up(dst_block,log2(TX_REGION_SIZE));
                        end if;
                    end if;
                    fifoxm_do_dst_block(i) <= dst_block;
                    dst_block := dst_block+1;
                end loop;
            end process;

            -- Ban reading of unfinished frames that do not continue to next word to avoid non-valid gaps in frames
            fifoxm_rd_allow_pr : process (all)
                variable allow : std_logic;
            begin
                fifoxm_rd_allow <= (others => '0');
                allow := '0';
                for i in BLOCKS-1 downto 0 loop
                    if (fifoxm_empty(i)='0') then
                        -- Start allowing when a valid block contains EOP or will be placed to the end of the TX word
                        if (fifoxm_do_dst_block(i)=BLOCKS-1 or fifoxm_do_eof(i)='1') then
                            allow := '1';
                        end if;

                        fifoxm_rd_allow(i) <= allow;
                    end if;
                end loop;
            end process;

            -- Output register 0 (per-BLock output)
            out_reg0_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then

                    if (out_dst_rdy='1') then
                        for i in 0 to BLOCKS-1 loop
                            for e in 0 to BLOCKS-1 loop
                                -- Use this block
                                out_reg0_data   (i) <= fifoxm_do_data   (e);
                                out_reg0_meta   (i) <= fifoxm_do_meta   (e);
                                out_reg0_sof    (i) <= fifoxm_do_sof    (e);
                                out_reg0_eof    (i) <= fifoxm_do_eof    (e);
                                out_reg0_eof_pos(i) <= fifoxm_do_eof_pos(e);
                                out_reg0_vld    (i) <= fifoxm_rd(e) and (not fifoxm_empty(e));

                                -- Stop when this is the correct place for this block
                                exit when (fifoxm_do_dst_block(e)=i);
                            end loop;
                        end loop;
                    end if;

                    if (RESET='1') then
                        out_reg0_vld <= (others => '0');
                    end if;
                end if;
            end process;

            -- Output register 1 (per-Region output)
            out_reg1_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then

                    if (out_dst_rdy='1') then

                        out_reg1_data <= slv_array_deser(slv_array_ser(out_reg0_data),TX_REGIONS);

                        -- Place correct SOF
                        for i in 0 to TX_REGIONS-1 loop
                            out_reg1_sof(i) <= '0';
                            for e in 0 to TX_REGION_SIZE-1 loop
                                out_reg1_sof_pos_res(i) <= std_logic_vector(resize_left(to_unsigned(e,log2(TX_REGION_SIZE)),TX_SOF_POS_W));
                                if (META_MODE=0) then -- Insert Metadata with SOF
                                    out_reg1_meta(i) <= out_reg0_meta(i*TX_REGION_SIZE+e);
                                end if;
                                if (out_reg0_sof(i*TX_REGION_SIZE+e)='1' and out_reg0_vld(i*TX_REGION_SIZE+e)='1') then
                                    out_reg1_sof(i) <= '1';
                                    exit;
                                end if;
                            end loop;
                        end loop;

                        -- Place correct EOF
                        for i in 0 to TX_REGIONS-1 loop
                            out_reg1_eof(i) <= '0';
                            for e in 0 to TX_REGION_SIZE-1 loop
                                out_reg1_eof_pos_res(i) <= std_logic_vector(resize_left(to_unsigned(e,log2(TX_REGION_SIZE)) & unsigned(out_reg0_eof_pos(i*TX_REGION_SIZE+e)),TX_EOF_POS_W));

                                if (META_MODE=1) then -- Insert Metadata with EOF
                                    out_reg1_meta(i) <= out_reg0_meta(i*TX_REGION_SIZE+e);
                                end if;
                                if (out_reg0_eof(i*TX_REGION_SIZE+e)='1' and out_reg0_vld(i*TX_REGION_SIZE+e)='1') then
                                    out_reg1_eof(i) <= '1';
                                    exit;
                                end if;
                            end loop;
                        end loop;

                        out_reg1_src_rdy <= (or out_reg0_vld);

                    end if;

                    if (RESET='1') then
                        out_reg1_src_rdy <= '0';
                    end if;
                end if;
            end process;

        end generate;

        gen_align_1 : if (FRAME_ALIGN = 1) generate

            -- When all frames are guaranteed to be at least as large as
            -- one TX MFB Region, the MFB can be converted without the needed
            -- to shift data and the logic is much more simple.

            RX_DST_RDY <= out_dst_rdy;

            -- Output register 1 (per-Region output)
            out_reg1_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then

                    if (out_dst_rdy='1') then
                        out_reg1_data    <= slv_array_deser(RX_DATA,TX_REGIONS);
                        out_reg1_src_rdy <= RX_SRC_RDY;

                        out_reg1_meta    <= (others => (others => '0'));
                        out_reg1_sof     <= (others => '0');
                        out_reg1_eof     <= (others => '0');
                        out_reg1_sof_pos <= (others => (others => '0'));
                        out_reg1_eof_pos <= (others => (others => '0'));

                        -- Assign SOF and SOF_POS (max 1 is valid per TX Region)
                        for i in 0 to TX_REGIONS-1 loop
                            for e in 0 to RX_R_PER_TX_R-1 loop
                                out_reg1_sof_pos(i) <= to_unsigned(e,log2(RX_R_PER_TX_R)) & unsigned(RX_SOF_POS_arr(i*RX_R_PER_TX_R+e));

                                if (META_MODE=0) then -- Insert Metadata with SOF
                                    out_reg1_meta(i) <= RX_META_arr(i*RX_R_PER_TX_R+e);
                                end if;
                                if (RX_SOF(i*RX_R_PER_TX_R+e)='1') then
                                    out_reg1_sof(i) <= '1';
                                    exit;
                                end if;
                            end loop;
                        end loop;

                        -- Assign EOF and EOF_POS (max 1 is valid per TX Region)
                        for i in 0 to TX_REGIONS-1 loop
                            for e in 0 to RX_R_PER_TX_R-1 loop
                                out_reg1_eof_pos(i) <= to_unsigned(e,log2(RX_R_PER_TX_R)) & unsigned(RX_EOF_POS_arr(i*RX_R_PER_TX_R+e));

                                if (META_MODE=1) then -- Insert Metadata with EOF
                                    out_reg1_meta(i) <= RX_META_arr(i*RX_R_PER_TX_R+e);
                                end if;
                                if (RX_EOF(i*RX_R_PER_TX_R+e)='1') then
                                    out_reg1_eof(i) <= '1';
                                    exit;
                                end if;
                            end loop;
                        end loop;
                    end if;

                    if (RESET='1') then
                        out_reg1_src_rdy <= '0';
                    end if;
                end if;
            end process;

            -- Correct width of SOF_POS and EOF_POS
            out_reg1_pos_res_gen : for i in 0 to TX_REGIONS-1 generate
                out_reg1_sof_pos_res(i) <= std_logic_vector(resize_right(out_reg1_sof_pos(i),TX_SOF_POS_W));
                out_reg1_eof_pos_res(i) <= std_logic_vector(resize_right(out_reg1_eof_pos(i),TX_EOF_POS_W));
            end generate;

        end generate;

        -- Propagate TX MFB

        out_dst_rdy <= '1' when TX_DST_RDY='1' or TX_SRC_RDY='0' else '0';

        TX_DATA    <= slv_array_ser(out_reg1_data);
        TX_META    <= slv_array_ser(out_reg1_meta);
        TX_SOF     <= out_reg1_sof;
        TX_EOF     <= out_reg1_eof;
        TX_SOF_POS <= slv_array_ser(out_reg1_sof_pos_res);
        TX_EOF_POS <= slv_array_ser(out_reg1_eof_pos_res);
        TX_SRC_RDY <= out_reg1_src_rdy;

    end generate;

    -- ------------------------------------------------------------------------

end architecture;
