-- block_reconfigurator.vhd: Implementation of MFB block_reconfigurator component
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

entity MFB_BLOCK_RECONFIGURATOR is
generic(
    -- =========================================================
    -- MFB Configuration
    --
    -- INEFFICIENCY WARNING (for FRAME_ALIGN == 0):
    -- When RX_REGION_SIZE > TX_REGION_SIZE all TX Frames are generated
    -- with SOF aligned to Region.
    -- Might decrease throughput due to unnessesary gaps.
    -- =========================================================

    REGIONS        : integer := 2;
    RX_REGION_SIZE : integer := 1;
    TX_REGION_SIZE : integer := 2;
    RX_BLOCK_SIZE  : integer := 8;
    ITEM_WIDTH     : integer := 32;
    META_WIDTH     : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Metadata validity mode
    --   - 0 -> with SOF
    --   - 1 -> with EOF
    META_MODE      : integer := 0;

    -- Input FIFO size (in number of MFB words)
    -- Only applies when RX_REGION_SIZE > TX_REGION_SIZE
    FIFO_SIZE      : integer := 32;

    -- Frame alignment mode (Only applies when RX_REGION_SIZE > TX_REGION_SIZE)
    --   - 0 - align to start of Region
    --   - 1 - align to start of Block (ONLY SUPPORTED WHEN ALL FRAMES ARE BIGGER THAN TX MFB BLOCK)
    FRAME_ALIGN    : integer := 0;

    -- Target device
    DEVICE         : string := "ULTRASCALE";

    -- Derived parameters
    -- DO NOT CHANGE!
    TX_BLOCK_SIZE  : integer := RX_BLOCK_SIZE*RX_REGION_SIZE/TX_REGION_SIZE
);
port(
    CLK   : in std_logic;
    RESET : in std_logic;

    -- =============================
    -- MFB input interface
    -- =============================

    RX_DATA    : in  std_logic_vector(REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
    RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
    RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
    RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    -- =============================
    -- MFB output interface
    -- =============================

    TX_DATA    : out std_logic_vector(REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
    TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
    TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of MFB_BLOCK_RECONFIGURATOR is

    constant TX_B_PER_RX_B     : natural := TX_REGION_SIZE/RX_REGION_SIZE;
    constant RX_SOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE));
    constant RX_EOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE));
    constant RX_SOF_POS_TRUE_W : natural := log2(RX_REGION_SIZE);
    constant RX_EOF_POS_TRUE_W : natural := log2(RX_REGION_SIZE*RX_BLOCK_SIZE);
    constant TX_SOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE));
    constant TX_EOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE));
    constant TX_SOF_POS_TRUE_W : natural := log2(TX_REGION_SIZE);
    constant TX_EOF_POS_TRUE_W : natural := log2(TX_REGION_SIZE*TX_BLOCK_SIZE);
    constant ITEMS             : natural := RX_REGION_SIZE*RX_BLOCK_SIZE;

    -- ------------------------------------------------------------------------
    -- RX Region Size = TX Region Size
    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Region Size < TX Region Size
    -- ------------------------------------------------------------------------

    signal RX_SOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(RX_SOF_POS_W-1 downto 0);
    signal RX_EOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(RX_EOF_POS_W-1 downto 0);
    signal TX_SOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(TX_SOF_POS_W-1 downto 0);
    signal TX_EOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(TX_EOF_POS_W-1 downto 0);
    signal TX_META_arr    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Region Size < TX Region Size
    -- ------------------------------------------------------------------------

    signal rx_block_regs_data    : std_logic_vector(REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_block_regs_meta    : std_logic_vector(REGIONS*RX_REGION_SIZE*META_WIDTH-1 downto 0);
    signal rx_block_regs_sof     : std_logic_vector(REGIONS*RX_REGION_SIZE-1 downto 0);
    signal rx_block_regs_eof     : std_logic_vector(REGIONS*RX_REGION_SIZE-1 downto 0);
    signal rx_block_regs_sof_pos : std_logic_vector(REGIONS*RX_REGION_SIZE*max(1,log2(1))-1 downto 0);
    signal rx_block_regs_eof_pos : std_logic_vector(REGIONS*RX_REGION_SIZE*max(1,log2(1*RX_BLOCK_SIZE))-1 downto 0);
    signal rx_block_regs_src_rdy : std_logic;
    signal rx_block_regs_dst_rdy : std_logic;

    constant TX_REC_REGIONS     : integer := tsel((FRAME_ALIGN=0),REGIONS       ,REGIONS*TX_REGION_SIZE       );
    constant TX_REC_REGION_SIZE : integer := tsel((FRAME_ALIGN=0),RX_REGION_SIZE,RX_REGION_SIZE/TX_REGION_SIZE);

    signal tx_block_regs_data    : std_logic_vector(TX_REC_REGIONS*TX_REC_REGION_SIZE*RX_BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_block_regs_meta    : std_logic_vector(TX_REC_REGIONS*META_WIDTH-1 downto 0);
    signal tx_block_regs_sof     : std_logic_vector(TX_REC_REGIONS-1 downto 0);
    signal tx_block_regs_eof     : std_logic_vector(TX_REC_REGIONS-1 downto 0);
    signal tx_block_regs_sof_pos : std_logic_vector(TX_REC_REGIONS*max(1,log2(TX_REC_REGION_SIZE))-1 downto 0);
    signal tx_block_regs_eof_pos : std_logic_vector(TX_REC_REGIONS*max(1,log2(TX_REC_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    signal tx_block_regs_src_rdy : std_logic;
    signal tx_block_regs_dst_rdy : std_logic;

    signal tx_block_regs_sof_pos_arr : slv_array_t(TX_REC_REGIONS-1 downto 0)(max(1,log2(TX_REC_REGION_SIZE))-1 downto 0);
    signal tx_block_regs_eof_pos_arr : slv_array_t(TX_REC_REGIONS-1 downto 0)(max(1,log2(TX_REC_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    signal tx_block_regs_meta_arr    : slv_array_t(TX_REC_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);

    -- ------------------------------------------------------------------------

begin

    -- ------------------------------------------------------------------------
    -- Asserts over generics
    -- ------------------------------------------------------------------------

    assert (2**log2(REGIONS) = REGIONS and REGIONS > 0)
        report "MFB_BLOCK_RECONFIGURATOR: REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_REGION_SIZE) = RX_REGION_SIZE and RX_REGION_SIZE > 0)
        report "MFB_BLOCK_RECONFIGURATOR: RX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_REGION_SIZE) = TX_REGION_SIZE and TX_REGION_SIZE > 0)
        report "MFB_BLOCK_RECONFIGURATOR: TX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_BLOCK_SIZE) = RX_BLOCK_SIZE and RX_BLOCK_SIZE > 0)
        report "MFB_BLOCK_RECONFIGURATOR: RX_BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(ITEM_WIDTH) = ITEM_WIDTH and ITEM_WIDTH > 0)
        report "MFB_BLOCK_RECONFIGURATOR: ITEM_WIDTH must be power of 2 and higher than 0."
        severity failure;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Region Size = TX Region Size
    -- ------------------------------------------------------------------------

    gen_arch_equal_gen : if (RX_REGION_SIZE = TX_REGION_SIZE) generate
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
    -- RX Region Size < TX Region Size
    -- ------------------------------------------------------------------------

    gen_arch_up_gen : if (RX_REGION_SIZE < TX_REGION_SIZE) generate

        TX_DATA    <= RX_DATA;
        TX_META    <= RX_META;
        TX_SOF     <= RX_SOF;
        TX_EOF     <= RX_EOF;
        TX_SRC_RDY <= RX_SRC_RDY;
        RX_DST_RDY <= TX_DST_RDY;

        -- Simply add zero bits at the end of each XOF_POS
        RX_SOF_POS_arr <= slv_array_deser(RX_SOF_POS,REGIONS);
        RX_EOF_POS_arr <= slv_array_deser(RX_EOF_POS,REGIONS);
        xof_resize_gen : for i in 0 to REGIONS-1 generate
            TX_SOF_POS_arr(i) <= std_logic_vector(resize_right(resize_left(unsigned(RX_SOF_POS_arr(i)),RX_SOF_POS_TRUE_W),TX_SOF_POS_W));
            TX_EOF_POS_arr(i) <= std_logic_vector(resize_right(resize_left(unsigned(RX_EOF_POS_arr(i)),RX_EOF_POS_TRUE_W),TX_EOF_POS_W));
        end generate;
        TX_SOF_POS <= slv_array_ser(TX_SOF_POS_arr);
        TX_EOF_POS <= slv_array_ser(TX_EOF_POS_arr);

    end generate;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- RX Region Size > TX Region Size
    -- ------------------------------------------------------------------------

    gen_arch_down_gen : if (RX_REGION_SIZE > TX_REGION_SIZE) generate

        -- Reconfigure MFB, so that each Block is one Region (requires minimum logic)
        rx_blocks_to_regs_reconf_i : entity work.MFB_REGION_RECONFIGURATOR
        generic map(
            RX_REGIONS     => REGIONS               ,
            TX_REGIONS     => REGIONS*RX_REGION_SIZE,
            RX_REGION_SIZE => RX_REGION_SIZE        ,
            BLOCK_SIZE     => RX_BLOCK_SIZE         ,
            ITEM_WIDTH     => ITEM_WIDTH            ,
            META_WIDTH     => META_WIDTH            ,
            META_MODE      => META_MODE             ,
            DEVICE         => DEVICE
        )
        port map(
            CLK   => CLK  ,
            RESET => RESET,

            RX_DATA    => RX_DATA   ,
            RX_META    => RX_META   ,
            RX_SOF     => RX_SOF    ,
            RX_EOF     => RX_EOF    ,
            RX_SOF_POS => RX_SOF_POS,
            RX_EOF_POS => RX_EOF_POS,
            RX_SRC_RDY => RX_SRC_RDY,
            RX_DST_RDY => RX_DST_RDY,

            TX_DATA    => rx_block_regs_data   ,
            TX_META    => rx_block_regs_meta   ,
            TX_SOF     => rx_block_regs_sof    ,
            TX_EOF     => rx_block_regs_eof    ,
            TX_SOF_POS => rx_block_regs_sof_pos,
            TX_EOF_POS => rx_block_regs_eof_pos,
            TX_SRC_RDY => rx_block_regs_src_rdy,
            TX_DST_RDY => rx_block_regs_dst_rdy
        );

        -- Reconfigure MFB, the number of Regions is the same as the target number of Blocks
        regs_to_tx_blocks_reconf_i : entity work.MFB_REGION_RECONFIGURATOR
        generic map(
            RX_REGIONS     => REGIONS*RX_REGION_SIZE,
            TX_REGIONS     => TX_REC_REGIONS        ,
            RX_REGION_SIZE => 1                     ,
            BLOCK_SIZE     => RX_BLOCK_SIZE         ,
            ITEM_WIDTH     => ITEM_WIDTH            ,
            META_WIDTH     => META_WIDTH            ,
            META_MODE      => META_MODE             ,
            FRAME_ALIGN    => 0                     , -- Align all Frames to start of Regions (future Blocks)
            FIFO_SIZE      => FIFO_SIZE             ,
            DEVICE         => DEVICE
        )
        port map(
            CLK   => CLK  ,
            RESET => RESET,

            RX_DATA    => rx_block_regs_data   ,
            RX_META    => rx_block_regs_meta   ,
            RX_SOF     => rx_block_regs_sof    ,
            RX_EOF     => rx_block_regs_eof    ,
            RX_SOF_POS => rx_block_regs_sof_pos,
            RX_EOF_POS => rx_block_regs_eof_pos,
            RX_SRC_RDY => rx_block_regs_src_rdy,
            RX_DST_RDY => rx_block_regs_dst_rdy,

            TX_DATA    => tx_block_regs_data   ,
            TX_META    => tx_block_regs_meta   ,
            TX_SOF     => tx_block_regs_sof    ,
            TX_EOF     => tx_block_regs_eof    ,
            TX_SOF_POS => tx_block_regs_sof_pos,
            TX_EOF_POS => tx_block_regs_eof_pos,
            TX_SRC_RDY => tx_block_regs_src_rdy,
            TX_DST_RDY => tx_block_regs_dst_rdy
        );

        -- Reorganize XOF_POSes and Metadata
        tx_block_regs_sof_pos_arr <= slv_array_deser(tx_block_regs_sof_pos,TX_REC_REGIONS);
        tx_block_regs_eof_pos_arr <= slv_array_deser(tx_block_regs_eof_pos,TX_REC_REGIONS);

        block_add_gen : if (FRAME_ALIGN=0) generate
            -- Simply reduce width of XOF_POS signals (there are now no shared Regions)
            TX_META <= tx_block_regs_meta;
            TX_SOF  <= tx_block_regs_sof;
            TX_EOF  <= tx_block_regs_eof;
            xof_resize_gen : for i in 0 to REGIONS-1 generate
                TX_SOF_POS_arr(i) <= std_logic_vector(resize_right(unsigned(tx_block_regs_sof_pos_arr(i)),TX_SOF_POS_W));
                TX_EOF_POS_arr(i) <= std_logic_vector(resize_right(unsigned(tx_block_regs_eof_pos_arr(i)),TX_EOF_POS_W));
            end generate;
        end generate;

        reg_to_block_conv_gen : if (FRAME_ALIGN=1) generate
            -- Convert Blocks in Region to Items and some Regions in Word to Blocks
            -- THIS CAN CAUSE MULTIPLE EOFS TO BE PLACED IN ONE REGION WHEN A FRAME IS NOT LARGER THEN MFB BLOCK!
            tx_block_regs_meta_arr <= slv_array_deser(tx_block_regs_meta,TX_REC_REGIONS);
            xof_resize_gen : for i in 0 to REGIONS-1 generate
                xof_pos_reg_pr : process (all)
                begin
                    -- Set correct SOF and SOF_POS
                    for e in 0 to TX_REGION_SIZE-1 loop
                        TX_SOF_POS_arr(i) <= std_logic_vector(resize_left(to_unsigned(e,log2(TX_REGION_SIZE)),TX_SOF_POS_W));
                        TX_SOF        (i) <= tx_block_regs_sof(i*TX_REGION_SIZE+e);
                        if (META_MODE=0) then -- Insert Metadata with SOF
                            TX_META_arr(i) <= tx_block_regs_meta_arr(i*TX_REGION_SIZE+e);
                        end if;
                        exit when (tx_block_regs_sof(i*TX_REGION_SIZE+e)='1');
                    end loop;
                    -- Set correct EOF and EOF_POS
                    for e in 0 to TX_REGION_SIZE-1 loop
                        TX_EOF_POS_arr(i) <= std_logic_vector(resize_left(to_unsigned(e,log2(TX_REGION_SIZE)) & resize_left(unsigned(tx_block_regs_eof_pos_arr(i*TX_REGION_SIZE+e)),log2(TX_BLOCK_SIZE)),TX_EOF_POS_W));
                        TX_EOF        (i) <= tx_block_regs_eof(i*TX_REGION_SIZE+e);
                        if (META_MODE=1) then -- Insert Metadata with EOF
                            TX_META_arr(i) <= tx_block_regs_meta_arr(i*TX_REGION_SIZE+e);
                        end if;
                        exit when (tx_block_regs_eof(i*TX_REGION_SIZE+e)='1');
                    end loop;
                end process;
            end generate;
            TX_META    <= slv_array_ser(TX_META_arr   );
        end generate;
        TX_SOF_POS <= slv_array_ser(TX_SOF_POS_arr);
        TX_EOF_POS <= slv_array_ser(TX_EOF_POS_arr);

        -- Connect remaining signals directly
        TX_DATA    <= tx_block_regs_data;
        TX_SRC_RDY <= tx_block_regs_src_rdy;
        tx_block_regs_dst_rdy <= TX_DST_RDY;

    end generate;

    -- ------------------------------------------------------------------------

end architecture;
