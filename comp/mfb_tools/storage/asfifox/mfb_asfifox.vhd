-- mfb_asfifox.vhd: MFB ASFIFOX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;

-- -------------------------------------------------------------------------
--                             Description
-- -------------------------------------------------------------------------

-- This component provides the transition between the clock domains of the two MFB interfaces through the ASFIFOX component.
-- For more information about ASFIFOX see the :ref:`documentation<asfifox>`
--
entity MFB_ASFIFOX is
    generic(
        -- ==================
        -- MFB parameters
        -- ==================

        -- any possitive value
        MFB_REGIONS                 : integer := 4;
        -- any possitive value
        MFB_REG_SIZE                : integer := 8;
        -- any possitive value
        MFB_BLOCK_SIZE              : integer := 8;
        -- any possitive value
        MFB_ITEM_WIDTH              : integer := 8;

        -- ==================
        -- FIFO PARAMETERS
        -- ==================

        -- FIFO depth in number of data words, must be power of two!
        -- Minimum value is 2.
        FIFO_ITEMS               : natural := 512;
        -- Select memory implementation. Options:
        -- "LUT"  - effective for shallow FIFO (approx. ITEMS <= 64),
        -- "BRAM" - effective for deep FIFO (approx. ITEMS > 64).
        RAM_TYPE            : string  := "BRAM";
        -- First Word Fall Through mode. If FWFT_MODE=True, valid data will be
        -- ready at the ASFIFOX output without RD_EN requests.
        FWFT_MODE           : boolean := True;
        -- Enabled output registers allow better timing for a few flip-flops.
        OUTPUT_REG          : boolean := True;
        -- Width of Metadata
        METADATA_WIDTH      : natural := 0;
        -- The DEVICE parameter is ignored in the current component version.
        -- It can be used in the future.
        DEVICE              : string  := "ULTRASCALE";
        -- Sets the maximum number of remaining free data words in the ASFIFOX
        -- that triggers the WR_AFULL signal.
        ALMOST_FULL_OFFSET  : natural := FIFO_ITEMS/2;
        -- Sets the maximum number of data words stored in the ASFIFOX that
        -- triggers the RD_AEMPTY signal.
        ALMOST_EMPTY_OFFSET : natural := FIFO_ITEMS/2
    );
    port(
        -- ==================
        -- RX MFB interface
        --
        -- Runs on RX_CLK
        -- ==================

        RX_CLK        : in  std_logic;
        RX_RESET      : in  std_logic;

        RX_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_META       : in  std_logic_vector(MFB_REGIONS*METADATA_WIDTH-1 downto 0) := (others => '0');
        RX_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY    : in  std_logic;
        RX_DST_RDY    : out std_logic;
        RX_AFULL      : out std_logic;
        RX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0);

        -- ==================
        -- TX MFB interface
        --
        -- Runs on TX_CLK
        -- ==================

        TX_CLK        : in  std_logic;
        TX_RESET      : in  std_logic;

        TX_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_META       : out std_logic_vector(MFB_REGIONS*METADATA_WIDTH-1 downto 0);
        TX_SOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_EOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_SOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_EOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in  std_logic;
        TX_AEMPTY     : out std_logic;
        TX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
    );
end entity;



architecture full of MFB_ASFIFOX is

    constant WORD_WIDTH        : integer := MFB_REGIONS * MFB_REG_SIZE * MFB_BLOCK_SIZE * MFB_ITEM_WIDTH;
    constant META_WIDTH        : integer := MFB_REGIONS * METADATA_WIDTH;
    constant SOF_POS_WIDTH     : integer := MFB_REGIONS * max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH     : integer := MFB_REGIONS * max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant DW : integer := WORD_WIDTH + META_WIDTH + SOF_POS_WIDTH + EOF_POS_WIDTH + MFB_REGIONS + MFB_REGIONS;

    subtype DW_DATA          is natural range WORD_WIDTH+META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS-1 downto META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS;
    subtype DW_META          is natural range META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS-1 downto SOF_POS_WIDTH+EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS;
    subtype DW_SOF_POS       is natural range SOF_POS_WIDTH+EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS-1 downto EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS;
    subtype DW_EOF_POS       is natural range EOF_POS_WIDTH+MFB_REGIONS+MFB_REGIONS-1 downto MFB_REGIONS+MFB_REGIONS;
    subtype DW_SOF           is natural range MFB_REGIONS+MFB_REGIONS-1 downto MFB_REGIONS;
    subtype DW_EOF           is natural range MFB_REGIONS-1 downto 0;

    signal di, do : std_logic_vector(DW-1 downto 0);
    signal full, empty : std_logic;

begin

    fifo_core : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => DW                 ,
        ITEMS               => FIFO_ITEMS         ,
        RAM_TYPE            => RAM_TYPE           ,
        FWFT_MODE           => FWFT_MODE          ,
        OUTPUT_REG          => OUTPUT_REG         ,
        DEVICE              => DEVICE             ,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET ,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
    ) port map (
        WR_CLK    => RX_CLK    ,
        WR_RST    => RX_RESET  ,

        WR_DATA   => di        ,
        WR_EN     => RX_SRC_RDY,
        WR_FULL   => full      ,
        WR_AFULL  => RX_AFULL  ,
        WR_STATUS => RX_STATUS ,

        RD_CLK    => TX_CLK    ,
        RD_RST    => TX_RESET  ,

        RD_DATA   => do        ,
        RD_EN     => TX_DST_RDY,
        RD_EMPTY  => empty     ,
        RD_AEMPTY => TX_AEMPTY ,
        RD_STATUS => TX_STATUS
    );

    di(DW_DATA) <= RX_DATA;
    di(DW_META) <= RX_META;
    di(DW_SOF_POS) <= RX_SOF_POS;
    di(DW_EOF_POS) <= RX_EOF_POS;
    di(DW_SOF) <= RX_SOF;
    di(DW_EOF) <= RX_EOF;
    RX_DST_RDY <= not full;

    TX_DATA    <= do(DW_DATA);
    TX_META    <= do(DW_META);
    TX_SOF_POS <= do(DW_SOF_POS);
    TX_EOF_POS <= do(DW_EOF_POS);
    TX_SOF     <= do(DW_SOF);
    TX_EOF     <= do(DW_EOF);
    TX_SRC_RDY <= not empty;

end architecture;
