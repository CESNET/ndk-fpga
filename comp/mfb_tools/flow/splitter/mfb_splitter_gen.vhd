-- mfb_splitter_gen.vhd: MFB+MVB bus splitter with generic number of outputs
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                           Entity Declaration
-- ----------------------------------------------------------------------------

-- MFB+MVB bus splitter with generic number of outputs.
--
-- A single :vhdl:entity:`MFB_SPLITTER_FLAT` unit routes the input to all outputs
-- in one step, whatever their number. An MFB FIFO can be placed in front of it.
-- Each of its MFB outputs can have an :vhdl:entity:`MFB_COMPACTOR` and an MFB
-- FIFO of its own.
--
-- With ``SPLITTER_OUTPUTS`` of 1 the input streams are connected straight to
-- output 0. No FIFO, compactor or splitter unit is generated.
--
-- .. warning::
--   Headers and frames are paired by order, not by content. The k-th frame on
--   RX MFB belongs to the k-th header that has ``RX_MVB_PAYLOAD(i)='1'``. A
--   header with ``'0'`` takes no frame.
--
entity MFB_SPLITTER_GEN is
    generic (
        -- number of splitter outputs
        SPLITTER_OUTPUTS     : integer := 2;

        -- ===================
        -- MVB characteristics
        -- ===================

        -- number of headers
        MVB_ITEMS            : integer := 2;
        -- width of header
        MVB_ITEM_WIDTH       : integer := 32;

        -- ===================
        -- MFB characteristics
        -- ===================

        -- number of regions in word
        MFB_REGIONS          : integer := 2;
        -- number of blocks in region
        MFB_REG_SIZE         : integer := 1;
        -- number of items in block
        MFB_BLOCK_SIZE       : integer := 8;
        -- width  of one item (in bits)
        MFB_ITEM_WIDTH       : integer := 32;

        -- ===================
        -- Others
        -- ===================

        -- Size of output MVB FIFOs (in words)
        -- Minimum value is 2!
        -- Obsolete, use OUT_MVB_FIFO_SIZE instead. This generic only sets its
        -- default value.
        OUTPUT_FIFO_SIZE     : integer := 8;

        -- Enable the input MFB FIFO. It stores the frame until the header that
        -- selects the output has arrived.
        IN_MFB_FIFO_EN       : boolean := false;

        -- Depth of the input MFB FIFO in words
        -- Only used when IN_MFB_FIFO_EN is true
        IN_MFB_FIFO_SIZE     : natural := 512;

        -- Depth of the output MVB FIFOs in words, minimum value is 2. These FIFOs
        -- are always generated and keep the headers aligned with the switch FIFO.
        OUT_MVB_FIFO_SIZE    : integer := OUTPUT_FIFO_SIZE;

        -- Enable the MFB_COMPACTOR on each output. It removes the Regions that
        -- the routing left empty between frames.
        OUT_MFB_COMPACTOR_EN : boolean := false;

        -- Enable the output MFB FIFOs. All outputs get a word in the same clock
        -- cycle, so without these FIFOs the slowest output stops all the others.
        OUT_MFB_FIFO_EN      : boolean := false;

        -- Obsolete, use OUT_MFB_FIFO_EN instead. Setting this generic to true
        -- has the same effect.
        MID_MFB_FIFOS_EN     : boolean := False;

        -- Size of MFB FIFOs (in words)
        -- Obsolete, use OUT_MFB_FIFO_SIZE instead. This generic only sets its
        -- default value.
        MFB_FIFO_DEPTH       : natural := 512;

        -- Depth of the output MFB FIFOs in words
        -- Only used when OUT_MFB_FIFO_EN is true
        OUT_MFB_FIFO_SIZE    : natural := MFB_FIFO_DEPTH;

        -- Obsolete, has no effect.
        OUT_PIPE_EN          : boolean := true;

        -- "ULTRASCALE", "STRATIX10",...
        DEVICE               : string  := "ULTRASCALE";

        -- "FULL", "SHAKEDOWN"
        FIFOX_MULTI_ARCH     : string  := "SHAKEDOWN"
    );
    port (
        -- ===================
        -- Common interface
        -- ===================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- ===================
        -- RX interfaces
        -- ===================

        RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- output select for each header
        RX_MVB_SWITCH  : in  std_logic_vector(MVB_ITEMS*log2(SPLITTER_OUTPUTS)-1 downto 0);
        -- the header is associated with a payload frame on MFB
        RX_MVB_PAYLOAD : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- ===================
        -- TX interface
        -- ===================

        TX_MVB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- the header is associated with a payload frame on MFB
        TX_MVB_PAYLOAD : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MVB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

        TX_MFB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SPLITTER_GEN is

    constant SOF_POS_WIDTH : natural := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant MFB_DATA_W    : natural := MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    -- RX MFB behind the optional input FIFO
    signal in_mfb_data    : std_logic_vector(MFB_DATA_W-1 downto 0);
    signal in_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal in_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal in_mfb_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal in_mfb_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal in_mfb_src_rdy : std_logic;
    signal in_mfb_dst_rdy : std_logic;

    -- MFB outputs of MFB_SPLITTER_FLAT
    signal spl_mfb_data    : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_DATA_W-1 downto 0);
    signal spl_mfb_sof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal spl_mfb_eof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal spl_mfb_sof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal spl_mfb_eof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal spl_mfb_src_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal spl_mfb_dst_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

    -- MFB outputs behind the optional MFB_COMPACTORs
    signal cmp_mfb_data    : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_DATA_W-1 downto 0);
    signal cmp_mfb_sof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal cmp_mfb_eof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal cmp_mfb_sof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal cmp_mfb_eof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal cmp_mfb_src_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal cmp_mfb_dst_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

begin

    -- With a single output there is nothing to route, so the streams are
    -- connected straight through.
    bypass_g : if (SPLITTER_OUTPUTS = 1) generate

        TX_MVB_DATA(0)    <= RX_MVB_DATA;
        TX_MVB_PAYLOAD(0) <= RX_MVB_PAYLOAD;
        TX_MVB_VLD(0)     <= RX_MVB_VLD;
        TX_MVB_SRC_RDY(0) <= RX_MVB_SRC_RDY;
        RX_MVB_DST_RDY    <= TX_MVB_DST_RDY(0);

        TX_MFB_DATA(0)    <= RX_MFB_DATA;
        TX_MFB_SOF(0)     <= RX_MFB_SOF;
        TX_MFB_EOF(0)     <= RX_MFB_EOF;
        TX_MFB_SOF_POS(0) <= RX_MFB_SOF_POS;
        TX_MFB_EOF_POS(0) <= RX_MFB_EOF_POS;
        TX_MFB_SRC_RDY(0) <= RX_MFB_SRC_RDY;
        RX_MFB_DST_RDY    <= TX_MFB_DST_RDY(0);

    end generate;

    splitter_g : if (SPLITTER_OUTPUTS > 1) generate

        -- =====================================================================
        --  OPTIONAL INPUT MFB FIFO
        -- =====================================================================
        -- A source may send the header only after the frame has ended. This FIFO
        -- stores the frame until its header arrives.

        in_mfb_fifo_g : if (IN_MFB_FIFO_EN) generate
            in_mfb_fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REG_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                FIFO_DEPTH  => IN_MFB_FIFO_SIZE,
                RAM_TYPE    => "AUTO",
                DEVICE      => DEVICE
            )
            port map (
                CLK        => CLK,
                RST        => RESET,

                RX_DATA    => RX_MFB_DATA,
                RX_SOF_POS => RX_MFB_SOF_POS,
                RX_EOF_POS => RX_MFB_EOF_POS,
                RX_SOF     => RX_MFB_SOF,
                RX_EOF     => RX_MFB_EOF,
                RX_SRC_RDY => RX_MFB_SRC_RDY,
                RX_DST_RDY => RX_MFB_DST_RDY,

                TX_DATA    => in_mfb_data,
                TX_SOF_POS => in_mfb_sof_pos,
                TX_EOF_POS => in_mfb_eof_pos,
                TX_SOF     => in_mfb_sof,
                TX_EOF     => in_mfb_eof,
                TX_SRC_RDY => in_mfb_src_rdy,
                TX_DST_RDY => in_mfb_dst_rdy
            );
        else generate
            in_mfb_data    <= RX_MFB_DATA;
            in_mfb_sof_pos <= RX_MFB_SOF_POS;
            in_mfb_eof_pos <= RX_MFB_EOF_POS;
            in_mfb_sof     <= RX_MFB_SOF;
            in_mfb_eof     <= RX_MFB_EOF;
            in_mfb_src_rdy <= RX_MFB_SRC_RDY;
            RX_MFB_DST_RDY <= in_mfb_dst_rdy;
        end generate;

        splitter_i : entity work.MFB_SPLITTER_FLAT
        generic map (
            SPLITTER_OUTPUTS  => SPLITTER_OUTPUTS,
            MVB_ITEMS         => MVB_ITEMS,
            MVB_ITEM_WIDTH    => MVB_ITEM_WIDTH,
            MFB_REGIONS       => MFB_REGIONS,
            MFB_REG_SIZE      => MFB_REG_SIZE,
            MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH,
            OUT_MVB_FIFO_SIZE => OUT_MVB_FIFO_SIZE,
            FIFOX_MULTI_ARCH  => FIFOX_MULTI_ARCH,
            DEVICE            => DEVICE
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_MVB_DATA    => RX_MVB_DATA,
            RX_MVB_SWITCH  => RX_MVB_SWITCH,
            RX_MVB_PAYLOAD => RX_MVB_PAYLOAD,
            RX_MVB_VLD     => RX_MVB_VLD,
            RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY => RX_MVB_DST_RDY,

            RX_MFB_DATA    => in_mfb_data,
            RX_MFB_SOF     => in_mfb_sof,
            RX_MFB_EOF     => in_mfb_eof,
            RX_MFB_SOF_POS => in_mfb_sof_pos,
            RX_MFB_EOF_POS => in_mfb_eof_pos,
            RX_MFB_SRC_RDY => in_mfb_src_rdy,
            RX_MFB_DST_RDY => in_mfb_dst_rdy,

            TX_MVB_DATA    => TX_MVB_DATA,
            TX_MVB_PAYLOAD => TX_MVB_PAYLOAD,
            TX_MVB_VLD     => TX_MVB_VLD,
            TX_MVB_SRC_RDY => TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY => TX_MVB_DST_RDY,

            TX_MFB_DATA    => spl_mfb_data,
            TX_MFB_SOF     => spl_mfb_sof,
            TX_MFB_EOF     => spl_mfb_eof,
            TX_MFB_SOF_POS => spl_mfb_sof_pos,
            TX_MFB_EOF_POS => spl_mfb_eof_pos,
            TX_MFB_SRC_RDY => spl_mfb_src_rdy,
            TX_MFB_DST_RDY => spl_mfb_dst_rdy
        );

        out_mfb_g : for i in 0 to SPLITTER_OUTPUTS-1 generate

            -- =================================================================
            --  OPTIONAL OUTPUT MFB COMPACTOR
            -- =================================================================
            -- Every output gets the whole word with only its own Regions marked
            -- valid. The compactor removes the Regions left empty between them.

            compactor_g : if (OUT_MFB_COMPACTOR_EN) generate
                compactor_i : entity work.MFB_COMPACTOR
                generic map (
                    REGIONS     => MFB_REGIONS,
                    REGION_SIZE => MFB_REG_SIZE,
                    BLOCK_SIZE  => MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => MFB_ITEM_WIDTH,
                    META_WIDTH  => 0
                )
                port map (
                    CLK        => CLK,
                    RESET      => RESET,

                    RX_DATA    => spl_mfb_data(i),
                    RX_META    => (others => '0'),
                    RX_SOF_POS => spl_mfb_sof_pos(i),
                    RX_EOF_POS => spl_mfb_eof_pos(i),
                    RX_SOF     => spl_mfb_sof(i),
                    RX_EOF     => spl_mfb_eof(i),
                    RX_SRC_RDY => spl_mfb_src_rdy(i),
                    RX_DST_RDY => spl_mfb_dst_rdy(i),

                    TX_DATA    => cmp_mfb_data(i),
                    TX_META    => open,
                    TX_SOF_POS => cmp_mfb_sof_pos(i),
                    TX_EOF_POS => cmp_mfb_eof_pos(i),
                    TX_SOF     => cmp_mfb_sof(i),
                    TX_EOF     => cmp_mfb_eof(i),
                    TX_SRC_RDY => cmp_mfb_src_rdy(i),
                    TX_DST_RDY => cmp_mfb_dst_rdy(i)
                );
            else generate
                cmp_mfb_data(i)    <= spl_mfb_data(i);
                cmp_mfb_sof_pos(i) <= spl_mfb_sof_pos(i);
                cmp_mfb_eof_pos(i) <= spl_mfb_eof_pos(i);
                cmp_mfb_sof(i)     <= spl_mfb_sof(i);
                cmp_mfb_eof(i)     <= spl_mfb_eof(i);
                cmp_mfb_src_rdy(i) <= spl_mfb_src_rdy(i);
                spl_mfb_dst_rdy(i) <= cmp_mfb_dst_rdy(i);
            end generate;

            -- =================================================================
            --  OPTIONAL OUTPUT MFB FIFO
            -- =================================================================
            -- All outputs get the word in the same clock cycle. A FIFO on each
            -- output holds the word, so an output stops the others only once its
            -- FIFO is full.

            out_mfb_fifo_g : if (MID_MFB_FIFOS_EN or OUT_MFB_FIFO_EN) generate
                mfb_fifo_i : entity work.MFB_FIFOX
                generic map (
                    REGIONS     => MFB_REGIONS,
                    REGION_SIZE => MFB_REG_SIZE,
                    BLOCK_SIZE  => MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => MFB_ITEM_WIDTH,
                    FIFO_DEPTH  => OUT_MFB_FIFO_SIZE,
                    RAM_TYPE    => "AUTO",
                    DEVICE      => DEVICE
                )
                port map (
                    CLK        => CLK,
                    RST        => RESET,

                    RX_DATA    => cmp_mfb_data(i),
                    RX_SOF_POS => cmp_mfb_sof_pos(i),
                    RX_EOF_POS => cmp_mfb_eof_pos(i),
                    RX_SOF     => cmp_mfb_sof(i),
                    RX_EOF     => cmp_mfb_eof(i),
                    RX_SRC_RDY => cmp_mfb_src_rdy(i),
                    RX_DST_RDY => cmp_mfb_dst_rdy(i),

                    TX_DATA    => TX_MFB_DATA(i),
                    TX_SOF_POS => TX_MFB_SOF_POS(i),
                    TX_EOF_POS => TX_MFB_EOF_POS(i),
                    TX_SOF     => TX_MFB_SOF(i),
                    TX_EOF     => TX_MFB_EOF(i),
                    TX_SRC_RDY => TX_MFB_SRC_RDY(i),
                    TX_DST_RDY => TX_MFB_DST_RDY(i)
                );
            else generate
                TX_MFB_DATA(i)     <= cmp_mfb_data(i);
                TX_MFB_SOF_POS(i)  <= cmp_mfb_sof_pos(i);
                TX_MFB_EOF_POS(i)  <= cmp_mfb_eof_pos(i);
                TX_MFB_SOF(i)      <= cmp_mfb_sof(i);
                TX_MFB_EOF(i)      <= cmp_mfb_eof(i);
                TX_MFB_SRC_RDY(i)  <= cmp_mfb_src_rdy(i);
                cmp_mfb_dst_rdy(i) <= TX_MFB_DST_RDY(i);
            end generate;

        end generate;

    end generate;

end architecture;
