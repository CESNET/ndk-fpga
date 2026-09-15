-- mfb_merger_gen.vhd: MFB+MVB bus merger with generic number of inputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- MFB+MVB bus merger with generic number of inputs.
--
-- Merges ``MERGER_INPUTS`` input MVB+MFB streams into one output stream. All
-- inputs are arbitrated in one step by a single
-- :vhdl:entity:`MFB_MERGER_FLAT` unit, whatever their number. This entity adds
-- the optional input FIFOs and the input and output pipes around it. A single
-- input is passed straight through instead.
--
-- The MVB interface carries the headers, for example DMA descriptors, and the
-- MFB interface the data payload. ``RX_MVB_PAYLOAD(i)(j)='1'`` marks that the
-- j-th header on input i has a frame on MFB. On each input the k-th frame
-- belongs to the k-th header that announces one.
--
-- ``RX_PAYLOAD_EN(i)`` set to false leaves out the MFB path of input i. Use it
-- for inputs that only send headers, it saves the MFB pipeline stages.
--
-- .. warning::
--   Headers and frames are paired by order, not by content. On one input the
--   k-th frame on MFB belongs to the k-th header that has
--   ``RX_MVB_PAYLOAD(i)(j)='1'``. A header with ``'0'`` takes no frame.
--
-- .. note::
--   A higher SW_TIMEOUT_WIDTH switches less often, and the other inputs then
--   wait longer. An input waits for up to (MERGER_INPUTS-1) grants, so size the
--   input MFB FIFOs for that wait.
--
entity MFB_MERGER_GEN is
    generic (
        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- Number of merger input streams, any positive integer
        MERGER_INPUTS   : integer := 2;

        -- =====================================================================
        -- MVB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MVB headers per word
        MVB_ITEMS       : integer := 2;
        -- Width of one MVB header in bits
        MVB_ITEM_WIDTH  : integer := 32;

        -- =====================================================================
        -- MFB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of Regions per MFB word
        MFB_REGIONS     : integer := 2;
        -- Number of Blocks per Region
        MFB_REG_SIZE    : integer := 1;
        -- Number of Items per Block
        MFB_BLOCK_SIZE  : integer := 8;
        -- Width of one MFB Item in bits
        MFB_ITEM_WIDTH  : integer := 32;
        -- Width of MFB metadata in bits
        MFB_META_WIDTH  : integer := 1;

        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- Enable the input MFB FIFOs. They hold a burst while the output is
        -- busy, instead of pushing back on the sources straight away.
        IN_MFB_FIFO_EN  : boolean := false;

        -- Obsolete, use IN_MFB_FIFO_SIZE instead, which it sets the default of
        INPUT_FIFO_SIZE : integer := 8;

        -- Depth of the input MFB FIFOs in words, minimum value is 2
        IN_MFB_FIFO_SIZE : integer := INPUT_FIFO_SIZE;

        -- Enable the input MVB FIFOs. An input the switch is not serving has its
        -- MVB DST_RDY held low. These FIFOs let it keep taking headers.
        IN_MVB_FIFO_EN  : boolean := false;

        -- Depth of the input MVB FIFOs in words, minimum value is 2
        IN_MVB_FIFO_SIZE : integer := 8;

        -- Depth of the switch FIFO in items. It holds one item per packet
        -- whose header announced a payload.
        SW_FIFO_ITEMS   : natural := MVB_ITEMS*32;

        -- Add a skid slot in front of each MFB input register. It shortens the
        -- longest path at the cost of one more word of registers per input.
        IN_REG_SKID_EN  : boolean := false;

        -- MFB data payload enable for each input port. False leaves out the
        -- MFB path of that input.
        RX_PAYLOAD_EN   : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);

        -- Width of the stream switch timeout counter. One input is served for
        -- 2**(SW_TIMEOUT_WIDTH-1) MVB words, or until it runs out of headers.
        SW_TIMEOUT_WIDTH : natural := 4;

        -- Obsolete, use IN_MFB_FIFO_EN instead, which it activates
        MID_MFB_FIFOS_EN : boolean := False;

        -- Enable the input PIPE stages
        IN_PIPE_EN      : boolean := false;

        -- Enable the output PIPE stage
        OUT_PIPE_EN     : boolean := true;

        -- Architecture of the internal FIFOX_MULTI, "SHAKEDOWN" or "FULL"
        FIFOX_MULTI_ARCH : string := "SHAKEDOWN";

        -- Target device family
        DEVICE          : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX INTERFACES (per input port)
        -- =====================================================================

        RX_MVB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- Bit j announces that header j on input i has a frame on MFB
        RX_MVB_PAYLOAD : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MVB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        RX_MFB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Passed to the output unchanged
        RX_MFB_META    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MFB_SOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        -- =====================================================================
        -- TX INTERFACE (merged output)
        -- =====================================================================

        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- Bit j announces that header j has a frame on MFB
        TX_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Metadata of the input the word came from, passed through unchanged
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER_GEN is

    constant HDR_WIDTH      : natural := MVB_ITEM_WIDTH;
    constant SOF_POS_WIDTH  : natural := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH  : natural := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant MFB_DATA_WIDTH : natural := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    -- The MFB path is only built when at least one input can carry a payload.
    function any_payload_en_f return boolean is
    begin
        for i in 0 to MERGER_INPUTS-1 loop
            if (RX_PAYLOAD_EN(i)) then
                return true;
            end if;
        end loop;
        return false;
    end function;

    constant ANY_PAYLOAD_EN : boolean := any_payload_en_f;

    -- The old name for the input FIFOs, kept working
    constant IN_FIFO_EN : boolean := MID_MFB_FIFOS_EN or IN_MFB_FIFO_EN;

    -- RX MVB and MFB after the optional input FIFOs
    signal fifo_mvb_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal fifo_mvb_payload : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal fifo_mvb_vld     : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal fifo_mvb_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal fifo_mvb_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    signal fifo_mfb_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal fifo_mfb_meta    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal fifo_mfb_sof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fifo_mfb_eof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fifo_mfb_sof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal fifo_mfb_eof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal fifo_mfb_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal fifo_mfb_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- RX MVB and MFB after the optional input PIPEs, as the core takes them
    signal pipe_mvb_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal pipe_mvb_payload : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal pipe_mvb_vld     : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal pipe_mvb_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal pipe_mvb_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    signal pipe_mfb_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal pipe_mfb_meta    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal pipe_mfb_sof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pipe_mfb_eof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pipe_mfb_sof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal pipe_mfb_eof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal pipe_mfb_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal pipe_mfb_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Merged streams as the core leaves them, before the output register
    signal core_mvb_data    : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal core_mvb_payload : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal core_mvb_vld     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal core_mvb_src_rdy : std_logic;
    signal core_mvb_dst_rdy : std_logic;

    signal core_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal core_mfb_meta    : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal core_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal core_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal core_mfb_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal core_mfb_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal core_mfb_src_rdy : std_logic;
    signal core_mfb_dst_rdy : std_logic;

    -- The header and its payload flag travel through the PIPEs as one item.
    signal in_mvb_hdr_p   : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
    signal pipe_mvb_hdr_p : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
    signal core_mvb_hdr_p : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
    signal tx_mvb_hdr_p   : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);

    -- Output register used when the output PIPE is not
    signal out_mvb_data_reg    : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal out_mvb_payload_reg : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal out_mvb_vld_reg     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal out_mvb_src_rdy_reg : std_logic;
    signal out_mvb_dst_rdy_reg : std_logic;

    signal out_mfb_data_reg    : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal out_mfb_meta_reg    : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal out_mfb_sof_reg     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal out_mfb_eof_reg     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal out_mfb_sof_pos_reg : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal out_mfb_eof_pos_reg : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal out_mfb_src_rdy_reg : std_logic;
    signal out_mfb_dst_rdy_reg : std_logic;

begin

    -- =========================================================================
    -- A single input needs no arbitration at all
    -- =========================================================================

    bypass_g : if (MERGER_INPUTS = 1) generate

        TX_MVB_DATA       <= RX_MVB_DATA(0);
        TX_MVB_PAYLOAD    <= RX_MVB_PAYLOAD(0);
        TX_MVB_VLD        <= RX_MVB_VLD(0);
        TX_MVB_SRC_RDY    <= RX_MVB_SRC_RDY(0);
        RX_MVB_DST_RDY(0) <= TX_MVB_DST_RDY;

        TX_MFB_DATA       <= RX_MFB_DATA(0);
        TX_MFB_META       <= RX_MFB_META(0);
        TX_MFB_SOF        <= RX_MFB_SOF(0);
        TX_MFB_EOF        <= RX_MFB_EOF(0);
        TX_MFB_SOF_POS    <= RX_MFB_SOF_POS(0);
        TX_MFB_EOF_POS    <= RX_MFB_EOF_POS(0);
        TX_MFB_SRC_RDY    <= RX_MFB_SRC_RDY(0);
        RX_MFB_DST_RDY(0) <= TX_MFB_DST_RDY;

    end generate;

    -- =========================================================================
    -- Every input arbitrated in one step
    -- =========================================================================

    merger_g : if (MERGER_INPUTS > 1) generate

        -- ---------------------------------------------------------------------
        --  1. OPTIONAL INPUT MVB FIFOS
        -- ---------------------------------------------------------------------
        -- An input the switch is not serving has its MVB DST_RDY held low for
        -- the whole grant. These FIFOs let such an input keep taking headers
        -- meanwhile. The MFB FIFOs below cannot do it, they only hold payload.

        in_mvb_fifo_g : for i in 0 to MERGER_INPUTS-1 generate
            -- The payload flag belongs to its header, so both are stored as one item.
            signal fifo_rx_data : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
            signal fifo_tx_data : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
        begin
            fifo_rx_data_g : for e in 0 to MVB_ITEMS-1 generate
                fifo_rx_data((e+1)*(1+HDR_WIDTH)-1)                              <= RX_MVB_PAYLOAD(i)(e);
                fifo_rx_data(e*(1+HDR_WIDTH)+HDR_WIDTH-1 downto e*(1+HDR_WIDTH)) <= RX_MVB_DATA(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
            end generate;

            in_mvb_fifo_en_g : if (IN_MVB_FIFO_EN) generate
                mvb_fifo_i : entity work.MVB_FIFOX
                generic map (
                    ITEMS      => MVB_ITEMS,
                    ITEM_WIDTH => 1+HDR_WIDTH,
                    FIFO_DEPTH => IN_MVB_FIFO_SIZE,
                    RAM_TYPE   => "AUTO",
                    DEVICE     => DEVICE
                )
                port map (
                    CLK        => CLK,
                    RESET      => RESET,

                    RX_DATA    => fifo_rx_data,
                    RX_VLD     => RX_MVB_VLD(i),
                    RX_SRC_RDY => RX_MVB_SRC_RDY(i),
                    RX_DST_RDY => RX_MVB_DST_RDY(i),

                    TX_DATA    => fifo_tx_data,
                    TX_VLD     => fifo_mvb_vld(i),
                    TX_SRC_RDY => fifo_mvb_src_rdy(i),
                    TX_DST_RDY => fifo_mvb_dst_rdy(i)
                );
            else generate
                fifo_tx_data        <= fifo_rx_data;
                fifo_mvb_vld(i)     <= RX_MVB_VLD(i);
                fifo_mvb_src_rdy(i) <= RX_MVB_SRC_RDY(i);
                RX_MVB_DST_RDY(i)   <= fifo_mvb_dst_rdy(i);
            end generate;

            fifo_mvb_out_g : for e in 0 to MVB_ITEMS-1 generate
                fifo_mvb_data(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH) <= fifo_tx_data(e*(1+HDR_WIDTH)+HDR_WIDTH-1 downto e*(1+HDR_WIDTH));
                fifo_mvb_payload(i)(e)                                 <= fifo_tx_data((e+1)*(1+HDR_WIDTH)-1);
            end generate;
        end generate;

        -- ---------------------------------------------------------------------
        --  2. OPTIONAL INPUT MFB FIFOS
        -- ---------------------------------------------------------------------

        in_mfb_fifo_g : for i in 0 to MERGER_INPUTS-1 generate
            in_mfb_fifo_en_g : if (IN_FIFO_EN) generate
                mfb_fifo_i : entity work.MFB_FIFOX
                generic map (
                    REGIONS     => MFB_REGIONS,
                    REGION_SIZE => MFB_REG_SIZE,
                    BLOCK_SIZE  => MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => MFB_ITEM_WIDTH,
                    META_WIDTH  => MFB_META_WIDTH,
                    FIFO_DEPTH  => IN_MFB_FIFO_SIZE,
                    RAM_TYPE    => "AUTO",
                    DEVICE      => DEVICE
                )
                port map (
                    CLK        => CLK,
                    RST        => RESET,

                    RX_DATA    => RX_MFB_DATA(i),
                    RX_META    => RX_MFB_META(i),
                    RX_SOF_POS => RX_MFB_SOF_POS(i),
                    RX_EOF_POS => RX_MFB_EOF_POS(i),
                    RX_SOF     => RX_MFB_SOF(i),
                    RX_EOF     => RX_MFB_EOF(i),
                    RX_SRC_RDY => RX_MFB_SRC_RDY(i),
                    RX_DST_RDY => RX_MFB_DST_RDY(i),

                    TX_DATA    => fifo_mfb_data(i),
                    TX_META    => fifo_mfb_meta(i),
                    TX_SOF_POS => fifo_mfb_sof_pos(i),
                    TX_EOF_POS => fifo_mfb_eof_pos(i),
                    TX_SOF     => fifo_mfb_sof(i),
                    TX_EOF     => fifo_mfb_eof(i),
                    TX_SRC_RDY => fifo_mfb_src_rdy(i),
                    TX_DST_RDY => fifo_mfb_dst_rdy(i)
                );
            else generate
                fifo_mfb_data(i)    <= RX_MFB_DATA(i);
                fifo_mfb_meta(i)    <= RX_MFB_META(i);
                fifo_mfb_sof_pos(i) <= RX_MFB_SOF_POS(i);
                fifo_mfb_eof_pos(i) <= RX_MFB_EOF_POS(i);
                fifo_mfb_sof(i)     <= RX_MFB_SOF(i);
                fifo_mfb_eof(i)     <= RX_MFB_EOF(i);
                fifo_mfb_src_rdy(i) <= RX_MFB_SRC_RDY(i);
                RX_MFB_DST_RDY(i)   <= fifo_mfb_dst_rdy(i);
            end generate;
        end generate;

        -- ---------------------------------------------------------------------
        --  3. OPTIONAL INPUT PIPES
        -- ---------------------------------------------------------------------

        in_pipe_g : if (IN_PIPE_EN) generate
            in_pipes_g : for i in 0 to MERGER_INPUTS-1 generate

                in_mvb_hdr_p_g : for e in 0 to MVB_ITEMS-1 generate
                    in_mvb_hdr_p(i)((e+1)*(1+HDR_WIDTH)-1)                              <= fifo_mvb_payload(i)(e);
                    in_mvb_hdr_p(i)(e*(1+HDR_WIDTH)+HDR_WIDTH-1 downto e*(1+HDR_WIDTH)) <= fifo_mvb_data(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
                end generate;

                mvb_in_pipe_i : entity work.MVB_PIPE
                generic map (
                    ITEMS       => MVB_ITEMS,
                    ITEM_WIDTH  => 1+HDR_WIDTH,
                    FAKE_PIPE   => false,
                    USE_DST_RDY => true,
                    DEVICE      => DEVICE
                )
                port map (
                    CLK        => CLK,
                    RESET      => RESET,

                    RX_DATA    => in_mvb_hdr_p(i),
                    RX_VLD     => fifo_mvb_vld(i),
                    RX_SRC_RDY => fifo_mvb_src_rdy(i),
                    RX_DST_RDY => fifo_mvb_dst_rdy(i),

                    TX_DATA    => pipe_mvb_hdr_p(i),
                    TX_VLD     => pipe_mvb_vld(i),
                    TX_SRC_RDY => pipe_mvb_src_rdy(i),
                    TX_DST_RDY => pipe_mvb_dst_rdy(i)
                );

                pipe_mvb_out_g : for e in 0 to MVB_ITEMS-1 generate
                    pipe_mvb_data(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH) <= pipe_mvb_hdr_p(i)(e*(1+HDR_WIDTH)+HDR_WIDTH-1 downto e*(1+HDR_WIDTH));
                    pipe_mvb_payload(i)(e)                                 <= pipe_mvb_hdr_p(i)((e+1)*(1+HDR_WIDTH)-1);
                end generate;

                mfb_in_pipe_i : entity work.MFB_PIPE
                generic map (
                    REGIONS     => MFB_REGIONS,
                    REGION_SIZE => MFB_REG_SIZE,
                    BLOCK_SIZE  => MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => MFB_ITEM_WIDTH,
                    META_WIDTH  => MFB_META_WIDTH,
                    FAKE_PIPE   => not RX_PAYLOAD_EN(i),
                    USE_DST_RDY => true,
                    DEVICE      => DEVICE
                )
                port map (
                    CLK        => CLK,
                    RESET      => RESET,

                    RX_DATA    => fifo_mfb_data(i),
                    RX_META    => fifo_mfb_meta(i),
                    RX_SOF_POS => fifo_mfb_sof_pos(i),
                    RX_EOF_POS => fifo_mfb_eof_pos(i),
                    RX_SOF     => fifo_mfb_sof(i),
                    RX_EOF     => fifo_mfb_eof(i),
                    RX_SRC_RDY => fifo_mfb_src_rdy(i),
                    RX_DST_RDY => fifo_mfb_dst_rdy(i),

                    TX_DATA    => pipe_mfb_data(i),
                    TX_META    => pipe_mfb_meta(i),
                    TX_SOF_POS => pipe_mfb_sof_pos(i),
                    TX_EOF_POS => pipe_mfb_eof_pos(i),
                    TX_SOF     => pipe_mfb_sof(i),
                    TX_EOF     => pipe_mfb_eof(i),
                    TX_SRC_RDY => pipe_mfb_src_rdy(i),
                    TX_DST_RDY => pipe_mfb_dst_rdy(i)
                );

            end generate;
        else generate
            no_in_pipe_g : for i in 0 to MERGER_INPUTS-1 generate
                pipe_mvb_data(i)    <= fifo_mvb_data(i);
                pipe_mvb_payload(i) <= fifo_mvb_payload(i);
                pipe_mvb_vld(i)     <= fifo_mvb_vld(i);
                pipe_mvb_src_rdy(i) <= fifo_mvb_src_rdy(i);
                fifo_mvb_dst_rdy(i) <= pipe_mvb_dst_rdy(i);

                pipe_mfb_data(i)    <= fifo_mfb_data(i);
                pipe_mfb_meta(i)    <= fifo_mfb_meta(i);
                pipe_mfb_sof(i)     <= fifo_mfb_sof(i);
                pipe_mfb_eof(i)     <= fifo_mfb_eof(i);
                pipe_mfb_sof_pos(i) <= fifo_mfb_sof_pos(i);
                pipe_mfb_eof_pos(i) <= fifo_mfb_eof_pos(i);
                pipe_mfb_src_rdy(i) <= fifo_mfb_src_rdy(i);
                fifo_mfb_dst_rdy(i) <= pipe_mfb_dst_rdy(i);
            end generate;
        end generate;

        -- ---------------------------------------------------------------------
        --  4. MERGER CORE
        -- ---------------------------------------------------------------------

        merger_i : entity work.MFB_MERGER_FLAT
        generic map (
            MERGER_INPUTS    => MERGER_INPUTS,
            MVB_ITEMS        => MVB_ITEMS,
            MVB_ITEM_WIDTH   => MVB_ITEM_WIDTH,
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REG_SIZE     => MFB_REG_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
            MFB_META_WIDTH   => MFB_META_WIDTH,
            IN_REG_SKID_EN   => IN_REG_SKID_EN,
            RX_PAYLOAD_EN    => RX_PAYLOAD_EN,
            SW_TIMEOUT_WIDTH => SW_TIMEOUT_WIDTH,
            SW_FIFO_ITEMS    => SW_FIFO_ITEMS,
            FIFOX_MULTI_ARCH => FIFOX_MULTI_ARCH,
            DEVICE           => DEVICE
        )
        port map (
            CLK            => CLK,
            RESET          => RESET,

            RX_MVB_DATA    => pipe_mvb_data,
            RX_MVB_PAYLOAD => pipe_mvb_payload,
            RX_MVB_VLD     => pipe_mvb_vld,
            RX_MVB_SRC_RDY => pipe_mvb_src_rdy,
            RX_MVB_DST_RDY => pipe_mvb_dst_rdy,

            RX_MFB_DATA    => pipe_mfb_data,
            RX_MFB_META    => pipe_mfb_meta,
            RX_MFB_SOF     => pipe_mfb_sof,
            RX_MFB_EOF     => pipe_mfb_eof,
            RX_MFB_SOF_POS => pipe_mfb_sof_pos,
            RX_MFB_EOF_POS => pipe_mfb_eof_pos,
            RX_MFB_SRC_RDY => pipe_mfb_src_rdy,
            RX_MFB_DST_RDY => pipe_mfb_dst_rdy,

            TX_MVB_DATA    => core_mvb_data,
            TX_MVB_PAYLOAD => core_mvb_payload,
            TX_MVB_VLD     => core_mvb_vld,
            TX_MVB_SRC_RDY => core_mvb_src_rdy,
            TX_MVB_DST_RDY => core_mvb_dst_rdy,

            TX_MFB_DATA    => core_mfb_data,
            TX_MFB_META    => core_mfb_meta,
            TX_MFB_SOF     => core_mfb_sof,
            TX_MFB_EOF     => core_mfb_eof,
            TX_MFB_SOF_POS => core_mfb_sof_pos,
            TX_MFB_EOF_POS => core_mfb_eof_pos,
            TX_MFB_SRC_RDY => core_mfb_src_rdy,
            TX_MFB_DST_RDY => core_mfb_dst_rdy
        );

        -- ---------------------------------------------------------------------
        --  5. OUTPUT REGISTERS
        -- ---------------------------------------------------------------------
        -- The core drives its outputs combinationally, so one of the two
        -- branches below always registers them.

        out_pipe_g : if (OUT_PIPE_EN) generate

            core_mvb_hdr_p_g : for i in 0 to MVB_ITEMS-1 generate
                core_mvb_hdr_p((i+1)*(1+HDR_WIDTH)-1 downto i*(1+HDR_WIDTH)) <= core_mvb_payload(i) & core_mvb_data((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH);
            end generate;

            mvb_out_pipe_i : entity work.MVB_PIPE
            generic map (
                ITEMS       => MVB_ITEMS,
                ITEM_WIDTH  => 1+HDR_WIDTH,
                FAKE_PIPE   => false,
                USE_DST_RDY => true,
                DEVICE      => DEVICE
            )
            port map (
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => core_mvb_hdr_p,
                RX_VLD     => core_mvb_vld,
                RX_SRC_RDY => core_mvb_src_rdy,
                RX_DST_RDY => core_mvb_dst_rdy,

                TX_DATA    => tx_mvb_hdr_p,
                TX_VLD     => TX_MVB_VLD,
                TX_SRC_RDY => TX_MVB_SRC_RDY,
                TX_DST_RDY => TX_MVB_DST_RDY
            );

            tx_mvb_hdr_g : for i in 0 to MVB_ITEMS-1 generate
                TX_MVB_DATA((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= tx_mvb_hdr_p(i*(1+HDR_WIDTH)+HDR_WIDTH-1 downto i*(1+HDR_WIDTH));
                TX_MVB_PAYLOAD(i)                                 <= tx_mvb_hdr_p((i+1)*(1+HDR_WIDTH)-1);
            end generate;

            mfb_out_pipe_i : entity work.MFB_PIPE
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REG_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                META_WIDTH  => MFB_META_WIDTH,
                FAKE_PIPE   => not ANY_PAYLOAD_EN,
                USE_DST_RDY => true,
                DEVICE      => DEVICE
            )
            port map (
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => core_mfb_data,
                RX_META    => core_mfb_meta,
                RX_SOF_POS => core_mfb_sof_pos,
                RX_EOF_POS => core_mfb_eof_pos,
                RX_SOF     => core_mfb_sof,
                RX_EOF     => core_mfb_eof,
                RX_SRC_RDY => core_mfb_src_rdy,
                RX_DST_RDY => core_mfb_dst_rdy,

                TX_DATA    => TX_MFB_DATA,
                TX_META    => TX_MFB_META,
                TX_SOF_POS => TX_MFB_SOF_POS,
                TX_EOF_POS => TX_MFB_EOF_POS,
                TX_SOF     => TX_MFB_SOF,
                TX_EOF     => TX_MFB_EOF,
                TX_SRC_RDY => TX_MFB_SRC_RDY,
                TX_DST_RDY => TX_MFB_DST_RDY
            );

        else generate

            mvb_out_reg_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (core_mvb_dst_rdy = '1') then
                        out_mvb_data_reg    <= core_mvb_data;
                        out_mvb_payload_reg <= core_mvb_payload;
                        out_mvb_vld_reg     <= core_mvb_vld;
                        out_mvb_src_rdy_reg <= core_mvb_src_rdy;
                    end if;

                    if (RESET = '1') then
                        out_mvb_src_rdy_reg <= '0';
                    end if;
                end if;
            end process;

            core_mvb_dst_rdy <= out_mvb_dst_rdy_reg or not out_mvb_src_rdy_reg;

            mfb_out_reg_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (core_mfb_dst_rdy = '1') then
                        out_mfb_data_reg    <= core_mfb_data;
                        out_mfb_meta_reg    <= core_mfb_meta;
                        out_mfb_sof_reg     <= core_mfb_sof;
                        out_mfb_eof_reg     <= core_mfb_eof;
                        out_mfb_sof_pos_reg <= core_mfb_sof_pos;
                        out_mfb_eof_pos_reg <= core_mfb_eof_pos;
                        out_mfb_src_rdy_reg <= core_mfb_src_rdy;
                    end if;

                    if (RESET = '1') then
                        out_mfb_src_rdy_reg <= '0';
                    end if;
                end if;
            end process;

            core_mfb_dst_rdy <= out_mfb_dst_rdy_reg or not out_mfb_src_rdy_reg;

            TX_MVB_DATA         <= out_mvb_data_reg;
            TX_MVB_PAYLOAD      <= out_mvb_payload_reg;
            TX_MVB_VLD          <= out_mvb_vld_reg;
            TX_MVB_SRC_RDY      <= out_mvb_src_rdy_reg;
            out_mvb_dst_rdy_reg <= TX_MVB_DST_RDY;

            TX_MFB_DATA         <= out_mfb_data_reg;
            TX_MFB_META         <= out_mfb_meta_reg;
            TX_MFB_SOF          <= out_mfb_sof_reg;
            TX_MFB_EOF          <= out_mfb_eof_reg;
            TX_MFB_SOF_POS      <= out_mfb_sof_pos_reg;
            TX_MFB_EOF_POS      <= out_mfb_eof_pos_reg;
            TX_MFB_SRC_RDY      <= out_mfb_src_rdy_reg;
            out_mfb_dst_rdy_reg <= TX_MFB_DST_RDY;

        end generate;

    end generate;

end architecture;
