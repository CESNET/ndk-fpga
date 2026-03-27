-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- This module breaks packets according to instructions from the PPW_INSTR_GEN.
-- SOFs at the output are aligned to the beginning of word.
--
entity PPW_PKT_BREAKER is
    generic (
        -- ========================================================
        -- MFB parameters
        -- ========================================================

        -- Number of MFB Regions in a word, can't handle more than 1.
        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        -- ========================================================
        -- AXI-Stream parameters
        -- ========================================================

        -- Uses the RX_AXI input interface when true, RX_MFB when false.
        AXI_RX_DIRECT   : boolean := true;
        AXI_TDATA_WIDTH : natural := 512;

        -- ========================================================
        -- Other parameters
        -- ========================================================

        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
        ADDRESS_WIDTH  : natural := 64;
        DEVICE         : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- ========================================================
        -- RX MFB Interface
        -- ========================================================

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Expecting only (others => '0').
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic := '0';
        RX_MFB_DST_RDY : out std_logic;

        -- ========================================================
        -- RX AXI-Stream Interface
        -- ========================================================

        RX_AXI_TDATA   : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP   : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST   : in  std_logic;
        RX_AXI_TVALID  : in  std_logic := '0';
        RX_AXI_TREADY  : out std_logic;

        -- ========================================================
        -- RX MVB Instructions Interface
        -- ========================================================

        RX_MVB_ADDRESS : in  std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_LAST    : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_VALID   : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        -- ========================================================
        -- TX MFB Interface
        -- ========================================================

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic;

        -- ========================================================
        -- TX MVB Interface
        -- ========================================================

        TX_MVB_ADDRESS : out std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
        TX_MVB_LENGTH  : out std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
        TX_MVB_VALID   : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PPW_PKT_BREAKER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant REGION_ITEMS  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant SOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    constant WORD_WIDTH    : natural := tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH, MFB_REGIONS*REGION_ITEMS*MFB_ITEM_WIDTH);
    constant WORD_ITEMS    : natural := tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH/8, MFB_REGIONS*REGION_ITEMS);

    -- MVB instruction combined:          last + address       + length
    constant MVB_INSTR_WIDTH : natural := 1    + ADDRESS_WIDTH + log2(PKT_MTU+1);
    -- Maximum amount of Words a single packet can stretch over.
    constant PKT_MAX_WORDS   : natural := div_roundup(PKT_MTU, WORD_ITEMS) + 1;
    -- Maximum offset we can bee looking for to break a packet.
    constant OFFSET_WIDTH    : natural := log2(PKT_MAX_WORDS*WORD_ITEMS);

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal rx_mvb_address_arr             : slv_array_t(MFB_REGIONS-1 downto 0)(ADDRESS_WIDTH-1 downto 0);
    signal rx_mvb_length_arr              : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal rx_mvb_data                    : slv_array_t(MFB_REGIONS-1 downto 0)(MVB_INSTR_WIDTH-1 downto 0);

    signal instr_data                     : std_logic_vector(MFB_REGIONS*MVB_INSTR_WIDTH-1 downto 0);
    signal instr_address                  : std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
    signal instr_length                   : std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal instr_last                     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal instr_valid                    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal instr_src_rdy                  : std_logic;
    signal instr_dst_rdy                  : std_logic;
    signal valid_instr_ready              : std_logic;
    signal comps_ready                    : std_logic;
    signal last_meets_last                : std_logic;
    signal logic_ready                    : std_logic;
    signal last_instr_holdup              : std_logic;

    signal word_count                     : u_array_t(MFB_REGIONS downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal offset                         : unsigned(log2(WORD_ITEMS) downto 0);
    signal offset_reg                     : unsigned(log2(WORD_ITEMS) downto 0);
    signal break_offset                   : u_array_t(MFB_REGIONS downto 0)(OFFSET_WIDTH-1 downto 0);
    signal break_offset_vld               : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal breakpoint_reached             : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal conv_tx_axi_tdata              : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal conv_tx_axi_tkeep              : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal conv_tx_axi_tlast              : std_logic;
    signal conv_tx_axi_tvalid             : std_logic;
    signal conv_tx_axi_tready             : std_logic;

    signal br_rx_axi_tdata                : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal br_rx_axi_tkeep                : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal br_rx_axi_tlast                : std_logic;
    signal br_rx_axi_tvalid               : std_logic;
    signal br_rx_axi_tready               : std_logic;
    signal br_rx_fracture_en              : std_logic;
    signal br_rx_fracture_offset          : std_logic_vector(EOF_POS_WIDTH-1 downto 0);

    signal br_tx_axi_tdata                : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal br_tx_axi_tkeep                : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal br_tx_axi_tlast                : std_logic;
    signal br_tx_axi_tvalid               : std_logic;
    signal br_tx_axi_tready               : std_logic;

begin

    -- =====================================================================
    --  Store MVB Instructions
    -- =====================================================================

    rx_mvb_address_arr <= slv_array_deser(RX_MVB_ADDRESS, MFB_REGIONS);
    rx_mvb_length_arr  <= slv_array_deser(RX_MVB_LENGTH, MFB_REGIONS);
    rx_mvb_data_g : for r in 0 to MFB_REGIONS-1 generate
        rx_mvb_data(r) <= RX_MVB_LAST(r) & rx_mvb_address_arr(r) & rx_mvb_length_arr(r);
    end generate;

    mvb_fifox_i : entity work.MVB_FIFOX
    generic map (
        ITEMS               => MFB_REGIONS,
        ITEM_WIDTH          => MVB_INSTR_WIDTH,
        FIFO_DEPTH          => 512,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        FAKE_FIFO           => False
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => slv_array_ser(rx_mvb_data),
        RX_VLD     => RX_MVB_VALID,
        RX_SRC_RDY => RX_MVB_SRC_RDY,
        RX_DST_RDY => RX_MVB_DST_RDY,

        TX_DATA    => instr_data,
        TX_VLD     => instr_valid,
        TX_SRC_RDY => instr_src_rdy,
        TX_DST_RDY => instr_dst_rdy,

        STATUS     => open,
        AFULL      => open,
        AEMPTY     => open
    );

    valid_instr_ready <= instr_src_rdy and instr_valid(0);

    (instr_last, instr_address, instr_length) <= instr_data;

    -- ---------------------------------------------------------------------
    -- Prep MVB FIFOX read signal
    -- ---------------------------------------------------------------------
    -- Components (source and destinations) are ready.
    comps_ready     <= TX_MVB_DST_RDY and conv_tx_axi_tvalid and br_rx_axi_tready;
    -- When Last word on the AXIS bus arrives at the same time as the Last instruction (=> the Last word does not need breaking).
    -- If this does not occur and the Last word does need breaking, last_instr_holdup is applied.
    last_meets_last <= (instr_last(0) and valid_instr_ready) and (conv_tx_axi_tvalid and conv_tx_axi_tlast);
    -- Hold transaction until the breakpoint is reached except it it is the "Last" instr.
    logic_ready     <= breakpoint_reached(0) or last_meets_last or last_instr_holdup;
    instr_dst_rdy   <= comps_ready and logic_ready;

    -- Deassert when Last has already passed on the AXIS bus but the Last MVB instruction has not yet been processed.
    -- Example scenario: There is a break in the Last word -> need to read the Last instr and pause the AXIS bus.
    fifo_instr_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((br_rx_axi_tvalid = '1') and (br_rx_axi_tready = '1')) then
                last_instr_holdup <= br_rx_axi_tlast and br_rx_fracture_en;
            end if;
            if ((RESET = '1') or (((instr_last(0) = '1') and (valid_instr_ready = '1')) and (comps_ready = '1'))) then
                last_instr_holdup <= '0';
            end if;
        end if;
    end process;

    -- =====================================================================
    --  Finding break offset from Instructions
    -- =====================================================================

    -- ---------------------------------------------------------------------
    -- Count words since SOF or breakpoint
    -- ---------------------------------------------------------------------
    word_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((conv_tx_axi_tvalid = '1') and (conv_tx_axi_tready = '1')) then
                if (conv_tx_axi_tlast = '0') then
                    word_count(0) <= word_count(MFB_REGIONS) + 1;
                else
                    word_count(0) <= (others => '0');
                end if;
            end if;
            if (RESET = '1') then
                word_count(0) <= (others => '0');
            end if;
        end if;
    end process;

    word_count_g: for r in 0 to MFB_REGIONS-1 generate
        word_count(r+1) <= (others => '0') when (breakpoint_reached(r) = '1') else word_count(r);
    end generate;

    -- ---------------------------------------------------------------------
    -- Adjust offset when breaking
    -- ---------------------------------------------------------------------
    offset <= ("0" & break_offset(0)(log2(WORD_ITEMS)-1 downto 0)) + 1;
    word_offset_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((conv_tx_axi_tvalid = '1') and (conv_tx_axi_tready = '1')) then
                if (conv_tx_axi_tlast = '1') then
                    offset_reg <= (others => '0');
                elsif (breakpoint_reached(0) = '1') then
                    offset_reg <= offset;
                end if;
            end if;
            if (RESET = '1') then
                offset_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- ---------------------------------------------------------------------
    -- Find the next breakpoint
    -- ---------------------------------------------------------------------
    break_offset    (0) <= unsigned(instr_length) - 1 + offset_reg;
    break_offset_vld(0) <= valid_instr_ready and not instr_last(0);
    offset_reached_g : for r in 0 to MFB_REGIONS-1 generate
        offset_reached_i : entity work.OFFSET_REACHED
        generic map (
            MAX_WORDS     => PKT_MAX_WORDS,
            OFFSET_WIDTH  => OFFSET_WIDTH,
            REGIONS       => MFB_REGIONS,
            REGION_ITEMS  => REGION_ITEMS,
            REGION_NUMBER => r
        )
        port map (
            RX_WORD    => word_count        (r),
            RX_OFFSET  => break_offset      (r),
            RX_VALID   => break_offset_vld  (r),
            TX_REACHED => breakpoint_reached(r)
        );
    end generate;

    -- =====================================================================
    --  Bus conversion to AXI Stream
    -- =====================================================================

    mfb2axis_g : if not AXI_RX_DIRECT generate
        mfb2axis_i : entity work.MFB2AXI
        generic map (
            USE_IN_PIPE    => False,
            USE_OUT_PIPE   => True,
            REGIONS        => MFB_REGIONS,
            REGION_SIZE    => MFB_REGION_SIZE,
            BLOCK_SIZE     => MFB_BLOCK_SIZE,
            ITEM_WIDTH     => MFB_ITEM_WIDTH,
            AXI_DATA_WIDTH => WORD_WIDTH,
            PIPE_TYPE      => "SHREG",
            DEVICE         => DEVICE
        )
        port map (
            CLK            => CLK,
            RST            => RESET,

            RX_MFB_DATA    => RX_MFB_DATA,
            RX_MFB_SOF_POS => RX_MFB_SOF_POS,
            RX_MFB_EOF_POS => RX_MFB_EOF_POS,
            RX_MFB_SOF     => RX_MFB_SOF,
            RX_MFB_EOF     => RX_MFB_EOF,
            RX_MFB_SRC_RDY => RX_MFB_SRC_RDY,
            RX_MFB_DST_RDY => RX_MFB_DST_RDY,

            TX_AXI_TDATA   => conv_tx_axi_tdata,
            TX_AXI_TKEEP   => conv_tx_axi_tkeep,
            TX_AXI_TLAST   => conv_tx_axi_tlast,
            TX_AXI_TVALID  => conv_tx_axi_tvalid,
            TX_AXI_TREADY  => conv_tx_axi_tready
        );

        RX_AXI_TREADY      <= '0';
    else generate
        conv_tx_axi_tdata  <= RX_AXI_TDATA;
        conv_tx_axi_tkeep  <= RX_AXI_TKEEP;
        conv_tx_axi_tlast  <= RX_AXI_TLAST;
        conv_tx_axi_tvalid <= RX_AXI_TVALID;
        RX_AXI_TREADY      <= conv_tx_axi_tready;
        RX_MFB_DST_RDY     <= '0';
    end generate;

    conv_tx_axi_tready <= TX_MVB_DST_RDY and br_rx_axi_tready and valid_instr_ready and not last_instr_holdup;

    -- =====================================================================
    --  Breaking packets
    -- =====================================================================

    br_rx_axi_tdata  <= conv_tx_axi_tdata;
    br_rx_axi_tkeep  <= conv_tx_axi_tkeep;
    br_rx_axi_tlast  <= conv_tx_axi_tlast;
    br_rx_axi_tvalid <= TX_MVB_DST_RDY and conv_tx_axi_tvalid and valid_instr_ready and not last_instr_holdup;

    br_rx_fracture_en     <= breakpoint_reached(0);
    br_rx_fracture_offset <= std_logic_vector(break_offset(0)(EOF_POS_WIDTH-1 downto 0));

    pkt_breaker_i : entity work.AXIS_FRAME_FRACTURER
    generic map (
        AXI_TDATA_WIDTH => WORD_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK                => CLK,
        RESET              => RESET,

        RX_AXI_TDATA       => br_rx_axi_tdata,
        RX_AXI_TKEEP       => br_rx_axi_tkeep,
        RX_AXI_TLAST       => br_rx_axi_tlast,
        RX_AXI_TVALID      => br_rx_axi_tvalid,
        RX_AXI_TREADY      => br_rx_axi_tready,
        RX_FRACTURE_EN     => br_rx_fracture_en,
        RX_FRACTURE_OFFSET => br_rx_fracture_offset,

        TX_AXI_TDATA       => br_tx_axi_tdata,
        TX_AXI_TKEEP       => br_tx_axi_tkeep,
        TX_AXI_TLAST       => br_tx_axi_tlast,
        TX_AXI_TVALID      => br_tx_axi_tvalid,
        TX_AXI_TREADY      => br_tx_axi_tready
    );

    -- =====================================================================
    --  Bus conversion back to MFB
    -- =====================================================================

    axis2mfb_i : entity work.AXI2MFB
    generic map (
        USE_IN_PIPE       => False,
        USE_OUT_PIPE      => True,
        REGIONS           => MFB_REGIONS,
        REGION_SIZE       => MFB_REGION_SIZE,
        BLOCK_SIZE        => MFB_BLOCK_SIZE,
        ITEM_WIDTH        => MFB_ITEM_WIDTH,
        AXI_DATA_WIDTH    => WORD_WIDTH,
        AXI_USER_WIDTH    => 0,
        META_WIDTH        => 0,
        MFB_META_WITH_SOF => True,
        PIPE_TYPE         => "SHREG",
        DEVICE            => DEVICE
    )
    port map (
        CLK            => CLK,
        RST            => RESET,

        RX_AXI_TDATA   => br_tx_axi_tdata,
        RX_AXI_TUSER   => (others => '0'),
        RX_AXI_TKEEP   => br_tx_axi_tkeep,
        RX_AXI_TLAST   => br_tx_axi_tlast,
        RX_AXI_TVALID  => br_tx_axi_tvalid,
        RX_AXI_TREADY  => br_tx_axi_tready,

        TX_MFB_DATA    => TX_MFB_DATA,
        TX_MFB_META    => open,
        TX_MFB_SOF_POS => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS => TX_MFB_EOF_POS,
        TX_MFB_SOF     => TX_MFB_SOF,
        TX_MFB_EOF     => TX_MFB_EOF,
        TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY => TX_MFB_DST_RDY
    );

    -- =====================================================================
    --  TX MVB interface assignments
    -- =====================================================================

    TX_MVB_ADDRESS <= instr_address;
    TX_MVB_LENGTH  <= instr_length;
    TX_MVB_VALID   <= instr_valid;
    TX_MVB_SRC_RDY <= instr_src_rdy and instr_dst_rdy;

end architecture;
