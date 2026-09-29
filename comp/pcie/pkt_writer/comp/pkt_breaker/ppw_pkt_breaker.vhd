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
-- Up to two break instructions can be applied to the same data word (double
-- break), which is needed when MPS < bus width or when a page-boundary break
-- and an MPS break both land in the same word.
--
-- Instructions are buffered in a small registered queue (IQ_DEPTH entries)
-- between the upstream MVB FIFO and the break-offset logic.  The queue head
-- (``iq(0)``) is the active instruction; ``iq(1)`` is a look-ahead that lets
-- the module detect double breaks without stalling.
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
        -- Uses the TX_AXI input interface when true, TX_MFB when false.
        AXI_TX_DIRECT   : boolean := true;
        AXI_TDATA_WIDTH : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

        -- ========================================================
        -- Other parameters
        -- ========================================================

        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
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
        -- TX AXI-Stream Interface
        -- ========================================================

        TX_AXI_TDATA   : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP   : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST   : out std_logic;
        TX_AXI_TVALID  : out std_logic;
        TX_AXI_TREADY  : in  std_logic
    );
end entity;

architecture FULL of PPW_PKT_BREAKER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant REGION_ITEMS    : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant EOF_POS_WIDTH   : natural := max(1,log2(REGION_ITEMS));
    constant WORD_WIDTH      : natural := tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH, MFB_REGIONS*REGION_ITEMS*MFB_ITEM_WIDTH);
    constant WORD_ITEMS      : natural := tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH/8, MFB_REGIONS*REGION_ITEMS);
    constant FR_OFFSET_WIDTH : natural := tsel(AXI_RX_DIRECT, log2(AXI_TDATA_WIDTH/8), EOF_POS_WIDTH);

    -- Maximum amount of Words a single packet can stretch over.
    constant PKT_MAX_WORDS   : natural := div_roundup(PKT_MTU+1, WORD_ITEMS);
    -- Maximum offset we can be looking for to break a packet.
    constant OFFSET_WIDTH    : natural := log2(PKT_MAX_WORDS*WORD_ITEMS);

    -- Width of the instruction length field.
    constant LEN_WIDTH       : natural := log2(PKT_MTU+1);

    -- Maximum number of fractures (breaks) per data word.
    constant MAX_FRACTURES   : natural := 2;

    -- Instruction queue depth.  The upstream FIFO provides one instruction
    -- per cycle while a double break consumes two.  Four entries give enough
    -- slack so that stalls due to queue exhaustion are rare (they only occur
    -- after several consecutive double breaks with no single-break gap).
    constant IQ_DEPTH        : natural := 4;
    constant IQ_CNT_W        : natural := log2(IQ_DEPTH+1);

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    -- ---------------------------------------------------------------------
    -- Instruction queue
    -- ---------------------------------------------------------------------

    -- Registered queue.  iq(0) is the active instruction, iq(1) the look-ahead.
    signal iq_len            : u_array_t(IQ_DEPTH-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal iq_last           : std_logic_vector(IQ_DEPTH-1 downto 0);
    signal iq_cnt            : unsigned(IQ_CNT_W-1 downto 0);

    -- Queue head aliases.
    signal iq0_vld           : std_logic;
    signal iq0_len           : unsigned(LEN_WIDTH-1 downto 0);
    signal iq0_last          : std_logic;
    signal iq1_vld           : std_logic;
    signal iq1_len           : unsigned(LEN_WIDTH-1 downto 0);
    signal iq1_last          : std_logic;

    -- Queue control.
    signal iq_consume        : unsigned(IQ_CNT_W-1 downto 0);
    signal iq_rd             : std_logic;
    signal iq_wr             : std_logic;

    -- ---------------------------------------------------------------------
    -- Break detection
    -- ---------------------------------------------------------------------

    signal comps_ready       : std_logic;
    signal last_meets_last   : std_logic;
    signal break_and_last    : std_logic;
    signal logic_ready       : std_logic;
    signal last_instr_holdup : std_logic;
    signal stall_for_iq1     : std_logic;
    signal data_accepted     : std_logic;

    signal word_count        : u_array_t(MFB_REGIONS downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);

    -- Break offset for instruction 0 (active instruction).
    signal break_offset_0     : unsigned(OFFSET_WIDTH-1 downto 0);
    signal break_offset_0_vld : std_logic;
    signal bp_reached_0       : std_logic;
    -- Byte position in the word right after break 0.
    signal offset_after_0     : unsigned(log2(WORD_ITEMS) downto 0);

    -- Break offset for instruction 1 (look-ahead).
    signal break_offset_1     : unsigned(OFFSET_WIDTH-1 downto 0);
    signal break_offset_1_vld : std_logic;
    signal bp_reached_1       : std_logic;
    -- Byte position in the word right after break 1.
    signal offset_after_1     : unsigned(log2(WORD_ITEMS) downto 0);

    signal double_bp          : std_logic;
    signal offset_reg         : unsigned(log2(WORD_ITEMS) downto 0);

    -- ---------------------------------------------------------------------
    -- Data path
    -- ---------------------------------------------------------------------

    signal conv_tx_axi_tdata   : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal conv_tx_axi_tkeep   : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal conv_tx_axi_tlast   : std_logic;
    signal conv_tx_axi_tvalid  : std_logic;
    signal conv_tx_axi_tready  : std_logic;

    signal br_rx_axi_tdata       : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal br_rx_axi_tkeep       : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal br_rx_axi_tlast       : std_logic;
    signal br_rx_axi_tvalid      : std_logic;
    signal br_rx_axi_tready      : std_logic;
    signal br_rx_fracture_en     : std_logic_vector(MAX_FRACTURES-1 downto 0);
    signal br_rx_fracture_offset : std_logic_vector(MAX_FRACTURES*FR_OFFSET_WIDTH-1 downto 0);

    signal br_tx_axi_tdata     : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal br_tx_axi_tkeep     : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal br_tx_axi_tlast     : std_logic;
    signal br_tx_axi_tvalid    : std_logic;
    signal br_tx_axi_tready    : std_logic;

begin

    assert IQ_DEPTH >= 4
        report "PPW_PKT_BREAKER: IQ_DEPTH must be at least 4!"
        severity Failure;

    -- =====================================================================
    --  Instruction queue
    -- =====================================================================
    --
    -- A small registered buffer between the upstream MVB FIFO and the
    -- break-offset logic.  Inspired by the switch queue in MFB_MERGER_FLAT:
    -- the FIFO refills the queue whenever it has room; the break logic reads
    -- iq(0) and iq(1) from registers, keeping the FIFO off the critical path.

    -- Queue head aliases.
    iq0_vld  <= '1' when (iq_cnt >= 1) else '0';
    iq0_len  <= iq_len(0);
    iq0_last <= iq_last(0);

    iq1_vld  <= '1' when (iq_cnt >= 2) else '0';
    iq1_len  <= iq_len(1);
    iq1_last <= iq_last(1);

    -- Read from the FIFO whenever the queue has room after this cycle's
    -- consumes.  The FIFO is FWFT, so DST_RDY = '1' advances to the next
    -- entry.  iq_wr is '1' when the FIFO actually provides data.
    iq_rd           <= '1' when ((iq_cnt - iq_consume) < IQ_DEPTH) else '0';
    RX_MVB_DST_RDY  <= iq_rd;
    iq_wr           <= iq_rd and RX_MVB_SRC_RDY and RX_MVB_VALID(0);

    iq_reg_p : process (CLK)
        variable cnt_after : unsigned(IQ_CNT_W-1 downto 0);
    begin
        if rising_edge(CLK) then
            cnt_after := iq_cnt - iq_consume;

            -- Shift entries down by iq_consume (0, 1, or 2).
            for i in 0 to IQ_DEPTH-1 loop
                if (i + to_integer(iq_consume) < IQ_DEPTH) then
                    iq_len(i)  <= iq_len(i + to_integer(iq_consume));
                    iq_last(i) <= iq_last(i + to_integer(iq_consume));
                else
                    iq_len(i)  <= (others => '0');
                    iq_last(i) <= '0';
                end if;
            end loop;

            -- Append the new entry from the FIFO at the first free slot.
            if (iq_wr = '1') then
                iq_len (to_integer(cnt_after)) <= unsigned(RX_MVB_LENGTH(LEN_WIDTH-1 downto 0));
                iq_last(to_integer(cnt_after)) <= RX_MVB_LAST(0);
                cnt_after                      := cnt_after + 1;
            end if;

            iq_cnt <= cnt_after;

            if (RESET = '1') then
                iq_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================
    --  Accepting instructions / flow control
    -- =====================================================================

    -- Components (source and destinations) are ready.
    comps_ready <= conv_tx_axi_tvalid and br_rx_axi_tready;

    -- When Last word on the AXIS bus arrives at the same time as the Last
    -- instruction (=> the Last word does not need breaking).
    last_meets_last <= (iq0_last and iq0_vld) and (conv_tx_axi_tvalid and conv_tx_axi_tlast);

    -- Break fires on TLAST and the look-ahead confirms the "last" instruction
    -- is ready.  Both the break and the "last" are consumed in one cycle,
    -- eliminating the need for last_instr_holdup in this (common) case.
    break_and_last <= bp_reached_0 and conv_tx_axi_tlast and iq1_vld and iq1_last;

    -- Hold transaction until the breakpoint is reached, except when it is the "Last" instr.
    logic_ready <= bp_reached_0 or last_meets_last or last_instr_holdup;

    -- Stall when break 0 fires, instruction 0 is not "last", and the
    -- look-ahead is unavailable (queue nearly empty after sustained double
    -- breaks).  Without iq(1) we cannot tell whether a double break is needed.
    stall_for_iq1 <= bp_reached_0 and (not iq0_last) and (not iq1_vld);

    conv_tx_axi_tready <= br_rx_axi_tready and iq0_vld and (not last_instr_holdup) and (not stall_for_iq1);

    -- Deassert when TLAST has already passed on the AXIS bus but the Last MVB
    -- instruction has not yet been processed.
    -- With the look-ahead queue, this only happens when a break fires on TLAST
    -- and iq(1) is not available yet.  When iq(1) IS the "last" instruction,
    -- break_and_last handles it in one cycle and no holdup is needed.
    last_instr_holdup_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((br_rx_axi_tvalid = '1') and (br_rx_axi_tready = '1')) then
                -- Set only when we cannot resolve break + last in one cycle.
                last_instr_holdup <= br_rx_axi_tlast and bp_reached_0 and (not iq1_vld);
            end if;
            -- Clear when the "last" instruction arrives and is consumed.
            if ((RESET = '1') or ((iq0_last = '1') and (iq0_vld = '1') and (comps_ready = '1'))) then
                last_instr_holdup <= '0';
            end if;
        end if;
    end process;

    -- A word was successfully sent to the fracturer this cycle.
    data_accepted <= br_rx_axi_tvalid and br_rx_axi_tready;

    -- How many instructions are consumed this cycle.
    iq_consume <=
    -- Double break: two non-last instructions consumed.
        to_unsigned(2, IQ_CNT_W) when (data_accepted = '1') and (double_bp = '1') else
    -- Break fires on TLAST and the look-ahead is the "last" instruction.
        to_unsigned(2, IQ_CNT_W) when (data_accepted = '1') and (break_and_last = '1') else
    -- Single break, or last_meets_last, or holdup clearing with data.
        to_unsigned(1, IQ_CNT_W) when (data_accepted = '1') and (logic_ready = '1') else
    -- Holdup clearing without a data handshake (rare: "last" instruction
    -- arrives while no new data is pending).
        to_unsigned(1, IQ_CNT_W) when (last_instr_holdup = '1') and (iq0_vld = '1')
                                  and (iq0_last = '1') and (comps_ready = '1') else
        to_unsigned(0, IQ_CNT_W);

    -- =====================================================================
    --  Finding break offset from Instructions
    -- =====================================================================

    -- ---------------------------------------------------------------------
    -- Count words since SOF or breakpoint
    -- ---------------------------------------------------------------------
    word_cnt_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
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

    word_count_g : for r in 0 to MFB_REGIONS-1 generate
        word_count(r+1) <= (others => '0') when (bp_reached_0 = '1') else word_count(r);
    end generate;

    -- ---------------------------------------------------------------------
    -- Adjust offset when breaking
    -- ---------------------------------------------------------------------

    -- Byte position in the word right after break 0.
    offset_after_0 <= ("0" & break_offset_0(log2(WORD_ITEMS)-1 downto 0)) + 1;
    -- Byte position in the word right after break 1 (used on double break).
    offset_after_1 <= ("0" & break_offset_1(log2(WORD_ITEMS)-1 downto 0)) + 1;

    word_offset_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((conv_tx_axi_tvalid = '1') and (conv_tx_axi_tready = '1')) then
                if (conv_tx_axi_tlast = '1') then
                    offset_reg <= (others => '0');
                elsif (double_bp = '1') then
                    -- After both breaks, the remainder starts after break 1.
                    offset_reg <= offset_after_1;
                elsif (bp_reached_0 = '1') then
                    offset_reg <= offset_after_0;
                end if;
            end if;
            if (RESET = '1') then
                offset_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- ---------------------------------------------------------------------
    -- Find the next breakpoint(s)
    -- ---------------------------------------------------------------------

    -- Instruction 0 (active): same computation as the original single-break design.
    break_offset_0     <= resize(iq0_len, OFFSET_WIDTH) - 1 + offset_reg;
    break_offset_0_vld <= iq0_vld and not iq0_last;

    offset_reached_0_i : entity work.OFFSET_REACHED
    generic map (
        MAX_WORDS     => PKT_MAX_WORDS,
        OFFSET_WIDTH  => OFFSET_WIDTH,
        REGIONS       => tsel(AXI_RX_DIRECT, 1, MFB_REGIONS),
        REGION_ITEMS  => tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH/8, REGION_ITEMS),
        REGION_NUMBER => 0
    )
    port map (
        RX_WORD    => word_count(0),
        RX_OFFSET  => break_offset_0,
        RX_VALID   => break_offset_0_vld,
        TX_REACHED => bp_reached_0
    );

    -- Instruction 1 (look-ahead): the next sub-packet starts right after
    -- break 0. Its break is at offset_after_0 + iq1_len - 1, relative to
    -- the start of the same word (word_count resets to 0 after break 0).
    -- Valid only when break 0 fires and iq(1) is a non-last instruction.
    break_offset_1     <= resize(iq1_len, OFFSET_WIDTH) - 1
                          + resize(offset_after_0, OFFSET_WIDTH);
    break_offset_1_vld <= bp_reached_0 and iq1_vld and (not iq1_last);

    -- After break 0, word_count is combinationally reset to 0, so the second
    -- OFFSET_REACHED checks against word 0.  It fires only when break 1 also
    -- falls within the current data word.
    offset_reached_1_i : entity work.OFFSET_REACHED
    generic map (
        MAX_WORDS     => PKT_MAX_WORDS,
        OFFSET_WIDTH  => OFFSET_WIDTH,
        REGIONS       => tsel(AXI_RX_DIRECT, 1, MFB_REGIONS),
        REGION_ITEMS  => tsel(AXI_RX_DIRECT, AXI_TDATA_WIDTH/8, REGION_ITEMS),
        REGION_NUMBER => 0
    )
    port map (
        RX_WORD    => (others => '0'),
        RX_OFFSET  => break_offset_1,
        RX_VALID   => break_offset_1_vld,
        TX_REACHED => bp_reached_1
    );

    double_bp <= bp_reached_0 and bp_reached_1;

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

    -- =====================================================================
    --  Breaking packets
    -- =====================================================================

    br_rx_axi_tdata  <= conv_tx_axi_tdata;
    br_rx_axi_tkeep  <= conv_tx_axi_tkeep;
    br_rx_axi_tlast  <= conv_tx_axi_tlast;
    br_rx_axi_tvalid <= conv_tx_axi_tvalid and iq0_vld and (not last_instr_holdup) and (not stall_for_iq1);

    br_rx_fracture_en(0) <= bp_reached_0;
    br_rx_fracture_en(1) <= bp_reached_1;

    br_rx_fracture_offset(FR_OFFSET_WIDTH-1 downto 0)
        <= std_logic_vector(break_offset_0(FR_OFFSET_WIDTH-1 downto 0));
    br_rx_fracture_offset(2*FR_OFFSET_WIDTH-1 downto FR_OFFSET_WIDTH)
        <= std_logic_vector(break_offset_1(FR_OFFSET_WIDTH-1 downto 0));

    pkt_breaker_i : entity work.AXIS_FRAME_FRACTURER
    generic map (
        AXI_TDATA_WIDTH => WORD_WIDTH,
        MAX_FRACTURES   => MAX_FRACTURES,
        INPUT_REG       => true,
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

    axis2mfb_g : if not AXI_TX_DIRECT generate

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

        TX_AXI_TVALID <= '0';

    else generate

        TX_AXI_TDATA     <= br_tx_axi_tdata;
        TX_AXI_TKEEP     <= br_tx_axi_tkeep;
        TX_AXI_TLAST     <= br_tx_axi_tlast;
        TX_AXI_TVALID    <= br_tx_axi_tvalid;
        br_tx_axi_tready <= TX_AXI_TREADY;

        TX_MFB_SRC_RDY <= '0';

    end generate;

end architecture;
