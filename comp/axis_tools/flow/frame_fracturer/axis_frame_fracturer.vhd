-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- This module divides packets in the current word at offset(s) specified by the RX_FRACTURE_OFFSET signal.
-- New packets are aligned to the start of the word as expected by the AXI-Stream protocol.
--
-- Up to two fracture points can be specified per input word. Each additional fracture in a word costs one extra output cycle
-- (the input is stalled). When only one fracture per word is active, throughput is identical to ``MAX_FRACTURES = 1``.
--
-- .. warning::
--
--      While RX_AXI_TLAST and RX_FRACTURE_EN are active, all offsets within RX_FRACTURE_OFFSET must be within the frame's range!
--
-- Caller contract for ``RX_FRACTURE_EN`` / ``RX_FRACTURE_OFFSET``:
--
-- - Enabled fractures must be contiguous from index 0 (no gaps, e.g. ``"01"`` is invalid).
-- - Offsets of enabled fractures must be strictly increasing: ``offset(i+1) > offset(i)``.
-- - Each enabled offset must point within the valid byte range of the current frame (TKEEP).
--
-- Architecture
-- ------------
--
-- This component's code may be somewhat confusing due to the FSM and its complicated state transition conditions and state logic.
-- However, the overall architecture is quite simple.
-- The component consists of three main blocks:
--
-- - Input shift register (two or more stages according to the :vhdl:genconstant:`SHREG_STAGES <AXIS_FRAME_FRACTURER.SHREG_STAGES>` generic)
-- - :ref:`Barrel Shifter <barrel_shifter>` (BS)
-- - Output AXI Stream FIFO
--
-- The core of the component is the FSM that
--
-- - aligns new frames after breaking to the start of the word (with the help of the BS),
-- - sets the BS's SEL signal and output TLAST and TKEEP, effectively breaking the frames, and
-- - pauses the input shift register when data need to be stored a little longer.
--
--
-- In case you need to understand this component's code or modify it, see this :ref:`section <axis_frfr_diagrams_and_notes>` below.
-- Note that the diagrams were made for AXIS_FRAME_FRACTURER's first version (MAX_FRACTURES=1).
--
entity AXIS_FRAME_FRACTURER is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH  : natural := 512;
        -- Maximum fractures per input word; must be 1 or 2.
        -- Offsets must be strictly increasing; enables must be contiguous from index 0.
        MAX_FRACTURES    : natural := 1;
        -- Number of shift register stages, must be at least 2.
        SHREG_STAGES     : natural := 2;
        -- Insert a register between the RX interface and the LAST_ONE + encoder
        -- combinational logic.  Breaks the long carry-chain path at the cost of
        -- one extra cycle of latency.  Recommended for wide buses (> 512 bits).
        INPUT_REG        : boolean := false;
        -- Target device.
        DEVICE           : string := "AGILEX"
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_AXI_TDATA       : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP       : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST       : in  std_logic;
        RX_AXI_TVALID      : in  std_logic;
        RX_AXI_TREADY      : out std_logic;

        -- Per-fracture enable bits. Valid with RX_AXI_TVALID.
        RX_FRACTURE_EN     : in  std_logic_vector(MAX_FRACTURES-1 downto 0);
        -- Per-fracture offsets; each specifies the last byte of the current sub-frame.
        RX_FRACTURE_OFFSET : in  std_logic_vector(MAX_FRACTURES*log2(AXI_TDATA_WIDTH/8)-1 downto 0);

        -- ========================================================
        -- TX Interface
        -- ========================================================

        TX_AXI_TDATA       : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP       : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST       : out std_logic;
        TX_AXI_TVALID      : out std_logic;
        TX_AXI_TREADY      : in  std_logic
    );
end entity;

architecture FULL of AXIS_FRAME_FRACTURER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant WORD_ITEMS    : natural := AXI_TDATA_WIDTH/8;
    constant OFF_W         : natural := log2(WORD_ITEMS);
    constant BS_BLOCKS     : natural := 2*WORD_ITEMS;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    type fsm_t is (ST_IDLE, ST_FLOW, ST_FRACTURE, ST_WAIT, ST_LAST);

    signal rx_axi_tkeep_lastone     : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal rx_axi_last_eofpos       : std_logic_vector(OFF_W-1 downto 0);

    -- Signals between the optional input register and the LAST_ONE + encoder.
    signal inp_axi_tdata            : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal inp_axi_tkeep            : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal inp_axi_tlast            : std_logic;
    signal inp_axi_tvalid           : std_logic;
    signal inp_fracture_en          : std_logic_vector(MAX_FRACTURES-1 downto 0);
    signal inp_fracture_offset      : std_logic_vector(MAX_FRACTURES*OFF_W-1 downto 0);

    signal stage_next               : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal stage_next_shreg         : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal ready                    : std_logic_vector(SHREG_STAGES-1 downto 0);

    signal shreg_axi_tdata          : slv_array_t    (SHREG_STAGES downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal shreg_axi_tlast          : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_axi_tvalid         : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_fracture_en        : slv_array_t    (SHREG_STAGES downto 0)(MAX_FRACTURES-1 downto 0);
    signal shreg_fracture_offset    : u_array_2d_t   (SHREG_STAGES downto 0)(MAX_FRACTURES-1 downto 0)(OFF_W-1 downto 0);
    signal shreg_last_eofpos        : u_array_t      (SHREG_STAGES downto 0)(OFF_W-1 downto 0);

    signal fsm_pstate               : fsm_t;
    signal fsm_nstate               : fsm_t;

    -- Selected stage of the input SHREG.
    -- SHREG_STAGES = fracture in top stage, SHREG_STAGES-1 = fracture in the stage below.
    signal stg                      : integer range 1 to SHREG_STAGES;

    -- Active fracture in the top stage: first enabled fracture with offset >= bs_shift.
    signal fracture_in_top_stage    : std_logic;
    signal active_top_offset        : unsigned(OFF_W-1 downto 0);
    -- Active fracture offset (top stage or stage below).
    signal active_offset            : unsigned(OFF_W-1 downto 0);
    signal new_shift                : unsigned(OFF_W-1 downto 0);

    -- More unprocessed fractures remain in the same word.
    signal more_fractures           : std_logic;
    -- More unprocessed fractures remain in the word in the stage below top.
    signal more_fractures_below     : std_logic;

    signal shreg_pause              : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal next_bs_shift            : unsigned(OFF_W-1 downto 0);

    signal bs_tx_axi_tdata          : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal bs_tx_axi_tkeep          : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal bs_tx_axi_tlast          : std_logic;
    signal bs_tx_axi_tvalid         : std_logic;
    signal tx_fifo_full             : std_logic;

    signal bs_din                   : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);
    signal bs_dout                  : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);
    signal bs_shift                 : unsigned(OFF_W-1 downto 0);

begin

    assert SHREG_STAGES >= 2
        report "AXIS_FRAME_FRACTURER: the lowest number of SHREG_STAGES is 2."
        severity Failure;

    assert (MAX_FRACTURES = 1) or (MAX_FRACTURES = 2)
        report "AXIS_FRAME_FRACTURER: MAX_FRACTURES must be 1 or 2."
        severity Failure;

    -- =====================================================================
    --  Input assignments
    -- =====================================================================

    RX_AXI_TREADY <= ready(0);

    -- When INPUT_REG is true, a register stage is inserted between the RX
    -- interface and the LAST_ONE + encoder combinational logic.  This breaks
    -- the long carry-chain path that is critical for wide buses (>= 2048 b).
    input_reg_g : if INPUT_REG generate

        process (CLK)
        begin
            if rising_edge(CLK) then
                if (ready(0) = '1') then
                    inp_axi_tdata       <= RX_AXI_TDATA;
                    inp_axi_tkeep       <= RX_AXI_TKEEP;
                    inp_axi_tlast       <= RX_AXI_TLAST;
                    inp_axi_tvalid      <= RX_AXI_TVALID;
                    inp_fracture_en     <= RX_FRACTURE_EN;
                    inp_fracture_offset <= RX_FRACTURE_OFFSET;
                end if;
                if (RESET = '1') then
                    inp_axi_tvalid <= '0';
                end if;
            end if;
        end process;

    else generate

        inp_axi_tdata       <= RX_AXI_TDATA;
        inp_axi_tkeep       <= RX_AXI_TKEEP;
        inp_axi_tlast       <= RX_AXI_TLAST;
        inp_axi_tvalid      <= RX_AXI_TVALID;
        inp_fracture_en     <= RX_FRACTURE_EN;
        inp_fracture_offset <= RX_FRACTURE_OFFSET;

    end generate;

    last_one_i : entity work.LAST_ONE
    generic map (
        DATA_WIDTH => WORD_ITEMS
    )
    port map (
        DI => inp_axi_tkeep,
        DO => rx_axi_tkeep_lastone
    );

    encoder_i : entity work.GEN_ENC
    generic map (
        ITEMS  => WORD_ITEMS,
        DEVICE => DEVICE
    )
    port map (
        DI   => rx_axi_tkeep_lastone,
        ADDR => rx_axi_last_eofpos
    );

    shreg_axi_tdata  (0) <= inp_axi_tdata;
    shreg_last_eofpos(0) <= unsigned(rx_axi_last_eofpos);
    shreg_axi_tlast  (0) <= inp_axi_tlast;
    shreg_axi_tvalid (0) <= inp_axi_tvalid;
    shreg_fracture_en(0) <= inp_fracture_en;

    rx_fracture_offset_deser_g : for f in 0 to MAX_FRACTURES-1 generate
        shreg_fracture_offset(0)(f) <= unsigned(inp_fracture_offset((f+1)*OFF_W-1 downto f*OFF_W));
    end generate;

    -- =====================================================================
    --  Runtime verification assertions (PSL)
    -- =====================================================================

    -- Rule 3a: Each enabled offset must be within the valid byte range of
    -- the current frame (only checkable on the TLAST word where TKEEP
    -- encodes the true end-of-frame position).
    -- psl assert_fracture_offset0_in_range :
    --      assert always ((inp_axi_tvalid = '1' and inp_fracture_en(0) = '1' and inp_axi_tlast = '1')
    --                     -> (shreg_fracture_offset(0)(0) <= shreg_last_eofpos(0))) abort (RESET) @rising_edge(CLK)
    --      report "AXIS_FRAME_FRACTURER: fracture offset(0) exceeds TKEEP valid range on TLAST word!";

    multi_fracture_asserts_g : if MAX_FRACTURES = 2 generate

        -- Rule 1: Enables must be contiguous from index 0 (no gaps).
        -- For MAX_FRACTURES=2: fracture(1) enabled implies fracture(0) enabled.
        -- psl assert_fracture_en_contiguous :
        --      assert always ((inp_axi_tvalid = '1') -> (inp_fracture_en(1) = '0' or inp_fracture_en(0) = '1')) abort (RESET) @rising_edge(CLK)
        --      report "AXIS_FRAME_FRACTURER: RX_FRACTURE_EN has a gap! Enables must be contiguous from index 0.";

        -- Rule 2: Enabled fracture offsets must be strictly increasing.
        -- psl assert_fracture_offset_increasing :
        --      assert always ((inp_axi_tvalid = '1' and inp_fracture_en(0) = '1' and inp_fracture_en(1) = '1')
        --                     -> (shreg_fracture_offset(0)(1) > shreg_fracture_offset(0)(0))) abort (RESET) @rising_edge(CLK)
        --      report "AXIS_FRAME_FRACTURER: fracture offsets are not strictly increasing! offset(1) must be > offset(0).";

        -- Rule 3b: same principle as Rule 3a, just for the 2nd fracture offset.
        -- psl assert_fracture_offset1_in_range :
        --      assert always ((inp_axi_tvalid = '1' and inp_fracture_en(1) = '1' and inp_axi_tlast = '1')
        --                     -> (shreg_fracture_offset(0)(1) <= shreg_last_eofpos(0))) abort (RESET) @rising_edge(CLK)
        --      report "AXIS_FRAME_FRACTURER: fracture offset(1) exceeds TKEEP valid range on TLAST word!";

    end generate;

    -- =====================================================================
    --  Input register(s)
    -- =====================================================================

    input_shreg_g : for s in 0 to SHREG_STAGES-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (ready(s) = '1') then
                    shreg_axi_tdata      (s+1) <= shreg_axi_tdata      (s);
                    shreg_last_eofpos    (s+1) <= shreg_last_eofpos    (s);
                    shreg_axi_tlast      (s+1) <= shreg_axi_tlast      (s);
                    shreg_axi_tvalid     (s+1) <= shreg_axi_tvalid     (s);
                    shreg_fracture_en    (s+1) <= shreg_fracture_en    (s);
                    shreg_fracture_offset(s+1) <= shreg_fracture_offset(s);
                end if;
                if (RESET = '1') then
                    shreg_axi_tvalid(s+1) <= '0';
                end if;
            end if;
        end process;

        ready(s) <= '1' when (fsm_pstate = ST_IDLE) else (not tx_fifo_full and not shreg_pause(s)) or stage_next(s);
    end generate;

    -- Load new data to SHREG (=shift stages) despite a Pause request or TX FIFO being full like so:
    -- 1) shift in all stages when the top-most stage does not have valid data or
    -- 2) keep the top-most stage the same and shift all other stages if the top stage contains valid data or
    -- 3) do not ask for any shift otherwise and leave it up to the Pause or FIFO full signals.
    stage_next_shreg(SHREG_STAGES-2 downto 0)   <= (others => '1');
    stage_next_shreg(SHREG_STAGES-1)            <= '0';

    stage_next <= (others => '1')  when (shreg_axi_tvalid(SHREG_STAGES  ) = '0') else
                  stage_next_shreg when (shreg_axi_tvalid(SHREG_STAGES-1) = '0') else
                  (others => '0');

    -- =====================================================================
    --  Active fracture detection
    -- =====================================================================

    -- Find first enabled fracture in the top stage with offset >= bs_shift.
    top_fracture_search_p : process (all)
    begin
        fracture_in_top_stage <= '0';
        active_top_offset     <= shreg_fracture_offset(SHREG_STAGES)(0);
        for f in 0 to MAX_FRACTURES-1 loop
            if ((shreg_fracture_en(SHREG_STAGES)(f) = '1') and
                (shreg_fracture_offset(SHREG_STAGES)(f) >= bs_shift)) then
                fracture_in_top_stage <= '1';
                active_top_offset     <= shreg_fracture_offset(SHREG_STAGES)(f);
                exit;
            end if;
        end loop;
    end process;

    -- Offset of the fracture being processed (top stage or stage below).
    active_offset <= active_top_offset when (fracture_in_top_stage = '1') else
                     shreg_fracture_offset(SHREG_STAGES-1)(0);

    new_shift <= active_offset + 1;

    -- Check for remaining fractures in the same word after the current one.
    one_fracture_g : if MAX_FRACTURES = 1 generate

        more_fractures       <= '0';
        more_fractures_below <= '0';

    else generate

        -- Another fracture in the top stage after the active one.
        -- The caller contract guarantees offset(1) > offset(0) when both
        -- enables are set, so the offset(1) >= new_shift comparison (where
        -- new_shift = offset(0) + 1) is always satisfied and is omitted to
        -- shorten the critical path through the adder + comparator.
        more_fractures <= '1' when (shreg_fracture_en(SHREG_STAGES)(0) = '1')
                               and (shreg_fracture_offset(SHREG_STAGES)(0) >= bs_shift)
                               and (new_shift /= 0)
                               and (shreg_fracture_en(SHREG_STAGES)(1) = '1') else
                          '0';

        -- Another fracture in the stage below top (will move to top next cycle).
        -- Same reasoning: offset(1) > offset(0) is guaranteed, so
        -- offset(1) >= offset(0) + 1 (= new_shift) is always true.
        more_fractures_below <= '1' when (new_shift /= 0) and (shreg_fracture_en(SHREG_STAGES-1)(1) = '1') else '0';

    end generate;

    -- =====================================================================
    --  FSM
    -- =====================================================================

    fsm_state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((tx_fifo_full = '0') or (fsm_pstate = ST_WAIT) or (fsm_pstate = ST_IDLE)) then
                fsm_pstate <= fsm_nstate;
            end if;
            if (RESET = '1') then
                fsm_pstate <= ST_IDLE;
            end if;
        end if;
    end process;

    fsm_state_transitions_p : process (all)
    begin
        case (fsm_pstate) is
            when ST_IDLE =>
                -- Wait for a valid word between packets.
                if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                    fsm_nstate <= ST_IDLE;
                elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                    fsm_nstate <= ST_FRACTURE;
                elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_FRACTURE =>
                -- Fracture detected in the word at the current Barrel Shifter view.
                -- Sets a new bs_shift according to the fracture offset and pauses the
                -- input SHREG when the fracture is in the top stage, preserving the
                -- unsent remainder of the word.
                if (next_bs_shift = 0) then
                    -- Fracture consumed the entire word remainder.
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                elsif (stg = SHREG_STAGES) then
                    -- Fracture is in the top-most stage.
                    if (more_fractures = '1') then
                        -- Another fracture in the same word.
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES) = '1') then
                        fsm_nstate <= ST_LAST;
                    elsif (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        -- Look one more word ahead as Pause will not apply for this stage.
                        if (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                            fsm_nstate <= ST_WAIT;
                        elsif ((shreg_fracture_en(SHREG_STAGES-2)(0) = '1') and (shreg_fracture_offset(SHREG_STAGES-2)(0) < next_bs_shift)) then
                            fsm_nstate <= ST_FRACTURE;
                        elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < next_bs_shift)) then
                            fsm_nstate <= ST_LAST;
                        else
                            fsm_nstate <= ST_FLOW;
                        end if;
                    elsif ((shreg_fracture_en(SHREG_STAGES-1)(0) = '1') and (shreg_fracture_offset(SHREG_STAGES-1)(0) < next_bs_shift)) then
                        fsm_nstate <= ST_FRACTURE;
                    elsif ((shreg_axi_tlast(SHREG_STAGES-1) = '1') and (shreg_last_eofpos(SHREG_STAGES-1) < next_bs_shift)) then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                else
                    -- Fracture is in the stage below top (stg = SHREG_STAGES-1).
                    if (more_fractures_below = '1') then
                        -- Another fracture in the same word (will move to top next cycle).
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif ((shreg_fracture_en(SHREG_STAGES-2)(0) = '1') and (shreg_fracture_offset(SHREG_STAGES-2)(0) < next_bs_shift)) then
                        fsm_nstate <= ST_FRACTURE;
                    elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < next_bs_shift)) then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                end if;

            when ST_FLOW =>
                -- Normal operation, full word is valid.
                if (bs_shift = 0) then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                -- bs_shift /= 0: the Barrel Shifter spans two SHREG stages, so
                -- both the top and second-top stages are guaranteed to hold valid
                -- data.  Check for Fracture/Last in the second-top stage first,
                -- then look one stage further ahead.
                elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                    fsm_nstate <= ST_FRACTURE;
                elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_LAST;
                elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                    fsm_nstate <= ST_WAIT;
                elsif ((shreg_fracture_en(SHREG_STAGES-2)(0) = '1') and (shreg_fracture_offset(SHREG_STAGES-2)(0) < bs_shift)) then
                    fsm_nstate <= ST_FRACTURE;
                elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_WAIT =>
                -- Handles invalid words (bubbles) inside input frames.
                -- Invalidates output and pauses the top SHREG stage when
                -- bs_shift /= 0, as part of that stage has not been sent yet.
                if (shreg_axi_tvalid(SHREG_STAGES) = '0') then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                    fsm_nstate <= ST_WAIT;
                elsif ((shreg_fracture_en(SHREG_STAGES-2)(0) = '1') and (shreg_fracture_offset(SHREG_STAGES-2)(0) < bs_shift)) then
                    fsm_nstate <= ST_FRACTURE;
                elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_LAST =>
                -- Very last part of the packet (after all Fractures).
                -- Sets output TKEEP and TLAST according to the frame's end position.
                if (shreg_axi_tlast(SHREG_STAGES) = '1') then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_IDLE;
                    elsif (shreg_fracture_en(SHREG_STAGES-1)(0) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                else
                    fsm_nstate <= ST_IDLE;
                end if;

            when others =>
                fsm_nstate <= ST_IDLE;

        end case;
    end process;

    fsm_state_logic_p : process (all)
        variable idx : integer range 0 to WORD_ITEMS-1;
    begin
        case (fsm_pstate) is

            when ST_IDLE =>
                next_bs_shift <= (others => '0');
                shreg_pause   <= (others => '0');
                stg           <= SHREG_STAGES;

                bs_tx_axi_tdata  <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep  <= (others => '0');
                bs_tx_axi_tlast  <= '0';
                bs_tx_axi_tvalid <= '0';

            when ST_FRACTURE =>
                next_bs_shift <= new_shift;
                -- Pause the SHREG when the fracture is in the top stage and there
                -- is a remainder (new_shift /= 0) -- the unsent tail must stay.
                shreg_pause   <= (others => '1') when ((fracture_in_top_stage = '1') and (new_shift /= 0)) else (others => '0');
                stg           <= SHREG_STAGES    when ((fracture_in_top_stage = '1') and (new_shift /= 0)) else SHREG_STAGES-1;

                -- MSB index of the active TKEEP bits.  The calculation differs
                -- depending on whether the fracture is in the top stage (offset
                -- relative to bs_shift) or the stage below (wraps around the word).
                if (fracture_in_top_stage = '1') then
                    idx := to_integer(active_offset - bs_shift);
                else
                    idx := to_integer(to_unsigned(WORD_ITEMS, OFF_W) - bs_shift + active_offset);
                end if;

                bs_tx_axi_tdata               <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                for i in bs_tx_axi_tkeep'range loop
                    if (i <= idx) then
                        bs_tx_axi_tkeep(i) <= '1';
                    else
                        bs_tx_axi_tkeep(i) <= '0';
                    end if;
                end loop;
                bs_tx_axi_tlast               <= '1';
                bs_tx_axi_tvalid              <= shreg_axi_tvalid(SHREG_STAGES  ) when (new_shift = 0) else
                                                 shreg_axi_tvalid(SHREG_STAGES-1)
                                                 or fracture_in_top_stage;

            when ST_FLOW =>
                next_bs_shift <= bs_shift;
                shreg_pause   <= (others => '0');
                stg           <= SHREG_STAGES-1;

                bs_tx_axi_tdata  <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep  <= (others => '1');
                bs_tx_axi_tlast  <= '0';
                bs_tx_axi_tvalid <= shreg_axi_tvalid(SHREG_STAGES) when (bs_shift = 0) else shreg_axi_tvalid(SHREG_STAGES-1);

            when ST_WAIT =>
                next_bs_shift                            <= bs_shift;
                -- Pause the top SHREG stage if it still holds unsent data
                -- (bs_shift /= 0 means the Barrel Shifter view spans into it).
                shreg_pause(shreg_pause'high           ) <= '1' when ((shreg_axi_tvalid(SHREG_STAGES) = '1') and (bs_shift /= 0)) else '0';
                shreg_pause(shreg_pause'high-1 downto 0) <= (others => '0');
                stg                                      <= SHREG_STAGES;

                bs_tx_axi_tdata  <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep  <= (others => '0');
                bs_tx_axi_tlast  <= '0';
                bs_tx_axi_tvalid <= '0';

            when ST_LAST =>
                next_bs_shift <= (others => '0');
                shreg_pause   <= (others => '0');
                stg           <= SHREG_STAGES;

                -- MSB index of the active TKEEP bits.  Calculation depends on
                -- whether TLAST is in the top stage or the stage below.
                if (shreg_axi_tlast(SHREG_STAGES) = '1') then
                    idx := to_integer(shreg_last_eofpos(SHREG_STAGES) - bs_shift);
                else
                    idx := to_integer(to_unsigned(WORD_ITEMS, OFF_W) - bs_shift + shreg_last_eofpos(SHREG_STAGES-1));
                end if;

                bs_tx_axi_tdata               <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                for i in bs_tx_axi_tkeep'range loop
                    if (i <= idx) then
                        bs_tx_axi_tkeep(i) <= '1';
                    else
                        bs_tx_axi_tkeep(i) <= '0';
                    end if;
                end loop;
                bs_tx_axi_tlast               <= '1';
                bs_tx_axi_tvalid              <= '1';

            when others =>
                next_bs_shift <= (others => '0');
                shreg_pause   <= (others => '0');
                stg           <= SHREG_STAGES;

                bs_tx_axi_tdata  <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep  <= (others => '0');
                bs_tx_axi_tlast  <= '0';
                bs_tx_axi_tvalid <= '0';

        end case;
    end process;

    -- =====================================================================
    --  Barrel shifter aligns data after fracture.
    -- =====================================================================

    bs_din(2*AXI_TDATA_WIDTH-1 downto AXI_TDATA_WIDTH) <= shreg_axi_tdata(SHREG_STAGES-1);
    bs_din(  AXI_TDATA_WIDTH-1 downto               0) <= shreg_axi_tdata(SHREG_STAGES);

    bs_shift_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (tx_fifo_full = '0') then
                bs_shift <= next_bs_shift;
            end if;
            if (RESET = '1') then
                bs_shift <= (others => '0');
            end if;
        end if;
    end process;

    barrel_shifter_i : entity work.BARREL_SHIFTER
    generic map (
        DATA_WIDTH => BS_BLOCKS * 8,
        BLOCKS     => BS_BLOCKS,
        SHIFT_LEFT => False
    )
    port map (
        DATA_IN  => bs_din,
        DATA_OUT => bs_dout,
        SEL      => std_logic_vector(resize(bs_shift, log2(BS_BLOCKS)))
    );

    -- =====================================================================
    --  Output FIFO (doesn't work with a register for some reason)
    -- =====================================================================

    tx_fifo_i : entity work.AXIS_FIFO
    generic map (
        AXI_TDATA_WIDTH     => AXI_TDATA_WIDTH,
        AXI_TUSER_WIDTH     => 0,
        ITEMS               => 4,
        FAKE_FIFO           => False,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        FIFO_TYPE           => 1
    )
    port map (
        CLK           => CLK,
        RESET         => RESET,

        RX_AXI_TDATA  => bs_tx_axi_tdata,
        RX_AXI_TKEEP  => bs_tx_axi_tkeep,
        RX_AXI_TUSER  => (others => '0'),
        RX_AXI_TLAST  => bs_tx_axi_tlast,
        RX_AXI_TVALID => bs_tx_axi_tvalid,
        RX_AXI_TREADY => open,
        FULL          => tx_fifo_full,
        AFULL         => open,
        STATUS        => open,

        TX_AXI_TDATA  => TX_AXI_TDATA,
        TX_AXI_TKEEP  => TX_AXI_TKEEP,
        TX_AXI_TUSER  => open,
        TX_AXI_TLAST  => TX_AXI_TLAST,
        TX_AXI_TVALID => TX_AXI_TVALID,
        TX_AXI_TREADY => TX_AXI_TREADY,
        EMPTY         => open,
        AEMPTY        => open
    );

end architecture;
