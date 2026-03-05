-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- This module divides packets in the current word at offset specified by the RX_FRACTURE_OFFSET signal.
-- New packets are aligned to the start of the word as expected by the AXI-Stream protocol.
--
-- .. warning::
--
--      While RX_AXI_TLAST and RX_FRACTURE_EN are active, RX_FRACTURE_OFFSET must be within the frame's range (within valid bytes specified by RX_AXI_TKEEP)!
--
-- Architecture
-- ------------
--
-- This component's code may be somewhat confusing due to the FSM and its complicated state transition conditions and state logic.
-- However, the overall architecture is quite simple.
-- The component consists of three main blocks:
--
-- - Input shift register (two or more stages according to the :vhdl:genconstant:`INPUT_REGS <AXIS_FRAME_FRACTURER.INPUT_REGS>` generic)
-- - :ref:`Barrel Shifter <barrel_shifter>` (BS)
-- - Output AXI Stream FIFO
--
-- The core of the component is the FSM that
--
-- - aligns new frames after breaking to the start of the word (with the help of the BS),
-- - sets the BS's output TLAST and TKEEP, effectively breaking the frames, and
-- - pauses the input shift register when data need to be stored a little longer.
--
--
-- In case you need to understand this component's code or modify it, see this :ref:`section <axis_frfr_diagrams_and_notes>` below.
--
entity AXIS_FRAME_FRACTURER is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH  : natural := 512;
        -- Number of input registers, must be at least 2.
        INPUT_REGS       : natural := 2;
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

        -- Fracture enable. Valid with RX_AXI_TVALID.
        RX_FRACTURE_EN     : in  std_logic;
        -- Fracture offset specifies the last byte of the current frame.
        RX_FRACTURE_OFFSET : in  std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);

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
    constant SHREG_STAGES  : natural := INPUT_REGS;
    constant BS_BLOCKS     : natural := 2*WORD_ITEMS;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    type fsm_t is (ST_IDLE, ST_FLOW, ST_FRACTURE, ST_WAIT, ST_LAST);

    signal rx_axi_tkeep_lastone     : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal rx_axi_last_eofpos       : std_logic_vector(log2(WORD_ITEMS)-1 downto 0);

    signal stage_next               : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal stage_next_shreg         : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal ready                    : std_logic_vector(SHREG_STAGES-1 downto 0);

    signal shreg_axi_tdata          : slv_array_t(SHREG_STAGES downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal shreg_axi_tlast          : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_axi_tvalid         : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_fracture_en        : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_fracture_offset    : u_array_t(SHREG_STAGES downto 0)(log2(WORD_ITEMS)-1 downto 0);
    signal shreg_last_eofpos        : u_array_t(SHREG_STAGES downto 0)(log2(WORD_ITEMS)-1 downto 0);

    signal fsm_pstate               : fsm_t;
    signal fsm_nstate               : fsm_t;

    -- Selected stage of the input SHREG.
    -- Indicates how far we need to look ahead (0 = top-most stage, 1 = the second-top stage).
    signal stg                      : integer range 1 to SHREG_STAGES;

    signal fracture_in_top_stage    : std_logic;
    signal new_shift                : unsigned(log2(WORD_ITEMS)-1 downto 0);

    signal shreg_pause              : std_logic_vector(SHREG_STAGES-1 downto 0);
    signal next_bs_shift            : unsigned(log2(WORD_ITEMS)-1 downto 0);

    signal bs_tx_axi_tdata          : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal bs_tx_axi_tkeep          : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal bs_tx_axi_tlast          : std_logic;
    signal bs_tx_axi_tvalid         : std_logic;
    signal tx_fifo_full             : std_logic;

    signal bs_din                   : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);
    signal bs_dout                  : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);
    signal bs_shift                 : unsigned(log2(WORD_ITEMS)-1 downto 0);

begin

    assert INPUT_REGS >= 2
        report "AXIS_FRAME_FRACTURER: the lowest number of INPUT_REGS is 2."
        severity Failure;

    -- =====================================================================
    --  Input assignments
    -- =====================================================================

    RX_AXI_TREADY <= ready(0);

    last_one_i : entity work.LAST_ONE
    generic map (
        DATA_WIDTH => WORD_ITEMS
    )
    port map (
        DI => RX_AXI_TKEEP,
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

    shreg_axi_tdata      (0) <= RX_AXI_TDATA;
    shreg_last_eofpos    (0) <= unsigned(rx_axi_last_eofpos);
    shreg_axi_tlast      (0) <= RX_AXI_TLAST;
    shreg_axi_tvalid     (0) <= RX_AXI_TVALID;
    shreg_fracture_en    (0) <= RX_FRACTURE_EN;
    shreg_fracture_offset(0) <= unsigned(RX_FRACTURE_OFFSET);

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
                -- The ST_IDLE state occurs only between packets. Just waits for a valid word.
                if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                    fsm_nstate <= ST_IDLE;
                elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_FRACTURE;
                elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_FRACTURE =>
                -- The ST_FRACTURE state occurs when a Fracture is detected in the word specified by current shift of the Barrel Shifter (bs_shift).
                -- It sets a new bs_shift according to the fracture offset and sets output tkeep and tlast signals.
                -- Also pauses the input if the Fracture is in the top-most word of the SHREG, as it is important to store the unsent rest of the word.
                if (next_bs_shift = 0) then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                -- (stg = 2) indicates the Fracture is in the top-most word (stage) of the SHREG.
                elsif (stg = 2) then
                    if (shreg_axi_tlast(SHREG_STAGES) = '1') then
                        fsm_nstate <= ST_LAST;
                    elsif (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        -- Look one more word ahead as Pause will not apply for this stage.
                        if (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                            fsm_nstate <= ST_WAIT;
                        elsif ((shreg_fracture_en(SHREG_STAGES-2) = '1') and (shreg_fracture_offset(SHREG_STAGES-2) < next_bs_shift)) then
                            fsm_nstate <= ST_FRACTURE;
                        elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < next_bs_shift)) then
                            fsm_nstate <= ST_LAST;
                        else
                            fsm_nstate <= ST_FLOW;
                        end if;
                    elsif ((shreg_fracture_en(SHREG_STAGES-1) = '1') and (shreg_fracture_offset(SHREG_STAGES-1) < next_bs_shift)) then
                        fsm_nstate <= ST_FRACTURE;
                    elsif ((shreg_axi_tlast(SHREG_STAGES-1) = '1') and (shreg_last_eofpos(SHREG_STAGES-1) < next_bs_shift)) then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                -- stg = 1 -> indicates the Fracture is in the 2nd top-most word (stage) of the SHREG.
                elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_LAST;
                elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                    fsm_nstate <= ST_WAIT;
                elsif ((shreg_fracture_en(SHREG_STAGES-2) = '1') and (shreg_fracture_offset(SHREG_STAGES-2) < next_bs_shift)) then
                    fsm_nstate <= ST_FRACTURE;
                elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < next_bs_shift)) then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_FLOW =>
                -- The ST_FLOW state occurs during normal operation when no Fracture is needed.
                -- The full word specified by current shift of the Barrel Shifter (bs_shift) is valid.
                if (bs_shift = 0) then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                -- If (bs_shift /= 0) and we are in this state, the top-most and second-top stages have valid data.
                -- Hence check for Fracture/Last in the second-top stage, then in the one before.
                elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_FRACTURE;
                elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                    fsm_nstate <= ST_LAST;
                elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                    fsm_nstate <= ST_WAIT;
                elsif ((shreg_fracture_en(SHREG_STAGES-2) = '1') and (shreg_fracture_offset(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_FRACTURE;
                elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_WAIT =>
                -- The ST_WAIT state handles invalid words inside input frames.
                -- Invalidates output and pauses the top-most SHREG stage if a part of it has not been sent yet.
                if (shreg_axi_tvalid(SHREG_STAGES) = '0') then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_WAIT;
                    elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_FRACTURE;
                    elsif (shreg_axi_tlast(SHREG_STAGES-1) = '1') then
                        fsm_nstate <= ST_LAST;
                    else
                        fsm_nstate <= ST_FLOW;
                    end if;
                elsif (shreg_axi_tvalid(SHREG_STAGES-2) = '0') then
                    fsm_nstate <= ST_WAIT;
                elsif ((shreg_fracture_en(SHREG_STAGES-2) = '1') and (shreg_fracture_offset(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_FRACTURE;
                elsif ((shreg_axi_tlast(SHREG_STAGES-2) = '1') and (shreg_last_eofpos(SHREG_STAGES-2) < bs_shift)) then
                    fsm_nstate <= ST_LAST;
                else
                    fsm_nstate <= ST_FLOW;
                end if;

            when ST_LAST =>
                -- The ST_LAST state handles the very last part of the packet (after all Fractures).
                -- Sets output tkeep and tlast signals.
                if (shreg_axi_tlast(SHREG_STAGES) = '1') then
                    if (shreg_axi_tvalid(SHREG_STAGES-1) = '0') then
                        fsm_nstate <= ST_IDLE;
                    elsif (shreg_fracture_en(SHREG_STAGES-1) = '1') then
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

    fracture_in_top_stage <= shreg_fracture_en(SHREG_STAGES) when (shreg_fracture_offset(SHREG_STAGES) >= bs_shift) else '0';

    new_shift <= shreg_fracture_offset(SHREG_STAGES  ) + 1 when (fracture_in_top_stage = '1') else
                 shreg_fracture_offset(SHREG_STAGES-1) + 1;

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
                shreg_pause   <= (others => '1') when ((fracture_in_top_stage = '1') and (new_shift /= 0)) else (others => '0');
                stg           <= SHREG_STAGES    when ((fracture_in_top_stage = '1') and (new_shift /= 0)) else SHREG_STAGES-1;

                -- Index of the Most Significant `active` Bit of the output TKEEP signal.
                -- Different calculations according to the stage where the last part is located.
                if (fracture_in_top_stage = '1') then
                    idx := to_integer(shreg_fracture_offset(SHREG_STAGES) - bs_shift);
                else
                    idx := to_integer(to_unsigned(WORD_ITEMS, log2(WORD_ITEMS)) - bs_shift + shreg_fracture_offset(stg));
                end if;

                bs_tx_axi_tdata               <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep               <= (others => '0');
                bs_tx_axi_tkeep(idx downto 0) <= (others => '1');
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

                -- Index of the Most Significant `active` Bit of the output TKEEP signal.
                -- Different calculations according to the stage where the Last part is located.
                if (shreg_axi_tlast(SHREG_STAGES) = '1') then
                    idx := to_integer(shreg_last_eofpos(SHREG_STAGES) - bs_shift);
                else
                    idx := to_integer(to_unsigned(WORD_ITEMS, log2(WORD_ITEMS)) - bs_shift + shreg_last_eofpos(SHREG_STAGES-1));
                end if;

                bs_tx_axi_tdata               <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);
                bs_tx_axi_tkeep               <= (others => '0');
                bs_tx_axi_tkeep(idx downto 0) <= (others => '1');
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
        RX_AXI_TDEST  => (others => '0'),
        RX_AXI_TLAST  => bs_tx_axi_tlast,
        RX_AXI_TVALID => bs_tx_axi_tvalid,
        RX_AXI_TREADY => open,
        FULL          => tx_fifo_full,
        AFULL         => open,
        STATUS        => open,

        TX_AXI_TDATA  => TX_AXI_TDATA,
        TX_AXI_TKEEP  => TX_AXI_TKEEP,
        TX_AXI_TDEST  => open,
        TX_AXI_TLAST  => TX_AXI_TLAST,
        TX_AXI_TVALID => TX_AXI_TVALID,
        TX_AXI_TREADY => TX_AXI_TREADY,
        EMPTY         => open,
        AEMPTY        => open
    );

end architecture;
