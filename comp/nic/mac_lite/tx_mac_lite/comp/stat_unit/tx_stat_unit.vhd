-- stat_unit.vhd: TX MAC Lite statistics counters
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_STAT_UNIT is
    generic(
        -- Number of regions within a data word, must be power of 2.
        MFB_REGIONS        : natural := 4;
        -- Width of length signals in bits.
        LENGTH_WIDTH       : natural := 16;
        -- Which FPGA will this component be used on? Options: 7SERIES, ULTRASCALE, STRATIX10 - this is only important for the counter
        DEVICE             : string  := "STRATIX10";
        -- Use counters in DSP blocks?
        USE_DSP_CNT        : boolean := False;
        -- Frame length is counted with CRC
        FRAME_LEN_WITH_CRC : boolean := False
    );
    port(
        -- =====================================================================
        --  CLOCK AND RESET
        -- =====================================================================
        CLK                         : in  std_logic;
        RESET                       : in  std_logic;

        -- =====================================================================
        --  STATS INPUT
        -- =====================================================================
        -- CONTROL INTERFACE
        CTRL_STROBE_CNT             : in  std_logic;
        CTRL_RESET_CNT              : in  std_logic;
        -- INCREMENTS INTERFACE
        VECTOR_INC_TOTAL_FRAMES     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        VECTOR_INC_SENT_FRAMES      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        VECTOR_INC_DISCARDED        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- FRAME LENGTH
        FRAME_LENGTH                : in  std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
        FRAME_LENGTH_VLD            : in  std_logic_vector(MFB_REGIONS-1 downto 0);

        -- =====================================================================
        --  STATS OUTPUT
        -- =====================================================================
        STAT_TOTAL_FRAMES           : out std_logic_vector(63 downto 0);
        STAT_TOTAL_SENT_FRAMES      : out std_logic_vector(63 downto 0);
        STAT_TOTAL_SENT_OCTECTS     : out std_logic_vector(63 downto 0);
        STAT_TOTAL_DISCARDED_FRAMES : out std_logic_vector(63 downto 0)
    );
end entity;

architecture FULL of TX_MAC_LITE_STAT_UNIT is

    constant REGION_CNT_W       : natural := max(log2(MFB_REGIONS+1), 2);

    signal frame_len_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal frame_len_full_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal frame_len_full       : std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);

    signal inc_total_frames     : std_logic_vector(REGION_CNT_W-1 downto 0);
    signal inc_sent_frames      : std_logic_vector(REGION_CNT_W-1 downto 0);
    signal inc_sent_bytes       : std_logic_vector(LENGTH_WIDTH-1 downto 0);
    signal inc_discarded_frames : std_logic_vector(REGION_CNT_W-1 downto 0);

    signal cnt_total_frames     : std_logic_vector(64-1 downto 0);
    signal cnt_sent_frames      : std_logic_vector(64-1 downto 0);
    signal cnt_sent_bytes       : std_logic_vector(64-1 downto 0);
    signal cnt_discarded_frames : std_logic_vector(64-1 downto 0);

begin

    -- =========================================================================
    --  FIRST STAGE
    -- =========================================================================

    -- Sum One counters --------------------------------------------------------

    sum_one_total_frame_i : entity work.SUM_ONE
    generic map(
        INPUT_WIDTH  => MFB_REGIONS,
        OUTPUT_WIDTH => REGION_CNT_W,
        OUTPUT_REG   => True
    )
    port map(
        -- CLOCK AND RESET
        CLK      => CLK,
        RESET    => RESET,
        -- INPUT
        DIN      => VECTOR_INC_TOTAL_FRAMES,
        DIN_MASK => (others => '1'),
        DIN_VLD  => '1',
        -- OUTPUT
        DOUT     => inc_total_frames,
        DOUT_VLD => open
    );

    sum_one_sent_frame_i : entity work.SUM_ONE
    generic map(
        INPUT_WIDTH  => MFB_REGIONS,
        OUTPUT_WIDTH => REGION_CNT_W,
        OUTPUT_REG   => True
    )
    port map(
        -- CLOCK AND RESET
        CLK      => CLK,
        RESET    => RESET,
        -- INPUT
        DIN      => VECTOR_INC_SENT_FRAMES,
        DIN_MASK => (others => '1'),
        DIN_VLD  => '1',
        -- OUTPUT
        DOUT     => inc_sent_frames,
        DOUT_VLD => open
    );

    sum_one_discarded_frame_i : entity work.SUM_ONE
    generic map(
        INPUT_WIDTH  => MFB_REGIONS,
        OUTPUT_WIDTH => REGION_CNT_W,
        OUTPUT_REG   => True
    )
    port map(
        -- CLOCK AND RESET
        CLK      => CLK,
        RESET    => RESET,
        -- INPUT
        DIN      => VECTOR_INC_DISCARDED,
        DIN_MASK => (others => '1'),
        DIN_VLD  => '1',
        -- OUTPUT
        DOUT     => inc_discarded_frames,
        DOUT_VLD => open
    );

    -- Sum of inc sent bytes ---------------------------------------------------

    frame_len_arr <= slv_array_deser(FRAME_LENGTH,MFB_REGIONS,LENGTH_WIDTH);

    frame_len_full_g : for r in 0 to MFB_REGIONS-1 generate
        frame_len_full_g2 : if (FRAME_LEN_WITH_CRC = False) generate
            -- Frame length was counted without CRC (4B)
            frame_len_full_arr(r) <= std_logic_vector(resize(unsigned(frame_len_arr(r)),LENGTH_WIDTH) + 4);
        else generate
            -- Frame length was counted with CRC
            frame_len_full_arr(r) <= std_logic_vector(resize(unsigned(frame_len_arr(r)),LENGTH_WIDTH));
        end generate;
    end generate;

    frame_len_full <= slv_array_ser(frame_len_full_arr,MFB_REGIONS,LENGTH_WIDTH);

    sum_inc_total_bytes_i : entity work.PIPE_TREE_ADDER
    generic map (
        ITEMS      => MFB_REGIONS,
        DATA_WIDTH => LENGTH_WIDTH,
        LATENCY    => 1
    )
    port map (
        CLK      => CLK,
        RESET    => '0',
        IN_DATA  => frame_len_full,
        IN_VLD   => FRAME_LENGTH_VLD,
        OUT_DATA => inc_sent_bytes
    );

    -- =========================================================================
    --  SECOND STAGE
    -- =========================================================================

    cnt_total_frames_i : entity work.DSP_COUNTER
    generic map (
        INPUT_WIDTH  => REGION_CNT_W,
        OUTPUT_WIDTH => 64,
        INPUT_REGS   => true,
        DEVICE       => DEVICE,
        DSP_ENABLE   => USE_DSP_CNT
    )
    port map (
        CLK       => CLK,
        CLK_EN    => '1',
        RESET     => CTRL_RESET_CNT,
        INCREMENT => inc_total_frames,
        MAX_VAL   => (others => '1'),
        RESULT    => cnt_total_frames
    );

    cnt_sent_frames_i : entity work.DSP_COUNTER
    generic map (
        INPUT_WIDTH  => REGION_CNT_W,
        OUTPUT_WIDTH => 64,
        INPUT_REGS   => true,
        DEVICE       => DEVICE,
        DSP_ENABLE   => USE_DSP_CNT
    )
    port map (
        CLK       => CLK,
        CLK_EN    => '1',
        RESET     => CTRL_RESET_CNT,
        INCREMENT => inc_sent_frames,
        MAX_VAL   => (others => '1'),
        RESULT    => cnt_sent_frames
    );

    cnt_discarded_frames_i : entity work.DSP_COUNTER
    generic map (
        INPUT_WIDTH  => REGION_CNT_W,
        OUTPUT_WIDTH => 64,
        INPUT_REGS   => true,
        DEVICE       => DEVICE,
        DSP_ENABLE   => USE_DSP_CNT
    )
    port map (
        CLK       => CLK,
        CLK_EN    => '1',
        RESET     => CTRL_RESET_CNT,
        INCREMENT => inc_discarded_frames,
        MAX_VAL   => (others => '1'),
        RESULT    => cnt_discarded_frames
    );

    cnt_sent_bytes_i : entity work.DSP_COUNTER
    generic map (
        INPUT_WIDTH  => LENGTH_WIDTH,
        OUTPUT_WIDTH => 64,
        INPUT_REGS   => true,
        DEVICE       => DEVICE,
        DSP_ENABLE   => USE_DSP_CNT
    )
    port map (
        CLK       => CLK,
        CLK_EN    => '1',
        RESET     => CTRL_RESET_CNT,
        INCREMENT => inc_sent_bytes,
        MAX_VAL   => (others => '1'),
        RESULT    => cnt_sent_bytes
    );

    -- =========================================================================
    --  LAST STAGE
    -- =========================================================================

    cnt_out_regs_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (CTRL_STROBE_CNT = '1') then
                STAT_TOTAL_FRAMES           <= cnt_total_frames;
                STAT_TOTAL_SENT_FRAMES      <= cnt_sent_frames;
                STAT_TOTAL_SENT_OCTECTS     <= cnt_sent_bytes;
                STAT_TOTAL_DISCARDED_FRAMES <= cnt_discarded_frames;
            end if;
        end if;
    end process;

end architecture;
