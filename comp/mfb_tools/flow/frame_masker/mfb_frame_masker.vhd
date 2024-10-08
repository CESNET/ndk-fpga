-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--  Description
-- =========================================================================

-- This component can outputs packets according to the TX_MASK value.
-- See readme.rst for more information and examples (Section "Component specification").

entity MFB_FRAME_MASKER is
    generic(
        -- ====================================================================
        -- MFB parameters
        -- ====================================================================

        -- Any power of two
        REGIONS     : integer := 4;
        -- Any power of two
        REGION_SIZE : integer := 8;
        -- Any power of two
        BLOCK_SIZE  : integer := 8;
        -- Any power of two
        ITEM_WIDTH  : integer := 8;
        -- Any power of two
        META_WIDTH  : integer := 0;

        -- ====================================================================
        -- Other parameters
        -- ====================================================================

        -- Enables MFB_PIPE on RX side
        USE_PIPE    : boolean := false;
        -- "SHREG" or "REG"
        PIPE_TYPE   : string := "SHREG";
        -- FPGA device name: 7SERIES, ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE      : string := "7SERIES"
    );

    port(
        -- ====================================================================
        -- Clock and Reset
        -- ====================================================================

        CLK                 : in  std_logic;
        RESET               : in  std_logic;

        -- ====================================================================
        -- MFB input interface
        -- ====================================================================

        RX_DATA             : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META             : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF              : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF              : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SOF_POS          : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS          : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY          : in  std_logic;
        RX_DST_RDY          : out std_logic;

        -- ====================================================================
        -- MFB output interface - MASKED
        --
        -- With masked packets (current mask applied).
        -- ====================================================================

        TX_DATA             : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META             : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_SOF_POS          : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS          : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        -- SOF with current mask applied.
        TX_SOF_MASKED       : out std_logic_vector(REGIONS-1 downto 0);
        -- EOF with current mask applied.
        TX_EOF_MASKED       : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY          : out std_logic;
        TX_DST_RDY          : in  std_logic;

        -- ====================================================================
        -- Auxiliary output interface - UNMASKED
        --
        -- Withouth the current mask applied.
        -- Either there is a new word (no mask applied) or
        -- an older word that is partially masked by a previous mask (or masks when masking the same word more than two clock cycles).
        -- ====================================================================

        -- SOF before the current mask was applied.
        TX_SOF_UNMASKED     : out std_logic_vector(REGIONS-1 downto 0);
        -- EOF before the current mask was applied.
        TX_EOF_UNMASKED     : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY_UNMASKED : out std_logic;

        -- ====================================================================
        -- Auxiliary output interface - ORIGINAL
        --
        -- With original packet layout (no mask applied).
        -- ====================================================================

        -- Original SOF that was at input.
        TX_SOF_ORIGINAL     : out std_logic_vector(REGIONS-1 downto 0);
        -- Original EOF that was at input.
        TX_EOF_ORIGINAL     : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY_ORIGINAL : out std_logic;

        -- ====================================================================
        -- Mask signal
        -- ====================================================================

        -- Mask per each Region, '1' specifies the request to read a packet starting in this Region.
        -- The Mask is valid with TX_DST_RDY and applied with SOF (TX_SOF_UNMASKED).
        TX_MASK             : in  std_logic_vector(REGIONS-1 downto 0)
    );
end entity;

architecture FULL of MFB_FRAME_MASKER is

    -- --------------------------------------------------------------------------
    --  Constants
    -- --------------------------------------------------------------------------

    constant SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    -- Last Valid implementation.
    -- Options: "serial", "parallel", "prefixsum"
    constant LAST_VLD_IMPL : string := "serial";

    -- --------------------------------------------------------------------------
    --  Signals
    -- --------------------------------------------------------------------------

    -- MFB_PIPE output
    signal pipe_tx_data           : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal pipe_tx_meta           : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal pipe_tx_sof            : std_logic_vector(REGIONS-1 downto 0);
    signal pipe_tx_eof            : std_logic_vector(REGIONS-1 downto 0);
    signal pipe_tx_sof_pos        : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal pipe_tx_eof_pos        : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal pipe_tx_src_rdy        : std_logic;
    signal pipe_tx_dst_rdy        : std_logic;

    -- Stored MFB data word
    signal data_reg               : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0) := (others => '0');
    signal meta_reg               : std_logic_vector(REGIONS*META_WIDTH-1 downto 0)                        := (others => '0');
    signal sof_pos_reg            : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0)                     := (others => '0');
    signal eof_pos_reg            : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0)                     := (others => '0');
    signal sof_reg                : std_logic_vector(REGIONS-1 downto 0)                                   := (others => '0');
    signal eof_reg                : std_logic_vector(REGIONS-1 downto 0)                                   := (others => '0');
    signal src_rdy_reg            : std_logic                                                              := '0';

    -- Load new word logic
    signal valid_mask             : std_logic_vector(REGIONS-1 downto 0);
    signal highest_sof_reg_index  : integer;
    signal some_sof_reg           : std_logic;
    signal masking_done           : std_logic;
    signal load_next_word         : std_logic;

    -- SOF masking
    signal current_accum_mask_sof : std_logic_vector(REGIONS-1 downto 0);
    signal current_sof_reg        : std_logic_vector(REGIONS-1 downto 0);
    signal masked_sof             : std_logic_vector(REGIONS-1 downto 0);

    -- EOF masking
    signal lv_rx_data             : std_logic_vector(REGIONS-1 downto 0);
    signal lv_rx_vld              : std_logic_vector(REGIONS-1 downto 0);
    signal lv_rx_src_rdy          : std_logic;
    signal lv_tx_data             : std_logic_vector(REGIONS-1 downto 0);
    signal lv_tx_data_presc       : std_logic_vector(REGIONS-1 downto 0);
    signal lv_tx_dst_rdy          : std_logic;

    signal u_array_sof_pos        : u_array_t       (REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal u_array_eof_pos        : u_array_t       (REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal whole_frame            : std_logic_vector(REGIONS-1 downto 0);
    signal eof_mask               : std_logic_vector(REGIONS-1 downto 0);
    signal masked_eof             : std_logic_vector(REGIONS-1 downto 0);

    signal current_accum_mask_eof : std_logic_vector(REGIONS-1 downto 0);
    signal current_eof_reg        : std_logic_vector(REGIONS-1 downto 0);

    -- Output logic
    signal pkt_cont               : std_logic_vector(REGIONS   downto 0);

begin

    -- --------------------------------------------------------------------------
    --  MFB_PIPE
    -- --------------------------------------------------------------------------

    mfb_pipe_i : entity work.MFB_PIPE
    generic map (
        REGIONS     => REGIONS     ,
        REGION_SIZE => REGION_SIZE ,
        BLOCK_SIZE  => BLOCK_SIZE  ,
        ITEM_WIDTH  => ITEM_WIDTH  ,
        META_WIDTH  => META_WIDTH  ,

        FAKE_PIPE   => not USE_PIPE,
        USE_DST_RDY => True        ,
        PIPE_TYPE   => PIPE_TYPE   ,
        DEVICE      => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => RX_DATA        ,
        RX_META    => RX_META        ,
        RX_SOF     => RX_SOF         ,
        RX_EOF     => RX_EOF         ,
        RX_SOF_POS => RX_SOF_POS     ,
        RX_EOF_POS => RX_EOF_POS     ,
        RX_SRC_RDY => RX_SRC_RDY     ,
        RX_DST_RDY => RX_DST_RDY     ,

        TX_DATA    => pipe_tx_data   ,
        TX_META    => pipe_tx_meta   ,
        TX_SOF     => pipe_tx_sof    ,
        TX_EOF     => pipe_tx_eof    ,
        TX_SOF_POS => pipe_tx_sof_pos,
        TX_EOF_POS => pipe_tx_eof_pos,
        TX_SRC_RDY => pipe_tx_src_rdy,
        TX_DST_RDY => pipe_tx_dst_rdy
    );

    pipe_tx_dst_rdy <= load_next_word;

    -- --------------------------------------------------------------------------
    --  Data registers
    -- --------------------------------------------------------------------------

    -- Stores the data word
    data_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (load_next_word = '1') then
                data_reg    <= pipe_tx_data;
                meta_reg    <= pipe_tx_meta;
                sof_reg     <= pipe_tx_sof;
                eof_reg     <= pipe_tx_eof;
                sof_pos_reg <= pipe_tx_sof_pos;
                eof_pos_reg <= pipe_tx_eof_pos;
                src_rdy_reg <= pipe_tx_src_rdy;
            end if;
        end if;
    end process;

    -- --------------------------------------------------------------------------
    --  Assess whether new data word can be loaded
    -- --------------------------------------------------------------------------

    valid_mask <= TX_MASK and TX_DST_RDY;

    -- Finds the index of the highest SOF bit
    highest_sof_reg_index_p : process (all)
    begin
        highest_sof_reg_index <= 0; -- Default val doesn't matter - it is not applied when no SOF is present
        for r in REGIONS-1 downto 0 loop
            if (sof_reg(r) = '1') then
                highest_sof_reg_index <= r;
                exit;
            end if;
        end loop;
    end process;

    -- Logic to signal readiness for the next word
    some_sof_reg <= '1' when (or sof_reg = '1') and (src_rdy_reg = '1') else '0';
    masking_done <= '1' when (some_sof_reg = '1') and (valid_mask(highest_sof_reg_index) = '1') else '0';
    load_next_word <= '1' when ((masking_done = '1') or (some_sof_reg = '0')) and (TX_DST_RDY = '1') else '0';

    -- --------------------------------------------------------------------------
    --  SOF masking logic
    -- --------------------------------------------------------------------------

    -- Accumulate SOF mask
    process(all)
    begin
        current_accum_mask_sof <= (others => '1');
        for r in REGIONS-1 downto 0 loop
            if (masked_sof(r) = '1') then
                current_accum_mask_sof(r downto 0) <= (others => '0');
                exit;
            end if;
        end loop;
    end process;

    -- Apply the SOF mask
    process(CLK)
    begin
        if rising_edge(CLK) then
            current_sof_reg <= current_sof_reg and current_accum_mask_sof;
            if (RESET = '1') or (load_next_word = '1') then
                current_sof_reg <= pipe_tx_sof;
            end if;
        end if;
    end process;

    masked_sof <= current_sof_reg and valid_mask;

    -- --------------------------------------------------------------------------
    --  EOF masking logic - derived from SOF masking logic
    -- --------------------------------------------------------------------------

    -- This basically just propagates the SOF mask to the following Region(s)
    lv_rx_data    <= masked_sof;
    lv_rx_vld     <= current_sof_reg;
    lv_rx_src_rdy <= src_rdy_reg;

    last_vld_i : entity work.MVB_AGGREGATE_LAST_VLD
    generic map(
        ITEMS          => REGIONS      ,
        ITEM_WIDTH     => 1            ,
        IMPLEMENTATION => LAST_VLD_IMPL,
        INTERNAL_REG   => true
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA         => lv_rx_data      ,
        RX_VLD          => lv_rx_vld       ,
        RX_SRC_RDY      => lv_rx_src_rdy   ,
        RX_DST_RDY      => open            ,

        REG_IN_DATA     => (others => '0') ,
        REG_IN_VLD      => '0'             ,
        REG_OUT_DATA    => open            ,
        REG_OUT_VLD     => open            ,
        REG_OUT_WR      => open            ,

        TX_DATA         => lv_tx_data      ,
        TX_VLD          => open            ,
        TX_PRESCAN_DATA => lv_tx_data_presc,
        TX_PRESCAN_VLD  => open            ,
        TX_SRC_RDY      => open            ,
        TX_DST_RDY      => lv_tx_dst_rdy
    );

    lv_tx_dst_rdy <= TX_DST_RDY;

    -- If the SOF mask is updated in this Region (one pkt ends, another begins), select the mask from the preious Region
    eof_mask_g : for r in 0 to REGIONS-1 generate
        eof_mask(r) <= lv_tx_data(r) when (whole_frame(r) = '1') else lv_tx_data_presc(r);
    end generate;

    masked_eof <= eof_reg and eof_mask;

    u_array_sof_pos <= slv_arr_to_u_arr(slv_array_downto_deser(sof_pos_reg, REGIONS));
    u_array_eof_pos <= slv_arr_to_u_arr(slv_array_downto_deser(eof_pos_reg, REGIONS));
    whole_frame_logic_g : for r in 0 to REGIONS-1 generate
        -- Indicates that the frame starts and ends in the same word
        whole_frame(r) <= '1' when (sof_reg(r) = '1' and eof_reg(r) = '1') and
                                   (u_array_sof_pos(r) < u_array_eof_pos(r)(EOF_POS_WIDTH-1 downto log2(BLOCK_SIZE))) else '0';
    end generate;

    process(CLK)
    begin
        if rising_edge(CLK) then
            current_eof_reg <= eof_reg and current_accum_mask_eof;
            if (RESET = '1') or (load_next_word = '1') then
                current_eof_reg <= pipe_tx_eof;
            end if;
        end if;
    end process;

    -- EOF Unmasked
    process(all)
    begin
        current_accum_mask_eof <= (others => '1');
        for r in REGIONS-1 downto 0 loop
            if (masked_eof(r) = '1') then
                current_accum_mask_eof(r downto 0) <= (others => '0');
                exit;
            end if;
        end loop;
    end process;

    -- --------------------------------------------------------------------------
    --  MFB output
    -- --------------------------------------------------------------------------

    -- logic for determining if the packet continues from the previous Region or not
    pkt_cont_g : for r in 0 to REGIONS-1 generate
        pkt_cont(r+1) <= (    masked_sof(r) and not masked_eof(r) and not pkt_cont(r)) or
                         (    masked_sof(r) and     masked_eof(r) and     pkt_cont(r)) or
                         (not masked_sof(r) and not masked_eof(r) and     pkt_cont(r));
    end generate;

    -- Transfer to the next word
    pkt_continues_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pkt_cont(0) <= '0';
            elsif (TX_DST_RDY = '1') and (src_rdy_reg = '1') then
                pkt_cont(0) <= pkt_cont(REGIONS);
            end if;
        end if;
    end process;

    -- Standard output interface with masked packets (SOFs and EOFs).
    TX_DATA       <= data_reg;
    TX_META       <= meta_reg;
    TX_SOF_MASKED <= masked_sof;
    TX_EOF_MASKED <= masked_eof;
    TX_SOF_POS    <= sof_pos_reg;
    TX_EOF_POS    <= eof_pos_reg;
    TX_SRC_RDY    <= src_rdy_reg and ((or masked_sof) or (or masked_eof) or (pkt_cont(0)));

    TX_SOF_UNMASKED     <= current_sof_reg;
    TX_EOF_UNMASKED     <= current_eof_reg;
    TX_SRC_RDY_UNMASKED <= src_rdy_reg;

    TX_SOF_ORIGINAL     <= sof_reg;
    TX_EOF_ORIGINAL     <= eof_reg;
    TX_SRC_RDY_ORIGINAL <= src_rdy_reg;

end architecture;
