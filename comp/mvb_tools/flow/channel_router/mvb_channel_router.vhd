-- mvb_channel_router.vhd
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

--  NOTES:
--  Round-robin distribution control register format:
--  31             23              15             7           0
-- +----------------------------------------------------------+
-- |     RSVD     |     ch_max    |    ch_min    |    incr    |
-- +----------------------------------------------------------+
-- Controls distribution of ethernet frames received from network to DMA channels
--   incr   : RR increment. 0 = round-robin disable (stay on current channel). Default 0x0
--   ch_min : low DMA channel limit for round-robin distribution. Default 0x0
--   ch_max : high DMA channel limit for round-robin distribution. Default 0x0
-- Examples:
--    0x000000: Do not distribute frames - frame from Eth chan N is routed to DMA chan N
--    0xff0001: Distribute frames to all available DMA channels
--    0x070401: Distribute frames to DMA channels 4 to 7
--    0xff0002: Distribute frames to even DMA channels
--    0x050501: Send all frames to DMA channel 5 only

entity MVB_CHANNEL_ROUTER is
    generic(
        -- MVB parameters: number of items in word
        ITEMS         : natural := 4;
        -- MVB parameters: width of item in bits
        ITEM_WIDTH    : natural := 32;
        -- Total number of source channels, max value = DST_CHANNELS
        -- max value = DST_CHANNELS
        SRC_CHANNELS  : natural := 4;
        -- Total number of destination channels, max value = 256
        DST_CHANNELS  : natural := 16;
        -- Optimized mode for better timing (best for high ITEMS) with limited
        -- configuration: (ch_max-ch_min+1) must be power of two
        OPT_MODE      : boolean := False;
        -- Name of FPGA device
        DEVICE        : string  := "ULTRASCALE"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- =====================================================================
        -- CONTROL REGISTERS
        -- =====================================================================
        CTRL_REGS    : in  std_logic_vector(SRC_CHANNELS*32-1 downto 0);
        CTRL_REGS_WR : in  std_logic_vector(SRC_CHANNELS-1 downto 0);

        -- =====================================================================
        -- INPUT MVB INTERFACE
        -- =====================================================================
        RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_CHANNEL : in  std_logic_vector(ITEMS*log2(SRC_CHANNELS)-1 downto 0);
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        -- OUTPUT MVB INTERFACE
        -- =====================================================================
        TX_DATA    : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_CHANNEL : out std_logic_vector(ITEMS*log2(DST_CHANNELS)-1 downto 0);
        TX_VLD     : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB_CHANNEL_ROUTER is

    constant SRC_CHANNELS_W : natural := max(log2(SRC_CHANNELS),1);
    constant DST_CHANNELS_W : natural := log2(DST_CHANNELS);

    signal s_ctrl_regs_arr  : slv_array_t(SRC_CHANNELS-1 downto 0)(32-1 downto 0);
    signal s_chan_max       : u_array_t(SRC_CHANNELS-1 downto 0)(8-1 downto 0);
    signal s_chan_min       : u_array_t(SRC_CHANNELS-1 downto 0)(8-1 downto 0);
    signal s_chan_inc       : u_array_t(SRC_CHANNELS-1 downto 0)(8-1 downto 0);
    signal s_chan_diff      : u_array_t(SRC_CHANNELS-1 downto 0)(8-1 downto 0);

    signal s_valid_word     : std_logic;
    signal s_src_chan_slv   : slv_array_t(ITEMS-1 downto 0)(SRC_CHANNELS_W-1 downto 0);
    signal s_src_chan       : u_array_t(ITEMS-1 downto 0)(SRC_CHANNELS_W-1 downto 0);
    signal s_mux_chan_inc   : u_array_t(ITEMS-1 downto 0)(8-1 downto 0);

    signal s_chan_cnt       : u_array_t(SRC_CHANNELS-1 downto 0)(DST_CHANNELS_W-1 downto 0);
    signal s_chan_cnt_arr   : u_array_2d_t(SRC_CHANNELS-1 downto 0)(ITEMS+1-1 downto 0)(DST_CHANNELS_W-1 downto 0);
    signal s_chan_cnt_next  : u_array_t(SRC_CHANNELS-1 downto 0)(DST_CHANNELS_W-1 downto 0);
    signal s_chan_cnt_items : u_array_2d_t(SRC_CHANNELS-1 downto 0)(ITEMS+1-1 downto 0)(DST_CHANNELS_W-1 downto 0);
    signal s_chan_cnt_inc   : u_array_2d_t(SRC_CHANNELS-1 downto 0)(ITEMS-1 downto 0)(DST_CHANNELS_W+1-1 downto 0);
    signal s_chan_cnt_out   : slv_array_t(ITEMS-1 downto 0)(DST_CHANNELS_W-1 downto 0);
    signal s_dst_channel    : slv_array_t(ITEMS-1 downto 0)(DST_CHANNELS_W-1 downto 0);

begin

    -- =========================================================================
    --  CONTROL REGISTERS
    -- =========================================================================

    s_ctrl_regs_arr <= slv_array_deser(CTRL_REGS,SRC_CHANNELS,32);

    ctrl_regs_decode_g : for i in 0 to SRC_CHANNELS-1 generate
        s_chan_max(i) <= unsigned(s_ctrl_regs_arr(i)(24-1 downto 16));
        s_chan_min(i) <= unsigned(s_ctrl_regs_arr(i)(16-1 downto 8));
        s_chan_inc(i) <= unsigned(s_ctrl_regs_arr(i)(8-1 downto 0));
        s_chan_diff(i) <= s_chan_max(i) - s_chan_min(i);
    end generate;

    -- =========================================================================
    --  CHANNEL ROUTING LOGIC
    -- =========================================================================

    s_valid_word <= RX_SRC_RDY and TX_DST_RDY;
    s_src_chan_slv_g: if SRC_CHANNELS > 1 generate
        s_src_chan_slv <= slv_array_deser(RX_CHANNEL,ITEMS,SRC_CHANNELS_W);
    else generate
        s_src_chan_slv <= (others => (others => '0'));
    end generate;

    mux_chan_regs_g : for i in 0 to ITEMS-1 generate
        s_src_chan(i)     <= unsigned(s_src_chan_slv(i));
        s_mux_chan_inc(i) <= s_chan_inc(to_integer(s_src_chan(i)));
    end generate;

    chan_cnt_g : for i in 0 to SRC_CHANNELS-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1' or CTRL_REGS_WR(i) = '1') then
                    if (OPT_MODE = true) then
                        s_chan_cnt(i) <= (others => '0');
                    else
                        s_chan_cnt(i) <= resize(s_chan_min(i),(minimum(DST_CHANNELS_W,8)));
                    end if;
                elsif (s_valid_word = '1') then
                    s_chan_cnt(i) <= s_chan_cnt_next(i);
                end if;
            end if;
        end process;

        opt_on_g: if OPT_MODE generate
            s_chan_cnt_arr(i)(0) <= s_chan_cnt(i);
            cnt_g : for r in 0 to ITEMS-1 generate
                process (all)
                    variable cnt_var : unsigned(DST_CHANNELS_W-1 downto 0);
                begin
                    cnt_var := (others => '0');
                    for j in 0 to r loop
                        if (RX_VLD(j) = '1' and s_src_chan(j) = i) then
                            cnt_var := cnt_var + resize(s_chan_inc(i),(minimum(DST_CHANNELS_W,8)));
                        end if;
                    end loop;
                    s_chan_cnt_arr(i)(r+1) <= (cnt_var + s_chan_cnt(i)) and resize(s_chan_diff(i),(minimum(DST_CHANNELS_W,8)));
                end process;
                s_chan_cnt_items(i)(r) <= s_chan_cnt_arr(i)(r) + resize(s_chan_min(i),(minimum(DST_CHANNELS_W,8)));
            end generate;
            s_chan_cnt_next(i) <= s_chan_cnt_arr(i)(ITEMS);
        end generate;

        opt_off_g: if not OPT_MODE generate
            process (all)
            begin
                s_chan_cnt_items(i)(0) <= s_chan_cnt(i);
                for j in 0 to ITEMS-1 loop
                    s_chan_cnt_inc(i)(j) <= resize(s_chan_cnt_items(i)(j),(DST_CHANNELS_W+1)) + resize(s_chan_inc(i),(minimum(DST_CHANNELS_W,8)));
                    if (RX_VLD(j) = '1' and s_src_chan(j) = i) then
                        if (s_chan_cnt_inc(i)(j) <= s_chan_max(i)) and (s_chan_cnt_inc(i)(j) <= (DST_CHANNELS-1)) and (s_chan_cnt_inc(i)(j) >= s_chan_min(i)) then
                            -- Increment the counter
                            s_chan_cnt_items(i)(j+1) <= s_chan_cnt_inc(i)(j)(DST_CHANNELS_W-1 downto 0);
                        else -- Reset the counter to min value
                            s_chan_cnt_items(i)(j+1) <= resize(s_chan_min(i),DST_CHANNELS_W);
                        end if;
                    else
                        s_chan_cnt_items(i)(j+1) <= s_chan_cnt_items(i)(j);
                    end if;
                end loop;
                s_chan_cnt_next(i) <= s_chan_cnt_items(i)(ITEMS);
            end process;
        end generate;
    end generate;

    dst_chan_g : for i in 0 to ITEMS-1 generate
        s_chan_cnt_out(i) <= std_logic_vector(s_chan_cnt_items(to_integer(s_src_chan(i)))(i));

        process (all)
        begin
            if (s_mux_chan_inc(i) /= 0) then
                s_dst_channel(i) <= s_chan_cnt_out(i);
            else
                s_dst_channel(i) <= std_logic_vector(resize(s_src_chan(i),DST_CHANNELS_W));
            end if;
        end process;
    end generate;

    -- =========================================================================
    --  MVB OUTPUT REGISTERS
    -- =========================================================================

    RX_DST_RDY <= TX_DST_RDY;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                TX_DATA    <= RX_DATA;
                TX_CHANNEL <= slv_array_ser(s_dst_channel,ITEMS,DST_CHANNELS_W);
                TX_VLD     <= RX_VLD;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TX_SRC_RDY <= '0';
            elsif (TX_DST_RDY = '1') then
                TX_SRC_RDY <= RX_SRC_RDY;
            end if;
        end if;
    end process;

end architecture;
