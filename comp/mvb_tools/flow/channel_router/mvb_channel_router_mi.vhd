-- mvb_channel_router_mi.vhd
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component works as a simple configurable routing table. It is primarily
-- used for basic routing of Ethernet frames to selected DMA channels. You can
-- use generics to set three modes of default behavior (see DEFAULT_MODE generic).
-- The user can change the routing rules through the MI interface.
--
-- **MI address space and register format:**
--
-- .. code-block::
--
--   Address space: SRC -> DST channel distribution table:
--      0x000000: Source channel 0 round-robin distr. control
--      0x000004: Source channel 1 round-robin distr. control
--      0x000008: Source channel 2 round-robin distr. control
--      ....
--
--    Round-robin distribution control register format:
--    31             23              15             7           0
--   +----------------------------------------------------------+
--   |     RSVD     |     ch_max    |    ch_min    |    incr    |
--   +----------------------------------------------------------+
--   Controls distribution of ethernet frames received from network to DMA channels
--     incr   : RR increment. 0 = round-robin disable (stay on source channel). Default 0x0
--     ch_min : low DMA channel limit for round-robin distribution. Default 0x0
--     ch_max : high DMA channel limit for round-robin distribution. Default 0x0
--
--   Examples:
--      0x000000: Do not distribute frames - frame from Eth chan N is routed to DMA chan N
--      0xff0001: Distribute frames to all available DMA channels
--      0x070401: Distribute frames to DMA channels 4 to 7
--      0xff0002: Distribute frames to even DMA channels
--      0x050501: Send all frames to DMA channel 5 only
--
-- **Channel number calculation:**
--
-- The channel number calculation method differs for OPT_MODE on and off.
-- In OPT_MODE = false mode (default), the destination channel number is calculated
-- according to the following algorithm independently for each source channel:
--
-- .. code-block::
--
--   reset: ch_cnt = ch_min;
--
--   ch_out = ch_cnt;
--   ch_next = ch_cnt + incr
--   if ((ch_next <= ch_max) and (ch_next < DST_CHANNELS) and (ch_next >= ch_min)):
--       ch_cnt = ch_cnt + incr;
--   else:
--       ch_cnt = ch_min;
--
-- In OPT_MODE = true mode, the destination channel number is calculated
-- according to the following algorithm independently for each source channel:
--
-- .. code-block::
--
--   reset: ch_cnt = 0;
--
--   ch_diff = ch_max - ch_min;
--   ch_out = ch_cnt + ch_min;
--   ch_cnt = (ch_cnt + incr) and (ch_diff);
--
entity MVB_CHANNEL_ROUTER_MI is
    generic(
        -- MVB parameters: number of items in word
        ITEMS         : natural := 4;
        -- MVB parameters: width of item in bits
        ITEM_WIDTH    : natural := 32;
        -- Total number of source channels, max value = DST_CHANNELS
        SRC_CHANNELS  : natural := 4;
        -- Total number of destination channels, max value = 256
        DST_CHANNELS  : natural := 16;
        -- Default routing mode: 0 = stay on source channel;
        -- 1 = each SRC channel is routed to all DST channels (round-robin);
        -- 2 = all DST channels are divided into separate groups for each SRC channel,
        -- there is round-robin routing in each group (SRC channel);
        DEFAULT_MODE  : natural := 0;
        -- Optimized mode for better timing (best for high ITEMS) with limited
        -- configuration: (ch_max-ch_min+1) must be power of two
        OPT_MODE      : boolean := False;
        -- MI parameters: width of data signals, min value is 32
        MI_DATA_WIDTH : natural := 32;
        -- MI parameters: width of address signal
        MI_ADDR_WIDTH : natural := 32;
        -- Name of FPGA device
        DEVICE        : string  := "ULTRASCALE"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================

        -- clock input
        CLK        : in  std_logic;
        -- reset input synchronized with CLK, minimum length is 4 cycles
        RESET      : in  std_logic;

        -- =====================================================================
        -- MI INTERFACE
        -- =====================================================================

        -- MI bus: data from master to slave (write data)
        MI_DWR     : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- MI bus: slave address
        MI_ADDR    : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        -- MI bus: byte enable, not supported in this component!
        MI_BE      : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        -- MI bus: read request
        MI_RD      : in  std_logic;
        -- MI bus: write request
        MI_WR      : in  std_logic;
        -- MI bus: ready of slave module
        MI_ARDY    : out std_logic;
        -- MI bus: data from slave to master (read data)
        MI_DRD     : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- MI bus: valid of MI_DRD data signal
        MI_DRDY    : out std_logic;

        -- =====================================================================
        -- INPUT MVB INTERFACE
        -- =====================================================================

        -- RX MVB: data word with MVB items
        RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- RX MVB: channel word with MVB items (SRC channel per each MVB item)
        RX_CHANNEL : in  std_logic_vector(ITEMS*log2(SRC_CHANNELS)-1 downto 0);
        -- RX MVB: valid of each MVB item
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        -- RX MVB: source ready
        RX_SRC_RDY : in  std_logic;
        -- RX MVB: destination ready
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        -- OUTPUT MVB INTERFACE
        -- =====================================================================

        -- TX MVB: data word with MVB items
        TX_DATA    : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- TX MVB: channel word with MVB items (DST channel per each MVB item)
        TX_CHANNEL : out std_logic_vector(ITEMS*log2(DST_CHANNELS)-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD     : out std_logic_vector(ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB_CHANNEL_ROUTER_MI is

    constant DST_PER_SRC_CHAN : natural := DST_CHANNELS/SRC_CHANNELS;

    signal s_ctrl_reg_addr : unsigned(log2(SRC_CHANNELS)-1 downto 0);
    signal s_ctrl_reg      : slv_array_t(SRC_CHANNELS-1 downto 0)(32-1 downto 0);
    signal s_ctrl_regs     : std_logic_vector(SRC_CHANNELS*32-1 downto 0);
    signal s_ctrl_regs_wr  : std_logic_vector(SRC_CHANNELS-1 downto 0);

begin

    -- =========================================================================
    --  MI LOGIC
    -- =========================================================================

    MI_ARDY <= MI_RD or MI_WR;

    s_ctrl_reg_addr <= unsigned(MI_ADDR(log2(SRC_CHANNELS)+2-1 downto 2));

    ctrl_reg_g : for i in 0 to SRC_CHANNELS-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_ctrl_reg(i) <= (others => '0');
                    if (DEFAULT_MODE = 1) then
                        s_ctrl_reg(i)(7 downto 0)   <= std_logic_vector(to_unsigned(1,8));
                        s_ctrl_reg(i)(23 downto 16) <= std_logic_vector(to_unsigned(DST_CHANNELS-1,8));
                    end if;
                    if (DEFAULT_MODE = 2) then
                        s_ctrl_reg(i)(7 downto 0)   <= std_logic_vector(to_unsigned(1,8));
                        s_ctrl_reg(i)(15 downto 8)  <= std_logic_vector(to_unsigned(i*DST_PER_SRC_CHAN,8));
                        s_ctrl_reg(i)(23 downto 16) <= std_logic_vector(to_unsigned((i+1)*DST_PER_SRC_CHAN-1,8));
                    end if;
                elsif ((s_ctrl_reg_addr = i or SRC_CHANNELS = 1) and (MI_WR = '1')) then
                    s_ctrl_reg(i)(23 downto 0) <= MI_DWR(23 downto 0);
                end if;
            end if;
        end process;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_ctrl_regs_wr(i) <= '0';
                if (s_ctrl_reg_addr = i or SRC_CHANNELS = 1) then
                    s_ctrl_regs_wr(i) <= MI_WR;
                end if;
            end if;
        end process;
    end generate;

    s_ctrl_regs <= slv_array_ser(s_ctrl_reg,SRC_CHANNELS,32);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            MI_DRD <= (others => '0');
            for i in 0 to SRC_CHANNELS-1 loop
                if (s_ctrl_reg_addr = i or SRC_CHANNELS = 1) then
                    MI_DRD(23 downto 0) <= s_ctrl_reg(i)(23 downto 0);
                end if;
            end loop;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                MI_DRDY <= '0';
            else
                MI_DRDY <= MI_RD;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  CHANNEL ROUTER LOGIC
    -- =========================================================================

    core_i : entity work.MVB_CHANNEL_ROUTER
    generic map (
        ITEMS        => ITEMS,
        ITEM_WIDTH   => ITEM_WIDTH,
        SRC_CHANNELS => SRC_CHANNELS,
        DST_CHANNELS => DST_CHANNELS,
        OPT_MODE     => OPT_MODE,
        DEVICE       => DEVICE
    )
    port map (
        CLK          => CLK,
        RESET        => RESET,

        CTRL_REGS    => s_ctrl_regs,
        CTRL_REGS_WR => s_ctrl_regs_wr,

        RX_DATA      => RX_DATA,
        RX_CHANNEL   => RX_CHANNEL,
        RX_VLD       => RX_VLD,
        RX_SRC_RDY   => RX_SRC_RDY,
        RX_DST_RDY   => RX_DST_RDY,

        TX_DATA      => TX_DATA,
        TX_CHANNEL   => TX_CHANNEL,
        TX_VLD       => TX_VLD,
        TX_SRC_RDY   => TX_SRC_RDY,
        TX_DST_RDY   => TX_DST_RDY
    );

end architecture;
