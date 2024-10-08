-- mfb_generator_mi32.vhd: This is the MI32 encapsulation of the mfb_generator component.
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

-- ============================================================================
--  Description
-- ============================================================================

-- This component allows the user to generate MFB frames with some configurable
-- options (like frame length) accessible over the MI.
--
-- The MI address space is (considering only the lowest 6 bits):
--
-- - 0x00 - Control (write 1 to start, 0 to stop)
-- - 0x04 - Length (set length of generated frames)
-- - 0x08 - Channel increment
-- - 0x0C - Channel minimum and maximum
-- - 0x10 - Dst MAC Low  (lower  part of destination MAC address)
-- - 0x14 - Dst MAC High (higher part of destination MAC address)
-- - 0x18 - Src MAC Low  (lower  part of source MAC address)
-- - 0x1C - Src MAC High (higher part of source MAC address)
-- - 0x20 - Cntr Low  (lower  part of counter for generated frames)
-- - 0x24 - Cntr High (higher part of counter for generated frames)
--
-- **Register format**
--
-- - Channel increment register (0x08):
--
-- .. code-block::
--
--   +------------------------------+--------------+-------------+
--   | 31                         16|15           8|7           0|
--   +------------------------------+--------------+-------------+
--   | burst_size                   | CONFIG       | incr        |
--   +------------------------------+--------------+-------------+
--
-- - Min Max channel value register (0x0C):
--
-- .. code-block::
--
--   +------------------------------+----------------------------+
--   |31                          16|15                         0|
--   +------------------------------+----------------------------+
--   | ch_max                       | ch_min                     |
--   +------------------------------+----------------------------+
--
-- Distribution of Ethernet frames to channels
--
-- - incr       : RR increment. 0 = round-robin disable (stay on zero channel). Default 0x01
-- - CONFIG     : CONFIG[0] = channel reverse enable, others bit are reserved. Default 0x00
--              : CONFIG[1] = Experimental: Enables burst mode in which the amount of burst_size
--                packets are sent and the transmission is stopped until next cycle of enable of the
--                generator occurs (that is burst is sent -> disable -> enable).
--                NOTE: Does not work with USE_PACP_ARCH set to true
-- - burst_size : number of packets to begenerated before channel is changed
-- - ch_min     : the lowest channel number for round-robin distribution. Default 0x0000
-- - ch_max     : the highest channel number for round-robin distribution. Default 0xFFFF
--
entity MFB_GENERATOR_MI32 is
    generic(
        -- number of regions in a data word
        REGIONS         : natural := 4;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- the width of length signal, max 32
        LENGTH_WIDTH    : natural := 15;
        -- the width of channel signal, must be <= PKT_CNT_WIDTH
        CHANNELS_WIDTH  : natural := 6;
        -- the width of packet counter, max 64 !!
        PKT_CNT_WIDTH   : natural := 32;
        -- use Packet Planner Generator Core architecture
        USE_PACP_ARCH   : boolean := true;
        -- FPGA device string
        DEVICE          : string  := "STRATIX10"
    );
    port(
        CLK             : in  std_logic;
        RST             : in  std_logic;

        -- MI32 interface

        MI_DWR          : in  std_logic_vector(31 downto 0);
        MI_ADDR         : in  std_logic_vector(31 downto 0);
        -- Byte enabling is not supported!
        MI_BE           : in  std_logic_vector(3 downto 0);
        MI_RD           : in  std_logic;
        MI_WR           : in  std_logic;
        MI_ARDY         : out std_logic;
        MI_DRD          : out std_logic_vector(31 downto 0);
        MI_DRDY         : out std_logic;

        -- TX interface

        TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- Contains the packet's channel number & it's length
        TX_MFB_META     : out std_logic_vector(REGIONS*(CHANNELS_WIDTH+LENGTH_WIDTH)-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic
    );
end entity;

architecture BEHAV of MFB_GENERATOR_MI32 is

    constant MAC_ADDR_WIDTH : natural := 48;

    -- select signals, they assert according to the MI32 address
    signal ctrl_reg_sel        : std_logic;
    signal len_reg_sel         : std_logic;
    signal chan_inc_reg_sel    : std_logic;
    signal chan_val_reg_sel    : std_logic;
    signal dmac_low_reg_sel    : std_logic;
    signal dmac_high_reg_sel   : std_logic;
    signal smac_low_reg_sel    : std_logic;
    signal smac_high_reg_sel   : std_logic;
    -- register signals
    signal en_reg              : std_logic;
    signal clr_reg             : std_logic;
    signal chan_inc_reg        : std_logic_vector(31 downto 0);
    signal chan_val_reg        : std_logic_vector(31 downto 0);
    signal len_reg             : std_logic_vector(LENGTH_WIDTH-1 downto 0);
    signal cnt_reg             : std_logic_vector(PKT_CNT_WIDTH-1 downto 0); -- counter output of the mfb_generator
    signal cnt_comb_reg_resize : std_logic_vector(63 downto 0); -- resized cnt_reg signal, so that its width is 32 multiplied by 2, larger number then 2^64 is not expected
    signal dmac_comb_reg       : std_logic_vector(MAC_ADDR_WIDTH-1 downto 0); -- combines dmac_low_reg and dmac_high_reg signals for the mfb_generator input
    signal dmac_low_reg        : std_logic_vector(31 downto 0); -- low bits of destination mac address
    signal dmac_high_reg       : std_logic_vector(MAC_ADDR_WIDTH-33 downto 0); -- high bits of destination mac address
    signal smac_comb_reg       : std_logic_vector(MAC_ADDR_WIDTH-1 downto 0); -- combines smac_low_reg and smac_high_reg signals for the mfb_generator input
    signal smac_low_reg        : std_logic_vector(31 downto 0); -- low bits of source mac address
    signal smac_high_reg       : std_logic_vector(MAC_ADDR_WIDTH-33 downto 0); -- high bits of source mac address

begin

    MI_ARDY <= MI_RD or MI_WR;

    mfb_generator_i : entity work.MFB_GENERATOR
    generic map (
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE,
        ITEM_WIDTH     => ITEM_WIDTH,
        LENGTH_WIDTH   => LENGTH_WIDTH,
        CHANNELS_WIDTH => CHANNELS_WIDTH,
        PKT_CNT_WIDTH  => PKT_CNT_WIDTH,
        USE_PACP_ARCH  => USE_PACP_ARCH,
        DEVICE         => DEVICE
    )
    port map (
        CLK              => CLK,
        RST              => RST,
        -- control interface
        CTRL_EN          => en_reg,
        CTRL_CHAN_INC    => chan_inc_reg,
        CTRL_CHAN_VAL    => chan_val_reg,
        CTRL_LENGTH      => len_reg,
        CTRL_MAC_DST     => dmac_comb_reg,
        CTRL_MAC_SRC     => smac_comb_reg,
        CTRL_PKT_CNT_CLR => clr_reg,
        CTRL_PKT_CNT     => cnt_reg,
        -- tx interface
        TX_MFB_DATA      => TX_MFB_DATA,
        TX_MFB_META      => TX_MFB_META,
        TX_MFB_SOF       => TX_MFB_SOF,
        TX_MFB_EOF       => TX_MFB_EOF,
        TX_MFB_SOF_POS   => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS   => TX_MFB_EOF_POS,
        TX_MFB_SRC_RDY   => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY   => TX_MFB_DST_RDY
    );

    -- signals for register selection
    ctrl_reg_sel      <= '1' when (MI_ADDR(6-1 downto 0) = "000000") else '0';
    len_reg_sel       <= '1' when (MI_ADDR(6-1 downto 0) = "000100") else '0';
    chan_inc_reg_sel  <= '1' when (MI_ADDR(6-1 downto 0) = "001000") else '0';
    chan_val_reg_sel  <= '1' when (MI_ADDR(6-1 downto 0) = "001100") else '0';
    dmac_low_reg_sel  <= '1' when (MI_ADDR(6-1 downto 0) = "010000") else '0';
    dmac_high_reg_sel <= '1' when (MI_ADDR(6-1 downto 0) = "010100") else '0';
    smac_low_reg_sel  <= '1' when (MI_ADDR(6-1 downto 0) = "011000") else '0';
    smac_high_reg_sel <= '1' when (MI_ADDR(6-1 downto 0) = "011100") else '0';

    -- ==================================================================
    -- transfering data to/from registers according to the select signals
    -- ==================================================================
    en_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                en_reg <= '0';
            elsif ((ctrl_reg_sel = '1') and (MI_WR = '1')) then
                en_reg <= MI_DWR(0);
            end if;
        end if;
    end process;

    -- clear signal will be asserted only for the given clock period
    clr_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                clr_reg <= '0';
            elsif ((ctrl_reg_sel = '1') and (MI_WR = '1')) then
                clr_reg <= MI_DWR(4);
            else
                clr_reg <= '0';
            end if;
        end if;
    end process;

    chan_inc_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                chan_inc_reg <= X"00010001";
            elsif ((chan_inc_reg_sel = '1') and (MI_WR = '1')) then
                chan_inc_reg <= MI_DWR;
            end if;
        end if;
    end process;

    chan_val_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                chan_val_reg <= X"FFFF0000";
            elsif ((chan_val_reg_sel = '1') and (MI_WR = '1')) then
                chan_val_reg <= MI_DWR;
            end if;
        end if;
    end process;

    -- the defaul packet lenght is 60 bytes (+ CRC = 64B)
    len_reg_p : process (CLK)
        begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                len_reg <= std_logic_vector(to_unsigned(60, LENGTH_WIDTH));
            elsif ((len_reg_sel = '1') and (MI_WR = '1')) then
                len_reg <= MI_DWR(LENGTH_WIDTH-1 downto 0);
            end if;
        end if;
    end process;

    -- the default destination MAC address is the broadcast address (FF:FF:FF:FF:FF:FF)
    dmac_low_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                dmac_low_reg <= (others => '1');
            elsif ((dmac_low_reg_sel = '1') and (MI_WR = '1')) then
                dmac_low_reg <= MI_DWR;
            end if;
        end if;
    end process;

    dmac_high_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                dmac_high_reg <= (others => '1');
            elsif ((dmac_high_reg_sel = '1') and (MI_WR = '1')) then
                dmac_high_reg <= MI_DWR(MAC_ADDR_WIDTH-33 downto 0);
            end if;
        end if;
    end process;

    dmac_comb_reg <= dmac_high_reg & dmac_low_reg;

    -- the default source MAC address is a common MAC address of our devices (00:11:17:60:00:00)
    smac_low_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                smac_low_reg <= X"60171100";
            elsif ((smac_low_reg_sel = '1') and (MI_WR = '1')) then
                smac_low_reg <= MI_DWR;
            end if;
        end if;
    end process;

    smac_high_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                smac_high_reg <= X"0000";
            elsif ((smac_high_reg_sel = '1') and (MI_WR = '1')) then
                smac_high_reg <= MI_DWR(MAC_ADDR_WIDTH-33 downto 0);
            end if;
        end if;
    end process;

    smac_comb_reg <= smac_high_reg & smac_low_reg;

    cnt_comb_reg_resize <= std_logic_vector(resize(unsigned(cnt_reg), 64));

    -- process for reading data from the register with the current address
    read_from_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            MI_DRD <= (others => '0');
            case (MI_ADDR(6-1 downto 0)) is
                when "000000"  => MI_DRD(0)                       <= en_reg;
                                  MI_DRD(1)                       <= TX_MFB_SRC_RDY; -- read only busy bit
                                  MI_DRD(4)                       <= clr_reg;
                when "000100"  => MI_DRD(LENGTH_WIDTH-1 downto 0) <= len_reg;
                when "001000"  => MI_DRD                          <= chan_inc_reg;
                when "001100"  => MI_DRD                          <= chan_val_reg;
                when "010000"  => MI_DRD                          <= dmac_low_reg;
                when "010100"  => MI_DRD(15 downto 0)             <= dmac_high_reg;
                when "011000"  => MI_DRD                          <= smac_low_reg;
                when "011100"  => MI_DRD(15 downto 0)             <= smac_high_reg;
                when "100000"  => MI_DRD                          <= cnt_comb_reg_resize(31 downto 0);
                when "100100"  => MI_DRD                          <= cnt_comb_reg_resize(63 downto 32);
                when others    => MI_DRD                          <= (others => '0');
            end case;
        end if;
    end process;

    drdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                MI_DRDY <= '0';
            else
                MI_DRDY <= MI_RD;
            end if;
        end if;
    end process;

end architecture;
