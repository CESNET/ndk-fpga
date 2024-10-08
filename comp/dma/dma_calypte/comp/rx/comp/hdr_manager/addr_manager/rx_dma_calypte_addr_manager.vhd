-- rx_dma_calypte_addr_manager.vhd: manages free space and addresses for PCIe transactions
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- This component manages addresses and pointer for each channel. Component is
-- working as follows: After receiving address request for the specific
-- channel, the HW pointers are increased and the address for storing the data
-- in RAM is created. The addres is valid as soon as the corresponding
-- area in a host memory is free.
entity RX_DMA_CALYPTE_ADDR_MANAGER is
    generic (
        -- number of managed channels
        CHANNELS      : integer;
        -- size of sent segments in bytes
        BLOCK_SIZE    : integer;
        -- RAM address width
        ADDR_WIDTH    : integer := 64;
        -- width of a pointer to the ring buffer log2(NUMBER_OF_ITEMS)
        POINTER_WIDTH : integer := 16;
        -- Specified device: "ULTRASCALE", "STRATIX10" or "AGILEX"
        DEVICE        : string  := "ULTRASCALE"
        );

    port (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK   : in std_logic;
        RESET : in std_logic;


        -- =====================================================================
        -- ADDRES REQUEST INTERFACE (To SW manager of the DMA)
        -- =====================================================================
        -- Address requesting for channel
        ADDR_CHANNEL    : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        -- Address base for channel
        ADDR_BASE       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        -- righ buffer size. log2(NUMBER_OF_MAX_ITEMS)
        ADDR_MASK       : in  std_logic_vector(POINTER_WIDTH-1 downto 0);
        -- SW pointer to ring buffer
        ADDR_SW_POINTER : in  std_logic_vector(POINTER_WIDTH-1 downto 0);


        -- =====================================================================
        -- HW UPDATE ADDRESS INTERFACE (To SW manager)
        -- =====================================================================
        POINTER_UPDATE_CHAN : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        POINTER_UPDATE_DATA : out std_logic_vector(POINTER_WIDTH-1 downto 0);
        POINTER_UPDATE_EN   : out std_logic;


        -- =====================================================================
        -- REQUEST ADDRES FOR CHANNEL (Metadata instructions)
        -- =====================================================================
        -- Requested channel
        CHANNEL       : in std_logic_vector(log2(CHANNELS)-1 downto 0);
        CHANNEL_VLD   : in std_logic;

        -- =====================================================================
        -- Detect start request of a channel (for the reset of internal pointer)
        -- =====================================================================
        START_REQ_VLD     : in std_logic;
        START_REQ_CHANNEL : in std_logic_vector(log2(CHANNELS) -1 downto 0);

        -- =====================================================================
        -- RESPONSE ADDRES (To be inserted to the PCIex header)
        -- =====================================================================
        -- Address to RAM
        ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        OFFSET   : out std_logic_vector(POINTER_WIDTH-1 downto 0);
        ADDR_VLD : out std_logic
        );

end entity;

architecture FULL of RX_DMA_CALYPTE_ADDR_MANAGER is

    signal hw_pointer_wr      : std_logic;
    signal hw_pointer_wr_addr : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal hw_pointer_wr_data : std_logic_vector(POINTER_WIDTH -1 downto 0);
    signal hw_pointer_rd_data : std_logic_vector(POINTER_WIDTH -1 downto 0);

    signal hw_pointer_new      : unsigned(POINTER_WIDTH-1 downto 0);
    signal hw_offset           : unsigned(ADDR_WIDTH-1 downto 0);

    signal channel_act_reg     : unsigned(log2(CHANNELS)-1 downto 0);
    signal channel_act_vld_reg : std_logic;

    signal packet_vld  : std_logic;
    signal packet_next : std_logic;

begin
    assert (2**log2(BLOCK_SIZE) = BLOCK_SIZE)
        report "ERROR: BLOCK_SIZE which is not power of two is not supported yet actual block size is " & integer'image(BLOCK_SIZE) & ". If you want to try on your own risk, delete this assert"
        severity FAILURE;

    --=====================================================================
    -- Storage of HW pointers
    --=====================================================================
    -- Upon the start of a channel, the pointer has to be cleared
    hw_pointer_wr_addr <= std_logic_vector(channel_act_reg) when START_REQ_VLD = '0' else START_REQ_CHANNEL;
    hw_pointer_wr_data <= std_logic_vector(hw_pointer_new)  when START_REQ_VLD = '0' else (others => '0');

    hw_pointers_lutram_i : entity work.GEN_LUTRAM
        generic map (
            DATA_WIDTH         => POINTER_WIDTH,
            ITEMS              => CHANNELS,
            RD_PORTS           => 1,
            RD_LATENCY         => 0,
            WRITE_USE_RD_ADDR0 => FALSE,
            MLAB_CONSTR_RDW_DC => FALSE,
            DEVICE             => DEVICE)
        port map (
            CLK     => CLK,
            WR_EN   => hw_pointer_wr,
            WR_ADDR => hw_pointer_wr_addr,
            WR_DATA => hw_pointer_wr_data,
            RD_ADDR => std_logic_vector(channel_act_reg),
            RD_DATA => hw_pointer_rd_data);

    --=====================================================================
    -- STORE CHANNEL
    --=====================================================================
    channel_act_p : process(CLK)
    begin
        if (rising_edge(CLK)) then

            if (RESET = '1') then

                channel_act_vld_reg <= '0';
                channel_act_reg     <= (others => '0');

            -- awaits for the instruction to process the next packet
            elsif(packet_next = '1') then

                channel_act_vld_reg <= CHANNEL_VLD;
                channel_act_reg     <= unsigned(CHANNEL);

            end if;
        end if;
    end process;

    ADDR_CHANNEL <= CHANNEL when packet_next = '1' else std_logic_vector(channel_act_reg);

    -- writing new values of the HW pointer for the specific channel
    hw_pointer_wr  <= packet_vld or START_REQ_VLD;
    -- increment by 1 thus the pointer points to the next block and mask the pointer bits so the
    -- pointer would not overflow
    hw_pointer_new <= unsigned(std_logic_vector(unsigned(hw_pointer_rd_data) + 1) and ADDR_MASK);

    -- channel_act_vld_reg asserts only if the input CHANNEL_VLD asserts too, for the output address to be valid,
    -- the HW pointer must not match the SW pointer
    packet_vld  <= '1' when channel_act_vld_reg = '1' and hw_pointer_new /= unsigned(ADDR_SW_POINTER) and START_REQ_VLD = '0' else '0';

    -- the components accepts a new packet either when the processing of the previous has been finished or the
    -- component is in the idle state
    packet_next <= '1' when packet_vld = '1' or channel_act_vld_reg = '0' else '0';

    -- assumes addresing to bytes, the new value of the pointer is shifted according to the current BLOCK_SIZE
    -- setting
    hw_offset <=
        (ADDR_WIDTH-1 downto POINTER_WIDTH +log2(BLOCK_SIZE) => '0')
        & unsigned(hw_pointer_rd_data)
        & (log2(BLOCK_SIZE)-1 downto 0 => '0');

    ADDR     <= std_logic_vector(unsigned(ADDR_BASE) + hw_offset);
    OFFSET   <= hw_pointer_rd_data;
    ADDR_VLD <= packet_vld;

    POINTER_UPDATE_CHAN <= std_logic_vector(channel_act_reg);
    POINTER_UPDATE_DATA <= std_logic_vector(hw_pointer_new);
    POINTER_UPDATE_EN   <= packet_vld;
end architecture;
