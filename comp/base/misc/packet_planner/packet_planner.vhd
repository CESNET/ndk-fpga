-- packet_planner.vhd: Packet Planner component for packet serialization and gaps generation
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.dma_bus_pack.all;

-- =========================================================================
--                                 Description
-- =========================================================================
-- This unit recieves up to M Packets from N parallel interfaces. It serializes
-- these packets to one stream and assigns an address to each of the in one
-- address space (the packets will be placed one after another). After that
-- it propagates the metadata and the assigned address back on N*M interfaces.
-- There can be a predefined GAP between each two packets and an alignment
-- for packet each start, which might further increase the actual gap.
-- =========================================================================

entity PACKET_PLANNER is
generic(
    -- Target device
    DEVICE            : string := "STRATIX10";

    -- Number of parallel interfaces for packets
    STREAMS           : natural := 4;
    -- Maximum number of Packet inputs and outputs on each Stream
    PKTS              : natural := 4;
    -- Maximum number of Packets actually planned in one CLK cycle
    -- Setting this value lower than STREAMS*PKTS will decrease
    -- the planning speed for small packets, but will probably
    -- greately improve timing.
    PLANNED_PKTS      : natural := STREAMS*PKTS;
    -- Width of Metadata passed with each Packet
    METADATA_WIDTH    : natural := 0;
    -- Size of address space to which the packets are being
    -- planned to
    SPACE_SIZE        : natural := 16;
    -- Size of one word in destination space
    -- The planner is only required to plan one word each cycle.
    -- This prevents blocking from having to plan multiple packets,
    -- that are together larger than the entire space. (If such case is possible.)
    -- Set to 'SPACE_SIZE' to eliminate this behavior when the blocking is not actually possible.
    SPACE_WORD_SIZE   : natural := SPACE_SIZE;
    -- Maximum size of one Pakcet
    PKT_SIZE          : natural := 64;
    -- Size of average gap between two planned packets
    GAP_SIZE          : natural := 12;
    -- Size of minimum gap between two planned packets
    GAP_SIZE_MIN      : integer := GAP_SIZE-4;
    -- Size of alignment of start of all packets
    ALIGN             : natural := 8;

    -- Internal input serialization FIFO size (in number of complete words)
    FIFO_ITEMS        : natural := 32;
    -- Internal input serialization FIFO Almost Full offset (in number of complete words)
    FIFO_AFULL_OFFSET : natural := 8;

    -- Enable for usage of Stream and global packet output
    -- Setting these parameters to FALSE will remove output FIFOs from
    -- the respective outputs and will disconnect the output interface
    STREAM_OUT_EN     : boolean := true;
    GLOBAL_OUT_EN     : boolean := true;

    -- This option removes output FIFOX Multi's on the respected TX interface
    -- by using the AFULL signal instead of the DST_RDY signal for flow control.
    -- The user is then responsible for being able to accept a number of TX
    -- words even after the raise of the AFULL signal.
    -- (The specific number depends on the number of registers in this unit
    -- after the internal input serialization FIFO.)
    -- Only relevant when the respected OUT_EN generic is True.
    -- IN STREAM_OUT_AFULL dont forget on MVB_SHAKEDOWN delay
    STREAM_OUT_AFULL  : boolean := false;
    GLOBAL_OUT_AFULL  : boolean := false
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK   : in  std_logic;
    RESET : in  std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Other interfaces
    -- =====================================================================

    RX_STR_PKT_META    : in  slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    RX_STR_PKT_LEN     : in  slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    RX_STR_PKT_VLD     : in  slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0);
    RX_STR_PKT_SRC_RDY : in  std_logic_vector(STREAMS-1 downto 0);
    -- Packets are stopped a few cycles up front to enable DST_RDY elimination
    -- (some packets can be accepted even after this signal rises (the number defined by FIFO_AFULL_OFFSET))
    RX_STR_PKT_AFULL   : out std_logic_vector(STREAMS-1 downto 0);

    -- Current destination space read pointer
    -- Serves to detect space filling (packet planning stops when the space is full)
    SPACE_GLB_RD_PTR   : in  std_logic_vector(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);
    -- Current destination space write pointer
    -- Serves only as possible additional information
    SPACE_GLB_WR_PTR   : out std_logic_vector(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);

    -- Packets with assigned addresses (individual for each Stream)
    -- Can be disabled by generic STREAM_OUT_EN.
    TX_STR_PKT_META    : out slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    TX_STR_PKT_LEN     : out slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    TX_STR_PKT_ADDR    : out slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    TX_STR_PKT_VLD     : out slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0);
    -- Only used when STREAM_OUT_AFULL==False
    TX_STR_PKT_DST_RDY : in  slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0) := (others => (others => '1')); -- read signal for FIFOX Multi
    -- Only used when STREAM_OUT_AFULL==True
    TX_STR_PKT_AFULL   : in  std_logic_vector(STREAMS-1 downto 0) := (others => '0');

    -- Packets with assigned addresses (globaly serialized over all Streams)
    -- Can be disabled by generic GLOBAL_OUT_EN.
    TX_GLB_PKT_META    : out slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    TX_GLB_PKT_LEN     : out slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    TX_GLB_PKT_ADDR    : out slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    TX_GLB_PKT_VLD     : out std_logic_vector(PLANNED_PKTS-1 downto 0);
    -- Only used when GLOBAL_OUT_AFULL==False
    TX_GLB_PKT_DST_RDY : in  std_logic_vector(PLANNED_PKTS-1 downto 0) := (others => '1'); -- read signal for FIFOX Multi
    -- Only used when GLOBAL_OUT_AFULL==True
    TX_GLB_PKT_AFULL   : in  std_logic := '0'

    -- =====================================================================
);
end entity;

architecture FULL of PACKET_PLANNER is

    -- =====================================================================
    --  Constants, aliases, functions
    -- =====================================================================

    constant PKT_WIDTH : natural := METADATA_WIDTH
                                   +log2(PKT_SIZE+1)
                                   +log2(STREAMS);

    constant OUT_PKT_WIDTH : natural := METADATA_WIDTH
                                       +log2(PKT_SIZE+1)
                                       +log2(SPACE_SIZE);

    -- When the FIFO is full and user starts reading TX packets at full speed,
    -- it takes some time for Almost Full signal to drop and new pakcets to start
    -- arriving to the FIFO input and be propagated to output.
    -- The FIFO must contain enough items to compensate this time,
    -- so VLD does not drop.
    constant OUT_FIFO_ITEMS        : natural := PLANNED_PKTS*32;
    constant OUT_FIFO_AFULL_OFFSET : natural := 6*PLANNED_PKTS;

    -- =====================================================================

    -- =====================================================================
    --  Pre-Planning Packet FIFO
    -- =====================================================================

    signal pktf_di         : std_logic_vector(STREAMS*PKTS*PKT_WIDTH-1 downto 0);
    signal pktf_wr         : std_logic_vector(STREAMS*PKTS-1 downto 0);
    signal pktf_full       : std_logic;
    signal pktf_afull      : std_logic;
    signal pktf_do         : std_logic_vector(PLANNED_PKTS*PKT_WIDTH-1 downto 0);
    signal pktf_rd         : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal pktf_empty      : std_logic_vector(PLANNED_PKTS-1 downto 0);

    signal pktf_di_arr     : slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(PKT_WIDTH-1 downto 0);
    signal pktf_do_arr     : slv_array_t     (PLANNED_PKTS-1 downto 0)(PKT_WIDTH-1 downto 0);
    signal pktf_do_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal pktf_do_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal pktf_do_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal pktf_do_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);

    signal pktf_do_len_over_word : std_logic_vector(PLANNED_PKTS-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Packet register 0
    -- =====================================================================

    signal reg0_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg0_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal reg0_gap_len : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
    signal reg0_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal reg0_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal reg0_dst_rdy : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Packet register 1
    -- =====================================================================

    signal reg1_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg1_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal reg1_gap_len : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
    signal reg1_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal reg1_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal reg1_dst_rdy : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Packet register 2
    -- =====================================================================

    signal reg2_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg2_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal reg2_dg_len  :   u_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+GAP_SIZE+ALIGN+1)-log2(ALIGN)+1-1 downto 0); -- length of data and gap together
    signal reg2_addr    : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg2_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal reg2_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal reg2_dst_rdy : std_logic;

    signal space_wr_ptr_reg : unsigned(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Packet register 3
    -- =====================================================================

    signal reg3_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg3_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal reg3_addr    : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg3_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal reg3_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal reg3_len_sum : unsigned        (log2(SPACE_SIZE+1)-log2(ALIGN)-1 downto 0);
    signal reg3_dst_rdy : std_logic;

    signal reg3_enough_space : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Packet register 4
    -- =====================================================================

    signal reg4_meta    : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal reg4_len     : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal reg4_addr    : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg4_stream  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(STREAMS)-1 downto 0);
    signal reg4_vld     : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal reg4_dst_rdy : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Output Shakedowns
    -- =====================================================================

    signal oshk_di      : slv_array_t     (STREAMS-1 downto 0)(PLANNED_PKTS*OUT_PKT_WIDTH-1 downto 0);
    signal oshk_wr      : slv_array_t     (STREAMS-1 downto 0)(PLANNED_PKTS-1 downto 0);
    signal oshk_full    : std_logic_vector(STREAMS-1 downto 0);
    signal oshk_rdy     : std_logic_vector(STREAMS-1 downto 0);
    signal oshk_afull   : std_logic_vector(STREAMS-1 downto 0);
    signal oshk_do      : slv_array_t     (STREAMS-1 downto 0)(PKTS*OUT_PKT_WIDTH-1 downto 0);
    signal oshk_rd      : slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0);
    signal oshk_empty   : slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0);
    signal oshk_vld     : slv_array_t     (STREAMS-1 downto 0)(PKTS-1 downto 0);

    signal oshk_di_arr  : slv_array_2d_t  (STREAMS-1 downto 0)(PLANNED_PKTS-1 downto 0)(OUT_PKT_WIDTH-1 downto 0);
    signal oshk_do_arr  : slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(OUT_PKT_WIDTH-1 downto 0);
    signal oshk_do_meta : slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal oshk_do_len  : slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal oshk_do_addr : slv_array_2d_t  (STREAMS-1 downto 0)(PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Global output Shakedown
    -- =====================================================================

    signal gshk_di      : std_logic_vector(PLANNED_PKTS*OUT_PKT_WIDTH-1 downto 0);
    signal gshk_wr      : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal gshk_full    : std_logic;
    signal gshk_afull   : std_logic;
    signal gshk_do      : std_logic_vector(PLANNED_PKTS*OUT_PKT_WIDTH-1 downto 0);
    signal gshk_rd      : std_logic_vector(PLANNED_PKTS-1 downto 0);
    signal gshk_empty   : std_logic_vector(PLANNED_PKTS-1 downto 0);

    signal gshk_di_arr  : slv_array_t     (PLANNED_PKTS-1 downto 0)(OUT_PKT_WIDTH-1 downto 0);
    signal gshk_do_arr  : slv_array_t     (PLANNED_PKTS-1 downto 0)(OUT_PKT_WIDTH-1 downto 0);
    signal gshk_do_meta : slv_array_t     (PLANNED_PKTS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal gshk_do_len  : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal gshk_do_addr : slv_array_t     (PLANNED_PKTS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Free Space counter
    -- =====================================================================

    signal free_space_cnt_reg   : unsigned(log2(SPACE_SIZE+1)-log2(ALIGN)-1 downto 0);
    signal old_space_rd_ptr_reg : unsigned(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);
    signal new_space            : unsigned(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);

    -- =====================================================================

begin

    assert (ALIGN>0)
        report "ERROR: Packet Planner: Packet ALIGN ("&to_string(ALIGN)&") must be higher than 0!"
        severity failure;

    assert (PKT_SIZE<=SPACE_SIZE)
        report "ERROR: Packet Planner: Maximum size of packet ("&to_string(PKT_SIZE)&") must not be higher than the total size of the destination space ("&to_string(SPACE_SIZE)&"!"
        severity failure;

    -- =====================================================================
    --  Pre-Planning Packet FIFO
    -- =====================================================================
    -- This FIFO buffers incoming Packets while the pipeline is stopped
    -- (for example when Output Buffer is full).
    -- The FIFO generates an Almost Full to stop generation of new packets.

    pktf_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => PKT_WIDTH                     ,
        ITEMS               => FIFO_ITEMS*STREAMS*PKTS       ,
        WRITE_PORTS         => STREAMS*PKTS                  ,
        READ_PORTS          => PLANNED_PKTS                  ,
        RAM_TYPE            => "AUTO"                        ,
        DEVICE              => DEVICE                        ,
        ALMOST_FULL_OFFSET  => FIFO_AFULL_OFFSET*STREAMS*PKTS,
        ALMOST_EMPTY_OFFSET => 0                             ,
        SAFE_READ_MODE      => true
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => pktf_di   ,
        WR     => pktf_wr   ,
        FULL   => pktf_full ,
        AFULL  => pktf_afull,

        DO     => pktf_do   ,
        RD     => pktf_rd   ,
        EMPTY  => pktf_empty,
        AEMPTY => open
    );

    -- Check Packet FIFO overflow
    assert (((or pktf_wr) and pktf_full)/='1')
        report "ERROR: Packet Planner: Packet FIFO overflow! RX_STR_PKT_AFULL was probably ignored or the FIFO_AFULL_OFFSET ("&to_string(FIFO_AFULL_OFFSET)&") is too low!"
        severity failure;

    -- Serialize all RX pakcets to one input for FIFOX Multi
    pktf_di_gen : for i in 0 to STREAMS-1 generate
        pktf_di_str_gen : for e in 0 to PKTS-1 generate
            -- Stream index is added to the packet to be able to return it back to the correct output at the end
            pktf_di_arr(i)(e) <= RX_STR_PKT_META(i)(e) & RX_STR_PKT_LEN(i)(e) & std_logic_vector(to_unsigned(i,log2(STREAMS)));
            pktf_wr(i*PKTS+e) <= RX_STR_PKT_VLD(i)(e) and RX_STR_PKT_SRC_RDY(i);
        end generate;
        RX_STR_PKT_AFULL(i) <= pktf_afull;
    end generate;
    pktf_di <= slv_array_2d_ser(pktf_di_arr);

    -- Parse FIFO output
    pktf_do_arr <= slv_array_deser(pktf_do,PLANNED_PKTS);
    pktf_do_gen : for i in 0 to PLANNED_PKTS-1 generate
        pktf_do_meta   (i) <= pktf_do_arr(i)(PKT_WIDTH-1 downto log2(PKT_SIZE+1)+log2(STREAMS));
        pktf_do_len    (i) <= pktf_do_arr(i)(log2(PKT_SIZE+1)+log2(STREAMS)-1 downto log2(STREAMS));
        pktf_do_stream (i) <= pktf_do_arr(i)(log2(STREAMS)-1 downto 0);
        pktf_do_vld    (i) <= '1' when pktf_empty(i)='0' and ((or pktf_do_len_over_word(i downto 0))='0' or i=0) else '0';

        -- This results in constant '0' when the space is large enough to contain PLANNED_PKTS maximum-sized packets at once or when space word size can fit a whole maximum-sized packet.
        pktf_do_len_over_word(i) <= '1' when unsigned(pktf_do_len(i))>SPACE_WORD_SIZE and SPACE_SIZE<(PLANNED_PKTS+1)*PKT_SIZE else '0';

        -- Distribute read signal
        pktf_rd(i) <= '1' when reg0_dst_rdy='1' and ((or pktf_do_len_over_word(i downto 0))='0' or i=0) else '0';

    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Packet register 0
    -- =====================================================================

    -- Only accept new input when no almost full is active
    reg0_dst_rdy <= reg1_dst_rdy and (nor oshk_afull) and (not gshk_afull);

    reg0_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Only overwrite when values can be propagated further
            if (reg1_dst_rdy='1') then
                reg0_meta   <= pktf_do_meta;
                reg0_len    <= pktf_do_len;
                reg0_stream <= pktf_do_stream;
                -- Only validate when Shakedowns are ready for new input
                reg0_vld    <= pktf_do_vld and (nor oshk_afull) and (not gshk_afull);
            end if;

            if (RESET='1') then
                reg0_vld <= (others => '0');
                -- The length must be reset for space full checking to work after reset
                reg0_len <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  Packet register 1
    -- =====================================================================

    -- No additional condition
    reg1_dst_rdy <= reg2_dst_rdy;

    reg1_pr : process (CLK)
        variable tmp_gap_len : u_array_t(PLANNED_PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
        variable tmp_rest    : unsigned(log2(ALIGN)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            -- Only overwrite when values can be propagated further
            if (reg2_dst_rdy='1') then
                reg1_meta    <= reg0_meta;
                reg1_len     <= reg0_len;
                reg1_gap_len <= reg0_gap_len;
                reg1_stream  <= reg0_stream;
                reg1_vld     <= reg0_vld;
            end if;

            if (RESET='1') then
                reg1_vld <= (others => '0');
                -- The length must be reset for space full checking to work after reset
                reg1_len <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- Deficit Idle Count component
    -- Counts gap after every packet according to Ethernet DIC specification
    dic_i : entity work.DEFICIT_IDLE_COUNTER
    generic map(
        PKTS         => PLANNED_PKTS,
        PKT_SIZE     => PKT_SIZE    ,
        GAP_SIZE     => GAP_SIZE    ,
        ALIGN        => ALIGN       ,
        MIN_GAP_SIZE => GAP_SIZE_MIN
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_PKT_LEN     => reg0_len    ,
        RX_PKT_VLD     => reg0_vld    ,
        RX_PKT_SRC_RDY => reg2_dst_rdy,
        RX_PKT_DST_RDY => open        ,

        TX_PKT_GAP     => reg0_gap_len,
        TX_PKT_VLD     => open        ,
        TX_PKT_SRC_RDY => open        ,
        TX_PKT_DST_RDY => reg2_dst_rdy
    );

    -- =====================================================================

    -- =====================================================================
    --  Packet register 2
    -- =====================================================================

    -- No additional condition
    reg2_dst_rdy <= reg3_dst_rdy;

    reg2_pr : process (CLK)
        variable tmp_addr   : unsigned(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);
        variable tmp_dg_len : unsigned(log2(SPACE_SIZE)-log2(ALIGN)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            -- Only overwrite when values can be propagated further
            if (reg3_dst_rdy='1') then
                reg2_meta    <= reg1_meta;
                reg2_len     <= reg1_len;
                reg2_stream  <= reg1_stream;
                reg2_vld     <= reg1_vld;

                -- Calculate address for each packet based on their gap sizes
                -- This is a CRITICAL PART of the logic
                tmp_addr := space_wr_ptr_reg;
                for i in 0 to PLANNED_PKTS-1 loop
                    -- Assign new address
                    reg2_addr(i)   <= std_logic_vector(enlarge_right(tmp_addr,log2(ALIGN)));

                    -- Move address to start of next packet (if this packet was valid)
                    -- Make sure the next address is aligned (this round_up is only needed when GAP_SIZE is not aligned)
                    tmp_dg_len     := enlarge_right(round_up(resize_left(unsigned(reg1_len(i)),log2(SPACE_SIZE)) + resize_left(unsigned(reg1_gap_len(i)),log2(SPACE_SIZE)),log2(ALIGN)),-log2(ALIGN));
                    --tmp_dg_len     := enlarge_right(resize_left(unsigned(reg1_len(i)),log2(SPACE_SIZE)) + resize_left(unsigned(reg1_gap_len(i)),log2(SPACE_SIZE)),-log2(ALIGN));
                    if (reg1_vld(i)='1') then
                        tmp_addr := tmp_addr + tmp_dg_len;
                        reg2_dg_len(i) <= resize_left(tmp_dg_len,reg2_dg_len(i)'length);
                    else
                        reg2_dg_len(i) <= (others => '0');
                    end if;
                end loop;
                -- Store address for next word
                space_wr_ptr_reg <= tmp_addr;
            end if;

            if (RESET='1') then
                reg2_vld         <= (others => '0');
                space_wr_ptr_reg <= (others => '0');
                -- The length must be reset for space full checking to work after reset
                reg2_len         <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- Propagate write pointer value to output
    SPACE_GLB_WR_PTR <= std_logic_vector(space_wr_ptr_reg);

    -- =====================================================================

    -- =====================================================================
    --  Packet register 3
    -- =====================================================================

    -- No additional condition
    reg3_dst_rdy <= reg4_dst_rdy;

    reg3_pr : process (CLK)
        variable tmp_start_addr : unsigned(log2(SPACE_SIZE+1)-1 downto 0);
        variable tmp_end_addr   : unsigned(log2(SPACE_SIZE+1)-1 downto 0);
        variable tmp_len_sum    : unsigned(log2(SPACE_SIZE+1)-log2(ALIGN)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            -- Only overwrite when values can be propagated further
            if (reg4_dst_rdy='1') then
                reg3_meta   <= reg2_meta;
                reg3_len    <= reg2_len;
                reg3_stream <= reg2_stream;
                reg3_addr   <= reg2_addr;
                reg3_vld    <= reg2_vld;

                -- Calculate total sum of space taken by the packets
                -- (and round up to ALIGN size)
                --tmp_start_addr := resize_left(unsigned(reg2_addr(0)),log2(SPACE_SIZE+1));
                --tmp_end_addr   := resize_left(unsigned(reg2_addr(PLANNED_PKTS-1)),log2(SPACE_SIZE+1));
                --tmp_end_addr   := tmp_end_addr + resize_left(enlarge_right(unsigned(reg2_dg_len(PLANNED_PKTS-1)),log2(ALIGN)),log2(SPACE_SIZE+1));
                --reg3_len_sum   <= enlarge_right(round_up(tmp_end_addr-tmp_start_addr,log2(ALIGN)),-log2(ALIGN));
                tmp_len_sum := (others => '0');
                for i in 0 to PLANNED_PKTS-1 loop
                    tmp_len_sum := tmp_len_sum + resize_left(reg2_dg_len(i),log2(SPACE_SIZE+1)-log2(ALIGN));
                end loop;
                reg3_len_sum <= tmp_len_sum;
            end if;

            if (RESET='1') then
                reg3_vld     <= (others => '0');
                -- The length must be reset for space full checking to work after reset
                reg3_len_sum <= (others => '0');
            end if;
        end if;
    end process;

    -- Check free space
    reg3_enough_space <= '1' when reg3_len_sum<=free_space_cnt_reg else '0';

    -- =====================================================================

    -- =====================================================================
    --  Packet register 4
    -- =====================================================================

    -- Only allow propagation when there is enough free space
    reg4_dst_rdy <= reg3_enough_space;

    reg4_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Save new values (old ones are allways passed further without dst_rdy)
            reg4_meta   <= reg3_meta;
            reg4_len    <= reg3_len;
            reg4_stream <= reg3_stream;
            reg4_addr   <= reg3_addr;

            -- Only allow propagation when there is enough free space
            reg4_vld  <= reg3_vld and reg3_enough_space;

            if (RESET='1') then
                reg4_vld <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  Output Shakedowns
    -- =====================================================================
    -- There is one Shakedown on each Stream output. These change the number
    -- of output packets back to original. They also solve TX_STR_PKT_DST_RDY
    -- by their Almost Full, which is propagated to the start of the pipeline.

    out_shake_en_gen : if (STREAM_OUT_EN) generate

        out_shake_gen : for i in 0 to STREAMS-1 generate

            out_shake_true_dst_rdy_gen : if (not STREAM_OUT_AFULL) generate

                out_shake_i : entity work.FIFOX_MULTI
                generic map(
                    DATA_WIDTH          => OUT_PKT_WIDTH        ,
                    ITEMS               => OUT_FIFO_ITEMS       ,
                    WRITE_PORTS         => PLANNED_PKTS         ,
                    READ_PORTS          => PKTS                 ,
                    RAM_TYPE            => "AUTO"               ,
                    DEVICE              => DEVICE               ,
                    ALMOST_FULL_OFFSET  => OUT_FIFO_AFULL_OFFSET,
                    ALMOST_EMPTY_OFFSET => 0                    ,
                    SAFE_READ_MODE      => true
                )
                port map(
                    CLK    => CLK  ,
                    RESET  => RESET,

                    DI     => oshk_di   (i),
                    WR     => oshk_wr   (i),
                    FULL   => oshk_full (i),
                    AFULL  => oshk_afull(i),

                    DO     => oshk_do   (i),
                    RD     => oshk_rd   (i),
                    EMPTY  => oshk_empty(i),
                    AEMPTY => open
                );

                -- Check Shakedown overflow
                assert (((or oshk_wr(i)) and oshk_full(i))/='1')
                    report "ERROR: Packet Planner: Output packet Shakedown overflow! The ALMOST_FULL_OFFSET is too low to compensate pipeline length!"
                    severity failure;

                TX_STR_PKT_VLD (i) <= not oshk_empty(i);

                -- Read when output is ready
                oshk_rd(i) <= TX_STR_PKT_DST_RDY(i);
            else generate

                out_mvb_shake_i : entity work.MVB_SHAKEDOWN
                generic map(
                    RX_ITEMS    => PLANNED_PKTS ,
                    TX_ITEMS    => PKTS         ,
                    ITEM_WIDTH  => OUT_PKT_WIDTH,
                    SHAKE_PORTS => 2
                )
                port map(
                    CLK        => CLK  ,
                    RESET      => RESET,

                    RX_DATA    => oshk_di (i),
                    RX_VLD     => oshk_wr (i),
                    RX_SRC_RDY => (or oshk_wr(i)),
                    RX_DST_RDY => oshk_rdy(i),

                    TX_DATA    => oshk_do (i),
                    TX_VLD     => oshk_vld(i),
                    TX_NEXT    => (others => '1')
                );

                -- Check Shakedown overflow
                assert (((or oshk_wr(i)) and (not oshk_rdy(i)))/='1')
                    report "ERROR: Packet Planner: Output packet Shakedown overflow! The ALMOST_FULL_OFFSET is too low to compensate pipeline length!"
                    severity failure;

                -- Propagate Almost Full from user DST_RDY
                oshk_afull(i) <= TX_STR_PKT_AFULL(i);

                TX_STR_PKT_VLD(i) <= oshk_vld(i);

            end generate;

            -- Generate Shakedown input
            oshk_di_gen : for e in 0 to PLANNED_PKTS-1 generate
                -- All Shakedowns get the same input
                oshk_di_arr(i)(e) <= reg4_meta(e) & reg4_len(e) & reg4_addr(e);
                -- Only packets belonging to this Stream are valid here
                oshk_wr(i)(e) <= '1' when reg4_vld(e)='1' and (unsigned(reg4_stream(e))=i or STREAMS=1) else '0';
            end generate;
            oshk_di(i) <= slv_array_ser(oshk_di_arr(i));

            -- Generate TX
            oshk_do_arr(i) <= slv_array_deser(oshk_do(i),PKTS);
            oshk_do_gen : for e in 0 to PKTS-1 generate
                signal tmp_meta : std_logic_vector(METADATA_WIDTH-1 downto 0);
                signal tmp_len  : std_logic_vector(log2(PKT_SIZE+1)-1 downto 0);
                signal tmp_addr : std_logic_vector(log2(SPACE_SIZE)-1 downto 0);
            begin
                (tmp_meta,
                 tmp_len ,
                 tmp_addr ) <= oshk_do_arr(i)(e);

                TX_STR_PKT_META(i)(e) <= tmp_meta;
                TX_STR_PKT_LEN (i)(e) <= tmp_len;
                TX_STR_PKT_ADDR(i)(e) <= tmp_addr;
            end generate;
        end generate;

    else generate
        oshk_afull <= (others => '0');
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Global output Shakedown
    -- =====================================================================
    -- There is one Shakedown for the global output. This should store the same
    -- number of packets as all the Stream shakedowns combined.

    out_glb_shake_en_gen : if (GLOBAL_OUT_EN) generate

        out_glb_shake_true_dst_rdy_gen : if (not GLOBAL_OUT_AFULL) generate

            out_glb_shake_i : entity work.FIFOX_MULTI
            generic map(
                DATA_WIDTH          => OUT_PKT_WIDTH        ,
                ITEMS               => OUT_FIFO_ITEMS       ,
                WRITE_PORTS         => PLANNED_PKTS         ,
                READ_PORTS          => PLANNED_PKTS         ,
                RAM_TYPE            => "AUTO"               ,
                DEVICE              => DEVICE               ,
                ALMOST_FULL_OFFSET  => OUT_FIFO_AFULL_OFFSET,
                ALMOST_EMPTY_OFFSET => 0                    ,
                SAFE_READ_MODE      => true
            )
            port map(
                CLK    => CLK  ,
                RESET  => RESET,

                DI     => gshk_di   ,
                WR     => gshk_wr   ,
                FULL   => gshk_full ,
                AFULL  => gshk_afull,

                DO     => gshk_do   ,
                RD     => gshk_rd   ,
                EMPTY  => gshk_empty,
                AEMPTY => open
            );

            -- Check Shakedown overflow
            assert (((or gshk_wr) and gshk_full)/='1')
                report "ERROR: Packet Planner: Output global packet Shakedown overflow! The ALMOST_FULL_OFFSET is too low to compensate pipeline length!"
                severity failure;

            -- Generate Shakedown input
            gshk_di_gen : for e in 0 to PLANNED_PKTS-1 generate
                -- All Shakedowns get the same input
                gshk_di_arr(e) <= reg4_meta(e) & reg4_len(e) & reg4_addr(e);
                -- Accepts packets from all Streams
                gshk_wr(e) <= '1' when reg4_vld(e)='1' else '0';
            end generate;
            gshk_di <= slv_array_ser(gshk_di_arr);

            -- Generate TX
            gshk_do_arr <= slv_array_deser(gshk_do, PLANNED_PKTS);
            gshk_do_gen : for e in 0 to PLANNED_PKTS-1 generate
                signal tmp_meta : std_logic_vector(METADATA_WIDTH-1 downto 0);
                signal tmp_len  : std_logic_vector(log2(PKT_SIZE+1)-1 downto 0);
                signal tmp_addr : std_logic_vector(log2(SPACE_SIZE)-1 downto 0);
            begin
                (tmp_meta,
                 tmp_len ,
                 tmp_addr ) <= gshk_do_arr(e);

                TX_GLB_PKT_META(e) <= tmp_meta;
                TX_GLB_PKT_LEN (e) <= tmp_len;
                TX_GLB_PKT_ADDR(e) <= tmp_addr;
                TX_GLB_PKT_VLD (e) <= not gshk_empty(e);
            end generate;

            -- Read when output is ready
            gshk_rd <= TX_GLB_PKT_DST_RDY;

        else generate

            -- Propagate Almost Full from user DST_RDY
            gshk_afull <= TX_GLB_PKT_AFULL;

            TX_GLB_PKT_META <= reg4_meta;
            TX_GLB_PKT_LEN  <= reg4_len;
            TX_GLB_PKT_ADDR <= reg4_addr;
            -- Accepts packets from all Streams
            glb_vld_gen : for e in 0 to PLANNED_PKTS-1 generate
                TX_GLB_PKT_VLD(e)  <= '1' when reg4_vld(e)='1' else '0';
            end generate;

        end generate;

    else generate
        gshk_afull <= '0';
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Free Space counter
    -- =====================================================================
    -- This register holds the size of actually free space to control
    -- space full status.

    free_space_pr : process (CLK)
        variable tmp_space : unsigned(log2(SPACE_SIZE+1)-log2(ALIGN)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            tmp_space := free_space_cnt_reg;

            -- Decrement when newly planned packets fit in the space
            if (reg4_dst_rdy='1') then
                tmp_space := tmp_space - reg3_len_sum;
            end if;

            -- Increment by the ammount of new freed space
            tmp_space := tmp_space + new_space;

            free_space_cnt_reg <= tmp_space;

            -- Update OLD space register
            old_space_rd_ptr_reg <= unsigned(SPACE_GLB_RD_PTR);

            if (RESET='1') then
                free_space_cnt_reg   <= (others => '0');
                free_space_cnt_reg(free_space_cnt_reg'high) <= '1';

                old_space_rd_ptr_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- New freed space is the difference between NEW read pointer and OLD read pointer
    new_space <= unsigned(SPACE_GLB_RD_PTR) - old_space_rd_ptr_reg;

    -- =====================================================================

end architecture;
