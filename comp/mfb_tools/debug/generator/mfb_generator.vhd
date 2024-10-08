-- mfb_generator.vhd: This component generates packets of desired length.
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
--   IT IS NESCESSARY FOR THE LENGHT OF PACKETS TO BE INPUT AS NUMBER OF ITEMS else it will not function properly
-- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
--   Packet length has to be larger than block size
-- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

-- NOTE: packets are generated by blocks

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity MFB_GENERATOR is
    Generic (
        -- number of regions in a data word
        REGIONS         : natural := 2;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- the width of rx_length signal
        LENGTH_WIDTH    : natural := 10;
        -- the width of channel signal, must be <= PKT_CNT_WIDTH
        CHANNELS_WIDTH  : natural := 6;
        -- the width of packet counter, must be >= CHANNELS_WIDTH
        PKT_CNT_WIDTH   : natural := 32;
        -- use Packet Planner Generator Core architecture
        USE_PACP_ARCH   : boolean := true;
        -- FPGA device string
        DEVICE          : string  := "STRATIX10"
    );
    Port (
        CLK             : in  std_logic;
        RST             : in  std_logic;

        -- Control interface
        CTRL_EN           : in std_logic;
        CTRL_CHAN_INC     : in std_logic_vector(32-1 downto 0);
        CTRL_CHAN_VAL     : in std_logic_vector(32-1 downto 0);
        CTRL_LENGTH       : in std_logic_vector(LENGTH_WIDTH-1 downto 0);
        CTRL_MAC_DST      : in std_logic_vector(48-1 downto 0);
        CTRL_MAC_SRC      : in std_logic_vector(48-1 downto 0);
        CTRL_PKT_CNT_CLR  : in std_logic;
        CTRL_PKT_CNT      : out std_logic_vector(PKT_CNT_WIDTH-1 downto 0);

        -- TX interface
        TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_META     : out std_logic_vector(REGIONS*(CHANNELS_WIDTH+LENGTH_WIDTH)-1 downto 0); -- packet channel & packet length
        TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic
    );
    end entity;

architecture BEHAV of MFB_GENERATOR is

    constant CHANNELS           : natural := 2**CHANNELS_WIDTH;
    constant ETHER_TYPE         : std_logic_vector(15 downto 0) := X"B588"; -- local experimental ethertype

    signal pkt_cnt              : u_array_t(REGIONS downto 0)(PKT_CNT_WIDTH-1 downto 0);
    signal pkt_cnt_reg          : unsigned(PKT_CNT_WIDTH-1 downto 0);

    signal sof                  : std_logic_vector(REGIONS-1 downto 0);
    signal eof                  : std_logic_vector(REGIONS-1 downto 0);
    signal sof_pos              : std_logic_vector(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
    signal eof_pos              : std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal src_rdy              : std_logic;
    signal dst_rdy              : std_logic;

    signal chan_inc             : unsigned(8-1 downto 0);
    signal chan_min             : unsigned(16-1 downto 0);
    signal chan_max             : unsigned(16-1 downto 0);
    signal chan_burst           : unsigned(16-1 downto 0);

    signal burst_size           : unsigned(16 -1 downto 0);
    signal burst_mode_en        : std_logic;
    -- Input delay register
    signal ctrl_en_delay        : std_logic;
    signal ctrl_length_delay    : std_logic_vector(LENGTH_WIDTH -1 downto 0);
    -- Rising edge detect
    signal ctrl_en_ris_edge     : std_logic;
    -- General control mask for regions to the packet generator
    signal gen_vld              : std_logic_vector(REGIONS -1 downto 0);
    -- Control mask for each region that controls the generator when burst_mode is enabled.
    signal gen_vld_regions      : std_logic_vector(REGIONS -1 downto 0);
    -- Confirmation signal that packets requested with gen_vld will be generated
    signal gen_accept           : std_logic_vector(REGIONS -1 downto 0);

    type burst_fsm_state_t is (S_TRIGGER_DETECT, S_BURST_COUNTDOWN);
    signal burst_fsm_pst : burst_fsm_state_t := S_TRIGGER_DETECT;
    signal burst_fsm_nst : burst_fsm_state_t := S_TRIGGER_DETECT;

    signal ones_offs_high       : unsigned(log2(REGIONS) -1 downto 0);
    signal ones_insert_en       : std_logic;

    signal my_burst_cntr_pst : unsigned(16 -1 downto 0);
    signal my_burst_cntr_nst : unsigned(16 -1 downto 0);

    signal burst_cnt            : u_array_t(REGIONS downto 0)(16-1 downto 0);
    signal chan_cnt             : u_array_t(REGIONS downto 0)(CHANNELS_WIDTH-1 downto 0);

    signal chan_normal          : slv_array_t(REGIONS-1 downto 0)(CHANNELS_WIDTH-1 downto 0);
    signal chan_reverse         : slv_array_t(REGIONS-1 downto 0)(CHANNELS_WIDTH-1 downto 0);
    signal chan_reverse_en      : std_logic;
    signal channel              : slv_array_t(REGIONS-1 downto 0)(CHANNELS_WIDTH-1 downto 0);
    signal meta                 : slv_array_t(REGIONS-1 downto 0)(CHANNELS_WIDTH+LENGTH_WIDTH-1 downto 0);
    signal data                 : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);

    signal free_cnt             : unsigned(16-1 downto 0);
    signal eth_hdr_128b         : std_logic_vector(128-1 downto 0);
    signal sof_pos_arr          : slv_array_t(REGIONS-1 downto 0)(max(1, log2(REGION_SIZE))-1 downto 0);
    signal sof_index            : u_array_t(REGIONS-1 downto 0)(max(1, log2(REGIONS*REGION_SIZE))-1 downto 0);
    signal data_word_plus       : slv_array_t(2*REGIONS*REGION_SIZE-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal data_word_plus_reg   : slv_array_t(REGIONS*REGION_SIZE-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal data_word            : slv_array_t(REGIONS*REGION_SIZE-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal data_word_ser        : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);

    function count_ones (
        INP_VECTOR : std_logic_vector)
        return unsigned is

        variable count : unsigned(log2(INP_VECTOR'length) downto 0);
    begin
        if (INP_VECTOR'length = 1) then
            return (INP_VECTOR'range => INP_VECTOR(0));
        end if;

        count := (others => '0');
        for i in INP_VECTOR'range loop
            count := count + ((count'high downto count'low+1 => '0') & INP_VECTOR(i));
        end loop;
        return count;
    end function;

begin

    core_arch_gen : if (not USE_PACP_ARCH) generate

        core_i : entity work.MFB_GENERATOR_CORE
        generic map(
            REGIONS        => REGIONS,
            REGION_SIZE    => REGION_SIZE,
            BLOCK_SIZE     => BLOCK_SIZE,
            ITEM_WIDTH     => ITEM_WIDTH,
            LENGTH_WIDTH   => LENGTH_WIDTH
        )
        port map(
            CLK            => CLK,
            RESET          => RST,

            GEN_LENGTH     => (others => ctrl_length_delay),
            GEN_VALID      => gen_vld,
            GEN_ACCEPT     => gen_accept,

            TX_MFB_SOF_POS => sof_pos,
            TX_MFB_EOF_POS => eof_pos,
            TX_MFB_SOF     => sof,
            TX_MFB_EOF     => eof,
            TX_MFB_SRC_RDY => src_rdy,
            TX_MFB_DST_RDY => dst_rdy
        );

    else generate

        core_pacp_i : entity work.MFB_GENERATOR_CORE_PACP
        generic map(
            REGIONS        => REGIONS,
            REGION_SIZE    => REGION_SIZE,
            BLOCK_SIZE     => BLOCK_SIZE,
            ITEM_WIDTH     => ITEM_WIDTH,
            LENGTH_WIDTH   => LENGTH_WIDTH,
            DEVICE         => DEVICE
        )
        port map(
            CLK            => CLK,
            RESET          => RST,

            GEN_LENGTH     => (others => CTRL_LENGTH),
            GEN_VALID      => (others => CTRL_EN),
            GEN_ACCEPT     => open,

            TX_MFB_SOF_POS => sof_pos,
            TX_MFB_EOF_POS => eof_pos,
            TX_MFB_SOF     => sof,
            TX_MFB_EOF     => eof,
            TX_MFB_SRC_RDY => src_rdy,
            TX_MFB_DST_RDY => dst_rdy
        );

    end generate;

    burst_mode_logic_g: if (not USE_PACP_ARCH) generate

        gen_vld <= (others => CTRL_EN) when burst_mode_en = '0' else gen_vld_regions;

        -- =============================================================================================
        -- Burst mode control
        -- =============================================================================================
        ctrl_en_delay_reg_p: process (CLK) is
        begin
            if (rising_edge(CLK)) then
                ctrl_en_delay     <= CTRL_EN;
                ctrl_length_delay <= CTRL_LENGTH;
            end if;
        end process;

        -- Detect rising edge
        ctrl_en_ris_edge <= (not ctrl_en_delay) and CTRL_EN;

        burst_mode_fsm_state_reg_p : process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    burst_fsm_pst <= S_TRIGGER_DETECT;
                    my_burst_cntr_pst <= (others => '0');
                else
                    burst_fsm_pst     <= burst_fsm_nst;
                    my_burst_cntr_pst <= my_burst_cntr_nst;
                end if;
            end if;
        end process;

        burst_mod_fsm_out_logic: process (all) is
            variable accepted_regions : unsigned(log2(REGIONS) downto 0);
        begin
            burst_fsm_nst     <= burst_fsm_pst;
            my_burst_cntr_nst <= my_burst_cntr_pst;
            ones_insert_en    <= '0';
            ones_offs_high    <= (others => '0');

            case burst_fsm_pst is
                when S_TRIGGER_DETECT =>

                    if (ctrl_en_ris_edge = '1' and burst_mode_en = '1') then

                        accepted_regions := BEHAV.count_ones(gen_accept);

                        if (dst_rdy = '1') then
                            my_burst_cntr_nst <= burst_size - accepted_regions;
                            ones_insert_en    <= '1';
                        end if;

                        if (burst_size > REGIONS) then
                            ones_offs_high <= (others => '1');
                        else
                            ones_offs_high <= resize(burst_size -1, log2(REGIONS));
                        end if;

                        -- If burst is bigger then the number of regions, the generation needs to be
                        -- split through more clock cycles OR if generator CORE is not able to process
                        -- all of the requested packets at once.
                        if (burst_size > REGIONS or accepted_regions < burst_size) then
                            burst_fsm_nst  <= S_BURST_COUNTDOWN;
                        end if;

                    end if;

                when S_BURST_COUNTDOWN =>

                    accepted_regions := BEHAV.count_ones(gen_accept);

                    if (dst_rdy = '1') then
                        my_burst_cntr_nst <= my_burst_cntr_pst - accepted_regions;
                        ones_insert_en <= '1';
                    end if;

                    if (my_burst_cntr_pst > REGIONS) then
                        ones_offs_high <= (others => '1');
                    else
                        if (accepted_regions = my_burst_cntr_pst) then
                            burst_fsm_nst <= S_TRIGGER_DETECT;
                        end if;

                        ones_offs_high <= resize(my_burst_cntr_pst -1, log2(REGIONS));
                    end if;
            end case;
        end process;

        ones_insertor_i : entity work.ONES_INSERTOR
            generic map (
                OFFSET_WIDTH => log2(REGIONS))
            port map (
                OFFSET_LOW  => (others => '0'),
                OFFSET_HIGH => ones_offs_high,
                VALID       => ones_insert_en,
                ONES_VECTOR => gen_vld_regions);
    end generate;

    -- ======================================================================================
    --  packet counter
    -- ======================================================================================
    pkt_cnt_p : process (all)
        variable v_pkt_cnt : unsigned(log2(REGIONS+1)-1 downto 0);
    begin
        v_pkt_cnt := (others => '0');
        pkt_cnt(0) <= pkt_cnt_reg;
        pkt_cnt_l : for i in 0 to REGIONS-1 loop
            if (sof(i) = '1') then
                v_pkt_cnt := v_pkt_cnt + '1';
            end if;
            pkt_cnt(i+1) <= pkt_cnt_reg + v_pkt_cnt;
        end loop;
    end process;

    pkt_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((RST = '1') or (CTRL_PKT_CNT_CLR = '1')) then
                pkt_cnt_reg <= (others => '0');
            elsif ((src_rdy = '1') and (dst_rdy = '1')) then
                pkt_cnt_reg <= pkt_cnt(REGIONS);
            end if;
        end if;
    end process;

    -- ======================================================================================
    --  Channel select
    -- ======================================================================================
    --  Round-robin distribution increment register format (signal CTRL_CHAN_INC):
    --  31             23              15             7           0
    -- +----------------------------------------------------------+
    -- | burst_size                   | CONFIG       |    incr    |
    -- +----------------------------------------------------------+

    --  Round-robin distribution value register format (signal CTRL_CHAN_VAL):
    --  31             23              15             7           0
    -- +----------------------------------------------------------+
    -- | ch_max                       | ch_min                    |
    -- +----------------------------------------------------------+

    -- Distribution of Ethernet frames to channels
    --   incr       : RR increment. 0 = round-robin disable (stay on zero channel). Default 0x01
    --   CONFIG     : CONFIG[0] = channel reverse enable, others bit are reserved. Default 0x00
    --              : CONFIG[1] = Experimental: Enables burst mode in which N packets (where N
    --                corresponds to burst_size) are send only with occurence of rising edge on
    --                CTRL_EN signal and the transmission stops unless another rising edge occurs.
    --                Setting this bit to 0 enables streaming mode where packets are sent
    --                continuously.
    --                NOTE: Does not work with USE_PACP_ARCH set to true
    --   burst_size : number of packets to begenerated before channel is changed
    --   ch_min     : the lowest channel number for round-robin distribution. Default 0x0000
    --   ch_max     : the highest channel number for round-robin distribution. Default 0xFFFF
    -- Distribution examples:
    --    0x000000: Do not distribute frames
    --    0xff0001: Distribute frames to all available channels
    --    0x070401: Distribute frames to channels 4 to 7
    --    0xff0002: Distribute frames to all even channels (0, 2, 4, ...)
    --    0x050501: Send all frames to channel number 5 only

    chan_inc        <= unsigned(CTRL_CHAN_INC(8-1 downto 0));
    chan_reverse_en <= CTRL_CHAN_INC(8);
    burst_mode_en   <= CTRL_CHAN_INC(9);
    burst_size      <= unsigned(CTRL_CHAN_INC(32-1 downto 16));

    chan_min        <= unsigned(CTRL_CHAN_VAL(16-1 downto 0));
    chan_max        <= unsigned(CTRL_CHAN_VAL(32-1 downto 16));

    chan_burst_p : process (CLK)
    begin
        -- One cycle delay is not a problem
        if (rising_edge(CLK)) then
            if ((or burst_size)='1') then
                -- Channel burst size is used decremented
                chan_burst <= burst_size - 1;
            else
                -- When size is 0
                chan_burst <= burst_size;
            end if;
        end if;
    end process;

    chan_cnt_g : for i in 0 to REGIONS-1 generate
        chan_cnt_p : process (all)
        begin
            if (sof(i) = '1') then

                if (burst_cnt(i) < chan_burst) then
                    -- Increment the counter
                    burst_cnt(i+1) <= burst_cnt(i) + 1;
                else -- Reset the counter to zero
                    burst_cnt(i+1) <= (others => '0');
                end if;

                if (burst_cnt(i) = chan_burst) then
                    -- Change channel counter
                    if (chan_cnt(i) < chan_max) and (chan_cnt(i) < (CHANNELS-1)) then
                        -- Increment the counter
                        chan_cnt(i+1) <= chan_cnt(i) + resize(chan_inc,minimum(CHANNELS_WIDTH,8));
                    else -- Reset the counter to min value
                        chan_cnt(i+1) <= resize(chan_min,CHANNELS_WIDTH);
                    end if;
                else
                    chan_cnt(i+1) <= chan_cnt(i);
                end if;

            else
                burst_cnt(i+1) <= burst_cnt(i);
                chan_cnt (i+1) <= chan_cnt (i);
            end if;
        end process;

        chan_normal(i) <= std_logic_vector(chan_cnt(i)) when (chan_inc /= 0) else (others => '0');

        chan_reverse_g : for j in 0 to CHANNELS_WIDTH-1 generate
            chan_reverse(i)(CHANNELS_WIDTH-1-j) <= chan_normal(i)(j);
        end generate;

        channel(i) <= chan_reverse(i) when (chan_reverse_en = '1') else chan_normal(i);
    end generate;

    chan_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                chan_cnt (0) <= (others => '0');
                burst_cnt(0) <= (others => '0');
            elsif ((src_rdy = '1') and (dst_rdy = '1')) then
                chan_cnt (0) <= chan_cnt (REGIONS);
                burst_cnt(0) <= burst_cnt(REGIONS);
            end if;
        end if;
    end process;

    -- ======================================================================================
    -- generation of other output signals and their connection to their respective interfaces
    -- ======================================================================================

    free_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                free_cnt <= (others => '0');
            elsif (dst_rdy = '1') then
                free_cnt <= free_cnt + 1;
            end if;
        end if;
    end process;

    eth_hdr_128b <= std_logic_vector(free_cnt) & ETHER_TYPE & CTRL_MAC_SRC & CTRL_MAC_DST;
    sof_pos_arr <= slv_array_deser(sof_pos,REGIONS,max(1, log2(REGION_SIZE)));

    process (all)
    begin
        for b in 0 to REGIONS*REGION_SIZE-1 loop
            data_word_plus(b) <= data_word_plus_reg(b);
        end loop;
        for c in REGIONS*REGION_SIZE to 2*REGIONS*REGION_SIZE-1 loop
            data_word_plus(c) <= (others => '0');
        end loop;
        for i in 0 to REGIONS-1 loop
            sof_index(i) <= resize(unsigned(sof_pos_arr(i)),log2(REGIONS*REGION_SIZE)) + i*REGION_SIZE;
            if (sof(i) = '1') then
                data_word_plus(to_integer(sof_index(i))) <= eth_hdr_128b(64-1 downto 0);
                data_word_plus(to_integer(sof_index(i))+1) <= eth_hdr_128b(128-1 downto 64);
            end if;
        end loop;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (dst_rdy = '1') then
                data_word_plus_reg <= data_word_plus(2*REGIONS*REGION_SIZE-1 downto REGIONS*REGION_SIZE);
            end if;
        end if;
    end process;

    data_word <= data_word_plus(REGIONS*REGION_SIZE-1 downto 0);
    data_word_ser <= slv_array_ser(data_word,REGIONS*REGION_SIZE,BLOCK_SIZE*ITEM_WIDTH);

    data_meta_g : for i in 0 to REGIONS-1 generate
        meta(i) <= channel(i) & CTRL_LENGTH;
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            CTRL_PKT_CNT <= std_logic_vector(pkt_cnt_reg);
        end if;
    end process;

    mfb_pipe_i : entity work.MFB_PIPE
    generic map(
       REGIONS     => REGIONS,
       REGION_SIZE => REGION_SIZE,
       BLOCK_SIZE  => BLOCK_SIZE,
       ITEM_WIDTH  => ITEM_WIDTH,
       META_WIDTH  => CHANNELS_WIDTH+LENGTH_WIDTH,
       FAKE_PIPE   => false,
       USE_DST_RDY => true,
       --PIPE_TYPE   => PIPE_TYPE,
       DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RST,

        RX_DATA    => data_word_ser,
        RX_META    => slv_array_ser(meta, REGIONS, (CHANNELS_WIDTH+LENGTH_WIDTH)),
        RX_SOF_POS => sof_pos,
        RX_EOF_POS => eof_pos,
        RX_SOF     => sof,
        RX_EOF     => eof,
        RX_SRC_RDY => src_rdy,
        RX_DST_RDY => dst_rdy,

        TX_DATA    => TX_MFB_DATA,
        TX_META    => TX_MFB_META,
        TX_SOF_POS => TX_MFB_SOF_POS,
        TX_EOF_POS => TX_MFB_EOF_POS,
        TX_SOF     => TX_MFB_SOF,
        TX_EOF     => TX_MFB_EOF,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
