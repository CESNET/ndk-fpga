-- mfb_splitter_simple.vhd: This component transmits recieved packets on one interface to one out of the two outputs accaoring to the select bit.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
-- TODO? : RESETS and OUTPUT REGISTERS

-- This component transmits received packets on one interface to one out of the two outputs according to the select bit.
entity MFB_SPLITTER_SIMPLE is
    Generic (
        -- number of regions in a data word
        REGIONS         : natural := 2;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- number of bits for metadata in a single region
        META_WIDTH      : natural := 8
    );
    Port (
        CLK             : in  std_logic;
        RST             : in  std_logic;

        -- ==============
        -- rx interface
        -- ==============

        -- is only valid with asserted sof signal
        RX_MFB_SEL      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_META     : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- ==============
        -- tx interface 0
        -- ==============

        TX0_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX0_MFB_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX0_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX0_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX0_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX0_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX0_MFB_SRC_RDY : out std_logic;
        TX0_MFB_DST_RDY : in  std_logic;

        -- ==============
        -- tx interface 1
        -- ==============

        TX1_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX1_MFB_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX1_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX1_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX1_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX1_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX1_MFB_SRC_RDY : out std_logic;
        TX1_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture behav of MFB_SPLITTER_SIMPLE is

    signal rx_dst_rdy           : std_logic;
    signal rx_sel               : std_logic_vector(REGIONS-1 downto 0);

    -- duplicated signals for output 0
    signal tx0_data             : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx0_meta             : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal tx0_sof_pos          : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx0_eof_pos          : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx0_sof              : std_logic_vector(REGIONS-1 downto 0);
    signal tx0_eof              : std_logic_vector(REGIONS-1 downto 0);
    signal tx0_src_rdy          : std_logic;

    -- duplicated signals for output 1
    signal tx1_data             : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx1_meta             : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal tx1_sof_pos          : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx1_eof_pos          : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx1_sof              : std_logic_vector(REGIONS-1 downto 0);
    signal tx1_eof              : std_logic_vector(REGIONS-1 downto 0);
    signal tx1_src_rdy          : std_logic;

    -- signals in SOF0 and EOF0 masking logic
    signal new_sof0             : std_logic_vector(REGIONS-1 downto 0);
    signal need_eof0            : std_logic_vector(REGIONS downto 0);
    signal need_eof0_reg        : std_logic;
    signal sof_pos0_to_comp     : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal eof_pos0_to_comp     : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal tx0_sof_b4_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal new_eof0             : std_logic_vector(REGIONS-1 downto 0);

    -- signals in new source ready 0 and new destination 0 logic
    signal pkt_cont0            : std_logic_vector(REGIONS downto 0);
    signal new_src_rdy0_regions : std_logic_vector(REGIONS-1 downto 0);
    signal new_src_rdy0         : std_logic;
    signal new_dst_rdy0         : std_logic;

    -- signals in SOF1 and EOF1 masking logic
    signal new_sof1             : std_logic_vector(REGIONS-1 downto 0);
    signal need_eof1            : std_logic_vector(REGIONS downto 0);
    signal need_eof1_reg        : std_logic;
    signal sof_pos1_to_comp     : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal eof_pos1_to_comp     : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal tx1_sof_b4_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal new_eof1             : std_logic_vector(REGIONS-1 downto 0);

    -- signals in new source ready 1 and new destination 1 logic
    signal pkt_cont1            : std_logic_vector(REGIONS downto 0);
    signal new_src_rdy1_regions : std_logic_vector(REGIONS-1 downto 0);
    signal new_src_rdy1         : std_logic;
    signal new_dst_rdy1         : std_logic;

    begin

    -- -------------------------------------------------------------------------
    --  data duplication
    -- -------------------------------------------------------------------------
    rx_dst_rdy  <= new_dst_rdy0 and new_dst_rdy1;
    rx_sel      <= RX_MFB_SEL;

    tx0_data    <= RX_MFB_DATA;
    tx0_meta    <= RX_MFB_META;
    tx0_sof_pos <= RX_MFB_SOF_POS;
    tx0_eof_pos <= RX_MFB_EOF_POS;
    tx0_sof     <= RX_MFB_SOF;
    tx0_eof     <= RX_MFB_EOF;
    tx0_src_rdy <= new_dst_rdy1 and RX_MFB_SRC_RDY; -- new dst_rdy

    tx1_data    <= RX_MFB_DATA;
    tx1_meta    <= RX_MFB_META;
    tx1_sof_pos <= RX_MFB_SOF_POS;
    tx1_eof_pos <= RX_MFB_EOF_POS;
    tx1_sof     <= RX_MFB_SOF;
    tx1_eof     <= RX_MFB_EOF;
    tx1_src_rdy <= new_dst_rdy0 and RX_MFB_SRC_RDY; -- new dst_rdy

    -- ˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇ
    --                                 OUTPUT 0
    -- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
    -- ˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇ

    -- -------------------------------------------------------------------------
    -- SOF0 masking logic
    -- -------------------------------------------------------------------------
    -- SOF is taken from the RX input and is masked by the select signal
    sof0_masking_p : process (all)
    begin
        sof0_l : for i in 0 to REGIONS-1 loop
            if (tx0_sof(i) = '1') then
                if (rx_sel(i) = '0') then
                    new_sof0(i) <= '1';
                else
                    new_sof0(i) <= '0';
                end if;
            else
                new_sof0(i) <= '0';
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------
    -- EOF0 masking logic
    -- -------------------------------------------------------------------------
    -- need_eof signal means there was a SOF and the next incoming EOF is needed for this output
    need_eof0_p : process (all)
    begin
        need_eof0(0) <= need_eof0_reg;
        sof0_l : for i in 0 to REGIONS-1 loop
            if (tx0_sof(i) = '1') then
                if (rx_sel(i) = '0') then
                    need_eof0(i+1) <= '1';
                else
                    need_eof0(i+1) <= '0';
                end if;
            else
                need_eof0(i+1) <= need_eof0(i);
            end if;
        end loop;
    end process;

    -- stores the value of the last bit of the need_eof signal from the previous data word
    need_eof0_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                need_eof0_reg <= '0';
            elsif ((tx0_src_rdy ='1') and (new_dst_rdy0 = '1')) then
                need_eof0_reg <= need_eof0(REGIONS);
            end if;
        end if;
    end process;

    -- deciding whether the packet ends in the same region as it starts
    tx0_sof_b4_eof_ifg : if REGION_SIZE > 1 generate -- this if-generate necessary for MFB configuration: 2, 1, 8, 32
        tx0_sof_b4_eof_g : for i in 0 to REGIONS-1 generate
            sof_pos0_to_comp(i) <= resize_right(unsigned(tx0_sof_pos(max(1,log2(REGION_SIZE           ))*(i+1)-1 downto max(1,log2(REGION_SIZE           ))*i)),log2(REGION_SIZE*BLOCK_SIZE));
            eof_pos0_to_comp(i) <= resize_right(unsigned(tx0_eof_pos(max(1,log2(REGION_SIZE*BLOCK_SIZE))*(i+1)-1 downto max(1,log2(REGION_SIZE*BLOCK_SIZE))*i)),log2(REGION_SIZE*BLOCK_SIZE));
            tx0_sof_b4_eof(i)   <= '1' when (sof_pos0_to_comp(i) <= eof_pos0_to_comp(i)) else '0';
        end generate;
    else generate
        tx0_sof_b4_eof <= (others => '1');
    end generate;

    -- this process solves the problematic situation at need_eof0(0), where it has to decide, whether it recieves value from the need_eof0_reg or is calculated in this region
    eof0_p : process (all)
    begin
        eof0_l : for i in 0 to REGIONS-1 loop
            if ((tx0_sof(i) = '1') and (tx0_eof(i) = '1') and (tx0_sof_b4_eof(i) = '1')) then
                if (rx_sel(i) = '0') then
                    new_eof0(i) <= '1';
                else
                    new_eof0(i) <= '0';
                end if;
            elsif ((need_eof0(i) = '1') and (tx0_eof(i) = '1')) then
                new_eof0(i) <= '1';
            else
                new_eof0(i) <= '0';
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------
    -- new source ready logic for output 0
    -- -------------------------------------------------------------------------
    -- logic for determining if the packet continues from the previous region or not
    pkt_cont0_g : for i in 0 to REGIONS-1 generate
        pkt_cont0(i+1) <= (new_sof0(i) and not new_eof0(i) and not pkt_cont0(i)) or
                         (new_sof0(i) and new_eof0(i) and pkt_cont0(i)) or
                         (not new_sof0(i) and not new_eof0(i) and pkt_cont0(i));
    end generate;

    -- stores the value of the last bit ot the pkt_cont0 signal from the previous data word
    pkt_continues_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                pkt_cont0(0) <= '0';
            elsif ((tx0_src_rdy = '1') and (new_dst_rdy0 = '1')) then
                pkt_cont0(0) <= pkt_cont0(REGIONS);
            end if;
        end if;
    end process;

    -- the src_rdy in the current region is asserted if there are some valid data, so if there is a SOF or the packet continues from the previous region
    new_src_rdy0_g : for i in 0 to REGIONS-1 generate
        new_src_rdy0_regions(i) <= new_sof0(i) or pkt_cont0(i);
    end generate;

    new_src_rdy0 <= (or (new_src_rdy0_regions)) and tx0_src_rdy;

    -- -------------------------------------------------------------------------
    -- new destination ready logic for output 0
    -- -------------------------------------------------------------------------
    new_dst_rdy0 <= TX0_MFB_DST_RDY or not TX0_MFB_SRC_RDY;

    -- -------------------------------------------------------------------------
    -- output 0 registers
    -- -------------------------------------------------------------------------
    data_and_stuff_0_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (new_dst_rdy0 = '1') then
                TX0_MFB_DATA    <= tx0_data;
                TX0_MFB_META    <= tx0_meta;
                TX0_MFB_SOF_POS <= tx0_sof_pos;
                TX0_MFB_EOF_POS <= tx0_eof_pos;
            end if;
        end if;
    end process;

    control_sig_0_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (new_dst_rdy0 = '1') then
                TX0_MFB_SOF     <= new_sof0;
                TX0_MFB_EOF     <= new_eof0;
                TX0_MFB_SRC_RDY <= new_src_rdy0;
            end if;
            if (RST = '1') then
                TX0_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- ˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇ
    --                                 OUTPUT 1
    -- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
    -- ˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇˇ

    -- -------------------------------------------------------------------------
    -- SOF1 masking logic
    -- -------------------------------------------------------------------------
    -- SOF is take from the RX input and is masked by the select signal
    sof1_masking_p : process (all)
    begin
        sof1_l : for i in 0 to REGIONS-1 loop
            if (tx1_sof(i) = '1') then
                if (rx_sel(i) = '1') then
                    new_sof1(i) <= '1';
                else
                    new_sof1(i) <= '0';
                end if;
            else
                new_sof1(i) <= '0';
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------
    -- EOF1 masking logic
    -- -------------------------------------------------------------------------
    -- need_eof signal means there was a SOF and the next incoming EOF is needed for this output
    need_eof1_p : process (all)
    begin
        need_eof1(0) <= need_eof1_reg;
        sof0_l : for i in 0 to REGIONS-1 loop
            if (tx1_sof(i) = '1') then
                if (rx_sel(i) = '1') then
                    need_eof1(i+1) <= '1';
                else
                    need_eof1(i+1) <= '0';
                end if;
            else
                need_eof1(i+1) <= need_eof1(i);
            end if;
        end loop;
    end process;

    -- stores the value of the last bit of the need_eof signal from the previous data word
    need_eof1_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                need_eof1_reg <= '0';
            elsif ((tx1_src_rdy ='1') and (new_dst_rdy1 = '1')) then
                need_eof1_reg <= need_eof1(REGIONS);
            end if;
        end if;
    end process;

    -- deciding whether the packet ends in the same region as it starts
    tx1_sof_b4_eof_ifg : if REGION_SIZE > 1 generate -- necessary for MFB configuration: 2, 1, 8, 32
        tx1_sof_b4_eof_g : for i in 0 to REGIONS-1 generate
            sof_pos1_to_comp(i) <= resize_right(unsigned(tx1_sof_pos(max(1,log2(REGION_SIZE           ))*(i+1)-1 downto max(1,log2(REGION_SIZE           ))*i)),log2(REGION_SIZE*BLOCK_SIZE));
            eof_pos1_to_comp(i) <= resize_right(unsigned(tx1_eof_pos(max(1,log2(REGION_SIZE*BLOCK_SIZE))*(i+1)-1 downto max(1,log2(REGION_SIZE*BLOCK_SIZE))*i)),log2(REGION_SIZE*BLOCK_SIZE));
            tx1_sof_b4_eof(i)   <= '1' when (sof_pos1_to_comp(i) <= eof_pos1_to_comp(i)) else '0';
        end generate;
    else generate
        tx1_sof_b4_eof <= (others => '1');
    end generate;

    -- this process solves the problematic situation at need_eof1(0), where it has to decide, whether it recieves value from the need_eof1_reg or is calculated in this region
    eof1_p : process (all)
    begin
        eof0_l : for i in 0 to REGIONS-1 loop
            if ((tx1_sof(i) = '1') and (tx1_eof(i) = '1') and (tx1_sof_b4_eof(i) = '1')) then
                if (rx_sel(i) = '1') then
                    new_eof1(i) <= '1';
                else
                    new_eof1(i) <= '0';
                end if;
            elsif ((need_eof1(i) = '1') and (tx1_eof(i) = '1')) then
                new_eof1(i) <= '1';
            else
                new_eof1(i) <= '0';
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------
    -- new source ready logic for output 1
    -- -------------------------------------------------------------------------
    -- logic for determining if the packet continues from the previous region or not
    pkt_cont1_g : for i in 0 to REGIONS-1 generate
        pkt_cont1(i+1) <= (new_sof1(i) and not new_eof1(i) and not pkt_cont1(i)) or
                         (new_sof1(i) and new_eof1(i) and pkt_cont1(i)) or
                         (not new_sof1(i) and not new_eof1(i) and pkt_cont1(i));
    end generate;

    -- stores the value of the last bit ot the pkt_cont1 signal from the previous data word
    pkt_cont1_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                pkt_cont1(0) <= '0';
            elsif ((tx1_src_rdy = '1') and (new_dst_rdy1 = '1')) then
                pkt_cont1(0) <= pkt_cont1(REGIONS);
            end if;
        end if;
    end process;

    -- the src_rdy in the current region is asserted if there are some valid data, so if there is a SOF or the packet continues from the previous region
    new_src_rdy1_g : for i in 0 to REGIONS-1 generate
        new_src_rdy1_regions(i) <= new_sof1(i) or pkt_cont1(i);
    end generate;

    new_src_rdy1 <= (or (new_src_rdy1_regions)) and tx1_src_rdy;

    -- -------------------------------------------------------------------------
    -- new destination ready logic for output 1
    -- -------------------------------------------------------------------------
    new_dst_rdy1 <= TX1_MFB_DST_RDY or not TX1_MFB_SRC_RDY;

    -- -------------------------------------------------------------------------
    -- output 1 registers
    -- -------------------------------------------------------------------------
    data_and_stuff_1_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (new_dst_rdy1 = '1') then
                TX1_MFB_DATA    <= tx1_data;
                TX1_MFB_META    <= tx1_meta;
                TX1_MFB_SOF_POS <= tx1_sof_pos;
                TX1_MFB_EOF_POS <= tx1_eof_pos;
            end if;
        end if;
    end process;

    tx1_control_sig_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (new_dst_rdy1 = '1') then
                TX1_MFB_SOF     <= new_sof1;
                TX1_MFB_EOF     <= new_eof1;
                TX1_MFB_SRC_RDY <= new_src_rdy1;
            end if;
            if (RST = '1') then
                TX1_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    -- rx destination ready logic
    -- -------------------------------------------------------------------------
    RX_MFB_DST_RDY <= new_dst_rdy0 and new_dst_rdy1;

end behav;
