-- pcie_avst2mfb.vhd: This component transfers AVST bus to MFB.
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

entity PCIE_AVST2MFB is
    Generic(
        REGIONS            : natural := 2;
        REGION_SIZE        : natural := 1; -- not to be changed
        BLOCK_SIZE         : natural := 8; -- not to be changed
        ITEM_WIDTH         : natural := 32; -- not to be changed
        META_WIDTH         : natural := 8;
        AVALON_RDY_LATENCY : natural := 1;
        FIFO_DEPTH         : natural := 32;
        FIFO_ENABLE        : boolean := true;
        FIFO_RAM_TYPE      : string  := "AUTO";
        DEVICE             : string  := "STRATIX10"
    );
    Port(
        CLK            : in  std_logic;
        RST            : in  std_logic;
        -- rx interface
        RX_AVST_DATA   : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_AVST_META   : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_AVST_SOP    : in  std_logic_vector(REGIONS-1 downto 0);
        RX_AVST_EOP    : in  std_logic_vector(REGIONS-1 downto 0);
        RX_AVST_EMPTY  : in  std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_AVST_VALID  : in  std_logic_vector(REGIONS-1 downto 0);
        RX_AVST_READY  : out std_logic;
        -- tx interface
        TX_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture behav of PCIE_AVST2MFB is

    constant META_SIGNAL_WIDTH : natural := REGIONS*META_WIDTH;
    constant DATA_WIDTH        : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant EOF_POS_WIDTH     : natural := REGIONS*log2(REGION_SIZE*BLOCK_SIZE); -- also for avst_empty
    constant FIFO_DATA_WIDTH   : natural := 2*REGIONS + EOF_POS_WIDTH + META_SIGNAL_WIDTH + DATA_WIDTH;

    signal rx_avst_sop_masked : std_logic_vector(REGIONS - 1 downto 0);
    signal rx_avst_eop_masked : std_logic_vector(REGIONS - 1 downto 0);
    signal avst_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal avst_sop           : std_logic_vector(REGIONS - 1 downto 0);
    signal avst_eop           : std_logic_vector(REGIONS - 1 downto 0);
    signal avst_meta          : std_logic_vector(META_SIGNAL_WIDTH - 1 downto 0);
    signal avst_empty         : std_logic_vector(EOF_POS_WIDTH - 1 downto 0);
    signal fifo_data_in       : std_logic_vector(FIFO_DATA_WIDTH - 1 downto 0);
    signal fifo_wr            : std_logic;
    signal fifo_full          : std_logic;
    signal fifo_afull         : std_logic;
    signal fifo_owf_err_reg   : std_logic;
    signal fifo_data_out      : std_logic_vector(FIFO_DATA_WIDTH - 1 downto 0);
    signal fifo_empty         : std_logic;
    signal avst_empty_arr     : slv_array_t(REGIONS - 1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE) - 1 downto 0);
    signal mfb_eof_pos_arr    : slv_array_t(REGIONS - 1 downto 0)(log2(REGION_SIZE*BLOCK_SIZE) - 1 downto 0);
    signal mfb_eof_pos        : std_logic_vector(EOF_POS_WIDTH - 1 downto 0);
    signal mfb_src_rdy        : std_logic;

    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of fifo_owf_err_reg : signal is true;

begin

    fifo_enable_g : if (FIFO_ENABLE = true) generate

        rx_avst_sop_masked <= RX_AVST_SOP and RX_AVST_VALID;
        rx_avst_eop_masked <= RX_AVST_EOP and RX_AVST_VALID;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                fifo_data_in <= rx_avst_sop_masked & rx_avst_eop_masked & RX_AVST_EMPTY & RX_AVST_META & RX_AVST_DATA;
            end if;
        end process;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    fifo_wr <= '0';
                else
                    fifo_wr <= or RX_AVST_VALID;
                end if;
            end if;
        end process;

        avst_ready_reg_p :process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    RX_AVST_READY <= '0';
                else
                    RX_AVST_READY <= not fifo_afull;
                end if;
            end if;
        end process;

        fifox_i: entity work.FIFOX
        generic map(
           DATA_WIDTH         => FIFO_DATA_WIDTH,
           ITEMS              => FIFO_DEPTH,
           ALMOST_FULL_OFFSET => AVALON_RDY_LATENCY+1+1,
           DEVICE             => DEVICE,
           RAM_TYPE           => FIFO_RAM_TYPE
        )
        port map(
            CLK    => CLK,
            RESET  => RST,
            DI     => fifo_data_in,
            WR     => fifo_wr,
            FULL   => fifo_full,
            AFULL  => fifo_afull,
            STATUS => open,
            DO     => fifo_data_out,
            RD     => TX_MFB_DST_RDY,
            EMPTY  => fifo_empty,
            AEMPTY => open
        );

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (fifo_wr = '1' and fifo_full = '1') then
                    fifo_owf_err_reg <= '1';
                end if;
                if (RST = '1') then
                    fifo_owf_err_reg <= '0';
                end if;
            end if;
        end process;

        assert (fifo_owf_err_reg /= '1')
            report "PCIE_AVST2MFB: fifox_i overflow!"
            severity failure;

        avst_sop   <= fifo_data_out(FIFO_DATA_WIDTH-1 downto DATA_WIDTH+META_SIGNAL_WIDTH+EOF_POS_WIDTH+REGIONS);
        avst_eop   <= fifo_data_out(DATA_WIDTH+META_SIGNAL_WIDTH+EOF_POS_WIDTH+REGIONS-1 downto DATA_WIDTH+META_SIGNAL_WIDTH+EOF_POS_WIDTH);
        avst_empty <= fifo_data_out(DATA_WIDTH+META_SIGNAL_WIDTH+EOF_POS_WIDTH-1 downto DATA_WIDTH+META_SIGNAL_WIDTH);
        avst_meta  <= fifo_data_out(DATA_WIDTH+META_SIGNAL_WIDTH-1 downto DATA_WIDTH);
        avst_data  <= fifo_data_out(DATA_WIDTH-1 downto 0);

        --(avst_sop, avst_eop, avst_empty, avst_meta, avst_data) <= fifo_data_out;

        avst_empty_arr <= slv_array_downto_deser(avst_empty, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

        eof_pos_array_g : for i in 0 to REGIONS - 1 generate
            mfb_eof_pos_arr(i) <= std_logic_vector((REGION_SIZE*BLOCK_SIZE-1) - unsigned(avst_empty_arr(i)));
        end generate ;

        mfb_eof_pos <= slv_array_ser(mfb_eof_pos_arr, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

        mfb_src_rdy <= not fifo_empty;

        TX_MFB_DATA    <= avst_data;
        TX_MFB_META    <= avst_meta;
        TX_MFB_SOF     <= avst_sop;
        TX_MFB_EOF     <= avst_eop;
        TX_MFB_EOF_POS <= mfb_eof_pos;
        TX_MFB_SRC_RDY <= mfb_src_rdy;

    else generate

        TX_MFB_DATA    <= RX_AVST_DATA;
        TX_MFB_META    <= RX_AVST_META;
        TX_MFB_SOF     <= RX_AVST_SOP and RX_AVST_VALID;
        TX_MFB_EOF     <= RX_AVST_EOP and RX_AVST_VALID;

        avst_empty_arr <= slv_array_downto_deser(RX_AVST_EMPTY, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

        eof_pos_array_g : for i in 0 to REGIONS - 1 generate
            mfb_eof_pos_arr(i) <= std_logic_vector((REGION_SIZE*BLOCK_SIZE-1) - unsigned(avst_empty_arr(i)));
        end generate ;

        TX_MFB_EOF_POS <= slv_array_ser(mfb_eof_pos_arr, REGIONS, log2(REGION_SIZE*BLOCK_SIZE));

        TX_MFB_SRC_RDY <= or (RX_AVST_VALID);

        RX_AVST_READY <= TX_MFB_DST_RDY;
    end generate;


end behav;
