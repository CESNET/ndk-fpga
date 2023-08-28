use WORK.many_core_package.ALL;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity many_core_system_tb is
end many_core_system_tb;

architecture many_core_system_tb_arch of many_core_system_tb is

component APP_SUBCORE is
    generic (
        MI_WIDTH : natural := 32;

        -- MFB parameters
        MFB_REGIONS     : integer := 1;  -- Number of regions in word
        MFB_REGION_SIZE : integer := 8;  -- Number of blocks in region
        MFB_BLOCK_SIZE  : integer := 8;  -- Number of items in block
        MFB_ITEM_WIDTH  : integer := 8;  -- Width of one item in bits

        -- Maximum size of a User packet (in bytes)
        -- Defines width of Packet length signals.
        USR_PKT_SIZE_MAX : natural := 2**12;

        -- Number of streams from DMA module
        DMA_RX_CHANNELS : integer;
        DMA_TX_CHANNELS : integer;

        -- Width of TX User Header Metadata information extracted from descriptor
        DMA_HDR_META_WIDTH : natural := 12;

        DEVICE : string := "ULTRASCALE"
        );
    port (
        -- =========================================================================
        -- Clock and Resets inputs
        -- =========================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =====================================================================
        -- TX DMA User-side MFB
        -- =====================================================================
        DMA_TX_MFB_META_PKT_SIZE : in std_logic_vector(log2(USR_PKT_SIZE_MAX + 1) -1 downto 0);
        DMA_TX_MFB_META_HDR_META : in std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
        DMA_TX_MFB_META_CHAN     : in std_logic_vector(log2(DMA_TX_CHANNELS) -1 downto 0);

        DMA_TX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        DMA_TX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_TX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_TX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
        DMA_TX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        DMA_TX_MFB_SRC_RDY : in  std_logic;
        DMA_TX_MFB_DST_RDY : out std_logic := '1';

        -- =====================================================================
        -- RX DMA User-side MFB
        -- =====================================================================
        DMA_RX_MFB_META_PKT_SIZE : out std_logic_vector(log2(USR_PKT_SIZE_MAX + 1) -1 downto 0);
        DMA_RX_MFB_META_HDR_META : out std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
        DMA_RX_MFB_META_CHAN     : out std_logic_vector(log2(DMA_RX_CHANNELS) -1 downto 0);

        DMA_RX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        DMA_RX_MFB_SOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_RX_MFB_EOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_RX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
        DMA_RX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        DMA_RX_MFB_SRC_RDY : out std_logic;
        DMA_RX_MFB_DST_RDY : in  std_logic;

        -- =========================================================================
        --  MI INTERFACE
        -- =========================================================================
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
        );
end component;

signal clk_p_tb, clk_n_tb, reset_tb, uart_rx_tb, uart_tx_tb: std_logic;
constant CLOCK_PERIOD: time := 10 ns;
signal stop_the_clock: boolean := false;
signal rx_mfb_meta_pkt_size: std_logic_vector(log2(USR_PKT_SIZE_MAX + 1) -1 downto 0);
signal rx_mfb_meta_dhr_meta: std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
signal rx_mfb_meta_chan: std_logic_vector(log2(DMA_RX_CHANNELS) -1 downto 0);
signal rx_mfb_data: std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
signal rx_mfb_sof: std_logic_vector(MFB_REGIONS -1 downto 0);
signal rx_mfb_eof: std_logic_vector(MFB_REGIONS -1 downto 0);
signal rx_mfb_sof_pos: std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
signal rx_mfb_eof_pos: std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
signal rx_mfb_src_rdy: std_logic;
signal rx_mfb_dst_rdy: std_logic;

begin

    uut_test: APP_SUBCORE port map (
				CLK => clk_tb,
				RESET => reset_tb,
				
				DMA_TX_MFB_META_PKT_SIZE => (others => '0'),
				DMA_TX_MFB_META_HDR_META => (others => '0'),
				DMA_TX_MFB_META_CHAN => (others => '0'),

				DMA_TX_MFB_DATA => (others => '0'),
				DMA_TX_MFB_SOF => (others => '0'),
				DMA_TX_MFB_EOF => (others => '0'),
				DMA_TX_MFB_SOF_POS => (others => '0'),
				DMA_TX_MFB_EOF_POS => (others => '0'),
				DMA_TX_MFB_SRC_RDY => '0');
				
				DMA_RX_MFB_META_PKT_SIZE => rx_mfb_meta_pkt_size,
				DMA_RX_MFB_META_HDR_META => rx_mfb_meta_dhr_meta,
				DMA_RX_MFB_META_CHAN => rx_mfb_meta_chan,

				DMA_RX_MFB_DATA => rx_mfb_data,
				DMA_RX_MFB_SOF  => rx_mfb_sof,
				DMA_RX_MFB_EOF => rx_mfb_eof,
				DMA_RX_MFB_SOF_POS => rx_mfb_sof_pos,
				DMA_RX_MFB_EOF_POS => rx_mfb_eof_pos,
				DMA_RX_MFB_SRC_RDY => rx_mfb_src_rdy,
				DMA_RX_MFB_DST_RDY  => rx_mfb_dst_rdy,
				
				MI_DWR => (others => '0'),
				MI_ADDR => (others => '0'),
				MI_BE => (others => '0'),
				MI_RD => '0',
				MI_WR => '0',
				MI_DRD => open,
				MI_ARDY => open,
				MI_DRDY => open);
				
    -- Clock
    clocking: process
    begin
        while not stop_the_clock loop
            clk_p_tb <= '0', '1' after clock_period / 2;
            wait for CLOCK_PERIOD;
        end loop;
        wait;
    end process;
    
    stimulus: process
    begin
        reset_tb <= '1'; -- reset
        wait for CLOCK_PERIOD;
        reset_tb <= '0'; -- reset
        wait for CLOCK_PERIOD;
        reset_tb <= '1'; -- reset
        wait for CLOCK_PERIOD;
        
        wait for 400000*CLOCK_PERIOD;
        stop_the_clock <= true;

        wait;  
    end process;

end many_core_system_tb_arch;
