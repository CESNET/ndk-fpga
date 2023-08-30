library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

use work.math_pack.all;
use work.type_pack.all;
use ieee.math_real.all;

use WORK.many_core_package.ALL;

entity app_subcore_tb is
end app_subcore_tb;

architecture app_subcore_tb_arch of app_subcore_tb is

constant MI_WIDTH : natural := 32;
constant MFB_REGIONS : integer := 1;
constant MFB_REGION_SIZE : integer := 4; 
constant MFB_BLOCK_SIZE  : integer := 8;
constant MFB_ITEM_WIDTH  : integer := 8;
constant USR_PKT_SIZE_MAX : natural := 2**12;
constant DMA_RX_CHANNELS : integer := 2;
constant DMA_TX_CHANNELS : integer := 2;
constant DMA_HDR_META_WIDTH : natural := 12;
constant DEVICE: string :=  "ULTRASCALE";

signal clk_tb,  reset_tb: std_logic;
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
signal rx_mfb_dst_rdy: std_logic := '0';

signal rand_num : integer := 0;

begin

    uut_test: entity work.APP_SUBCORE 
        generic map(
         MI_WIDTH => MI_WIDTH,
         MFB_REGIONS => MFB_REGIONS,
         MFB_REGION_SIZE => MFB_REGION_SIZE,
         MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
         MFB_ITEM_WIDTH => MFB_ITEM_WIDTH,
         USR_PKT_SIZE_MAX => USR_PKT_SIZE_MAX,
         DMA_RX_CHANNELS => DMA_RX_CHANNELS,
         DMA_TX_CHANNELS => DMA_TX_CHANNELS,
         DMA_HDR_META_WIDTH => DMA_HDR_META_WIDTH,
         DEVICE => DEVICE
        )
        port map (
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
				DMA_TX_MFB_SRC_RDY => '0',
				
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
            clk_tb <= '0', '1' after clock_period / 2;
            wait for CLOCK_PERIOD;
        end loop;
        wait;
    end process;
    
    stimulus: process
    begin
        reset_tb <= '0'; -- reset
        wait for CLOCK_PERIOD;
        reset_tb <= '1'; -- reset
        wait for CLOCK_PERIOD;
        reset_tb <= '0'; -- reset
        wait for CLOCK_PERIOD;        
        
        wait for 400000*CLOCK_PERIOD;
        stop_the_clock <= true;

        wait;  
    end process;
    
   dst_rdy_random:  process
                    variable seed1, seed2: positive;   -- seed values for random generator
                    variable rand: real;   -- random real-number value in range 0 to 1.0  
                    variable range_of_rand : real := 10.0;    -- the range of random values created will be 0 to +1000.
                    begin
                        uniform(seed1, seed2, rand);   -- generate random number
                        rand_num <= integer(rand*range_of_rand);  -- rescale to 0..1000, convert integer part 
                        for i in 0 to rand_num loop
                            wait until rising_edge(clk_tb);
                        end loop;
                        rx_mfb_dst_rdy <= not rx_mfb_dst_rdy;
                    end process;

end app_subcore_tb_arch;