-- app_subcore.vhd: User application subcore
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Vladislav Vlake <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;

use WORK.many_core_package.ALL;
use WORK.RISCV_package.ALL;

entity APP_SUBCORE is
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
end entity;

architecture FULL of APP_SUBCORE is

component many_core_system is
    generic (NUM_ELEMENTS: positive := 1);
    port (  clk: in std_logic;
            reset: in std_logic;
            o_data_valid: out std_logic;
            o_data_out: out std_logic_vector (NUM_ELEMENTS*32 - 1 downto 0);  -- data out
            o_all_cores_done: out std_logic);
end component;

component dual_port_byte_en_RAM is
    generic (   SIZE: integer := 1024;
                ADDR_WIDTH: integer := 10;
                COL_WIDTH: integer := 8;
                NB_COL: integer := 4);
    port (  clka: in std_logic;
            ena: in std_logic;
            wea: in std_logic_vector(NB_COL - 1 downto 0);
            addra: in std_logic_vector(ADDR_WIDTH - 1 downto 0);
            dina: in std_logic_vector(NB_COL*COL_WIDTH - 1 downto 0);
            douta: out std_logic_vector(NB_COL*COL_WIDTH - 1 downto 0);
            clkb: in std_logic;
            enb: in std_logic;
            web: in std_logic_vector(NB_COL - 1 downto 0);
            addrb: in std_logic_vector(ADDR_WIDTH - 1 downto 0);
            dinb: in std_logic_vector(NB_COL*COL_WIDTH - 1 downto 0);
            doutb : out std_logic_vector(NB_COL*COL_WIDTH - 1 downto 0));
end component;

--signals for 8 BRAMs generated for frame buffer 
type rd_data_type is array(0 to 7) of DATA_TYPE;
signal rd_data_arr: rd_data_type;
signal wr_addr, rd_addr: std_logic_vector(13 downto 0);
signal ena_arr, enb_arr: std_logic_vector(0 to 7);
signal wr_data_in, buffer_data_32bit: DATA_TYPE;
signal valid, all_cores_done: std_logic; 
signal wr_en: std_logic_vector(3 downto 0);  -- write 4 individual bytes in BRAM  


-- signals for PCI
signal packed_data: std_logic_vector(511 downto 0);
signal packed_data_counter: integer range 0 to 15;
signal next_read_buffer, enable_PCI, ready_to_send, send_first_half: std_logic;

begin

    MI_DRD  <= (others => '0');
    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;

 /*   DMA_RX_MFB_META_PKT_SIZE <= DMA_TX_MFB_META_PKT_SIZE;
    DMA_RX_MFB_META_HDR_META <= DMA_TX_MFB_META_HDR_META;
    DMA_RX_MFB_META_CHAN     <= DMA_TX_MFB_META_CHAN;

    DMA_RX_MFB_DATA    <= DMA_TX_MFB_DATA;
    DMA_RX_MFB_SOF     <= DMA_TX_MFB_SOF;
    DMA_RX_MFB_EOF     <= DMA_TX_MFB_EOF;
    DMA_RX_MFB_SOF_POS <= DMA_TX_MFB_SOF_POS;
    DMA_RX_MFB_EOF_POS <= DMA_TX_MFB_EOF_POS;
    DMA_RX_MFB_SRC_RDY <= DMA_TX_MFB_SRC_RDY;
    DMA_TX_MFB_DST_RDY <= DMA_RX_MFB_DST_RDY;*/

    DMA_RX_MFB_META_PKT_SIZE <= std_logic_vector(to_unsigned(256, DMA_RX_MFB_META_PKT_SIZE'length));
    DMA_RX_MFB_META_HDR_META <= (others => '0');
    DMA_RX_MFB_META_CHAN <= (others => '0');
    
    many_core:  many_core_system 
                port map (  clk => clk,
                            reset => reset,
                            o_data_valid => valid,                          
                            o_data_out => wr_data_in,
                            o_all_cores_done => all_cores_done);
                            
-- Code specific to many_core_system testing Mandelbrot Set Computation
-- We need a frame buffer of size 16384 elements,each 16 bits wide -- too big to fit into one BRAM!
-- We need to instantiate 8 BRAMs                          
gen_frame_buffer:   for i in 0 to 7 generate
                    begin
                        gen_BRAM:   dual_port_byte_en_RAM 
                                        generic map (   SIZE => 2048,
                                                        ADDR_WIDTH => 11,
                                                        COL_WIDTH => 8,
                                                        NB_COL => 4)
                                        port map (  clka => CLK,
                                                    ena => ena_arr(i),
                                                    wea => wr_en, 
                                                    addra => wr_addr(10 downto 0),
                                                    dina => wr_data_in,
                                                    douta => open,
                                                    clkb => CLK,
                                                    enb => enb_arr(i),
                                                    web => (others =>'0'),
                                                    addrb => rd_addr(10 downto 0),
                                                    dinb => (others => '0'),
                                                    doutb => rd_data_arr(i));       
                        end generate gen_frame_buffer;
                        
    wr_en <= (others => '1') when (valid = '1') else (others => '0') ; -- write 4 individual bytes in BRAM                  
    wr_addr <= wr_data_in((9 + JOB_ID_BIT_WIDTH) downto 10); -- location in BRAM, iteration counter for Mandelbrot is 10 bits wide          
          
-- select the correct BRAM for writing
BRAM_wr_proc:   process(all)
                    begin
                        for i in 0 to 7 loop
                            if (wr_addr(13 downto 11) = std_logic_vector(to_unsigned(i, 3))) then
                                ena_arr(i) <='1';
                            else 
                                ena_arr(i) <='0';
                            end if;
                        end loop;      
                 
                    end process; 
               
-- read from frame buffer and send to PCI interface logic                                                                                                                                                                                      
 transfer_to_PCI:   process(clk)
                    begin
                        if (rising_edge(clk)) then
                            if (reset = '1') then
                                packed_data_counter <= 1;
                                DMA_RX_MFB_SRC_RDY <= '0';
                                next_read_buffer <= '1';
                                ready_to_send <= '0';
                                enable_PCI <= '0';
                                send_first_half <= '1';
                            elsif ( (all_cores_done = '1') and (unsigned(rd_addr) < NUM_JOBS) and (next_read_buffer = '1') ) then 
								for i in 0 to 7 loop
									if (rd_addr(13 downto 11) = std_logic_vector(to_unsigned(i, 3))) then
										enb_arr(i) <='1';
										enable_PCI <= '1';
										buffer_data_32bit <= rd_data_arr(i);
									else 
										enb_arr(i) <= '0';
										enable_PCI <= '0';
									end if;
								end loop; 
								rd_addr <= std_logic_vector(unsigned(rd_addr) + 1);  		
                            elsif (ready_to_send = '1') then                                                                     
                                if (DMA_TX_MFB_DST_RDY = '1') then
									if(send_first_half = '1') then										
										DMA_RX_MFB_DATA    <= packed_data(255 downto 0);
										DMA_RX_MFB_SOF     <= "1";
										DMA_RX_MFB_EOF     <= "0";
										DMA_RX_MFB_SOF_POS <= (others => '0');
										DMA_RX_MFB_EOF_POS <= (others => '1');
										DMA_RX_MFB_SRC_RDY <= '1';
										ready_to_send <= '1';
										next_read_buffer <= '1';
										send_first_half <= '0';		
									else									
										DMA_RX_MFB_DATA    <= packed_data(511 downto 256);
										DMA_RX_MFB_SOF     <= "0";
										DMA_RX_MFB_EOF     <= "1";
										DMA_RX_MFB_SOF_POS <= (others => '0');
										DMA_RX_MFB_EOF_POS <= (others => '1');
										DMA_RX_MFB_SRC_RDY <= '1';
										ready_to_send <= '0';
										send_first_half <= '1';	
								    end if;																											
								else
									next_read_buffer <= '0';
								end if;    
                            elsif ( (enable_PCI = '1') and (packed_data_counter <= 15) and (ready_to_send = '0') ) then  
								packed_data((packed_data_counter*32 - 1) downto 0) <= buffer_data_32bit;
                                packed_data_counter <= packed_data_counter + 1;
                                if (packed_data_counter = 15) then
									ready_to_send <= '1';
								end if;								  
                            end if;
                        end if;                   
                    end process;   
    
end architecture;
