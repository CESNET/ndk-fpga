use WORK.RISCV_package.ALL;
use WORK.many_core_package.ALL;

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity many_core_system_top is
    port (  CLK: in std_logic;
            RESET: in std_logic;
            TX: out std_logic);  
end many_core_system_top;

architecture many_core_system_top_arch of many_core_system_top is

-- in case collect FIFOs is preferred
-- default number of times 4 barrel cores, each with a FIFO will be replicated
-- the 4 cores share a collect FIFO
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

-- signals for frame buffer
signal wr_addr, rd_addr: std_logic_vector(13 downto 0);
signal rd_data: std_logic_vector(15 downto 0);
signal data_valid: std_logic;
signal wr_en: std_logic_vector(1 downto 0);  -- write 2 individual bytes in BRAM  

--signals for 8 BRAMs generated for frame buffer 
type rd_data_type is array(0 to 7) of std_logic_vector(15 downto 0);
signal rd_data_arr: rd_data_type;
signal ena_arr, enb_arr: std_logic_vector(0 to 7);
signal data_out: DATA_TYPE;
signal wr_data_in: std_logic_vector(15 downto 0); 

-- signal for all core done
signal all_cores_done: std_logic;

signal test_data: DATA_TYPE;

attribute keep : string;
attribute keep of wr_addr, rd_addr, rd_data, data_valid, data_out, test_data: signal is "true";
attribute keep of ena_arr, enb_arr, all_cores_done: signal is "true";
             
begin

uut_many_core:    many_core_system generic map (NUM_ELEMENTS => 1)
                                   port map (   clk => CLK,
                                                reset => RESET,
                                                o_data_valid => data_valid,
                                                o_data_out => data_out,
                                                o_all_cores_done => all_cores_done);                                                                                                   
                                                   
-- We need a frame buffer of size 16384 elements,each 16 bits wide -- too big to fit into one BRAM!
-- We need to instantiate 8 BRAMs                          
gen_frame_buffer:   for i in 0 to 7 generate
                    begin
                        gen_BRAM:   dual_port_byte_en_RAM 
                                        generic map (   SIZE => 2048,
                                                        ADDR_WIDTH => 11,
                                                        COL_WIDTH => 8,
                                                        NB_COL => 2)
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
                        
    wr_en <= "11" when (data_valid = '1') else "00"; -- write 2 individual bytes in BRAM                  
    wr_addr <= data_out((9 + JOB_ID_BIT_WIDTH) downto 10); -- location in BRAM
    wr_data_in <= func_zero_ext(data_out(9 downto 0), 16); -- iteration counter for Mandelbrot is 10 bits            
          
-- select the correct BRAM for writing
sel_BRAM_wr_proc:   process(wr_addr)
                    begin
                        for i in 0 to 7 loop
                            if (wr_addr(13 downto 11) = std_logic_vector(to_unsigned(i, 3))) then
                                ena_arr(i) <='1';
                            else 
                                ena_arr(i) <='0';
                            end if;
                        end loop;                          
                    end process; 
               
-- select the correct BRAM for reading                  
sel_BRAM_rd_proc:   process(rd_addr)
                    begin                   
                        for i in 0 to 7 loop
                            if (rd_addr(13 downto 11) = std_logic_vector(to_unsigned(i, 3))) then
                                enb_arr(i) <='1';
                                rd_data <= rd_data_arr(i);
                            else 
                                enb_arr(i) <= '0';
                            end if;
                        end loop;                          
                    end process;                                                                                                                                       
    
    -- just for testing purposes and for using the pin uart_tx  
    --uart_tx <= buffer_rd_data(0); 
    
-- read from mem buffer to check output 
-- later this will replaced by the PCI interface
read_from_mem_buffer:   process (CLK)
                        begin
                            if rising_edge(CLK) then
                                if (RESET = '0') then
                                    rd_addr <= (others => '0');
                                    test_data <= (others => '0');
                                elsif ( (all_cores_done = '1') and (unsigned(rd_addr) < NUM_JOBS) ) then 
                                    rd_addr <= std_logic_vector(unsigned(rd_addr) + 1); 
                                    test_data <= func_sign_ext(rd_data, DATA_WIDTH);   
                                end if; 
                            end if;
                        end process; 
                                    
                        
end many_core_system_top_arch;