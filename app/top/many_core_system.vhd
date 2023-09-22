-- default number of times 4 barrel cores, each with a FIFO will be replicated
-- the 4 cores share a collect FIFO

use WORK.many_core_package.ALL;
use WORK.RISCV_package.ALL;

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

use work.math_pack.all;

entity many_core_system is
    generic (NUM_ELEMENTS: positive := 1);
    port (  clk: in std_logic;
            reset: in std_logic;
            o_data_valid: out std_logic;
            o_data_out: out std_logic_vector (NUM_ELEMENTS*32 - 1 downto 0);  -- data out, multiple of 32 bits
            o_all_cores_done: out std_logic);
end many_core_system;

architecture many_core_system_arch of many_core_system is

-- regFile 1 and 2 in BRAM, data mem in BRAM with regFile2, instr mem distributed, no multiplier
component barrel_core_variant_1 is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job 
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core 
            o_core_done: out std_logic); -- this core is done, all its threads are done         
end component;

-- regFile 2 in BRAM, data mem in BRAM with regFile2, regFile1 distributed, instr mem distributed, no multiplier    
component barrel_core_variant_2 is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job 
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core 
            o_core_done: out std_logic); -- this core is done, all its threads are done              
end component;

-- regFile 1 and 2 distributed mem, instr mem and data mem combi in BRAM, no multiplier  
component barrel_core_variant_3 is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            i_data_from_mem: in DATA_TYPE; -- data read from memory
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_data_mem_wr_en: out std_logic_vector(3 downto 0); --enable for data memory
            o_data_mem_addr: out std_logic_vector(DATA_MEM_ADDR_WIDTH - 1 downto 0); -- addr of data to be read from memory
            o_data_to_mem: out DATA_TYPE; -- data to be written to memory
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job  
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core  
            o_core_done: out std_logic); -- this core is done, all its threads are done  
end component;

-- regFile 1 and 2 in BRAM, data mem in BRAM with regFile2, instr mem distributed, WITH multiplier
component barrel_core_variant_1_mult is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job 
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core 
            o_core_done: out std_logic); -- this core is done, all its threads are done      
end component;

-- regFile 2 in BRAM, data mem in BRAM with regFile2, regFile1 distributed, instr mem distributed, WITH multiplier  
component barrel_core_variant_2_mult is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job 
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core 
            o_core_done: out std_logic); -- this core is done, all its threads are done          
end component;

 -- regFile 1 and 2 distributed mem, instr mem and data mem combi in BRAM, WITH multiplier  
component barrel_core_variant_3_mult is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(log2(NUM_CORES) - 1 downto 0);
            i_core_dispatch_en: in std_logic; -- this core is currently enabled by dispatcher to dispatch job
            i_core_result_en: in std_logic; -- this core is currently enabled by dispatcher to collect job result
            i_job_value: in std_logic_vector(DATA_WIDTH - 1 downto 0); -- incoming job incl. param
            i_instr: in DATA_TYPE; -- incoming instruction
            i_data_from_mem: in DATA_TYPE; -- data read from memory
            o_next_instr_addr: out std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0); -- pc 
            o_data_mem_wr_en: out std_logic_vector(3 downto 0); --enable for data memory
            o_data_mem_addr: out std_logic_vector(DATA_MEM_ADDR_WIDTH - 1 downto 0); -- addr of data to be read from memory
            o_data_to_mem: out DATA_TYPE; -- data to be written to memory
            o_fifo_write: out std_logic;  -- write enable for fifo
            o_data_to_fifo: out std_logic_vector(DATA_WIDTH - 1 downto 0); -- data to be written to FIFO
            o_job_request: out std_logic; -- request for a new job  
            o_job_done: out std_logic; -- result can be read from core 
            o_job_result: out DATA_TYPE; -- result to be sent out of core  
            o_core_done: out std_logic); -- this core is done, all its threads are done  
end component;

-- instr memory
component instr_rom is
    port ( clk: in std_logic;
           addr: in std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
           data: out DATA_TYPE); 
end component;

-- instr and data memory in BRAM
component instr_data_mem_combi is
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

-- fifo for writing results from core
component fifo is
    generic ( depth : integer := 16; -- depth of fifo
              width : integer := 32);  -- width of data
    port (    clk : in std_logic;
              reset : in std_logic;
              rd_en : in std_logic; -- enable read, '0' when not in use
              wr_en : in std_logic; -- enable write, 0' when not in use
              din : in std_logic_vector ((width - 1) downto 0); -- input data
              dout : out std_logic_vector((width - 1) downto 0); -- output data
              empty : out std_logic; -- set as '1' when the queue is empty
              full : out std_logic); -- set as '1' when the queue is full
end component;

type core_id_matrix is array (0 to NUM_CORES_DIM - 1, 0 to NUM_CORES_DIM - 1) of std_logic_vector(log2(NUM_CORES)- 1 downto 0);
type fifo_array is array (0 to NUM_CORES + NUM_COLLECT_FIFOS - 1) of DATA_TYPE;
type instr_addr_array is array (0 to NUM_CORES - 1) of std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
type data_mem_addr_array is array (0 to NUM_CORES - 1) of std_logic_vector(DATA_MEM_ADDR_WIDTH - 1 downto 0); 
type data_array is array (0 to NUM_CORES - 1) of DATA_TYPE; 
type mem_wr_en_array is array (0 to NUM_CORES - 1) of std_logic_vector(3 downto 0); 
type bit_array is array (0 to NUM_CORES - 1) of std_logic; 

signal core_id: core_id_matrix;
signal data_to_fifo, data_out_of_fifo: fifo_array;
signal instr, data_to_mem, data_from_mem: data_array;
signal instr_addr: instr_addr_array;
signal fifo_read, fifo_write, fifo_empty, fifo_full: std_logic_vector(0 to NUM_CORES + NUM_COLLECT_FIFOS - 1);
signal fifo_read_local_final, fifo_read_local_final_1: std_logic; 
signal core_dispatch_en, core_result_en,  job_request, job_done: bit_array;
signal job_value, result_value: data_array;
signal data_mem_wr_en: mem_wr_en_array;
signal data_mem_addr: data_mem_addr_array;

-- signal for all core done
signal all_cores_done_reg: std_logic_vector(NUM_CORES - 1 downto 0);
signal results_count: unsigned(log2(NUM_JOBS) downto 0);

-- signals for job dispatcher 
signal job_count: unsigned(log2(NUM_JOBS)  downto 0);
signal core_index, core_index_1, core_index_2: unsigned(log2(NUM_CORES) - 1 downto 0);
signal wr_en, wr_en_1,wr_en_2: std_logic;

--attribute keep : string;
--attribute keep of data_to_mem, data_mem_wr_en, data_mem_addr, core_dispatch_en, core_index, core_index_1, core_index_2, wr_en, wr_en_1, wr_en_2, job_count, job_value, result_value, job_request, job_done: signal is "true";
--attribute keep of core_id: signal is "true";
--attribute keep of fifo_read, fifo_write, fifo_empty, fifo_full, data_to_fifo, data_out_of_fifo: signal is "true";
--attribute keep of results_count, o_all_cores_done, all_cores_done_reg, fifo_read_local_final, fifo_read_local_final_1: signal is "true";
             
begin

-- initialize core IDs in 2 dimensional array
init_proc:  process(clk)
            begin
                if rising_edge(clk) then
                    if (reset = '0') then
                        for i in 0 to NUM_CORES_DIM - 1 loop
                            for j in 0 to NUM_CORES_DIM - 1 loop
                                core_id(i, j) <= std_logic_vector(to_unsigned(NUM_CORES_DIM*i + j, log2(NUM_CORES))); 
                            end loop;
                        end loop; 
                    end if;
                end if;
            end process;

-- instantiation barrel core system in 2 dimensions - size NUM_CORES_DIM in each dimension 

-- regFile 1 and 2 in BRAM, data mem in BRAM with regFile2, instr mem distributed, no multiplier
if_gen_core:    if ( (REGFILE_1_SELECT = '1') and (REGFILE_2_SELECT = '1') and (DATA_MEM_SELECT = '1') and (INSTR_MEM_SELECT = '0') and (MULTIPLIER_SELECT = '0') ) generate 
                    gen_i:  for i in 0 to (NUM_CORES_DIM - 1) generate          
                            begin   
                            gen_j:  for j in 0 to (NUM_CORES_DIM  - 1) generate
                                    begin
                                        -- instantiation core
                                        C: barrel_core_variant_1 port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j), 
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));  
                                    end generate gen_j;                                     
                            end generate gen_i;                             

 -- regFile 2 in BRAM, data mem in BRAM with regFile2, regFile1 distributed, instr mem distributed, no multiplier                                
                elsif ( (REGFILE_1_SELECT = '0') and (REGFILE_2_SELECT = '1') and (DATA_MEM_SELECT = '1') and (INSTR_MEM_SELECT = '0') and (MULTIPLIER_SELECT = '0') ) generate 
                    gen_i:  for i in 0 to NUM_CORES_DIM  - 1 generate          
                            begin   
                            gen_j:  for j in 0 to NUM_CORES_DIM  - 1 generate
                                    begin
                                        -- instantiation core
                                        C: barrel_core_variant_2 port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j),
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));    
                                    end generate gen_j;                                     
                            end generate gen_i;   
                                                  
 -- regFile 1 and 2 distributed mem, instr mem and data mem combi in BRAM, no multiplier                                
                elsif ( (REGFILE_1_SELECT = '0') and (REGFILE_2_SELECT = '0') and (DATA_MEM_SELECT = '0') and (INSTR_MEM_SELECT = '1') and (MULTIPLIER_SELECT = '0') ) generate 
                    gen_i:  for i in 0 to NUM_CORES_DIM - 1 generate          
                            begin   
                            gen_j:  for j in 0 to NUM_CORES_DIM - 1 generate
                                    begin
                                        -- instantiation core
                                        C: barrel_core_variant_3 port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        i_data_from_mem => data_from_mem(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_data_mem_wr_en => data_mem_wr_en(NUM_CORES_DIM*i + j),
                                                        o_data_mem_addr => data_mem_addr(NUM_CORES_DIM*i + j),
                                                        o_data_to_mem => data_to_mem(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));   
                                end generate gen_j;                                     
                            end generate gen_i;   
                                                                
 -- regFile 1 and 2 in BRAM, data mem in BRAM with regFile2, instr mem distributed, WITH multiplier                                                                                       
                 elsif ( (REGFILE_1_SELECT = '1') and (REGFILE_2_SELECT = '1') and (DATA_MEM_SELECT = '1') and (INSTR_MEM_SELECT = '0') and (MULTIPLIER_SELECT = '1') ) generate 
                    gen_i:  for i in 0 to NUM_CORES_DIM - 1 generate          
                            begin   
                            gen_j:  for j in 0 to NUM_CORES_DIM - 1 generate
                                    begin
                                        -- instantiation core
                                      C: barrel_core_variant_1_mult port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j), 
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));  
                                    end generate gen_j;                                     
                            end generate gen_i;                                      
                                    
 -- regFile 2 in BRAM, data mem in BRAM with regFile2, regFile1 distributed, instr mem distributed, WITH multiplier                                
                elsif ( (REGFILE_1_SELECT = '0') and (REGFILE_2_SELECT = '1') and (DATA_MEM_SELECT = '1') and (INSTR_MEM_SELECT = '0') and (MULTIPLIER_SELECT = '1') ) generate 
                    gen_i:  for i in 0 to NUM_CORES_DIM - 1 generate          
                            begin   
                            gen_j:  for j in 0 to NUM_CORES_DIM - 1 generate
                                    begin
                                        -- instantiation core
                                        C: barrel_core_variant_2_mult port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j), 
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));     
                                   end generate gen_j;                                     
                             end generate gen_i;    
                                                      
 -- regFile 1 and 2 distributed mem, instr mem and data mem combi in BRAM, WITH multiplier                                
                elsif ( (REGFILE_1_SELECT = '0') and (REGFILE_2_SELECT = '0') and (DATA_MEM_SELECT = '0') and (INSTR_MEM_SELECT = '1') and (MULTIPLIER_SELECT = '1') ) generate 
                    gen_i:  for i in 0 to NUM_CORES_DIM - 1 generate          
                            begin   
                            gen_j:  for j in 0 to NUM_CORES_DIM - 1 generate
                                    begin
                                        -- instantiation core
                                        C: barrel_core_variant_3_mult port map (
                                                        clk => clk,
                                                        reset => reset,
                                                        i_id => core_id(i,j),
                                                        i_core_dispatch_en => core_dispatch_en(NUM_CORES_DIM*i + j),
                                                        i_core_result_en => core_result_en(NUM_CORES_DIM*i + j),
                                                        i_job_value => job_value(NUM_CORES_DIM*i + j), 
                                                        i_instr => instr(NUM_CORES_DIM*i + j),
                                                        i_data_from_mem => data_from_mem(NUM_CORES_DIM*i + j),
                                                        o_next_instr_addr => instr_addr(NUM_CORES_DIM*i + j),
                                                        o_data_mem_wr_en => data_mem_wr_en(NUM_CORES_DIM*i + j),
                                                        o_data_mem_addr => data_mem_addr(NUM_CORES_DIM*i + j),
                                                        o_data_to_mem => data_to_mem(NUM_CORES_DIM*i + j),
                                                        o_fifo_write => fifo_write(NUM_CORES_DIM*i + j),
                                                        o_data_to_fifo => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        o_job_request => job_request(NUM_CORES_DIM*i + j),
                                                        o_job_done => job_done(NUM_CORES_DIM*i + j),
                                                        o_job_result => result_value(NUM_CORES_DIM*i + j), 
                                                        o_core_done => all_cores_done_reg(NUM_CORES_DIM*i + j));                                                                                                                                                                                                                                                                                            
                                    end generate gen_j;                                     
                            end generate gen_i;    
                end generate if_gen_core; 
               
 -- instantiation of instr mem and data mem
if_gen_instr_data_mem:  if ( (DATA_MEM_SELECT = '1') and (INSTR_MEM_SELECT = '0') ) generate      
                            gen_IM_i:   for i in 0 to NUM_CORES_DIM - 1 generate          
                                        begin   
                                            gen_IM_j:  for j in 0 to NUM_CORES_DIM - 1 generate
                                                        begin                                                                                   
                                                            IM: instr_rom port map(
                                                                    clk => clk, 
                                                                    addr => instr_addr(NUM_CORES_DIM*i + j), -- address output from riscv core                                  
                                                                    data => instr(NUM_CORES_DIM*i + j));    
                                                        end generate gen_IM_j;                                     
                                        end generate gen_IM_i; 
                                
                        --  instr mem and data mem combi              
                        elsif ( (DATA_MEM_SELECT = '0') and (INSTR_MEM_SELECT = '1') ) generate 
                        -- instr and data mem in 1 BRAM  
                            gen_DM_i:   for i in 0 to (NUM_CORES_DIM - 1) generate          
                                        begin   
                                            gen_DM_j:  for j in 0 to (NUM_CORES_DIM - 1) generate
                                                       begin                                                              
                                                            DM: instr_data_mem_combi                                      
                                                                    generic map (   SIZE => 1024,
                                                                                    ADDR_WIDTH => 10,
                                                                                    COL_WIDTH => 8,
                                                                                    NB_COL => 4)
                                                                    port map (  clka => clk,
                                                                                ena => '1',
                                                                                wea => (others => '0'),
                                                                                addra => instr_addr(NUM_CORES_DIM*i + j),
                                                                                dina => (others => '0'),
                                                                                douta => instr(NUM_CORES_DIM*i + j),
                                                                                clkb => clk,
                                                                                enb => '1',
                                                                                web => data_mem_wr_en(NUM_CORES_DIM*i + j),
                                                                                addrb => data_mem_addr(NUM_CORES_DIM*i + j),
                                                                                dinb => data_to_mem(NUM_CORES_DIM*i + j),
                                                                                doutb => data_from_mem(NUM_CORES_DIM*i + j));      
                                                        end generate gen_DM_j;                                     
                                         end generate gen_DM_i;        
                        end generate if_gen_instr_data_mem;
                        
-- generation of FIFOs for each core only when using collect FIFOs
if_gen_FIFO:    if (COLLECT_MODE = '0') generate                     
            gen_FIFO_i: for i in 0 to NUM_CORES_DIM - 1 generate          
                        begin   
                        gen_FIFO_i:  for j in 0 to NUM_CORES_DIM - 1 generate
                                begin                                                                                            
                                    F: fifo generic map (depth => 16, width => 32)
                                            port map (  clk => clk,
                                                        reset => reset,
                                                        din => data_to_fifo(NUM_CORES_DIM*i + j),
                                                        wr_en => fifo_write(NUM_CORES_DIM*i + j),
                                                        rd_en => fifo_read(NUM_CORES_DIM*i + j),
                                                        dout => data_out_of_fifo(NUM_CORES_DIM*i + j),
                                                        full => fifo_full(NUM_CORES_DIM*i + j),
                                                        empty => fifo_empty(NUM_CORES_DIM*i + j));                            
                                end generate gen_FIFO_i;                                     
                        end generate gen_FIFO_i;                                                                                                                                                                                           
                end generate if_gen_FIFO;
                                                                                  
    -- all_cores_done_reg is initially 0, so we first invert them.
    -- when the vector reg is 0, all cores are done 
    --o_all_cores_done <= '1' when all_cores_done_reg = all_ones else '0';     
       
-- dispatch jobs the cores by selecting each core sequentially
-- dispatcher does not collect results, collect is done using fifos, separate process tranfers to mem buffer     
if_job_dispatch:    if (COLLECT_MODE = '0') generate  
                        job_dispatch:   process(clk)
                                        begin
                                            if rising_edge(clk) then
                                                if (reset = '0') then
                                                    job_count <= (others => '0');
                                                    core_index <= (others => '0');
                                                    core_dispatch_en <= (others => '0');  
                                                -- enable dispatch for this core
                                                else
                                                    core_dispatch_en <= (others => '0');
                                                    -- enable dispatch for this core
                                                    if ( (to_integer(job_count )< NUM_JOBS) and (job_request(to_integer(core_index)) = '1') ) then
                                                        core_dispatch_en(to_integer(core_index)) <= '1';  
                                                        job_count <= job_count + 1;                   
                                                        job_value(to_integer(core_index)) <= func_zero_ext(std_logic_vector(job_count), DATA_WIDTH);                                                 
                                                    end if;
                                                                                                
                                                    -- go through each core sequentially
                                                    core_index <= core_index + 1; 
                                                    
                                                end if;                                         
                                            end if;
                                        end process;           
        
        -- dispatcher also collects results and tranfers to mem buffer                        
        elsif (COLLECT_MODE = '1') generate                                                                                                      
            job_dispatch_and_collect:   process(clk)
                                        begin
                                            if rising_edge(clk) then
                                                if (reset = '0') then
                                                    job_count <= (others => '0');
                                                    core_index <= (others => '0');
                                                    core_index_1 <= (others => '0');
                                                    wr_en <= '0';
                                                    results_count <= (others => '0');
                                                    o_all_cores_done <= '0';
                                                else
                                                    core_dispatch_en <= (others => '0');
                                                    core_result_en <= (others => '0');
                                                    
                                                    -- enable dispatch for this core
                                                    if ((to_integer(job_count) < NUM_JOBS) and (job_request(to_integer(core_index)) = '1')) then  
                                                        core_dispatch_en(to_integer(core_index)) <= '1';  
                                                        job_count <= job_count + 1;                   
                                                        job_value(to_integer(core_index)) <= func_zero_ext(std_logic_vector(job_count), DATA_WIDTH);                                                          
                                                    end if;
                                                    
                                                    -- enable collect result for this core
                                                    if (results_count < NUM_JOBS) then
                                                        core_result_en(to_integer(core_index)) <= '1';
                                                        if (job_done(to_integer(core_index_2)) = '1') then
                                                            results_count <= results_count + 1;                                                                                                                                                          
                                                            wr_en <= '1';  
                                                        else
                                                            wr_en <= '0';   
                                                        end if;
                                                    else
                                                        wr_en <= '0';   
                                                    end if;
                                                    
                                                     -- go through each core sequentially  
                                                    core_index <= core_index + 1;      
                                                    core_index_1 <= core_index;
                                                    core_index_2 <= core_index_1;
 
                                                    wr_en_1 <= wr_en;
                                                    wr_en_2 <= wr_en_1;
                                                    
                                                    if (wr_en_2 = '1') then 
                                                        o_data_valid <= '1'; -- indicate data is valid
                                                        o_data_out <= result_value(to_integer(core_index_1));               
                                                    else
                                                        o_data_valid <= '0'; 
                                                    end if;                                                                                                     
                                                                                               
                                                    -- to signal when all cores are done
                                                    if (results_count = NUM_JOBS - 1) then
                                                        o_all_cores_done <= '1';
                                                    end if;
                                                                      
                                                end if;
                                            end if;
                                        end process;                                                             
                                                
                   end generate if_job_dispatch;                           
                           
 -- collect results with FIFOs
 if_gen_collect:    if (COLLECT_MODE = '0') generate       
                    -- semi-recursively instantiate collect-fifos until only one collect-fifo is left
                    -- during each round, the number of fifos is reduced by 4              
                    gen_collect_fifos:  
                        for i in 0 to (NUM_COLLECT_FIFOS - 1) generate                  
                            -- signals for FSM collect FIFO signal
                            type state_type is (fifo0, fifo1, fifo2, fifo3); -- results are collected from 4 FIFOs
                            type state_arr_type is array (0 to NUM_COLLECT_FIFOS - 1) of state_type;
                            signal state: state_arr_type;
                            
                            signal fifo_read_local: std_logic_vector(0 to 3);
                            signal fifo_data_valid_local: std_logic_vector(0 to 3);
                            signal fifo_write_local: std_logic;
                            signal data_to_fifo_local: std_logic_vector(31 downto 0);
                            signal index, index_previous, index_previous_1: integer range 0 to 3; -- for collecting data from FIFOs/collect FIFOs  
                           
                            begin   
                                if_1:   if (i < NUM_COLLECT_FIFOS) generate
                                            fifo_collect: fifo generic map (depth => 32, width => 32)
                                                               port map (   clk => clk,
                                                                            reset => reset,    
                                                                            rd_en => fifo_read(NUM_CORES + i),
                                                                            wr_en => fifo_write(NUM_CORES + i),
                                                                            din => data_to_fifo(NUM_CORES + i),
                                                                            dout => data_out_of_fifo(NUM_CORES + i),
                                                                            empty => fifo_empty(NUM_CORES + i),
                                                                            full => fifo_full(NUM_CORES + i));                                                                                                                                                     
                                        end generate if_1;
                                        
    --                             if_2:   if (i > NUM_CORES - 1) and (i < NUM_CORES + NUM_COLLECT_FIFOS) generate                                 
    --                                            fifo_collect: fifo      port map (  clk => clk_out,
    --                                                                                rd_en => fifo_read(NUM_CORES + i),
    --                                                                                wr_en => fifo_write(NUM_CORES + i),
    --                                                                                din => data_to_fifo(NUM_CORES + i),
    --                                                                                dout => data_out_of_fifo(NUM_CORES + i),
    --                                                                                empty => fifo_empty(NUM_CORES + i),
    --                                                                                full => fifo_full(NUM_CORES + i));                                                                                                                                                     
    --                                    end generate if_2;
                                
    --                            if_3:   if (i = NUM_CORES + NUM_COLLECT_FIFOS - 1) generate                                 
    --                                            fifo_collect: fifo      port map (  clk => clk_out,
    --                                                                                rd_en => fifo_read(NUM_CORES + i),
    --                                                                                wr_en => fifo_write(NUM_CORES + i),
    --                                                                                din => data_to_fifo(NUM_CORES + i),
    --                                                                                dout => data_out_of_fifo(NUM_CORES + i),
    --                                                                                empty => fifo_empty(NUM_CORES + i),
    --                                                                                full => fifo_full(NUM_CORES + i));                                                                                                                                                     
    --                                    end generate if_3;
                                
                                  collect_wr_proc:  process (clk)
                                                    variable ptr: integer range 0 to (NUM_CORES + NUM_COLLECT_FIFOS - 1) := 0;
                                                    --attribute keep of ptr: variable is "true";
                                                    begin                                              
                                                        if rising_edge(clk) then
                                                            ptr := to_integer(unsigned(std_logic_vector(to_unsigned(i, NUM_CORES_COLLECT_BIT_WIDTH)) and MASK_COLLECT_FIFO));
                                                            ptr := ptr*4;
                                                            
                                                            if (reset = '0') then
                                                                index <= 0;
                                                                index_previous <= 0;
                                                                index_previous_1 <= 0;
                                                                fifo_read_local <= (others => '0');
                                                                state(i) <= fifo0;
                                                                fifo_read_local <= "0000"; 
                                                            else                                                        
                                                                index_previous <= index; 
                                                                index_previous_1 <= index_previous;                                          

                                                                case (state(i)) is
                                                                    when fifo0 =>	
                                                                        if (fifo_empty(ptr) = '0') then
                                                                            index <= 1;
                                                                            state(i) <= fifo1;
                                                                            fifo_read_local(0) <= '1';
                                                                        elsif (fifo_empty(ptr + 1) = '0') then
                                                                            index <= 1;
                                                                            state(i) <= fifo1;
                                                                        elsif (fifo_empty(ptr + 1) = '1') and (fifo_empty(ptr + 2) = '0') then
                                                                            index <= 2;
                                                                            state(i) <= fifo2;
                                                                        elsif (fifo_empty(ptr + 1) = '1') and (fifo_empty(ptr + 2) = '1') and (fifo_empty(ptr + 3) = '0') then
                                                                            index <= 3;
                                                                            state(i) <= fifo3;
                                                                        end if;                                                                          
                                                                                                              
                                                                    when fifo1 =>	
                                                                        if (fifo_empty(ptr + 1) = '0') then
                                                                            index <= 2;
                                                                            state(i) <= fifo2;
                                                                            fifo_read_local(1) <= '1';
                                                                        elsif (fifo_empty(ptr + 2) = '0') then
                                                                            index <= 2;
                                                                            state(i) <= fifo2;
                                                                        elsif (fifo_empty(ptr + 2) = '1') and (fifo_empty(ptr + 3) = '0') then
                                                                            index <= 3;
                                                                            state(i) <= fifo3;
                                                                        elsif (fifo_empty(ptr + 2) = '1') and (fifo_empty(ptr + 3) = '1') and (fifo_empty(ptr) = '0') then
                                                                            index <= 0;
                                                                            state(i) <= fifo0;
                                                                        end if;                                                                         
                                                         
                                                                    when fifo2 =>	
                                                                        if (fifo_empty(ptr + 2) = '0') then 
                                                                            index <= 3;
                                                                            state(i) <= fifo3;
                                                                            fifo_read_local(2) <= '1';
                                                                        elsif (fifo_empty(ptr + 3) = '0') then
                                                                            index <= 3;
                                                                            state(i) <= fifo3;
                                                                        elsif (fifo_empty(ptr + 3) = '1') and (fifo_empty(ptr) = '0') then
                                                                            index <= 0;
                                                                            state(i) <= fifo0;
                                                                        elsif (fifo_empty(ptr + 3) = '1') and (fifo_empty(ptr) = '1') and (fifo_empty(ptr + 1) = '0') then
                                                                            index <= 1;
                                                                            state(i) <= fifo1;
                                                                        end if;                                                                         
                                                      
                                                                    when fifo3 =>	
                                                                        if (fifo_empty(ptr + 3) = '0') then
                                                                            index <= 0;
                                                                            state(i) <= fifo0;
                                                                            fifo_read_local(3) <= '1';                                                                      
                                                                        elsif (fifo_empty(ptr) = '0') then
                                                                            index <= 0;
                                                                            state(i) <= fifo0;
                                                                        elsif (fifo_empty(ptr) = '1') and (fifo_empty(ptr + 1) = '0') then
                                                                            index <= 1;
                                                                            state(i) <= fifo1;
                                                                        elsif (fifo_empty(ptr) = '1') and (fifo_empty(ptr + 1) = '1') and (fifo_empty(ptr + 2) = '0') then
                                                                            index <= 2;
                                                                            state(i) <= fifo2;
                                                                        end if;
                                                            
                                                                    when others =>	
                                                                        index <= 0;
                                                                        state(i) <= fifo0;
                                                                end case;                                                                                                   
                                                                                                                        
                                                                if (fifo_read_local(index_previous) = '1') then
                                                                    fifo_data_valid_local(index_previous) <= '1';
                                                                    fifo_read_local(index_previous) <= '0'; 
                                                                else
                                                                    fifo_data_valid_local(index_previous) <= '0'; 
                                                                end if;                                                                                        
                                                               
                                                                if (fifo_data_valid_local(index_previous_1) = '1') and (fifo_full(i) = '0')  then               
                                                                    fifo_write_local <= '1';
                                                                    data_to_fifo_local <= data_out_of_fifo(index_previous_1 + ptr);
                                                                    fifo_data_valid_local(index_previous_1) <= '0';    
                                                                else
                                                                    fifo_write_local <= '0';
                                                                end if;                                                                                                      
                                                          end if;
                                                        end if;        
                                                    end process;                                                                                                                                
                    
                            fifo_read(i*4 to (i*4 + 3)) <= fifo_read_local;
                            fifo_write(NUM_CORES + i) <= fifo_write_local;
                            data_to_fifo(NUM_CORES + i) <= data_to_fifo_local;     
                                                                         
        end generate gen_collect_fifos;  
    end generate if_gen_collect;
   
  -- transfer from collect FIFO to memory output      
 if_gen_collect_transfer: 
        if (COLLECT_MODE = '0') generate     
            transmit_to_mem_output: process (clk)
                                    begin
                                        if rising_edge(clk) then
                                           if (reset = '0') then
                                                fifo_read_local_final <= '0';
                                                fifo_read_local_final_1 <= '0';
                                                results_count <= (others =>'0');
                                                o_all_cores_done <= '0';
                                           else 
                                                if (fifo_empty(NUM_CORES + NUM_COLLECT_FIFOS - 1) = '0') then
                                                    fifo_read_local_final <= '1';
                                                    -- read from last collect fifo, data arrives one cycle later
                                                    fifo_read(NUM_CORES + NUM_COLLECT_FIFOS - 1) <= '1';                                          
                                                else
                                                    fifo_read_local_final <= '0';
                                                    fifo_read(NUM_CORES + NUM_COLLECT_FIFOS - 1) <= '0';    
                                                end if;
                                                                                 
                                                fifo_read_local_final_1 <= fifo_read_local_final; 
                                        
                                                if (fifo_read_local_final_1 = '1') and (fifo_read_local_final /= '0') then
                                                    o_data_valid <= '1'; -- indicate data is valid
                                                    o_data_out <= data_out_of_fifo(NUM_CORES + NUM_COLLECT_FIFOS - 1);  
                                                     -- for dynamic distribution, we need a way of finding out when the output is ready to be transmitted e.g. by UART 
                                                    results_count <= results_count + 1; -- increment the number of elements being written so that we know when we are done
                                                    if (results_count = NUM_JOBS - 2) then
                                                        o_all_cores_done <= '1';
                                                    end if;
                                                else
                                                    o_data_valid <= '0';  
                                                end if;     
                                                                                                             
                                           end if; 
                                        end if;
                                    end process;
      end generate if_gen_collect_transfer;
                                   
end many_core_system_arch;
