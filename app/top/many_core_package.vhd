use WORK.RISCV_package.ALL;

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

package many_core_package is
    -- CONSTANTS 
--    constant NUM_CORES : positive := 4; -- number of cores
--    constant NUM_CORES_DIM : positive := 2; -- number of cores
--    constant NUM_COLLECT_FIFOS : positive := 1; -- number of extra fifos required to collect results from each group of 4 fifos recursively
--    constant NUM_CORES_COLLECT_BIT_WIDTH : positive := 3; -- number of cores bis size  
    constant NUM_CORES : positive := 16; -- number of cores
    constant NUM_CORES_DIM : positive := 4; -- number of cores
    constant NUM_COLLECT_FIFOS : positive := 5; -- number of extra fifos required to collect results from each group of 4 fifos recursively
    constant NUM_CORES_COLLECT_BIT_WIDTH : positive := 5; -- number of cores bis size  
--    constant NUM_CORES : positive := 64; -- number of cores
--    constant NUM_CORES_DIM : positive := 8; -- number of cores
--    constant NUM_COLLECT_FIFOS : positive := 21; -- number of extra fifos required to collect results from each group of 4 fifos recursively
--    constant NUM_CORES_COLLECT_BIT_WIDTH : positive := 7; -- number of cores bis size  
--    constant NUM_CORES : positive := 256; -- number of cores
--    constant NUM_CORES_DIM : positive := 16; -- number of cores
--    constant NUM_COLLECT_FIFOS : positive := 85; -- number of extra fifos required to collect results from each group of 4 fifos recursively
--    constant NUM_CORES_COLLECT_BIT_WIDTH : positive := 9; -- number of cores bis size  

    constant NUM_JOBS : positive := 16384; -- number of jobs
 
    -- constant for checking if all cores are done, they are done when all elements of the vector are 1
    constant all_ones : std_logic_vector(NUM_CORES - 1 downto 0) := (others => '1');
    
    -- constant for finding the 4 fifos from which a give collect fifos gets its data (4 cores)
--    constant MASK_COLLECT_FIFO : std_logic_vector(NUM_CORES_COLLECT_BIT_WIDTH - 1 downto 0) := "001";     
    -- constant for finding the 4 fifos from which a give collect fifos gets its data (16 cores)
    constant MASK_COLLECT_FIFO : std_logic_vector(NUM_CORES_COLLECT_BIT_WIDTH - 1 downto 0) := "00111"; 
    -- constant for finding the 4 fifos from which a give collect fifos gets its data (64 cores)
--    constant MASK_COLLECT_FIFO : std_logic_vector(NUM_CORES_COLLECT_BIT_WIDTH - 1 downto 0) := "0011111";
    -- constant for finding the 4 fifos from which a give collect fifos gets its data (256 cores)
--    constant MASK_COLLECT_FIFO : std_logic_vector(NUM_CORES_COLLECT_BIT_WIDTH - 1 downto 0) := "001111111";
   
    -- OPTIONS for conditional generate of core variants   
    -- implementation of regFile 1 either in BRAM or in LUTRAM
    -- when only 1 regFile should be in LUTRAM, then it has to regFile 1
    constant REGFILE_1_SELECT : std_logic := '1'; -- '1' for BRAM, '0' for LUTRAM
    -- implementation of regFile 2 either in BRAM or in LUTRAM
    constant REGFILE_2_SELECT : std_logic := '1'; -- '1' for BRAM, '0' for LUTRAM
    -- implementation of data memory either in stand-alone BRAM or in the BRAM in which regFile 1 is located 
    constant DATA_MEM_SELECT : std_logic := '1'; -- '1' for BRAM, '0' with instr mem 
    -- implementation of instr memory either in BRAM together with data memory or in LUTRAM
    constant INSTR_MEM_SELECT : std_logic := '0'; -- '1' for BRAM , '0' for LUTRAM
    -- availability of multiplier 
    constant MULTIPLIER_SELECT : std_logic := '1'; -- '1' for multiplier, '0' for no multiplier
    -- collect the data either with FIFOs or for polling
    constant COLLECT_MODE : std_logic := '0'; -- '0' for collect FIFOS, '1' for polling
   -- barrel_core_variant_1: = REGFILE_1_SELECT = 1, REGFILE_2_SELECT = 1 , DATA_MEM_SELECT = 1, INSTR_MEM_SELECT = 0 
   -- barrel_core_variant_2: = REGFILE_1_SELECT = 0, REGFILE_2_SELECT = 1 , DATA_MEM_SELECT = 1, INSTR_MEM_SELECT = 0 
   -- barrel_core_variant_3: = REGFILE_1_SELECT = 0, REGFILE_2_SELECT = 0 , DATA_MEM_SELECT = 0, INSTR_MEM_SELECT = 1 
   
   -- barrel_core_system_variant_1 uses either barrel_core_variant_1 or barrel_core_variant_2 
   --   when either both regFile(s) are in BRAM /or/ regFile2 is in BRAM and regFile 1 is in LUTRAM, data mem is in lower half of BRAM
   -- barrel_core_system_variant_2 uses either barrel_core_variant_3 
   --   when both of regFiles are in LUTRAM, instr mem and data mem are in 1 BRAM
   
end many_core_package;