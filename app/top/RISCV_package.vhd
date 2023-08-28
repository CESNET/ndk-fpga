-----------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

package RISCV_package is
    -- Constants for width parameters and register counts
    constant DATA_WIDTH : positive := 32; -- data size
    constant INSTR_WIDTH : positive := 32; -- instr size
    constant INT_REG_COUNT : positive := 32; -- number of integer registers
    --constant FLOAT_REG_COUNT : positive := 32; -- number of floating-point registers
    constant INT_REGFILE_ADDR: positive := 5; -- number of bits for addressing integer registers
    --constant FLOAT_REGFILE_ADDR: positive := 5; -- number of bits for addressing floating-point registers
    
    -- instr and data memory can be smaller than 2**32 bits - byte addressable
    constant INSTR_MEM_ADDR_WIDTH: positive := 10; -- fits 64 32-bit instructions 
    constant DATA_MEM_ADDR_WIDTH: positive := 10; -- size of data memory = 512 words
    
    subtype DATA_TYPE is std_logic_vector(DATA_WIDTH - 1 downto 0);
    subtype INSTR_TYPE is std_logic_vector(INSTR_WIDTH - 1 downto 0);
    
    type INT_REG_FILE_TYPE is array(0 to INT_REG_COUNT - 1) of DATA_TYPE; -- integer register file
    type PROGRAM_SEQUENCE is array (integer range <>) of std_logic_vector(7 downto 0); -- instr mem for program   
    
    -- for sequential processor
    -- all instructions are equally long - needed for the non-pipelined barrel processor later
    -- one instruction is available every two clock cycles
    -- the load instruction takes 3 clock cycles, the loaded value is written to register in the third clock cycle
    constant NUM_SUBCYCLES: positive := 2; -- number of cycles for all instructions - determined by longest instr
    
    -- for barrel processor
    constant NUM_THREADS: positive := 8; -- number of threads - should be at least equal to num of pipeline stages to avoid stalls
    -- all threads share the data memory, but each thread will load data relative to a base pointer, up to a block size of 1024 byte addresses
    constant THREAD_DATA_MEM_BLOCKSIZE: positive := 64; -- size of memory for each thread bytes, 16 words
    -- barrel register file shift amount; instead of multiplying by 32, we shift by 5 to the left to get the right register for a given thread
    constant BARREL_REG_FILE_SHIFT_AMOUNT: positive := 5; -- 32 * 4 = 2^7 since one register is 4 bytes wide
    -- barrel thread data memory block size shift amount; instead of mult
    constant BARREL_DATA_MEM_BLOCK_SHIFT_AMOUNT: positive := 6;
 
    -- the size of the register file is multiplied by a factor of NUM_THREADS, each thread has its own set of registers
    type INT_REG_FILE_ARRAY_TYPE is array (0 to (INT_REG_COUNT * NUM_THREADS) - 1) of DATA_TYPE;
    -- each thread has its own PC
    type PC_ARRAY is array (0 to (NUM_THREADS - 1)) of std_logic_vector((INSTR_MEM_ADDR_WIDTH - 1) downto 0);

 -- memory mapped addr for FIFO
    constant FIFO_addr: std_logic_vector := x"0000FFFF";
    -- memory mapped addr for load thread ID: second last word of data memory
    constant thread_id_addr: std_logic_vector := x"0000FFFC";
    -- memory mapped addr for job request
    constant job_request_addr: std_logic_vector := x"0000FFF8";
    -- memory mapped addr for job parameter
    constant job_value_addr: std_logic_vector := x"0000FFF0";
    -- memory mapped addr for core ID
    constant core_id_addr: std_logic_vector := x"0000FFEC";
    -- memory mapped addr for core ID
    constant thread_per_core_done_addr: std_logic_vector := x"0000FFE8";
    -- memory mapped addr for result value
    constant job_done_addr: std_logic_vector := x"0000FFE4";
    -- memory mapped addr for result value                      
    constant job_result_addr: std_logic_vector := x"0000FFE0";
    
    -- Function prototypes for zero and sign extension
    function func_zero_ext(I: std_logic_vector; L: natural) return std_logic_vector;
    function func_sign_ext(I: std_logic_vector; L: natural) return std_logic_vector;

end RISCV_package;
 
package body RISCV_package is

-- Zero extension input to L bits (L must be larger than I'length):
function func_zero_ext (I : std_logic_vector; L : natural)return std_logic_vector is 
    variable var_result: std_logic_vector(L-1 downto 0);
    begin
        var_result(I'length - 1 downto 0) := I;
        for index in L-1 downto I'length loop
            var_result(index) := '0';
        end loop;
        return var_result;
    end func_zero_ext;

-- Sign extension input to L bits (L must be larger than I'length):
function func_sign_ext (I : std_logic_vector; L : natural) return std_logic_vector is 
    variable var_result: std_logic_vector(L-1 downto 0);
    begin
        var_result(I'length-1 downto 0) := I;
        for index in L-1 downto I'length loop
            var_result(index) := I(I'length - 1);
        end loop;
        return var_result;
    end func_sign_ext;  
    
end RISCV_package;