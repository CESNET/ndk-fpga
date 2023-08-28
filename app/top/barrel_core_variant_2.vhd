-- barrel core variant 2
-- regFile 1 is in distributed memory and regFile 2 are in BRAM 
-- data mem is also implemented in the lower half of regFile 2 BRAM (no external data mem)
-- NO multiplier

use WORK.RISCV_package.ALL;
use WORK.many_core_package.ALL;

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity barrel_core_variant_2 is
    port(   clk, reset: in std_logic;
            i_id: in std_logic_vector(NUM_CORES_BIT_WIDTH - 1 downto 0);
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
end barrel_core_variant_2;

architecture barrel_core_variant_2_arch of barrel_core_variant_2 is

-- BRAM regFile and data mem in one BRAM
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
            doutb: out std_logic_vector(NB_COL*COL_WIDTH - 1 downto 0));
end component;
                  
--cycle count used for stall due until first instr comes from instr mem
signal cycle_counter: natural := 0; 

-- signals for barrel logic, instruction fetch, program counter
signal current_thread_id, next_thread_id, thread_id_pipe_0, thread_id_pipe_1, thread_id_pipe_2: integer range 0 to 7;
signal thread_id_pipe_3, thread_id_pipe_4, thread_id_pipe_5, thread_id_pipe_6: integer range 0 to 7;
signal pc_pipe_0, pc_pipe_1, pc_pipe_2: std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
signal barrel_pc: PC_ARRAY;

-- next pc before jump instruction must be saved and written to register file one cycle later
signal next_instr_addr, next_pc, next_pc_before_jump_pipe_0, next_pc_before_jump_pipe_1: std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
signal next_pc_before_jump_pipe_2, next_pc_before_jump_pipe_3, next_pc_before_jump_pipe_4: std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
signal next_pc_before_jump_pipe_5, next_pc_before_jump_pipe_6: std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);

signal pc_sel_jmp, pc_sel_pipe_1, pc_sel_pipe_2, pc_sel_pipe_3, pc_sel_pipe_4: std_logic;
signal pc_sel_br, pc_sel_br_pipe_3, pc_sel_br_pipe_4: std_logic;

-- register file array - register file has a set of registers for each thread
signal barrel_regFile_array: INT_REG_FILE_ARRAY_TYPE := (others => (others => '0')); 
signal reg1, reg2, reg1_pipe_2, reg2_pipe_2: DATA_TYPE;
signal src1_addr, src2_addr, dest_addr: std_logic_vector(INT_REGFILE_ADDR - 1 downto 0); 
signal reg_wr_back_data: DATA_TYPE;

-- immediate generator
signal imm_val_12: std_logic_vector(11 downto 0); -- 12 bit immediate value for ADDI, ANDI, ..
signal imm_val_12_store: std_logic_vector(11 downto 0); -- 12 bit immediate value for store
signal imm_val_13_branch: std_logic_vector(12 downto 0); -- 13 bit immediate value for branch, LSB 0
signal imm_val_21_jump: std_logic_vector(20 downto 0); -- 21 bit immediate value for jump             

-- select signal for immediate values, required until the write back stage for store in data mem in BRAM
signal imm_val, imm_val_pipe_1, imm_val_pipe_2, imm_val_pipe_3, imm_val_pipe_4, imm_val_pipe_5, imm_val_pipe_6: DATA_TYPE;

-- signals for branch logic
-- if comparison for branch is unsigned, equal and less than comparison
signal br_unsigned, br_unsigned_pipe_1, br_unsigned_pipe_2, br_eq, br_lt: std_logic;

-- signals for ALU
signal alu_operand_1, alu_operand_2, alu_operand_1_pipe_3, alu_operand_2_pipe_3: DATA_TYPE;

signal alu_opcode, alu_opcode_pipe_1, alu_opcode_pipe_2, alu_opcode_pipe_3, alu_opcode_pipe_4: std_logic_vector(3 downto 0);

signal alu_operand_1_sel, alu_operand_2_sel: std_logic; 
signal alu_operand_1_sel_pipe_1, alu_operand_1_sel_pipe_2: std_logic;
signal alu_operand_2_sel_pipe_1, alu_operand_2_sel_pipe_2: std_logic;

-- the alu result has to wait one extra cycle to be written back to register
signal alu_result, alu_result_final, alu_result_pipe_4, alu_result_pipe_5, alu_result_pipe_6: DATA_TYPE;
signal alu_result_add, alu_result_1, alu_result_2, alu_result_1_pipe_4, alu_result_2_pipe_4, alu_result_add_pipe_4: DATA_TYPE;
signal alu_result_1_tmp, alu_result_1_tmp_1, alu_result_1_tmp_2, alu_result_1_tmp_3, alu_result_1_tmp_4, alu_result_1_tmp_5: DATA_TYPE;
signal alu_result_2_tmp, alu_result_2_tmp_1, alu_result_2_tmp_2, alu_result_2_tmp_3, alu_result_2_tmp_4: DATA_TYPE;
signal alu_group, alu_group_pipe_3, alu_group_pipe_4: std_logic; 

-- register value to be stored
signal reg_value_to_store_pipe_3, reg_value_to_store_pipe_4, reg_value_to_store_pipe_5, reg_value_to_store_pipe_6: DATA_TYPE;

-- signals for memory 
-- enable data memory write, individual bytes can be written in BRAM  
signal data_from_mem_BRAM_2, data_from_mem_BRAM_pipe_3, data_from_mem_BRAM_pipe_4, data_from_mem_BRAM_pipe_5, data_from_mem_BRAM_pipe_6: DATA_TYPE;

-- signals for FIFO
signal fifo_write, fifo_write_pipe_5, fifo_write_pipe_6: std_logic; 
signal data_to_fifo, data_to_fifo_pipe_5, data_to_fifo_pipe_6: DATA_TYPE; 

-- signals for write-back to register file
-- select between ALU result, memory output or PC+4 to write to register  
signal reg_wb_sel, reg_wb_sel_tmp, reg_wb_sel_pipe_1, reg_wb_sel_pipe_2, reg_wb_sel_pipe_3: std_logic_vector(2 downto 0); 
signal reg_wb_sel_pipe_4, reg_wb_sel_pipe_5, reg_wb_sel_pipe_6: std_logic_vector(2 downto 0); 
-- enable register write
signal reg_wr_en, reg_wr_en_pipe_1, reg_wr_en_pipe_2, reg_wr_en_pipe_3, reg_wr_en_pipe_4, reg_wr_en_pipe_5, reg_wr_en_pipe_6: std_logic_vector(3 downto 0);
signal reg_wr_en_BRAM: std_logic_vector(3 downto 0);

-- destination register 
signal dest_addr_pipe_1, dest_addr_pipe_2, dest_addr_pipe_3: std_logic_vector(INT_REGFILE_ADDR - 1 downto 0);
signal dest_addr_pipe_4, dest_addr_pipe_5, dest_addr_pipe_6: std_logic_vector(INT_REGFILE_ADDR - 1 downto 0);

-- signals for optimization of decoder
signal instr_opcode: std_logic_vector(4 downto 0);
signal func_opcode, func_opcode_pipe_1, func_opcode_pipe_2: std_logic_vector(2 downto 0);
signal is_branch_instr, is_branch_instr_pipe_1, is_branch_instr_pipe_2: std_logic;
signal is_load_instr, is_load_instr_pipe_1, is_load_instr_pipe_2, is_load_instr_pipe_3, is_load_instr_pipe_4: std_logic;
signal is_store_instr, is_store_instr_pipe_1, is_store_instr_pipe_2, is_store_instr_pipe_3, is_store_instr_pipe_4: std_logic;
signal is_add_op, is_add_op_pipe_3, is_add_op_pipe_4: std_logic;

-- signals for memory implemented in BRAM
signal is_load_1_instr, is_load_1_instr_pipe_1, is_load_1_instr_pipe_2, is_load_1_instr_pipe_3: std_logic;
signal is_load_1_instr_pipe_4, is_load_1_instr_pipe_5, is_load_1_instr_pipe_6: std_logic;
signal is_store_1_instr, is_store_1_instr_pipe_1,is_store_1_instr_pipe_2, is_store_1_instr_pipe_3: std_logic;
signal is_store_1_instr_pipe_4, is_store_1_instr_pipe_5, is_store_1_instr_pipe_6: std_logic;
signal is_mem_mapped_store_instr, is_mem_mapped_store_instr_pipe_5, is_mem_mapped_store_instr_pipe_6: std_logic;

-- signals for BRAM port addresses
signal rd_addr_BRAM, wr_addr_BRAM: std_logic_vector(DATA_MEM_ADDR_WIDTH - 1 downto 0);

-- distinguish write-back data in BRAM in the WB stage between normal mem or loaded from BRAM in the decoder stage
signal data_load_from_mem_BRAM: DATA_TYPE;
-- data written in the WB stage can be to the regFile or to the BRAM mem 
signal data_wb: DATA_TYPE; 

-- signals for load from memory mapped addresses
signal loaded_mem_mapped_data, loaded_mem_mapped_data_pipe_5, loaded_mem_mapped_data_pipe_6: DATA_TYPE;

-- registers for receiving jobs and sending results
type thread_ID_queue_type is array ((NUM_THREADS - 1) downto 0) of integer range 0 to 7; 
type data_reg_type is array ((NUM_THREADS - 1) downto 0) of DATA_TYPE; 
signal job_request_queue, job_done_queue: thread_ID_queue_type;
signal job_value_reg, job_result_reg: data_reg_type;
signal job_request_reg, job_done_reg: std_logic_vector(NUM_THREADS - 1 downto 0);
signal thread_ptr_new_request, thread_ptr_to_allocate, thread_ptr_new_result, thread_ptr_result_sent: integer range 0 to 7;
signal num_incoming_requests, num_requests_allocated, num_pending_requests, num_incoming_results, num_results_sent, num_pending_results: integer range 0 to NUM_JOBS;

-- signal when all threads are done, the core is done
signal threads_per_core_done_reg: std_logic_vector(NUM_THREADS - 1 downto 0) := (others => '1');

attribute keep : string;
attribute keep of i_instr, cycle_counter, thread_ptr_new_request, thread_ptr_to_allocate, thread_ptr_new_result, thread_ptr_result_sent: signal is "true";
attribute keep of next_instr_addr: signal is "true";
attribute keep of imm_val, imm_val_12, imm_val_pipe_1, imm_val_pipe_2, imm_val_pipe_3,imm_val_pipe_4, imm_val_pipe_5, imm_val_pipe_6 : signal is "true";
attribute keep of current_thread_id, thread_id_pipe_0: signal is "true";
attribute keep of thread_id_pipe_1, thread_id_pipe_2, thread_id_pipe_3, thread_id_pipe_4, thread_id_pipe_5, thread_id_pipe_6: signal is "true";
attribute keep of next_thread_id : signal is "true";
attribute keep of next_pc : signal is "true";
attribute keep of pc_pipe_0 : signal is "true";
attribute keep of src1_addr : signal is "true";
attribute keep of src2_addr : signal is "true";
attribute keep of dest_addr, dest_addr_pipe_1,  dest_addr_pipe_2, dest_addr_pipe_3, dest_addr_pipe_4, dest_addr_pipe_5, dest_addr_pipe_6: signal is "true";
attribute keep of reg_wr_back_data : signal is "true";
attribute keep of next_pc_before_jump_pipe_0 : signal is "true";
attribute keep of reg1 : signal is "true";
attribute keep of reg2 : signal is "true";
attribute keep of alu_operand_1, alu_operand_1_pipe_3, alu_operand_2_pipe_3  : signal is "true";
attribute keep of alu_operand_2 : signal is "true";
attribute keep of alu_opcode : signal is "true";
attribute keep of alu_result, alu_result_final, alu_result_1, alu_result_2, alu_result_pipe_4, alu_result_pipe_5, alu_result_add, alu_result_add_pipe_4 : signal is "true";
attribute keep of alu_operand_1_sel : signal is "true";
attribute keep of alu_operand_2_sel : signal is "true";
attribute keep of reg_wb_sel, reg_wb_sel_pipe_3, reg_wb_sel_pipe_4, reg_wb_sel_pipe_5, reg_wb_sel_tmp : signal is "true";
attribute keep of reg_wr_en, reg_wr_en_BRAM, reg_wr_en_pipe_6: signal is "true";
attribute keep of pc_sel_jmp : signal is "true";
attribute keep of pc_sel_br, pc_sel_br_pipe_3, pc_sel_br_pipe_4 : signal is "true";
attribute keep of func_opcode : signal is "true";
attribute keep of br_unsigned : signal is "true";
attribute keep of br_eq : signal is "true";
attribute keep of br_lt : signal is "true";
attribute keep of is_load_instr, is_store_instr : signal is "true";
attribute keep of is_add_op, is_add_op_pipe_3, is_add_op_pipe_4, alu_group,  alu_group_pipe_3: signal is "true";
attribute keep of alu_result_1_tmp_1, alu_result_1_tmp_2, alu_result_1_tmp_3, alu_result_1_tmp_4,  alu_result_1_tmp_5: signal is "true";
attribute keep of reg_value_to_store_pipe_3, reg_value_to_store_pipe_4, reg_value_to_store_pipe_5, reg_value_to_store_pipe_6: signal is "true";
attribute keep of rd_addr_BRAM, wr_addr_BRAM: signal is "true";
attribute keep of is_load_1_instr, is_load_1_instr_pipe_1, is_load_1_instr_pipe_2: signal is "true";
attribute keep of is_store_1_instr, is_store_1_instr_pipe_1, is_store_1_instr_pipe_2, is_store_1_instr_pipe_3: signal is "true";
attribute keep of is_store_1_instr_pipe_4, is_store_1_instr_pipe_5, is_store_1_instr_pipe_6: signal is "true";
attribute keep of is_mem_mapped_store_instr, is_mem_mapped_store_instr_pipe_5, is_mem_mapped_store_instr_pipe_6: signal is "true";
attribute keep of data_from_mem_BRAM_pipe_3, data_from_mem_BRAM_pipe_4, data_from_mem_BRAM_pipe_5, data_from_mem_BRAM_pipe_6: signal is "true";
attribute keep of data_wb: signal is "true";
attribute keep of threads_per_core_done_reg, data_to_fifo, data_to_fifo_pipe_5, data_to_fifo_pipe_6, fifo_write, fifo_write_pipe_5, fifo_write_pipe_6: signal is "true";

begin  
    -- cycle count to allow for first instr fetch latency and possibly for measurement purposes
    cycle_count: process (clk)
    begin 
        if rising_edge(clk) then -- rising edge
            if (reset = '0') then     
                cycle_counter <= 0;             
            else
                cycle_counter <= cycle_counter + 1;
            end if;
        end if;
    end process;                               
                        
    -- keep track of current thread ID
    barrel_proc:    process(clk)
                    begin 
                        if rising_edge(clk) then -- rising edge
                            if (reset = '0') then   
                                current_thread_id <= 0; -- start with thread 0
                                thread_id_pipe_0 <= 0;
                            -- cycle_counter > 0 because instr mem has a latency of 1 cycle
                            -- otherwise thread ID will be incremented but the instr is not yet available
                            elsif (cycle_counter > 0) then
                                current_thread_id <= current_thread_id + 1; -- move to the next thread - wraps around
                                -- to be passed to the next stage, while the current stage fetches the next instr 
                                thread_id_pipe_0 <= current_thread_id; 
                            end if;
                        end if;
                    end process;           
     
    -- compute the next PC within each thread, this value is not sent to mem to overcome latency
    -- but instead saved as the next pc for the current thread because the next thread will now run
    next_pc <= std_logic_vector(unsigned(barrel_pc(current_thread_id)) + 4) when (cycle_counter > 0) else (others => '0'); 
                                      
    -- prepare for fetching the next instr 
    next_thread_id <= current_thread_id + 1;    
    o_next_instr_addr <= next_instr_addr;
    
    -- Instr Fetch - Stage 0   
    -- update program counter - all instructions are equally long
    pc_update: process (clk)
    begin 
        if rising_edge(clk) then -- rising edge
            if (reset = '0') then  -- reset active low 
                for index in 0 to NUM_THREADS - 1 loop
                    barrel_pc(index) <= (others => '0'); -- the others are 0 because they will be sent to memory early enough             
                end loop;
            else
                pc_pipe_0 <= barrel_pc(current_thread_id);
                barrel_pc(current_thread_id) <= next_pc;
                next_instr_addr <= barrel_pc(next_thread_id);
                -- address of the next instr BEFORE the jump is taken - passed down the pipeline
                next_pc_before_jump_pipe_0 <= std_logic_vector(unsigned(barrel_pc(current_thread_id)) + 4);
            end if;
            -- update the barrel pc for that thread ID
            -- the alu result is the target address for a branch or a jump coming from EX-Stage
            if ((pc_sel_pipe_4 = '1') or (pc_sel_br_pipe_4 = '1')) then
                barrel_pc(thread_id_pipe_4) <= alu_result_add_pipe_4(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
            end if;            
        end if;
    end process;
     
    -- Decode First Stage - Stage 1  	
    instr_opcode <= i_instr(6 downto 2);    
    func_opcode <= i_instr(14 downto 12);   
                                                          
    decode_proc:    process (all) 
                    begin                   
                        -- defaults to prevent inferred latches
                        src1_addr <= i_instr(19 downto 15); -- reg number for src1      
                        src2_addr <= i_instr(24 downto 20); -- reg number for scr2
                        dest_addr <= i_instr(11 downto 7); -- reg number for dest  
                        alu_operand_1_sel <= '0'; -- reg instead of PC
                        alu_operand_2_sel <= '0'; -- reg instead of immediate value
                        alu_opcode <= "0000"; -- ALU opcode add 
                        reg_wr_en <= "0000"; -- enable dest reg to be written 
                        reg_wb_sel <= "000"; -- select ALU result 
                        pc_sel_jmp <= '0';  -- normal increment  
                        imm_val <= (others => '0');
                        is_branch_instr <= '0';
                        br_unsigned <= '0';
                        is_load_instr <= '0';
                        is_store_instr <= '0';
                        is_load_1_instr <= '0';
                        is_store_1_instr <= '0';

                        case instr_opcode is
                            -- ALU Reg R-type and ALU Immediate I-type 
                            -- instr_opcode "01100", "00100"
                            when "01100" | "00100"=>                       
                                reg_wr_en <= "1111"; -- enable dest reg to be written 
                                case (instr_opcode(3)) is
                                    when '0' =>  -- I-type
                                        alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                        imm_val <= func_sign_ext(imm_val_12, 32);          
                                    when others => 
                                        alu_operand_2_sel <= '0'; 
                                        imm_val <= (others => '0');                                       
                                 end case;
           
                                 case func_opcode is -- func field
                                    when "000" => -- add/sub 
                                        if (instr_opcode(3) = '1') then -- only for R-type            
                                            if (i_instr(30) = '1') then    -- distinguish between add and sub                       
                                                alu_opcode <= "1000"; -- ALU opcode sub, I-type has no sub
                                            end if;                                                                              
                                        end if;
                                    when "001" => -- left shift logical sll
                                       alu_opcode <= "0001"; -- ALU opcode sll
                                    when "010" => -- less than comparison slt
                                       alu_opcode <= "0010"; -- ALU opcode slt 
                                    when "011" => -- less than comparison unsigned sltu
                                       alu_opcode <= "0011"; -- ALU opcode sltu 
                                    when "100" => -- xor
                                       alu_opcode <= "0100"; -- ALU opcode xor
                                    when "101" => -- right shift logical/arithmetic (srl/sra)
                                        if (i_instr(30) = '0') then                           
                                            alu_opcode <= "0101"; -- ALU opcode srl
                                        else
                                            alu_opcode <= "1101"; -- ALU opcode sra;
                                         end if;   
                                    when "110" => -- or
                                       alu_opcode <= "0110"; -- ALU opcode or
                                    when "111" => -- and
                                       alu_opcode <= "0111"; -- ALU opcode and                     
                                end case;                        
                            
                            -- Load I-type, load for BRAM instead of mem
                            -- load from mem in BRAM and store in regFile in BRAM
                            when "00000" => 
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= func_sign_ext(imm_val_12, 32);  
                                is_load_instr <= '1';                            
                                -- enable register write to write loaded value to reg 
								reg_wr_en <= "1111"; 
                                -- all bytes are written, but depending on reg_wb_sel, reg_wr_back_data contains the correct bytes
								reg_wb_sel <= "001"; -- select data memory output     								
                                case func_opcode is
                                    when "000" => reg_wb_sel <= "010"; -- select data memory output - load byte
                                    when "001" => reg_wb_sel <= "011"; -- select data memory output - load halfword
                                    when "010" => reg_wb_sel <= "001"; -- select data memory output - load word
                                    when "100" => reg_wb_sel <= "100"; -- select data memory output - load byte unsigned
                                    when "101" => reg_wb_sel <= "101"; -- select data memory output - load halfword unsigned
                                    when others => reg_wb_sel <= "001"; -- select data memory output - load word
                                end case;
                                
                                if (imm_val_12(11) = '1') then
                                    is_load_1_instr <= '1'; -- load for combi BRAM-regFile instead of external mem 
                                else
                                    is_load_1_instr <= '0';
                                end if;
                                
                             -- Store S-type, store for BRAM instead of external mem 
                             -- read from regFile in BRAM and store in mem in BRAM
                             when "01000" => 
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= func_sign_ext(imm_val_12_store, 32);
                                is_store_instr <= '1';
								reg_wr_en <= "1111"; -- enable register write to write loaded value into combi BRAM-regFile
                                -- we write data mem in BRAM or to external mem in the write back stage 
                                reg_wb_sel <= "001";                                                 
                                if (imm_val_12(11) = '1') then
                                    is_store_1_instr <= '1'; -- store for BRAM instead of external mem 
                                    -- enable register write to write loaded value into regFile BRAM
                                    case i_instr(14 downto 12) is
                                        when "000" => reg_wr_en <= "0001"; -- write enable for byte
                                        when "001" => reg_wr_en <= "0011"; -- write enable for halfword
                                        when "010" => reg_wr_en <= "1111"; -- write enable for word
                                        when others => reg_wr_en <= "1111"; -- write enable for word
                                    end case;
                                end if;
                            
                            --Branch B-type 
                            when "11000" => 
                                alu_operand_1_sel <= '1'; -- PC instead of reg
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= func_sign_ext(imm_val_13_branch, 32);                               
                                -- branch decision is taken in EX stages since the register values are then available
                                is_branch_instr <= '1';
                                case func_opcode is
                                    when "110" | "111" => br_unsigned <= '1'; 
                                    when others => br_unsigned <= '0';
                                end case;
                                
                            --JAL J-type 
                            when "11011" =>
                                alu_operand_1_sel <= '1'; -- jump, first ALU operand comes from PC instead of reg
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= func_sign_ext(imm_val_21_jump, 32);
                                reg_wb_sel <= "110"; -- select PC+4, write to reg to save return address
                                reg_wr_en <= "1111"; -- register write                             
                                pc_sel_jmp <= '1'; -- branch unconditional                        
                                
                            --JALR I-type 
                            when "11001" =>
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= func_sign_ext(imm_val_12, 32);
                                reg_wb_sel <= "110"; -- select PC+4, write to reg to save return address
                                reg_wr_en <= "1111"; -- register write
                                pc_sel_jmp <= '1'; -- branch unconditional
                                
                            -- LUI U-type 
                            when "01101" => 
                                src1_addr <= (others => '0'); -- reg number for src1 - 0 is added to the imm const
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg
                                imm_val <= i_instr(31 downto 12) & "000000000000";
                                reg_wr_en <= "1111"; -- enable dest reg to be written  
                                
                            -- AUIPC U-type 
                            when "00101" => 
                                alu_operand_1_sel <= '1'; -- PC instead of reg 
                                alu_operand_2_sel <= '1'; -- immediate value instead of reg;
                                reg_wr_en <= "1111"; -- enable dest reg to be written              
                                imm_val <= i_instr(31 downto 12) & "000000000000";
                            
                            --System instructions I-type ECALL, EBREAK
                            --when "1110011" 
               
                            -- default
                            when others => null;
                        end case;  
                    
                    -- GENERATE IMMEDIATE OPERANDS
                    -- build 12 bit immediate value for ADDI, ANDI, ..
                    imm_val_12 <= i_instr(31 downto 20);
                   
                    -- build the immediate value for store
                    imm_val_12_store <= i_instr(31 downto 25) & i_instr(11 downto 7);
                    
                    -- build the immediate value for branch
                    imm_val_13_branch <= i_instr(31) & i_instr(7) & i_instr(30 downto 25) & i_instr(11 downto 8) & '0';
                    
                    -- build the immediate value for jump
                    imm_val_21_jump <= i_instr(31) & i_instr(19 downto 12) & i_instr(20) & i_instr(30 downto 21) & '0';
                                                      		                             
                end process; 
                

    -- Register File 1 is implemented using distributed memory.
    -- Register File 2 is implemented using 1 BRAM shared with data memory.
    regFile_1:  process(clk)
                begin
                    if (clk'event and clk='1') then
                        reg1 <= barrel_regFile_array(to_integer(shift_left(to_unsigned(thread_id_pipe_0, DATA_WIDTH), BARREL_REG_FILE_SHIFT_AMOUNT)) + 
                                        to_integer(unsigned(src1_addr)));                
                        if (to_integer(unsigned(dest_addr_pipe_6)) /= 0) then -- reg0 is always 0
                            -- write data
                            if (reg_wr_en_pipe_6 = "1111") then
                                barrel_regFile_array(to_integer(shift_left(to_unsigned(thread_id_pipe_6, DATA_WIDTH), BARREL_REG_FILE_SHIFT_AMOUNT)) + 
                                    to_integer(unsigned(dest_addr_pipe_6))) <= reg_wr_back_data; 
                            elsif (reg_wr_en_pipe_6 = "0001") then
                                barrel_regFile_array(to_integer(shift_left(to_unsigned(thread_id_pipe_6, DATA_WIDTH), BARREL_REG_FILE_SHIFT_AMOUNT)) + 
                                    to_integer(unsigned(dest_addr_pipe_6)))(7 downto 0) <= reg_wr_back_data(7 downto 0); 
                            elsif (reg_wr_en_pipe_6 = "0011") then
                                barrel_regFile_array(to_integer(shift_left(to_unsigned(thread_id_pipe_6, DATA_WIDTH), BARREL_REG_FILE_SHIFT_AMOUNT)) + 
                                    to_integer(unsigned(dest_addr_pipe_6)))(15 downto 0) <= reg_wr_back_data(15 downto 0); 
                            end if;
                        end if;
                    end if;
                end process;    
                                                
    -- regFile 2 is implemented in BRAM                                                                                                                              
    -- addr for 2. read port - src2_addr provided by decoder
    BRAM_regFile_2_data_mem: dual_port_byte_en_RAM 
                        generic map (   SIZE => 1024,
                                        ADDR_WIDTH => 10,
                                        COL_WIDTH => 8,
                                        NB_COL => 4)
                        port map (  clka => clk,
                                    ena => '1',
                                    wea => (others => '0'),
                                    addra => rd_addr_BRAM,
                                    dina => (others => '0'),
                                    douta => reg2,
                                    clkb => clk,
                                    enb => '1',
                                    web => reg_wr_en_BRAM,
                                    addrb => wr_addr_BRAM,
                                    dinb => reg_wr_back_data,
                                    doutb => open);                                            
                                           
    -- addr for 1. read port    
    -- BRAM is divided into parts: upper part is regFile, lower part is data mem
    -- BRAM: RegFile has addresses "0" & "ttt" & "sssss" -- t for thread id an s for source addr
    -- BRAM: DataMem has addresses "1" & "ttt" & "sssss" -- t for thread id an s for source addr
    -- for a load from combi BRAM-regFile, imm_val is used to calculate the address 
    -- if it is move into reg from data mem
    -- use the addr for data mem in BRAM built from the immediate field
    -- semantically, rs1 is assumed to be 0
    -- the effective address is the immediate value + base address for data mem in the BRAM
    -- for 512 elements allocated for BRAM, base address = 512 (10 0000 0000)
    -- the 2 LSB are discarded because the addr is a byte-addr but we need an index for each word of 4 bytes for the array   
    
    rd_addr_BRAM <= "10" & std_logic_vector(to_unsigned(thread_id_pipe_0, 3)) & imm_val_12(6 downto 2) 
                                when (is_load_1_instr = '1') else
                                "00" & std_logic_vector(to_unsigned(thread_id_pipe_0, 3)) & src2_addr;  
    
    -- addr for write port
    -- dest addr forregFile implemented in distributed memory - dest_addr provided by decoder 
    -- if it is a move into mem, use the addr for data mem in BRAM built from the immediate value
    wr_addr_BRAM <= "10" & std_logic_vector(to_unsigned(thread_id_pipe_6, 3)) & imm_val_pipe_6(6 downto 2) 
                            when (is_store_1_instr_pipe_6 = '1') else
                            "00" & std_logic_vector(to_unsigned(thread_id_pipe_6, 3)) & dest_addr_pipe_6;                               
    
    -- regFile write enable provided by decoder 
    -- but set to 0000 if the dest register is 0 and it is a NOT a load/store for BRAM, except for memory mapped addresses
    reg_wr_en_BRAM <= "0000" when ( ((to_integer(unsigned(dest_addr_pipe_6)) = 0) and 
                                    (is_store_1_instr_pipe_6 = '0') and (is_load_1_instr_pipe_6 = '0')) 
                                 or ((is_mem_mapped_store_instr_pipe_6 = '1')) )
                            else reg_wr_en_pipe_6;   
                                                                                                                                    
    -- Into Decode Second Stage - Stage 2
    -- Now the read register values are available                                                        
    pipe_1: process(clk)
            begin 
                if rising_edge(clk) then
                    if (reset = '0') then
                        thread_id_pipe_1 <= 0;
                        pc_pipe_1 <= (others => '0'); 
                        pc_sel_pipe_1 <= '0';
                        func_opcode_pipe_1 <= (others => '0'); 
                        is_branch_instr_pipe_1 <= '0';
                        is_load_instr_pipe_1 <= '0'; 
                        is_store_instr_pipe_1 <= '0'; 
                        is_load_instr_pipe_1 <= '0';
                        is_store_instr_pipe_1 <= '0';
                        br_unsigned_pipe_1 <= '0';
                        dest_addr_pipe_1 <= (others => '0');             
                        reg_wr_en_pipe_1 <= "0000";
                        next_pc_before_jump_pipe_1 <= (others => '0'); 
                        reg_wb_sel_pipe_1 <= (others => '0'); 
                        alu_opcode_pipe_1  <= (others => '0');
                        imm_val_pipe_1  <= (others => '0');    
                        alu_operand_1_sel_pipe_1  <= '0';
                        alu_operand_2_sel_pipe_1  <= '0';                             
                    else  
                        thread_id_pipe_1 <= thread_id_pipe_0;
                        pc_pipe_1 <= pc_pipe_0;
                        pc_sel_pipe_1 <= pc_sel_jmp; 
                        func_opcode_pipe_1 <= func_opcode; 
                        is_branch_instr_pipe_1 <= is_branch_instr;
                        is_load_instr_pipe_1 <= is_load_instr;
                        is_store_instr_pipe_1 <= is_store_instr;
                        is_load_1_instr_pipe_1 <= is_load_1_instr; 
                        is_store_1_instr_pipe_1 <= is_store_1_instr;
                        br_unsigned_pipe_1 <= br_unsigned;
                        dest_addr_pipe_1 <= dest_addr;                          
                        reg_wr_en_pipe_1 <= reg_wr_en;
                        next_pc_before_jump_pipe_1 <= next_pc_before_jump_pipe_0;
                        reg_wb_sel_pipe_1 <= reg_wb_sel; 
                        alu_opcode_pipe_1 <= alu_opcode;
                        imm_val_pipe_1 <= imm_val; 
                        alu_operand_1_sel_pipe_1 <= alu_operand_1_sel;
                        alu_operand_2_sel_pipe_1 <= alu_operand_2_sel;                    
                    end if;  
                end if;              
            end process; 
              
        -- Into EX Stage - Stage 3                                                               
    pipe_2:     process(clk)
                    begin 
                        if (clk'event and clk = '1') then
                            if (reset = '0') then
                                thread_id_pipe_2 <= 0;
                                pc_pipe_2 <= (others => '0'); 
                                pc_sel_pipe_2 <= '0';
                                func_opcode_pipe_2 <= (others => '0'); 
                                is_branch_instr_pipe_2 <= '0'; 
                                is_load_instr_pipe_2 <= '0'; 
                                is_store_instr_pipe_2 <= '0'; 
                                is_load_1_instr_pipe_2 <= '0';
                                is_store_1_instr_pipe_2 <= '0'; 
                                br_unsigned_pipe_2 <= '0';
                                dest_addr_pipe_2 <= (others => '0');             
                                reg_wr_en_pipe_2 <=  "0000";
                                next_pc_before_jump_pipe_2 <= (others => '0'); 
                                reg_wb_sel_pipe_2 <= (others => '0'); 
                                alu_opcode_pipe_2 <= (others => '0');
                                imm_val_pipe_2 <= (others => '0');
                                alu_operand_1_sel_pipe_2 <= '0';
                                alu_operand_2_sel_pipe_2 <= '0'; 
                                reg1_pipe_2 <= (others => '0');
                                reg2_pipe_2 <= (others => '0');                                   
                            else  
                                thread_id_pipe_2 <= thread_id_pipe_1;
                                pc_pipe_2 <= pc_pipe_1;
                                pc_sel_pipe_2 <= pc_sel_pipe_1;
                                func_opcode_pipe_2 <= func_opcode_pipe_1; 
                                is_branch_instr_pipe_2 <= is_branch_instr_pipe_1;
                                is_load_instr_pipe_2 <= is_load_instr_pipe_1; 
                                is_store_instr_pipe_2 <= is_store_instr_pipe_1;                                 
                                is_load_1_instr_pipe_2 <= is_load_1_instr_pipe_1;  
                                is_store_1_instr_pipe_2 <= is_store_1_instr_pipe_1;
                                br_unsigned_pipe_2 <= br_unsigned_pipe_1;
                                dest_addr_pipe_2 <= dest_addr_pipe_1;                          
                                reg_wr_en_pipe_2 <= reg_wr_en_pipe_1;
                                next_pc_before_jump_pipe_2 <= next_pc_before_jump_pipe_1;
                                reg_wb_sel_pipe_2 <= reg_wb_sel_pipe_1; 
                                alu_opcode_pipe_2 <= alu_opcode_pipe_1;
                                imm_val_pipe_2 <= imm_val_pipe_1;
                                alu_operand_1_sel_pipe_2 <= alu_operand_1_sel_pipe_1;
                                alu_operand_2_sel_pipe_2 <= alu_operand_2_sel_pipe_1;
                                reg1_pipe_2 <= reg1;
                                reg2_pipe_2 <= reg2;
                        end if;  
                    end if;              
    end process; 
    
    -- ALU operation add is done separately because it is used by branch/jump instructions
    -- it should be faster because it is used to increment, to calculate target addr
    -- The rest of ALU operations are carried in two groups in parallel:
    -- Group 1: sub, shift-left, shift-right, compare less than signed/unsigned
    -- Group 2: xor, or, and, shift-right with extension
    
    is_add_op <= '1' when (alu_opcode_pipe_2 = "0000") else '0'; -- add instr needed for collecting ALU result                  
    alu_group <= '1' when ((alu_opcode_pipe_2 = "1000") or (alu_opcode_pipe_2 = "0001") or (alu_opcode_pipe_2 = "0101")
                                    or (alu_opcode_pipe_2 = "0010") or (alu_opcode_pipe_2 = "0011"))                             
                                else '0';             
                                                   
    -- BRANCH LOGIC in Stage EX, once reg1 and reg2 are available
    br_eq <= '1' when (reg1_pipe_2 = reg2_pipe_2 ) else '0'; -- is reg1 = reg2
    br_lt <= '1' when (((signed(reg1_pipe_2) < signed(reg2_pipe_2)) and (br_unsigned_pipe_2 = '0')) or -- is reg1 < reg2
                            ((unsigned(reg1_pipe_2) < unsigned(reg2_pipe_2)) and (br_unsigned_pipe_2 = '1'))) else '0';
                              
    branch_decision:    process(all)
                        begin 
                            if (is_branch_instr_pipe_2 = '1') then
                                pc_sel_br <= '0';                                         
                                case func_opcode_pipe_2 is
                                    when "000" =>   -- BEQ
                                        if br_eq = '1' then
                                            pc_sel_br <= '1'; -- branch taken  
                                        end if;
                                    when "001" =>   -- BNE
                                        if br_eq= '0' then
                                            pc_sel_br <= '1'; -- branch taken  
                                        end if;   
                                    when "100" =>   -- BLT
                                        if br_lt = '1' then
                                            pc_sel_br <= '1'; -- branch taken     
                                        end if;
                                    when "101" =>   -- BGE
                                        if br_lt = '0' then
                                            pc_sel_br <= '1'; -- branch taken 
                                        end if;
                                    when "110" =>   -- BLTU
                                        if br_lt = '1' then
                                            pc_sel_br <= '1'; -- branch taken 
                                        end if;                                    
                                    when "111" =>   -- BGEU
                                        if br_lt = '0' then
                                            pc_sel_br <= '1'; -- branch taken  
                                        end if;
                                    when others => 
                                        pc_sel_br <= '0';
                                end case;
                            else
                                pc_sel_br <= '0';    -- default branch not taken  
                            end if; 
                        end process;                                                                                                     
                                                         
     -- select alu operands             
    -- select the first operand for ALU either from register source 1 or PC for branch or JAL/JALR
    alu_operand_1 <= reg1_pipe_2 when alu_operand_1_sel_pipe_2 = '0' else func_zero_ext(pc_pipe_2, DATA_WIDTH);                                                                                                                                                        
    -- select for operand 2 of ALU: either 0 for data from reg or 1 for immediate value
    alu_operand_2 <= reg2_pipe_2 when alu_operand_2_sel_pipe_2 = '0' else imm_val_pipe_2; 
    
   -- Into Data Mem First Stage - Stage 4 
    pipe_3:     process(clk)
                begin 
                    if (clk'event and clk = '1') then
                        if (reset = '0') then
                            thread_id_pipe_3 <= 0;
                            pc_sel_pipe_3 <= '0';
                            pc_sel_br_pipe_3 <='0'; 
                            is_load_instr_pipe_3 <='0';
                            is_store_instr_pipe_3 <='0';
                            is_load_1_instr_pipe_3 <= '0';
                            is_store_1_instr_pipe_3 <= '0';
                            dest_addr_pipe_3 <= (others => '0');             
                            reg_wr_en_pipe_3 <=  "0000";
                            next_pc_before_jump_pipe_3 <= (others => '0'); 
                            reg_wb_sel_pipe_3 <= (others => '0'); 
                            alu_opcode_pipe_3 <= (others => '0');
                            is_add_op_pipe_3 <= '0';
                            alu_group_pipe_3 <= '0';
                            imm_val_pipe_3 <= imm_val_pipe_2;
                            alu_operand_1_pipe_3 <= (others => '0');
                            alu_operand_2_pipe_3 <= (others => '0'); 
                            reg_value_to_store_pipe_3 <= (others => '0'); 
                            data_from_mem_BRAM_pipe_3 <= (others => '0');                                  
                        else  
                            thread_id_pipe_3 <= thread_id_pipe_2;
                            pc_sel_pipe_3 <= pc_sel_pipe_2;
                            pc_sel_br_pipe_3 <= pc_sel_br;
                            is_load_instr_pipe_3 <= is_load_instr_pipe_2;
                            is_store_instr_pipe_3 <=is_store_instr_pipe_2;
                            is_load_1_instr_pipe_3 <= is_load_1_instr_pipe_2;
                            is_store_1_instr_pipe_3 <= is_store_1_instr_pipe_2; 
                            dest_addr_pipe_3 <= dest_addr_pipe_2;                          
                            reg_wr_en_pipe_3 <= reg_wr_en_pipe_2;
                            next_pc_before_jump_pipe_3 <= next_pc_before_jump_pipe_2;
                            reg_wb_sel_pipe_3 <= reg_wb_sel_pipe_2; 
                            alu_opcode_pipe_3 <= alu_opcode_pipe_2;
                            is_add_op_pipe_3 <= is_add_op;
                            alu_group_pipe_3 <= alu_group; 
                            imm_val_pipe_3 <= imm_val_pipe_2;
                            alu_operand_1_pipe_3 <= alu_operand_1;
                            alu_operand_2_pipe_3 <= alu_operand_2;
                            reg_value_to_store_pipe_3 <= reg2_pipe_2;
                            data_from_mem_BRAM_pipe_3 <= reg2_pipe_2;
                        end if;  
                    end if;              
                end process;  
                   
    alu:    process(all)
            begin 
                alu_result_add <= (others => '0');
                
                -- add operation
                if (alu_opcode_pipe_3 = "0000") then -- add
                   alu_result_add <= std_logic_vector(signed(alu_operand_1_pipe_3) + signed(alu_operand_2_pipe_3));
                end if;
                
                -- alu operations group 1
                if (alu_opcode_pipe_3 = "1000") then  -- sub  
                    alu_result_1_tmp_1 <= std_logic_vector(signed(alu_operand_1_pipe_3) - signed(alu_operand_2_pipe_3));
                else
                    alu_result_1_tmp_1 <= (others => '0');
                end if;
                
                if (alu_opcode_pipe_3 = "0001") then  -- left shift logical -- shamt: 5 bit immediate value
                    alu_result_1_tmp_2 <= std_logic_vector(shift_left(unsigned(alu_operand_1_pipe_3), 
                                            to_integer((unsigned(alu_operand_2_pipe_3(4 downto 0)))))); 
                else
                    alu_result_1_tmp_2 <= (others => '0');
                end if;
                
                if (alu_opcode_pipe_3 = "0101") then  -- right shift logical -- shamt: 5 bit immediate value           
                    alu_result_1_tmp_3 <= std_logic_vector(shift_right(unsigned(alu_operand_1_pipe_3), 
                                                to_integer((unsigned(alu_operand_2_pipe_3(4 downto 0)))))); 
                else
                    alu_result_1_tmp_3 <= (others => '0');
                end if;
                
                if (alu_opcode_pipe_3 = "0010") then  -- comparison less than signed             
                    if (signed(alu_operand_1_pipe_3) < signed(alu_operand_2_pipe_3)) then 
                        alu_result_1_tmp_4 <= (0 => '1', others => '0');
                    else
                        alu_result_1_tmp_4 <= (others => '0');
                    end if;            
                else
                    alu_result_1_tmp_4 <= (others => '0');
                end if;
                        
                if (alu_opcode_pipe_3 = "0011") then  -- comparison less than unsigned 
                    if (unsigned(alu_operand_1_pipe_3) < unsigned(alu_operand_2_pipe_3)) then 
                        alu_result_1_tmp_5 <= (0 => '1', others => '0');
                    else
                        alu_result_1_tmp_5 <= (others => '0');
                    end if;            
                else
                    alu_result_1_tmp_5 <= (others => '0');
                end if;       
                                            
                alu_result_1 <= alu_result_1_tmp_1 or alu_result_1_tmp_2 or alu_result_1_tmp_3 or alu_result_1_tmp_4 or alu_result_1_tmp_5;
                
                -- alu operations group 2
                if (alu_opcode_pipe_3 = "0100") then  -- xor         
                    alu_result_2_tmp_1 <= alu_operand_1_pipe_3 xor alu_operand_2_pipe_3;    
                else
                    alu_result_2_tmp_1 <= (others => '0');
                end if;  
                
                if (alu_opcode_pipe_3 = "1101") then  -- right shift arithmetic with sign expansion -- shamt: 5 bit immediate value    
                    alu_result_2_tmp_2 <= std_logic_vector(shift_right(signed(alu_operand_1_pipe_3), 
                                    to_integer((unsigned(alu_operand_2_pipe_3(4 downto 0))))));   
                else
                    alu_result_2_tmp_2 <= (others => '0');
                end if;                 
                
                if (alu_opcode_pipe_3 = "0110") then  -- or        
                    alu_result_2_tmp_3 <= alu_operand_1_pipe_3 or alu_operand_2_pipe_3;    
                else
                    alu_result_2_tmp_3 <= (others => '0');
                end if;  
                
                if (alu_opcode_pipe_3 = "0111") then  -- and       
                    alu_result_2_tmp_4 <= alu_operand_1_pipe_3 and alu_operand_2_pipe_3;      
                else
                    alu_result_2_tmp_4 <= (others => '0');
                end if;   
          
                alu_result_2 <= alu_result_2_tmp_1 or alu_result_2_tmp_2 or alu_result_2_tmp_3 or alu_result_2_tmp_4;
                
       end process;
     
    -- Into Data Mem First Stage - Stage 5 
    pipe_4: process(clk)
            begin 
                if (clk'event and clk = '1') then
                    if (reset = '0') then
                        thread_id_pipe_4 <= 0;
                        pc_sel_pipe_4 <= '0';                        
                        pc_sel_br_pipe_4 <= '0';
                        is_load_instr_pipe_4 <= '0';
                        is_store_instr_pipe_4 <= '0';
                        is_load_1_instr_pipe_4 <= '0';
                        is_store_1_instr_pipe_4 <= '0';
                        is_add_op_pipe_4 <= '0';
                        dest_addr_pipe_4 <= (others => '0');             
                        reg_wr_en_pipe_4 <=  "0000";
                        next_pc_before_jump_pipe_4 <= (others => '0');
                        reg_value_to_store_pipe_4 <= (others => '0'); 
                        reg_wb_sel_pipe_4 <= (others => '0');
                        is_add_op_pipe_4 <= '0';
                        alu_group_pipe_4 <= '0';
                        imm_val_pipe_4 <= (others => '0'); 
                        alu_result_add_pipe_4 <= (others => '0'); 
                        alu_result_pipe_4 <= (others => '0');
                        data_from_mem_BRAM_pipe_4 <= (others => '0');
                    else  
                        thread_id_pipe_4 <= thread_id_pipe_3;
                        pc_sel_pipe_4 <= pc_sel_pipe_3;
                        pc_sel_br_pipe_4 <= pc_sel_br_pipe_3;
                        is_load_instr_pipe_4 <= is_load_instr_pipe_3;
                        is_store_instr_pipe_4 <=is_store_instr_pipe_3;
                        is_load_1_instr_pipe_4 <= is_load_1_instr_pipe_3; 
                        is_store_1_instr_pipe_4 <= is_store_1_instr_pipe_3;
                        dest_addr_pipe_4 <= dest_addr_pipe_3;                      
                        reg_wr_en_pipe_4 <= reg_wr_en_pipe_3;
                        next_pc_before_jump_pipe_4 <= next_pc_before_jump_pipe_3;
                        reg_value_to_store_pipe_4 <= reg_value_to_store_pipe_3; 
                        reg_wb_sel_pipe_4 <= reg_wb_sel_pipe_3;
                        is_add_op_pipe_4 <= is_add_op_pipe_3;
                        alu_group_pipe_4 <= alu_group_pipe_3;
                        imm_val_pipe_4 <= imm_val_pipe_3;
                        alu_result_add_pipe_4 <= alu_result_add; 
                        alu_result_1_pipe_4 <= alu_result_1;
                        alu_result_2_pipe_4 <= alu_result_2;
                        data_from_mem_BRAM_pipe_4 <= data_from_mem_BRAM_pipe_3;
                    end if;  
                end if;              
            end process;       
   
   -- select the ALU result because they were generated separately: add result / the result from the two groups
    alu_result_final <= alu_result_add_pipe_4 when (is_add_op_pipe_4 = '1') else alu_result;   
    alu_result <= alu_result_1_pipe_4 when alu_group_pipe_4 = '1' else alu_result_2_pipe_4; 
    
    -- select correct for memory-mapped addresses in the WB stage                                             
    reg_wb_sel_tmp <= "111" when (((alu_result_add_pipe_4 = thread_id_addr) or (alu_result_add_pipe_4 = job_request_addr)
                                        or (alu_result_add_pipe_4 = job_value_addr) or (alu_result_add_pipe_4 = core_id_addr) or
                                           (alu_result_add_pipe_4 = job_done_addr)) 
                                 and (is_load_instr_pipe_4 = '1')) else reg_wb_sel_pipe_4;
    
    -- used to disable data memory write for memory mapped addresses 
    is_mem_mapped_store_instr <= '1' when ( (   (alu_result_add_pipe_4 = FIFO_addr) or 
                                                (alu_result_add_pipe_4 = thread_per_core_done_addr) or
                                                (alu_result_add_pipe_4 = job_request_addr) or
                                                (alu_result_add_pipe_4 = job_value_addr) or
                                                (alu_result_add_pipe_4 = job_result_addr) or
                                                (alu_result_add_pipe_4 = job_done_addr)  ) and (is_store_instr_pipe_4 = '1')) else '0' ;                                                        
            
    loaded_mem_mapped_data <= (others => '0') when (is_load_instr_pipe_4 = '0') else
                                std_logic_vector(to_unsigned(thread_id_pipe_4, DATA_WIDTH)) when (alu_result_add_pipe_4 = thread_id_addr)  else 
                                x"0000000" & "000" & job_request_reg(thread_id_pipe_4) when (alu_result_add_pipe_4 = job_request_addr) else
                                x"0000000" & "000" & job_done_reg(thread_id_pipe_4) when (alu_result_add_pipe_4 = job_done_addr) else
                                job_value_reg(thread_id_pipe_4) when (alu_result_add_pipe_4 = job_value_addr) else
                                func_zero_ext(i_id, DATA_WIDTH) when (alu_result_add_pipe_4 = core_id_addr) else
                                (others => '0');       
    
    -- FIFO_addr = x"0000FFFF" is a memory mapped addr for FIFO
    fifo_write <= '1' when ((alu_result_add_pipe_4 = FIFO_addr) and (is_store_instr_pipe_4 = '1')) else '0'; 
    data_to_fifo <= reg_value_to_store_pipe_4; -- byte to be sent to FIFO but written in the last stage        
    
-- allocate jobs to threads and read results, handle requests, acknowledgements, parameters using memory-mapped addresses
    -- memory address is calculated in the EX-stage   
    -- case of collecting results using fifos     
if_gen_collect:     
        if (COLLECT_MODE = '0') generate
           gen_fifo:    process (clk)    
                        variable var_thread_id_1, var_thread_id_2: integer range 0 to 7;              
                        begin 
                            if rising_edge(clk) then -- rising edge
                                if (reset = '0') then
                                    thread_ptr_new_request <= 0;
                                    thread_ptr_to_allocate <= 0;
                                    num_incoming_requests <= 0;
                                    num_requests_allocated <= 0;
                                    num_pending_requests <= 0;
                                    thread_ptr_new_result <= 0;
                                    thread_ptr_result_sent <= 0;    
                                    num_incoming_results <= 0;
                                    num_results_sent <= 0;
                                    num_pending_results <= 0;
                                    for index in 0 to NUM_THREADS - 1 loop
                                        job_request_reg(index) <= '0';
                                        job_done_reg(index) <= '0'; 
                                        job_value_reg(index) <= (others => '0');
                                        job_result_reg(index) <= (others => '0'); 
                                    end loop;
                                else                                   
                                    -- a new job is allocated 
                                    var_thread_id_1 := job_request_queue(thread_ptr_to_allocate);                                     
                                    if ((i_core_dispatch_en = '1') and (num_pending_requests > 0)) then                                                                       
                                        thread_ptr_to_allocate <= thread_ptr_to_allocate + 1; -- move pointer forward for the next request
                                        num_requests_allocated <= num_requests_allocated + 1; -- decrease num of pending requests
                                        job_value_reg(var_thread_id_1) <= i_job_value(DATA_WIDTH - 1 downto 0); -- save parameter in param reg for index thread id            
                                        job_request_reg(var_thread_id_1) <= '0'; -- so that the thread waiting for this request can go ahead
                                    end if;  
                                                                        
                                    -- write job request to job request register if a thread makes a request
                                    if ((alu_result_add_pipe_4 = job_request_addr) and (is_store_instr_pipe_4 = '1')) then                                                                             
                                        job_request_queue(thread_ptr_new_request) <= thread_id_pipe_4;  
                                        thread_ptr_new_request <= thread_ptr_new_request + 1;
                                        num_incoming_requests <= num_incoming_requests + 1; -- increase num of pending requests
                                        job_request_reg(thread_id_pipe_4) <= '1';       
                                    end if;
                                    
                                    num_pending_requests <= num_incoming_requests - num_requests_allocated;
                                    -- a new job is required, make a request                   
                                    if (num_pending_requests > 0) then
                                        o_job_request <= '1';
                                    else
                                        o_job_request <= '0';
                                    end if;                                                                                     
                                end if;
                            end if;
                        end process;  
                          
                        -- irrelevant for collect mode using FIFOs
                        o_job_done <= '0';
                        o_job_result <= (others => '0');        
                                
        elsif (COLLECT_MODE = '1') generate
           gen_poll:    process (clk)    
                        variable var_thread_id_1, var_thread_id_2: integer range 0 to 7;              
                        begin 
                            if rising_edge(clk) then -- rising edge
                                if (reset = '0') then
                                    thread_ptr_new_request <= 0;
                                    thread_ptr_to_allocate <= 0;
                                    num_incoming_requests <= 0;
                                    num_requests_allocated <= 0;
                                    num_pending_requests <= 0;
                                    num_incoming_results <= 0;
                                    num_results_sent <= 0;
                                    num_pending_results <= 0;
                                    thread_ptr_new_result <= 0;
                                    thread_ptr_result_sent <= 0;
                                    for index in 0 to NUM_THREADS - 1 loop
                                        job_request_reg(index) <= '0'; 
                                        job_done_reg(index) <= '0'; 
                                        job_value_reg(index) <= (others => '0');
                                        job_result_reg(index) <= (others => '0');
                                    end loop;
                                else   
                                    -- write job request to job request register if a thread makes a request
                                    if ((alu_result_add_pipe_4 = job_request_addr) and (is_store_instr_pipe_4 = '1')) then                                                                             
                                        job_request_queue(thread_ptr_new_request) <= thread_id_pipe_4;  
                                        thread_ptr_new_request <= thread_ptr_new_request + 1;
                                        num_incoming_requests <= num_incoming_requests + 1; -- increase num of pending requests
                                        job_request_reg(thread_id_pipe_4) <= '1';       
                                    end if;   
                                                                 
                                    -- a new job is allocated 
                                    var_thread_id_1 := job_request_queue(thread_ptr_to_allocate);                                     
                                    if (i_core_dispatch_en = '1') and (num_pending_requests > 0) then                                                                       
                                        thread_ptr_to_allocate <= thread_ptr_to_allocate + 1; -- move pointer forward for the next request
                                        num_requests_allocated <= num_requests_allocated + 1; -- decrease num of pending requests
                                        job_value_reg(var_thread_id_1) <= i_job_value(DATA_WIDTH - 1 downto 0); -- save parameter in param reg for index thread id            
                                        job_request_reg(var_thread_id_1) <= '0'; -- so that the thread waiting for this request can go ahead
                                    end if;  
                                                                                                             
                                    num_pending_requests <= num_incoming_requests - num_requests_allocated;
                                    -- a new job is required, make a request                   
                                    if (num_pending_requests > 0) then
                                        o_job_request <= '1';
                                    else
                                        o_job_request <= '0';
                                    end if; 
                                    
                                -- result is ready from a thread, insert in done queue and write job_value_reg
                                if ((alu_result_add_pipe_4 = job_result_addr) and (is_store_instr_pipe_4 = '1')) then
                                    job_done_queue(thread_ptr_new_result) <= thread_id_pipe_4; 
                                    job_result_reg(thread_id_pipe_4) <= reg_value_to_store_pipe_4;
                                    thread_ptr_new_result <= thread_ptr_new_result + 1;
                                    num_incoming_results <= num_incoming_results + 1; -- increment num of new results avaiilable
                                    job_done_reg(thread_id_pipe_4) <= '1'; 
                                end if;
                
                                -- pass the result to the dispatcher
                                var_thread_id_2 := job_done_queue(thread_ptr_result_sent);                                        
                                if ( (i_core_result_en = '1') and (num_pending_results > 0) ) then                                                                    
                                    o_job_result <= job_result_reg(var_thread_id_2); -- result to be sent out to the port                                      
                                    thread_ptr_result_sent <= thread_ptr_result_sent + 1; -- move pointer forward for the next result to be sent
                                    num_results_sent <= num_results_sent + 1; -- increment num of results sent   
                                    job_done_reg(var_thread_id_2) <= '0';
                                    o_job_done <= '1'; 
                                else
                                    o_job_done <= '0';              
                                end if;                                
                                
                                -- are there any results to be sent?
                                num_pending_results <= num_incoming_results - num_results_sent;
                                
                                -- a thread is done with its job
                                if ((alu_result_add_pipe_4 = thread_per_core_done_addr) and (is_store_instr_pipe_4 = '1'))  then
                                    threads_per_core_done_reg(thread_id_pipe_4) <= '0';   
                                end if;
                                                                             
                            end if;
                        end if;
                    end process;                                                                                        
        end generate if_gen_collect;
             
    -- threads_done_reg is initialized to 1, when a thread is done, the element at that thread index of threads_done_reg is set 0
    -- when threads_done_reg is 0, all threads for this core is done         
    o_core_done <= '1' when (unsigned(threads_per_core_done_reg)) = 0 else '0';     
     
    -- Into Data Mem Second Stage - Stage 6  
    pipe_5: process(clk)
            begin 
                if (clk'event and clk = '1') then
                    if (reset = '0') then
                        thread_id_pipe_5 <= 0;
                        is_load_1_instr_pipe_5 <= '0'; 
                        is_store_1_instr_pipe_5 <= '0';
                        is_mem_mapped_store_instr_pipe_5 <= '0'; 
                        dest_addr_pipe_5 <= (others => '0');             
                        reg_wr_en_pipe_5 <=  "0000";
                        next_pc_before_jump_pipe_5 <= (others => '0');
                        reg_value_to_store_pipe_5 <= (others => '0');
                        reg_wb_sel_pipe_5 <= (others => '0');
                        imm_val_pipe_5 <= (others => '0');
                        alu_result_pipe_5 <= (others => '0'); 
                        fifo_write_pipe_5 <= '0'; 
                        data_to_fifo_pipe_5 <= (others => '0');
                        data_from_mem_BRAM_pipe_5 <= (others => '0'); 
                        loaded_mem_mapped_data_pipe_5 <= (others => '0');                      
                    else                 
                        thread_id_pipe_5 <= thread_id_pipe_4;
                        is_load_1_instr_pipe_5 <= is_load_1_instr_pipe_4; 
                        is_store_1_instr_pipe_5 <= is_store_1_instr_pipe_4; 
                        is_mem_mapped_store_instr_pipe_5 <= is_mem_mapped_store_instr; 
                        dest_addr_pipe_5 <= dest_addr_pipe_4;                          
                        reg_wr_en_pipe_5 <= reg_wr_en_pipe_4;
                        next_pc_before_jump_pipe_5 <= next_pc_before_jump_pipe_4;
                        reg_value_to_store_pipe_5 <= reg_value_to_store_pipe_4;
                        reg_wb_sel_pipe_5 <= reg_wb_sel_tmp; 
                        imm_val_pipe_5 <= imm_val_pipe_4; 
                        alu_result_pipe_5 <= alu_result_final; 
                        fifo_write_pipe_5 <= fifo_write; 
                        data_to_fifo_pipe_5 <= data_to_fifo;
                        data_from_mem_BRAM_pipe_5 <= data_from_mem_BRAM_pipe_4; 
                        loaded_mem_mapped_data_pipe_5 <= loaded_mem_mapped_data; 
                    end if;  
                end if;              
            end process;                      
             
    -- Into Write-Back Stage - Stage 7                                                                                                                        
    pipe_6: process(clk)
            begin
                if (clk'event and clk = '1') then
                    if (reset = '0') then
                        thread_id_pipe_6 <= 0;
                        is_load_1_instr_pipe_6 <= '0'; 
                        is_store_1_instr_pipe_6 <= '0'; 
                        is_mem_mapped_store_instr_pipe_6 <= '0'; 
                        dest_addr_pipe_6 <= (others => '0');
                        alu_result_pipe_6 <= (others => '0');
                        reg_wb_sel_pipe_6 <= (others => '0');
                        imm_val_pipe_6 <= (others => '0');
                        reg_wr_en_pipe_6 <=  "0000";
                        next_pc_before_jump_pipe_6 <= (others => '0');
                        reg_value_to_store_pipe_6 <= (others => '0');
                        fifo_write_pipe_6 <= '0'; 
                        data_to_fifo_pipe_6 <= (others => '0');
                        data_from_mem_BRAM_pipe_6 <= (others => '0');    
                        loaded_mem_mapped_data_pipe_6 <= (others => '0');  
                    else
                        thread_id_pipe_6 <= thread_id_pipe_5;
                        is_load_1_instr_pipe_6 <= is_load_1_instr_pipe_5;
                        is_store_1_instr_pipe_6 <= is_store_1_instr_pipe_5; 
                        is_mem_mapped_store_instr_pipe_6 <= is_mem_mapped_store_instr_pipe_5; 
                        dest_addr_pipe_6 <= dest_addr_pipe_5;
                        alu_result_pipe_6 <= alu_result_pipe_5;
                        reg_wb_sel_pipe_6 <= reg_wb_sel_pipe_5;
                        imm_val_pipe_6 <= imm_val_pipe_5;
                        reg_wr_en_pipe_6 <= reg_wr_en_pipe_5;
                        next_pc_before_jump_pipe_6 <= next_pc_before_jump_pipe_5;
                        reg_value_to_store_pipe_6 <= reg_value_to_store_pipe_5;
                        fifo_write_pipe_6 <= fifo_write_pipe_5; 
                        data_to_fifo_pipe_6 <= data_to_fifo_pipe_5;
                        data_from_mem_BRAM_pipe_6 <= data_from_mem_BRAM_pipe_5; 
                        loaded_mem_mapped_data_pipe_6 <= loaded_mem_mapped_data_pipe_5;  
                    end if;                           
                end if;                        
            end process;                                      
    
    -- data to be written to reg from memory or from BRAM
    data_wb <= reg_value_to_store_pipe_6 when (is_store_1_instr_pipe_6 = '1') else data_from_mem_BRAM_pipe_6;  
                 
    -- select for data to be written to register file: either from ALU, thread ID, job ack, or job param
    -- or saved pc for JAL/JALR or loaded data from mem
    reg_wr_back_data <= alu_result_pipe_6 when (reg_wb_sel_pipe_6 = "000") else
                        loaded_mem_mapped_data_pipe_6 when (reg_wb_sel_pipe_6 = "111") else
                        -- 110 for saved PC+4 (for JAL/JALR)     
                        func_zero_ext(next_pc_before_jump_pipe_6, DATA_WIDTH) when (reg_wb_sel_pipe_6 = "110") else  
                        -- 010 for data memory - load byte
                        func_sign_ext(data_wb(7 downto 0), DATA_WIDTH) when reg_wb_sel_pipe_6 = "010" else
                        -- 011 for data memory - load halfword
                        func_sign_ext(data_wb(15 downto 0), DATA_WIDTH) when reg_wb_sel_pipe_6 = "011" else 
                        -- 100 for data memory - load byte unsigned
                        func_zero_ext(data_wb(7 downto 0), DATA_WIDTH) when reg_wb_sel_pipe_6 = "100" else 
                        -- 101 for data memory - load halfword unsigned
                        func_zero_ext(data_wb(15 downto 0), DATA_WIDTH) when reg_wb_sel_pipe_6 = "101" else   
                        data_wb;  -- default loaded word                    
                        
    
    -- output to FIFO on the top level                    
    o_fifo_write <= fifo_write_pipe_6;
    o_data_to_fifo <= func_zero_ext(data_to_fifo_pipe_6, DATA_WIDTH); 
    
end barrel_core_variant_2_arch;
