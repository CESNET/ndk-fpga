----------------------------------------------------------------------------------
-- Create Date: 09.02.2023 18:18:50
-- Design Name: 
-- Module Name: instr_rom - instr_rom_arch
----------------------------------------------------------------------------------
use WORK.RISCV_package.ALL;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity instr_rom is
    port ( clk: in std_logic;
           addr: in std_logic_vector(INSTR_MEM_ADDR_WIDTH - 1 downto 0);
           data: out DATA_TYPE); 
end instr_rom;

architecture instr_rom_arch of instr_rom is
signal instr_mem: PROGRAM_SEQUENCE (0 to (2**INSTR_MEM_ADDR_WIDTH) - 1):= (
--collect fifo
x"B7", x"F3", x"FF", x"0F",
x"93", x"D3", x"C3", x"00",
x"37", x"81", x"FF", x"0F",
x"13", x"51", x"C1", x"00",
x"37", x"02", x"FF", x"0F",
x"13", x"52", x"C2", x"00",
x"13", x"06", x"00", x"08",
x"B7", x"96", x"EB", x"FE",
x"93", x"D6", x"C6", x"40",
x"37", x"D7", x"CC", x"01",
x"13", x"57", x"C7", x"00",
x"93", x"07", x"F0", x"07",
x"13", x"08", x"00", x"F8",
x"93", x"0B", x"80", x"3E",
x"B7", x"0E", x"00", x"40",
x"93", x"DE", x"EE", x"00",
x"93", x"00", x"10", x"00",
x"33", x"0F", x"00", x"00",
x"23", x"20", x"11", x"00",
x"83", x"22", x"01", x"00",
x"E3", x"1E", x"50", x"FE",
x"03", x"23", x"02", x"00",
x"B3", x"09", x"60", x"00",
x"B3", x"F9", x"F9", x"00",
x"B3", x"89", x"C9", x"02",
x"33", x"8A", x"D9", x"00",
x"B3", x"09", x"60", x"00",
x"B3", x"F9", x"09", x"01",
x"93", x"D9", x"79", x"40",
x"B3", x"89", x"C9", x"02",
x"B3", x"0A", x"37", x"41",
x"B3", x"0D", x"40", x"01",
x"33", x"0E", x"50", x"01",
x"33", x"8B", x"BD", x"03",
x"13", x"5B", x"EB", x"40",
x"B3", x"09", x"60", x"01",
x"33", x"0B", x"CE", x"03",
x"13", x"5B", x"EB", x"40",
x"33", x"8C", x"CD", x"03",
x"13", x"5C", x"DC", x"40",
x"B3", x"8D", x"3D", x"01",
x"B3", x"8D", x"6D", x"41",
x"33", x"0E", x"8E", x"01",
x"13", x"0F", x"1F", x"00",
x"63", x"56", x"7F", x"01",
x"B3", x"8C", x"69", x"01",
x"E3", x"D6", x"9E", x"FD",
x"13", x"13", x"A3", x"00",
x"33", x"6F", x"E3", x"01",
x"23", x"A0", x"E3", x"01",
x"6F", x"F0", x"DF", x"F7",
-- result write
--x"B7", x"F3", x"FF", x"0F",
--x"93", x"D3", x"C3", x"00",
--x"37", x"81", x"FF", x"0F",
--x"13", x"51", x"C1", x"00",
--x"37", x"02", x"FF", x"0F",
--x"13", x"52", x"C2", x"00",
--x"B7", x"41", x"FE", x"0F",
--x"93", x"D1", x"C1", x"00",
--x"37", x"04", x"FE", x"0F",
--x"13", x"54", x"C4", x"00", 
--x"13", x"06", x"00", x"08",
--x"B7", x"96", x"EB", x"FE",
--x"93", x"D6", x"C6", x"40",
--x"37", x"D7", x"CC", x"01",
--x"13", x"57", x"C7", x"00",
--x"93", x"07", x"F0", x"07",
--x"13", x"08", x"00", x"F8",
--x"93", x"0B", x"30", x"00",
--x"B7", x"0E", x"00", x"40",
--x"93", x"DE", x"EE", x"00",
--x"93", x"00", x"10", x"00",
--x"33", x"0F", x"00", x"00",
--x"23", x"20", x"11", x"00",
--x"83", x"22", x"01", x"00",
--x"E3", x"1E", x"50", x"FE",
--x"03", x"23", x"02", x"00",
--x"B3", x"09", x"60", x"00",
--x"B3", x"F9", x"F9", x"00",
--x"B3", x"89", x"C9", x"02",
--x"33", x"8A", x"D9", x"00",
--x"B3", x"09", x"60", x"00",
--x"B3", x"F9", x"09", x"01",
--x"93", x"D9", x"79", x"40",
--x"B3", x"89", x"C9", x"02",
--x"B3", x"0A", x"37", x"41",
--x"B3", x"0D", x"40", x"01",
--x"33", x"0E", x"50", x"01",
--x"33", x"8B", x"BD", x"03",
--x"13", x"5B", x"EB", x"40",
--x"B3", x"09", x"60", x"01",
--x"33", x"0B", x"CE", x"03",
--x"13", x"5B", x"EB", x"40",
--x"33", x"8C", x"CD", x"03",
--x"13", x"5C", x"DC", x"40",
--x"B3", x"8D", x"3D", x"01",
--x"B3", x"8D", x"6D", x"41",
--x"33", x"0E", x"8E", x"01",
--x"13", x"0F", x"1F", x"00",
--x"63", x"56", x"7F", x"01",
--x"B3", x"8C", x"69", x"01",
--x"E3", x"D6", x"9E", x"FD",
--x"13", x"13", x"A3", x"00",
--x"33", x"6F", x"E3", x"01",
--x"83", x"A2", x"01", x"00",
--x"E3", x"1E", x"50", x"FE",
--x"23", x"20", x"E4", x"01", 
--x"6F", x"F0", x"5F", x"F7",
-- load-store 
--x"93", x"01", x"90", x"81",
--x"23", x"20", x"30", x"00",
--x"13", x"82", x"11", x"00",
--x"23", x"2B", x"40", x"02",
--x"83", x"22", x"60", x"03",
--x"93", x"02", x"12", x"00",
--x"23", x"2E", x"50", x"04",
--x"13", x"83", x"12", x"00",
--x"23", x"20", x"60", x"80",
--x"83", x"23", x"00", x"80",
--x"93", x"88", x"13", x"00",
--x"23", x"2B", x"10", x"83",
--x"03", x"24", x"60", x"83",
--x"13", x"09", x"14", x"00",
--x"23", x"2E", x"20", x"85",
--x"83", x"24", x"C0", x"85",
--x"93", x"89", x"14", x"00",
--x"A3", x"2F", x"30", x"87",
--x"03", x"25", x"F0", x"87",
--x"13", x"0A", x"15", x"00",
--x"23", x"20", x"40", x"81",
--x"83", x"15", x"00", x"80",
--x"93", x"8A", x"C5", x"0C",
--x"23", x"2B", x"50", x"83",
--x"03", x"46", x"60", x"83",
--x"13", x"0B", x"16", x"00",
--x"23", x"2E", x"50", x"85",
--x"83", x"16", x"C0", x"85",
--x"93", x"8B", x"16", x"00",
--x"A3", x"2F", x"70", x"87",
--x"03", x"57", x"F0", x"87",
--x"13", x"0C", x"17", x"00",
--x"23", x"20", x"00", x"80",
--x"23", x"00", x"70", x"80",
--x"93", x"03", x"40", x"81",
--x"03", x"24", x"00", x"80",
--x"23", x"2B", x"00", x"82",
--x"23", x"1B", x"70", x"82",
--x"03", x"14", x"60", x"83",
--x"83", x"54", x"60", x"83",
others => x"00");    
     
attribute keep : string;
attribute keep of addr : signal is "true";
attribute keep of data : signal is "true";
                                
begin   
    process(clk)
    begin
        if rising_edge(clk) then    
            data <=     instr_mem(to_integer(unsigned(addr) + 3 )) &
                        instr_mem(to_integer(unsigned(addr) + 2 )) &
                        instr_mem(to_integer(unsigned(addr) + 1 )) &
                        instr_mem(to_integer(unsigned(addr)));    
        end if;
    end process;
       
end instr_rom_arch;