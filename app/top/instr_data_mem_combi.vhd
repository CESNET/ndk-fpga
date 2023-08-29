-- instr mem and data mem share a BRAM
-- instr mem in lower BRAM and data mem in upper BRAM
-- to be used with barrel_core_variant_3

use WORK.RISCV_package.ALL;
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity instr_data_mem_combi is
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
end instr_data_mem_combi;

architecture instr_data_mem_combi_arch of instr_data_mem_combi is
type ram_type is array (0 to SIZE - 1) of std_logic_vector (NB_COL*COL_WIDTH - 1 downto 0);
shared variable RAM: ram_type := (
--write result
--x"0FFFF3B7",
--x"00C3D393",
--x"0FFF8137",
--x"00C15113",
--x"0FFF0237",
--x"00C25213",
--x"0FFE41B7",
--x"00C1D193",
--x"0FFE0437",
--x"00C45413",
--x"08000613",
--x"FEEB96B7",
--x"40C6D693",
--x"01CCD737",
--x"00C75713",
--x"07F00793",
--x"F8000813",
--x"00300B93",
--x"40000EB7",
--x"00EEDE93",
--x"00100093",
--x"00000F33",
--x"00112023",
--x"00012283",
--x"FE501EE3",
--x"00022303",
--x"006009B3",
--x"00F9F9B3",
--x"02C989B3",
--x"00D98A33",
--x"006009B3",
--x"0109F9B3",
--x"4079D993",
--x"02C989B3",
--x"41370AB3",
--x"01400DB3",
--x"01500E33",
--x"03BD8B33",
--x"40EB5B13",
--x"016009B3",
--x"03CE0B33",
--x"40EB5B13",
--x"03CD8C33",
--x"40DC5C13",
--x"013D8DB3",
--x"416D8DB3",
--x"018E0E33",
--x"001F0F13",
--x"017F5663",
--x"01698CB3",
--x"FD9ED6E3",
--x"00A31313",
--x"01E36F33",
--x"0001A283",
--x"FE501EE3",
--x"01E42023",
--x"F75FF06F",
--collect fifo
x"0FFFF3B7",
x"00C3D393",
x"0FFF8137",
x"00C15113",
x"0FFF0237",
x"00C25213",
x"08000613",
x"FEEB96B7",
x"40C6D693",
x"01CCD737",
x"00C75713",
x"07F00793",
x"F8000813",
x"00300B93",
x"40000EB7",
x"00EEDE93",
x"00100093",
x"00000F33",
x"00112023",
x"00012283",
x"FE501EE3",
x"00022303",
x"006009B3",
x"00F9F9B3",
x"02C989B3",
x"00D98A33",
x"006009B3",
x"0109F9B3",
x"4079D993",
x"02C989B3",
x"41370AB3",
x"01400DB3",
x"01500E33",
x"03BD8B33",
x"40EB5B13",
x"016009B3",
x"03CE0B33",
x"40EB5B13",
x"03CD8C33",
x"40DC5C13",
x"013D8DB3",
x"416D8DB3",
x"018E0E33",
x"001F0F13",
x"017F5663",
x"01698CB3",
x"FD9ED6E3",
x"00A31313",
x"01E36F33",
x"01E3A023",
x"F7DFF06F",
---- load-store 
--x"81900193",
--x"00302023",
--x"003181B3",
--x"00302223",
--x"003181B3",
--x"00302423",
--x"00012183",
--x"00410113",
--x"00012303",
--x"00410113",
--x"00012383",
--x"003181B3",
--x"00312023",
--x"00612223",
--x"00712423",
--x"00012203",
--x"00412303",
--x"00812383",
--x"00310023",
--x"00012203",
--x"00311023",
--x"003181B3",
--x"00010203",
--x"00011203",
--x"00012203",
--x"003181B3",
--x"00312023",
--x"00014203",
--x"003181B3",
--x"00312023",
--x"00015203",
--x"00520193",
--x"00012203",
others => (others => '0'));  

begin
    -- instr mem is in the upper half of the BRAM
    -- Port A --
    process (clka)
    begin
        if rising_edge(clka) then
            if (ena = '1') and (to_integer(unsigned(addra)) < (SIZE/2 - 1)) then
                douta <= RAM(to_integer(unsigned(addra))); 
            end if;
        end if;
    end process;
    
    -- data mem is in the lower half of the BRAM
    -- Port B --
    process (clkb)
    begin
        if rising_edge(clkb) then
            if enb = '1' then
                doutb <= RAM(to_integer(unsigned(addrb)) + SIZE/2);
                for i in 0 to NB_COL - 1 loop
                    if web(i) = '1' then
                        RAM(to_integer(unsigned(addrb)) + SIZE/2)((i+1)*COL_WIDTH - 1 downto i*COL_WIDTH) :=
                                        dinb((i+1)*COL_WIDTH - 1 downto i*COL_WIDTH);
                    end if;
                end loop;
            end if;
        end if;
    end process;

end instr_data_mem_combi_arch;
