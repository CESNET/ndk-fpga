library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity fifo is
    generic (   depth : integer := 16; -- depth of fifo
                width : integer := 32);  -- width of data  
    port (    clk : in std_logic;
              reset : in std_logic;
              rd_en : in std_logic; -- enable read, '0' when not in use
              wr_en : in std_logic; -- enable write, 0' when not in use
              din : in std_logic_vector (width - 1 downto 0); -- input data
              dout : out std_logic_vector(width - 1 downto 0); -- output data
              empty : out std_logic; -- set as '1' when the queue is empty
              full : out std_logic); -- set as '1' when the queue is full
end fifo;

architecture fifo_arch of fifo is

type memory_type is array (0 to depth - 1) of std_logic_vector(width - 1 downto 0);
signal memory : memory_type :=(others => (others => '0')); -- memory for queue
signal readptr, writeptr : integer := 0;  -- read and write pointers
signal empty_1, full_1 : std_logic := '0';

attribute keep : string;
attribute keep of readptr, writeptr, empty_1,  full_1, empty, full, rd_en, wr_en, din, dout : signal is "true";

begin
    empty <= empty_1;
    full <= full_1;

    process(clk)
    -- this is the number of elements stored in fifo at a time
    -- this variable is used to decide whether the fifo is empty or full
    variable num_elem : integer := 0;  
    begin
        if(rising_edge(clk)) then
            if(reset = '0') then
                dout <= (others => '0');
                empty_1 <= '1';
                full_1 <= '0';
                readptr <= 0;
                writeptr <= 0;
                num_elem := 0;
            else
                if(rd_en = '1' and empty_1 = '0') then -- read
                    dout <= memory(readptr);
                    readptr <= readptr + 1;      
                    num_elem := num_elem - 1;
                    -- wrap around
                    if(readptr = depth - 1) then -- reset read pointer
                        readptr <= 0;
                    end if;
                end if;
                
                if(wr_en ='1' and full_1 = '0') then -- write
                    memory(writeptr) <= din;
                    writeptr <= writeptr + 1;  
                    num_elem := num_elem + 1;
                    -- wrap around
                    if(writeptr = depth - 1) then -- reset write pointer
                        writeptr <= 0;
                    end if; 
                end if;
      
                -- set empty and full flags
                if(num_elem = 0) then
                    empty_1 <= '1';
                else
                    empty_1 <= '0';
                end if;
                if(num_elem = depth) then
                    full_1 <= '1';
                else
                    full_1 <= '0';
                end if;
            end if;
        end if; 
end process;

end fifo_arch;