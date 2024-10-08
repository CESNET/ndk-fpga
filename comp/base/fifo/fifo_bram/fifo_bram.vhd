-- fifo_bram.vhd: Block RAM Fifo
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor     pus@liberouter.org
--            Jakub Cabal    cabal@cesnet.cz
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity fifo_bram is
   generic(
      -- ITEMS = Numer of items in FIFO
      ITEMS          : integer := 1024;
      -- BLOCK_SIZE = Number of items in one block
      BLOCK_SIZE     : integer := 4;
      -- Data Width
      DATA_WIDTH     : integer := 36;
      -- Automatic transfer of valid data to the output of the FIFO
      AUTO_PIPELINE  : boolean := false;
      -- compute value of status signal
      STATUS_ENABLED : boolean := false;
      -- for better timing on output
      DO_REG         : boolean := true
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;
      -- Write interface
      WR       : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL     : out std_logic;
      LSTBLK   : out std_logic;
      STATUS   : out std_logic_vector(log2(ITEMS) downto 0);
      -- Read interface
      RD       : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DV       : out std_logic;
      EMPTY    : out std_logic
   );
end entity fifo_bram;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of fifo_bram is

   -- Number of address bits
   constant FADDR : integer := LOG2(ITEMS)-1;

   signal write_allow                : std_logic;
   signal read_allow                 : std_logic;
   signal empty_int                  : std_logic;
   signal full_int                   : std_logic;

   signal sig_rd                     : std_logic;
   signal sig_dv                     : std_logic;

   signal reg_empty                  : std_logic;
   signal reg_full                   : std_logic;
   signal reg_lstblk                 : std_logic;

   signal cnt_write_addr             : std_logic_vector((FADDR+1) downto 0);
   signal cnt_read_addr              : std_logic_vector((FADDR+1) downto 0);
   signal reg_read_addr              : std_logic_vector((FADDR+1) downto 0);
   signal reg_write_addr             : std_logic_vector((FADDR+1) downto 0);

	signal cnt_write_addr_low         : std_logic_vector(FADDR downto 0);
	signal cnt_write_addr_high        : std_logic;
	signal cnt_write_addr_high_next   : std_logic;
	signal cnt_write_addr_load_enable : std_logic;

	signal cnt_read_addr_low          : std_logic_vector(FADDR downto 0);
	signal cnt_read_addr_high         : std_logic;
	signal cnt_read_addr_high_next    : std_logic;
	signal cnt_read_addr_load_enable  : std_logic;

   signal cnt_diff                   : std_logic_vector((FADDR+1) downto 0) := (others => '0');
   signal cnt_diff_ce                : std_logic;
   signal cnt_diff_dir               : std_logic;
   signal data_out                   : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal lstblk_plus_one            : std_logic;
   signal lstblk_minus_one           : std_logic;

-- ----------------------------------------------------------------------------

begin

assert (ITEMS >= 2) report "FIFO_BRAM: ITEMS lower than 2 is not supported" severity failure;

cond_ap : if AUTO_PIPELINE = true generate
   sig_rd <= RD or not sig_dv;
end generate;

cond_nap : if AUTO_PIPELINE = false generate
   sig_rd <= RD;
end generate;

-- new simple dualport BRAM compatible with Xilinx and Altera/Intel FPGA
bram_i : entity work.SDP_BRAM_BEHAV
generic map(
   DATA_WIDTH  => DATA_WIDTH,
   ITEMS       => ITEMS,
   OUTPUT_REG  => DO_REG
)
port map(
   -- WRITE INTERFACE
   WR_CLK      => CLK,
   WR_ADDR     => reg_write_addr(FADDR downto 0),
   WR_EN       => write_allow,
   WR_DIN      => DI,
   -- READ INTERFACE
   RD_CLK      => CLK,
   RD_RST      => RESET,
   RD_ADDR     => reg_read_addr(FADDR downto 0),
   RD_CE       => sig_rd,
   RD_REG_CE   => sig_rd,
   RD_EN       => read_allow,
   RD_DOUT     => data_out,
   RD_DOUT_VLD => sig_dv
);

-- ----------------------------------------------------------------------------
--                   Address counters and registers
-- ----------------------------------------------------------------------------

-- cnt_write_addr_low counter
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_write_addr_low <= conv_std_logic_vector(1, cnt_write_addr_low'length);
      elsif (write_allow = '1') then
			if cnt_write_addr_load_enable = '1' then
				cnt_write_addr_low <= (others => '0');
			else
				cnt_write_addr_low <= cnt_write_addr_low + 1;
			end if;
      end if;
   end if;
end process;

process(cnt_write_addr_low)
begin
	if cnt_write_addr_low = conv_std_logic_vector(ITEMS-1, cnt_write_addr_low'length) then
		cnt_write_addr_load_enable <= '1';
	else
		cnt_write_addr_load_enable <= '0';
	end if;
end process;

process(cnt_write_addr_high, cnt_write_addr_load_enable)
begin
	if cnt_write_addr_load_enable = '1' then
		cnt_write_addr_high_next <= not cnt_write_addr_high;
	else
		cnt_write_addr_high_next <= cnt_write_addr_high;
	end if;
end process;

-- cnt_write_addr_high counter
process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         cnt_write_addr_high <= '0';
		elsif write_allow = '1' then
			cnt_write_addr_high <= cnt_write_addr_high_next;
		end if;
   end if;
end process;

cnt_write_addr <= cnt_write_addr_high & cnt_write_addr_low;

-- cnt_read_addr_low counter
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_read_addr_low <= conv_std_logic_vector(1, cnt_read_addr_low'length);
      elsif (read_allow = '1') then
			if cnt_read_addr_load_enable = '1' then
				cnt_read_addr_low <= (others => '0');
			else
				cnt_read_addr_low <= cnt_read_addr_low + 1;
			end if;
      end if;
   end if;
end process;

process(cnt_read_addr_low)
begin
	if cnt_read_addr_low = conv_std_logic_vector(ITEMS-1, cnt_read_addr_low'length) then
		cnt_read_addr_load_enable <= '1';
	else
		cnt_read_addr_load_enable <= '0';
	end if;
end process;

process(cnt_read_addr_high, cnt_read_addr_load_enable)
begin
	if cnt_read_addr_load_enable = '1' then
		cnt_read_addr_high_next <= not cnt_read_addr_high;
	else
		cnt_read_addr_high_next <= cnt_read_addr_high;
	end if;
end process;

process(CLK)
begin
   if CLK'event and CLK = '1' then
      if RESET = '1' then
         cnt_read_addr_high <= '0';
		elsif read_allow = '1' then
			cnt_read_addr_high <= cnt_read_addr_high_next;
		end if;
   end if;
end process;

cnt_read_addr <= cnt_read_addr_high & cnt_read_addr_low;

-- reg_write_addr register
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_write_addr <= (others => '0');
      elsif (write_allow = '1') then
         reg_write_addr <= cnt_write_addr;
      end if;
   end if;
end process;

-- reg_read_addr register
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_read_addr <= (others => '0');
      elsif (read_allow = '1') then
         reg_read_addr <= cnt_read_addr;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
--                            Control Logic
-- ----------------------------------------------------------------------------

-- allow logic
read_allow <= sig_rd and (not reg_empty);
write_allow <= WR and (not reg_full);

-- empty, full logic
process(cnt_read_addr, reg_write_addr, read_allow, write_allow)
begin
	if ((cnt_read_addr = reg_write_addr) and (read_allow = '1') and (write_allow = '0')) then
		empty_int <= '1';
	else
		empty_int <= '0';
	end if;
end process;

process(reg_read_addr, cnt_write_addr, write_allow, read_allow)
begin
	if ((reg_read_addr(FADDR downto 0) = cnt_write_addr(FADDR downto 0))
        and (reg_read_addr(FADDR+1) /= cnt_write_addr(FADDR+1))
        and (write_allow = '1') and (read_allow = '0')) then
		full_int <= '1';
	else
		full_int <= '0';
	end if;
end process;

-- reg_empty register
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_empty <= '1';
      elsif ((read_allow = '1') or (write_allow = '1')) then
         reg_empty <= empty_int;
      end if;
   end if;
end process;

-- reg_full register
process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_full <= '0';
      elsif ((write_allow = '1') or (read_allow = '1')) then
         reg_full <= full_int;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------

LAST_BLOCK_DETECTION : if (BLOCK_SIZE > 0) or STATUS_ENABLED generate

process(cnt_diff, read_allow, write_allow)
begin
	if (cnt_diff = BLOCK_SIZE) and (read_allow = '1') and (write_allow = '0') then
		lstblk_plus_one <= '1';
	else
		lstblk_plus_one <= '0';
	end if;
end process;

process(cnt_diff, write_allow, read_allow)
begin
	if (cnt_diff = BLOCK_SIZE + 1 ) and (write_allow = '1') and (read_allow = '0') then
		lstblk_minus_one <= '1';
	else
		lstblk_minus_one <= '0';
	end if;
end process;

-- cnt_diff counter
cnt_diff_ce <= read_allow xor write_allow;
cnt_diff_dir <= read_allow;

process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_diff <= conv_std_logic_vector(ITEMS, cnt_diff'length);
      elsif (cnt_diff_ce = '1') then
         if (cnt_diff_dir = '1') then
            cnt_diff <= cnt_diff + 1;
         else
            cnt_diff <= cnt_diff - 1;
         end if;
      end if;
   end if;
end process;


-- register reg_lstblk
reg_lstblkp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         if (BLOCK_SIZE < ITEMS) then
            reg_lstblk <= '0';
         else
            reg_lstblk <= '1';
         end if;
      elsif (lstblk_plus_one = '1') or (lstblk_minus_one = '1') then
         reg_lstblk <= lstblk_minus_one and not lstblk_plus_one;
      end if;
   end if;
end process;

end generate;

-- ----------------------------------------------------------------------------

-- interface mapping
FULL     <= reg_full;
EMPTY    <= reg_empty;
LSTBLK   <= reg_lstblk;
STATUS   <= cnt_diff;
DO       <= data_out;
DV       <= sig_dv;

end architecture behavioral;
