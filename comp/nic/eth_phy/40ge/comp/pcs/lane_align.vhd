-- lane_align.vhd : Lane alignment for 40/100GE PCS
-- Copyright (C) 2013-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity lane_align_deprecated is
    generic (
        SHIFTS : natural := 16 -- shift register width = lanes skew size
    );
    port (
        RESET         : in std_logic;
        CLK           : in std_logic;
        EN            : in std_logic_vector(4-1 downto 0); -- Input enable for each lane
        D             : in std_logic_vector(4*66-1 downto 0);  -- Input data for each lane
        Q             : out std_logic_vector(4*66-1 downto 0) := (others => '0'); -- Output data for each lane
        QV            : out std_logic := '0'; -- Otput data valid
        BLK_LOCK      : in std_logic_vector(4-1 downto 0);  -- Block lock for each lane
        -- Status ports
        LOCKED        : out std_logic;  -- valid mark found on each lane
        LANE_MAP      : out std_logic_vector(4*5-1 downto 0); -- output mapping for each lane
        LANES_ALIGNED : out std_logic_vector(4-1 downto 0); -- alignment confirmed for eac line
        BIP_ERR_CNTRS : out std_logic_vector((4*16)-1 downto 0); -- BIP error counters out
        CLR_ERR_CNTRS : in  std_logic_vector(4-1 downto 0) := (others => '0'); -- BIP error counters reset

        --DEBUG
        shift_cntrs_reset_DBG   : out std_logic_vector(4-1 downto 0);
        lanes_align_reset_DBG   : out std_logic_vector(4-1 downto 0);
        lane_align_err_DBG      : out std_logic_vector(4-1 downto 0);
        am_invld_cntrs_end_DBG  : out std_logic_vector(4-1 downto 0);
        am_match_DBG            : out std_logic_vector(4*4-1 downto 0);
        am_lock_DBG             : out std_logic_vector(4-1 downto 0);
        am_cntrs_end_DBG        : out std_logic_vector(4-1 downto 0);
        am_found_DBG            : out std_logic_vector(4-1 downto 0);
        bip_match_DBG           : out std_logic_vector(4-1 downto 0);
        bip_err_DBG             : out std_logic_vector(4-1 downto 0)
    );
end lane_align_deprecated;

architecture behavioral of lane_align_deprecated is

constant LANES  : natural := 4;

type t_int_array_shift is array (0 to LANES-1) of natural range 0 to SHIFTS-1;
type t_int_array_lanes is array (0 to LANES-1) of natural range 0 to LANES-1;

type t_shift_r is array (0 to SHIFTS-1) of std_logic_vector(66 downto 0);
type t_shift_r_arr is array (0 to LANES-1) of t_shift_r;

function reg_width(Max : natural) return natural is
variable pow_2_i : positive := 1;
variable i : natural := 0;
begin
   while (pow_2_i <= Max) loop
      i := i + 1;
      pow_2_i := pow_2_i * 2;
   end loop;
   return i;
end function;

function one_hot_to_bin(one_hot : std_logic_vector; bin_width: positive) return std_logic_vector is
variable bin : std_logic_vector(bin_width-1 downto 0) := (others => '0');
begin
   for i in one_hot'range loop
      if (one_hot(i) = '1') then
         bin := conv_std_logic_vector(i,bin_width);
      end if;
   end loop;
   return bin;
end function;

function get_lane_mux_sel(lane_mapping : std_logic_vector) return t_int_array_lanes is
variable lane_mux_sel : t_int_array_lanes := (others => 0);
begin
   for i in t_int_array_lanes'range loop
      lane_mux_sel(conv_integer(lane_mapping(5*(i+1)-1 downto 5*i))) := i;
   end loop;
   return lane_mux_sel;
end function;

signal blk_lock_all               : std_logic; -- block lock on all lanes
signal blk_lock_all_r             : std_logic := '0'; -- block lock on all lanes history register

signal reset_i                    : std_logic := '1'; -- inside reset

signal D_postpipe                 : std_logic_vector(LANES*66-1 downto 0) := (others => '0');  -- Input data for each lane (pipelined)

signal en_blk_lock_prepipe        : std_logic_vector(LANES-1 downto 0); -- lane enable (while block lock)
signal en_blk_lock                : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- pipelined
signal en_r                       : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- lane enable history register
signal en_or                      : std_logic_vector(LANES-1 downto 0);
signal en_all                     : std_logic; -- all lines enabled
signal en_all_r                   : std_logic := '0';

signal am_match_prepipe           : std_logic_vector(LANES*LANES-1 downto 0); -- lane mark index
signal am_match                   : std_logic_vector(LANES*LANES-1 downto 0) := (others => '0'); -- pipelined
signal bip_match_prepipe          : std_logic_vector(LANES-1 downto 0); -- mark BIP match
signal bip_match                  : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- pipelined
signal am_found_prepipe           : std_logic_vector(LANES-1 downto 0); -- mark found
signal am_found_postpipe          : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- pipelined
signal am_found                   : std_logic_vector(LANES-1 downto 0); -- mark found (while mark wanted)
signal am_found_en                : std_logic_vector(LANES-1 downto 0); -- am_found while lane enable

signal bip_err                    : std_logic_vector(LANES-1 downto 0); -- mark found and no BIP match
signal bip_err_cntrs_i            : std_logic_vector((LANES*16)-1 downto 0) := (others => '0'); -- BIP error counters

signal am_lock                    : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- first mark found register
signal am_lock_all                : std_logic; -- first mark found on each lane

signal shift_r                    : t_shift_r_arr := (others => (others => (others => '0'))); -- deskew shift registers
signal shift_di                   : std_logic_vector(LANES*67-1 downto 0); -- skewed input
signal shift_do                   : std_logic_vector(LANES*67-1 downto 0); -- deskewed output
signal shift_lock                 : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- lane deskewed register
signal shift_cntrs_up_en          : std_logic_vector(LANES-1 downto 0); -- deskew enable
signal shift_cntrs_cor_en         : std_logic_vector(LANES-1 downto 0);
signal shift_cntrs_cor_en_r       : std_logic_vector(LANES-1 downto 0) := (others => '0');
signal shift_cntrs_down_en        : std_logic_vector(LANES-1 downto 0);
signal shift_cntrs_reset_prepipe  : std_logic_vector(LANES-1 downto 0); -- deskew error and reset
signal shift_cntrs_reset          : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- pipelined
signal shift_cntrs                : std_logic_vector(LANES*reg_width(SHIFTS-1)-1 downto 0) := (others => '0'); -- deskew counters
signal shift_mapping              : t_int_array_shift; -- shift register output mapping

signal lane_index                 : std_logic_vector(LANES*5-1 downto 0); -- lane current mapping index
signal lane_mapping               : std_logic_vector(LANES*5-1 downto 0) := (others => '0'); -- lane first mapping index register
signal lane_mux_sel               : t_int_array_lanes; -- lane output mapping
signal sh_am_found                : std_logic_vector(LANES-1 downto 0); -- mark found on shift register output
signal am_cntrs                   : std_logic_vector(LANES*14-1 downto 0) := (others => '0'); -- alignment counters
signal am_cntrs_end               : std_logic_vector(LANES-1 downto 0); -- alignment counters highest value
signal lane_am_expect             : std_logic_vector(LANES-1 downto 0); -- mark expected
signal lane_am_valid              : std_logic_vector(LANES-1 downto 0); -- mark found and valid
signal lane_align_ok              : std_logic_vector(LANES-1 downto 0); -- alignment ok
signal lane_align_err             : std_logic_vector(LANES-1 downto 0); -- alignment error
signal lanes_aligned_i            : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- LANES_ALIGNED output register
signal am_invld_cntrs             : std_logic_vector(LANES*2-1 downto 0) := (others => '0'); -- alignment invalid counters
signal am_invld_cntrs_end         : std_logic_vector(LANES-1 downto 0); -- alignment invalid counters highest value
signal lanes_align_reset_prepipe  : std_logic_vector(LANES-1 downto 0); -- lane alignment error and reset
signal lanes_align_reset          : std_logic_vector(LANES-1 downto 0) := (others => '0'); -- pipelined
signal locked_i                   : std_logic := '0'; -- LOCKED output register
signal qi                         : std_logic_vector(LANES*66-1 downto 0); -- Output data
signal qvi                        : std_logic; -- Output data enable
signal am_lock_or_found_en        : std_logic_vector(LANES-1 downto 0);
signal en_r_and_en_all            : std_logic_vector(LANES-1 downto 0);
signal en_blk_lock_and_not_en_all : std_logic_vector(LANES-1 downto 0);
signal en_blk_lock_filt  : std_logic_vector(LANES-1 downto 0);


function AND_REDUCE (D : in std_logic_vector) return std_logic is
variable tmp : std_logic;
begin
   tmp := D(D'right);
   for i in D'right+1 to D'left loop
      tmp := tmp and D(i);
   end loop;
   return tmp;
end function AND_REDUCE;

function OR_REDUCE (D : in std_logic_vector) return std_logic is
variable tmp : std_logic;
begin
   tmp := D(D'right);
   for i in D'right+1 to D'left loop
      tmp := tmp or D(i);
   end loop;
   return tmp;
end function OR_REDUCE;


begin


-- block_lock control
blk_lock_all <= AND_REDUCE(BLK_LOCK);

BLK_LOCK_ALL_P: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         blk_lock_all_r <= '0';
      elsif (blk_lock_all = '1') then
         blk_lock_all_r <= '1';
      end if;
   end if;
end process;


-- inner reset
reset_i <=  RESET or (not OR_REDUCE(BLK_LOCK)) or (blk_lock_all_r and (not blk_lock_all)) -- inside reset activation
            or OR_REDUCE(shift_cntrs_reset) or OR_REDUCE(lanes_align_reset);

en_blk_lock_prepipe <= EN and BLK_LOCK;

-- PIPELINE to cut critical path
PIPE_P: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         en_blk_lock        <= (others => '0');
         en_blk_lock        <= (others => '0');
         -- D_postpipe         <= (others => '0');
         am_found_postpipe  <= (others => '0');
         am_match           <= (others => '0');
         bip_match          <= (others => '0');
         shift_cntrs_reset  <= (others => '0');
         lanes_align_reset  <= (others => '0');
      else
         en_blk_lock        <= en_blk_lock_prepipe;
         -- D_postpipe         <= D;
         am_found_postpipe  <= am_found_prepipe;
         am_match           <= am_match_prepipe;
         bip_match          <= bip_match_prepipe;
         shift_cntrs_reset  <= shift_cntrs_reset_prepipe;
         lanes_align_reset  <= lanes_align_reset_prepipe;
      end if;
   end if;
end process;

-- PIPELINE to cut critical path - without reset
PIPE_NORST: process(CLK)
begin
   if CLK'event and CLK = '1' then
      D_postpipe         <= D;
   end if;
end process;

-- inter-lanes signals
en_or <= en_r or en_blk_lock;
en_all <= AND_REDUCE(en_or);

am_lock_or_found_en <= am_lock or am_found_en;
am_lock_all <= AND_REDUCE(am_lock_or_found_en);

-- deskew correction enable
shift_cntrs_cor_en <= en_blk_lock and en_r_and_en_all and shift_lock;

-- en_all history register
EN_ALL_R_P: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         en_all_r <= '0';
      else
         en_all_r <= en_all;
      end if;
   end if;
end process;

-- deskew correction history register
SHIFT_CNTRS_COR_EN_R_P: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         shift_cntrs_cor_en_r <= (others => '0');
      else
         shift_cntrs_cor_en_r <= shift_cntrs_cor_en;
      end if;
   end if;
end process;

-- generate for each lane
GEN_AM_LOOKUP: for i in 0 to LANES-1 generate
signal local_am_match : std_logic_vector(LANES-1 downto 0);
begin

   en_r_and_en_all(i) <= en_r(i) and en_all;
   en_blk_lock_and_not_en_all(i) <= en_blk_lock(i) and (not en_all);

   en_blk_lock_filt(i) <= '0' when (shift_lock(i) = '0') and (en_all = '1') else en_blk_lock(i);

   -- lane enable (while block lock) history register
   EN_CONTROL: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            en_r(i) <= '0';
         elsif (en_blk_lock_and_not_en_all(i) = '1') or (en_r_and_en_all(i) = '1') then
            en_r(i) <= en_blk_lock_filt(i);
         end if;
      end if;
   end process;

   AM_LOOKUP_4: entity work.am_check_4
   port map (
       RESET     => am_found_prepipe(i),
       CLK       => CLK,
       EN        => en_blk_lock_prepipe(i),
       D         => D(66*(i+1)-1 downto 66*i),
       MATCH     => am_match_prepipe(LANES*(i+1)-1 downto LANES*i),
       BIP_MATCH => bip_match_prepipe(i)
   );

   -- test if marker found on lane
   am_found_prepipe(i) <= OR_REDUCE(am_match_prepipe(LANES*(i+1)-1 downto LANES*i));
   am_found(i) <= am_found_postpipe(i) and ((not am_lock(i)) or am_cntrs_end(i));
   am_found_en(i) <= en_blk_lock(i) and am_found(i);


   -- test if BIP error occured
   bip_err(i) <= am_found_en(i) and (not bip_match(i)) and lanes_aligned_i(i);

   -- BIP error counter
   ERR_CNTRS : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (RESET = '1') or (CLR_ERR_CNTRS(i) = '1') then
            bip_err_cntrs_i((i+1)*16-1 downto i*16) <= (others => '0');
         elsif (bip_err(i) = '1') and (bip_err_cntrs_i((i+1)*16-1 downto i*16) /= X"FFFF") then
            bip_err_cntrs_i((i+1)*16-1 downto i*16) <= bip_err_cntrs_i((i+1)*16-1 downto i*16) + 1;
         end if;
      end if;
   end process;


   -- first mark found register
   AM_LOCK_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            am_lock(i) <= '0';
         elsif (am_found_en(i) = '1') then
            am_lock(i) <= '1';
         end if;
      end if;
   end process;


   shift_di(67*(i+1)-2 downto 67*i) <= D_postpipe(66*(i+1)-1 downto 66*i);
   shift_di(67*(i+1)-1) <= am_found(i);

   -- deskew shift register
   SHIFT_REG: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (en_blk_lock(i) = '1') then
            shift_r(i) <= shift_di(67*(i+1)-1 downto 67*i) & shift_r(i)(0 to SHIFTS-2);
         end if;
      end if;
   end process;

   -- lane deskewed register
   SHIFT_LOCK_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            shift_lock(i) <= '0';
         elsif (en_or(i) = '1') and (am_lock_all = '1') then
            shift_lock(i) <= '1';
         end if;
      end if;
   end process;

   -- deskew enable
   shift_cntrs_up_en(i) <= (en_blk_lock(i) and am_lock(i) and (not shift_lock(i))) or (shift_cntrs_cor_en(i) and (not shift_cntrs_cor_en_r(i)));
   shift_cntrs_down_en(i) <= shift_cntrs_cor_en_r(i) and (not shift_cntrs_cor_en(i));
   -- deskew error and reset
   shift_cntrs_reset_prepipe(i) <= '1' when (shift_cntrs_up_en(i) = '1') and (shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) = SHIFTS-1) else '0';

   -- deskew counter
   SHIFT_CNTR: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) <= (others => '0');
         elsif (shift_cntrs_up_en(i) = '1') then
            shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) <= shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) + 1;
         elsif (shift_cntrs_down_en(i) = '1') then
            shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) <= shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i) - 1;
         end if;
      end if;
   end process;

   -- shift register output mapping
   shift_mapping(i) <= conv_integer(shift_cntrs(reg_width(SHIFTS-1)*(i+1)-1 downto reg_width(SHIFTS-1)*i));

   -- shift register output multiplexer
   shift_do(67*(i+1)-1 downto 67*i) <= shift_r(i)(shift_mapping(i));


   -- compute lane current mapping index
   local_am_match <= am_match(LANES*(i+1)-1 downto LANES*i);
   lane_index((i+1)*5-1 downto i*5) <= one_hot_to_bin(local_am_match,5);

   -- lane_first mapping index register
   LANE_MAPPING_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            lane_mapping(5*(i+1)-1 downto 5*i) <= (others => '0');
         elsif (am_found_en(i) = '1') and (am_lock(i) = '0') then
            lane_mapping(5*(i+1)-1 downto 5*i) <= lane_index(5*(i+1)-1 downto 5*i);
         end if;
      end if;
   end process;

   FOUR_LANE_MUX: process(shift_do, lane_mux_sel(i))
   begin
      case lane_mux_sel(i) is
         when 0 => qi(66*(i+1)-1 downto i*66) <= shift_do(67*1-2 downto 67*0);
         when 1 => qi(66*(i+1)-1 downto i*66) <= shift_do(67*2-2 downto 67*1);
         when 2 => qi(66*(i+1)-1 downto i*66) <= shift_do(67*3-2 downto 67*2);
         when 3 => qi(66*(i+1)-1 downto i*66) <= shift_do(67*4-2 downto 67*3);
         when others => qi(66*(i+1)-1 downto i*66) <= (others => '-');
      end case;
   end process;

   -- mark found on shift register output
   sh_am_found(i) <= shift_do(67*(i+1)-1);


   -- alignment counter
   AM_CNTRS_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            am_cntrs(14*(i+1)-1 downto 14*i) <= (others => '0');
         elsif (en_blk_lock(i) = '1') and (am_lock(i) = '1') then
            am_cntrs(14*(i+1)-1 downto 14*i) <= am_cntrs(14*(i+1)-1 downto 14*i) + 1;
         end if;
      end if;
   end process;

   -- alignment counter highest value
   am_cntrs_end(i) <= AND_REDUCE(am_cntrs(14*(i+1)-1 downto 14*i));

   -- mark expected
   lane_am_expect(i) <= en_blk_lock(i) and am_cntrs_end(i);
   -- mark found and valid
   lane_am_valid(i) <= '1' when (am_found(i) = '1') and (lane_index(5*(i+1)-1 downto 5*i) = lane_mapping(5*(i+1)-1 downto 5*i)) else '0';

   --alignment ok
   lane_align_ok(i) <= lane_am_expect(i) and lane_am_valid(i);
   -- alignment error
   lane_align_err(i) <= lane_am_expect(i) and (not lane_am_valid(i));

   -- LANES_ALIGNED output register
   LANES_ALIGNED_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') then
            lanes_aligned_i(i) <= '0';
         elsif (lane_align_ok(i) = '1') then
            lanes_aligned_i(i) <= '1';
         end if;
      end if;
   end process;

   -- alignment invalid counter
   AM_INVLD_CNTRS_P: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (reset_i = '1') or (lane_align_ok(i) = '1') then
            am_invld_cntrs(2*(i+1)-1 downto i*2) <= (others => '0');
         elsif (lane_align_err(i) = '1') then
            am_invld_cntrs(2*(i+1)-1 downto i*2) <= am_invld_cntrs(2*(i+1)-1 downto i*2) + 1;
         end if;
      end if;
   end process;

   -- alignment invalid counter highest value
   am_invld_cntrs_end(i) <= AND_REDUCE(am_invld_cntrs(2*(i+1)-1 downto i*2));

   -- lane alignment error and reset
   lanes_align_reset_prepipe(i) <= lane_align_err(i) and ((not lanes_aligned_i(i)) or (lanes_aligned_i(i) and am_invld_cntrs_end(i)));

end generate;

-- lanes output multiplexers reordering select
lane_mux_sel <= get_lane_mux_sel(lane_mapping);

-- LOCKED output register
AM_LOCKED_P: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         locked_i <= '0';
      elsif (am_lock_all = '1') then
         locked_i <= '1';
      end if;
   end if;
end process;

-- output assignment
LOCKED        <= locked_i;
LANES_ALIGNED <= lanes_aligned_i;
BIP_ERR_CNTRS <= bip_err_cntrs_i;
LANE_MAP      <= lane_mapping;

-- output enable
qvi <= en_all_r and AND_REDUCE(lanes_aligned_i) and (not OR_REDUCE(sh_am_found));

-- output data and data enable registers
OUTPUT_REGS: process(CLK)
begin
   if CLK'event and CLK = '1' then
      if (reset_i = '1') then
         QV <= '0';
      else
         QV <= qvi;
      end if;
      Q <= qi;
   end if;
end process;

-- DEBUG
shift_cntrs_reset_DBG   <= shift_cntrs_reset;
lanes_align_reset_DBG   <= lanes_align_reset;
lane_align_err_DBG      <= lane_align_err;
am_invld_cntrs_end_DBG  <= am_invld_cntrs_end;

am_match_DBG      <= am_match;
am_lock_DBG       <= am_lock;
am_cntrs_end_DBG  <= am_cntrs_end;
am_found_DBG      <= am_found;
bip_match_DBG     <= bip_match;
bip_err_DBG       <= bip_err;

end behavioral;
