--
-- sh_reg_base_dynamic_arch.vhd: generic buss from Shift Register
-- Copyright (C) 2015 CESNET
-- Author(s): Radek Isa <xisara00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        architectuere
-- ----------------------------------------------------------------------------

architecture sh_reg_dynamic_arch of SH_REG_BASE_DYNAMIC is

  --constants
  constant OPT_THRESHOLD : integer := 16;

  constant DEVICE_HAS_SRL16E : boolean := (DEVICE = "7SERIES" or DEVICE = "ULTRASCALE")
  --pragma synthesis_off
    and false
  --pragma synthesis_on
  ;


  --signals in/out data
  signal sig_in  : std_logic_vector(DATA_WIDTH -1 downto 0);
  signal sig_out : std_logic_vector(DATA_WIDTH -1 downto 0);


  -- type
  type array_slv is array (DATA_WIDTH -1 downto 0) of std_logic_vector(NUM_BITS -1 downto 0);

  ------------------------
  -- conversion function
  function sh_reg_init_conv  return array_slv is
    variable out_init : array_slv;
  begin
    --type of init
    --if (INIT_TYPE = 0) then
    for i in  (DATA_WIDTH -1) downto 0 loop
      out_init(i) := (others => '0');
    end loop;

    if (INIT_TYPE = 1) then
      for i in (DATA_WIDTH -1) downto 0 loop
        out_init(i) := INIT(0 to NUM_BITS-1);
      end loop;
    elsif (INIT_TYPE = 2) then
      for i in (DATA_WIDTH -1) downto 0 loop
        for k in (NUM_BITS -1) downto 0 loop
          out_init(i)(k) := INIT(DATA_WIDTH -1 - i);
        end loop;
      end loop;
    elsif (INIT_TYPE = 3) then
       for i in (DATA_WIDTH -1) downto 0 loop
        for k in (NUM_BITS -1) downto 0 loop
          out_init(i)(k) := INIT(DATA_WIDTH*NUM_BITS -1 - k*DATA_WIDTH - i);
        end loop;
      end loop;
    end if;

    --return value
    return out_init;
  end sh_reg_init_conv;


  ------------------------------
  -- conversion function to init srl register
  function sh_reg_init_conv_srl (poz : integer) return std_logic_vector is
    variable ret : std_logic_vector(15 downto 0);
  begin
    -- set 0 to all values
    ret := (others => '0');

    if(INIT_TYPE = 1) then
      ret(NUM_BITS-1 downto 0) := INIT(0 to NUM_BITS -1);
    elsif (INIT_TYPE = 2) then
      for i in (NUM_BITS-1) downto 0 loop
        ret(i) := INIT(DATA_WIDTH -1 -poz);
      end loop;
    elsif (INIT_TYPE = 3) then
      for i in (NUM_BITS-1) downto 0 loop
        ret(i) := INIT(DATA_WIDTH*NUM_BITS -1 - i*DATA_WIDTH - poz);
      end loop;
    end if;

    return ret;
  end sh_reg_init_conv_srl;


  -------------------------------------
  -- choose optimalization betven REG, VIVADO
  function get_shreg_extract_opt return string is
  begin
    if (OPT = "REG") then
      return "no";
    end if;

    -- default value
    return "yes";
  end get_shreg_extract_opt;


  -- AREA, SPEED, BALANCE, OFF
  -- attribute OPTIMIZE : string;
  -- attribute OPTIMIZE of sh_reg_dynamic_arch : architecture is "AREA";

   component SRL16E
   generic (
      INIT            : bit_vector(15 downto 0);
      IS_CLK_INVERTED : bit
   );
   port (
      Q   : out std_logic;
      CE  : in  std_logic;
      CLK : in  std_logic;
      D   : in  std_logic;
      A0  : in  std_logic;
      A1  : in  std_logic;
      A2  : in  std_logic;
      A3  : in  std_logic
   );
   end component;

begin

  -------------------------------
  -- I/O signals
  sig_in <= DIN;
  DOUT   <= sig_out;




    --SH_REG_VIVADO : if (NUM_BITS > OPT_THRESHOLD or OPTIMALIZATION = "VIVADO") generate
    SH_REG_VIVADO : if ((not DEVICE_HAS_SRL16E) or NUM_BITS > OPT_THRESHOLD or OPT /= "SRL") generate
      signal sig_addr : std_logic_vector(log2(NUM_BITS) -1  downto 0);
    begin
      -- adress
      sig_addr <= ADDR;

    -------------------------------------
    -- CLK not invertid
    SH_REG_VIVADO_NOT_CLK_INVERTED : if(IS_CLK_INVERTED = '0') generate
      signal reg_shift : array_slv := sh_reg_init_conv;

      attribute SHREG_EXTRACT : string;
      attribute SHREG_EXTRACT of reg_shift : signal is get_shreg_extract_opt; -- "no" => REG, "yes" => VIVADO
    begin
      process (CLK)
      begin
         if CLK='1' and CLK'event then
            if CE = '1' then
             for i in 0 to DATA_WIDTH-1 loop
                 reg_shift(i) <= reg_shift(i)(NUM_BITS-2 downto 0) & sig_in(i);
             end loop;
            end if;
         end if;
      end process;

      process(reg_shift,sig_addr)
      begin
         for i in 0 to DATA_WIDTH-1 loop
            sig_out(i) <= reg_shift(i)(conv_integer(sig_addr));
         end loop;
      end process;
    end generate;

    -------------------------------------
    -- CLK invertid
    SH_REG_VIVADO_CLK_INVERTED : if( IS_CLK_INVERTED = '1') generate
      signal reg_shift : array_slv := sh_reg_init_conv;

      attribute SHREG_EXTRACT : string;
      attribute SHREG_EXTRACT of reg_shift : signal is get_shreg_extract_opt; -- "no" => REG, "yes" => VIVADO
    begin
      process (CLK)
      begin
         if CLK='0' and CLK'event then
            if CE = '1' then
             for i in 0 to DATA_WIDTH-1 loop
                 reg_shift(i) <= reg_shift(i)(NUM_BITS-2 downto 0) & sig_in(i);
             end loop;
            end if;
         end if;
      end process;

      process(reg_shift,sig_addr)
      begin
         for i in 0 to DATA_WIDTH-1 loop
            sig_out(i) <= reg_shift(i)(conv_integer(sig_addr));
         end loop;
      end process;
    end generate;
  --end generate optimalization
  end generate;







  --------------------------------------------
  -- 16- bit
  SH_REG_SRL : if (DEVICE_HAS_SRL16E and NUM_BITS  <= OPT_THRESHOLD and OPT = "SRL") generate
    constant ADDR_MAX   : integer := 3;
    constant ADDR_SPLIT : integer := ADDR'left;
    signal sig_addr : std_logic_vector(3 downto 0);
  begin
    --addres if ADDR is to small
    sig_addr(ADDR_MAX   downto ADDR_SPLIT +1) <= (others => '0');
    sig_addr(ADDR_SPLIT downto 0) <= ADDR;


    --generate data width
    SH_REG_SRL_WIDTH: for i in (DATA_WIDTH -1) downto 0 generate
      SH_REG_SRL16 : SRL16E
        generic map(
          INIT => to_bitvector(sh_reg_init_conv_srl(i)),
          IS_CLK_INVERTED => IS_CLK_INVERTED
        )
        port map(
           --output
          Q   => sig_out(i),
          CE  => CE,
          CLK => CLK,
          D   => sig_in(i),

          A0 => sig_addr(0),
          A1 => sig_addr(1),
          A2 => sig_addr(2),
          A3 => sig_addr(3)
        );
    end generate;
  end generate;


end sh_reg_dynamic_arch;





