--
-- buf_mem.vhd - encapsulates BRAM and LUT memory to one component
-- Copyright (C) 2008 CESNET
-- Author(s): Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity BUF_MEM is
  generic(
    LUT_MEMORY : boolean := false;
    DATA_WIDTH : integer := 16;
    ITEMS      : integer := 16;
    OUTPUT_REG : boolean := false
  );

  port(
    CLK      : in  std_logic;
    RESET    : in  std_logic;

    -- Write interface
    WR_ADDR  : in  std_logic_vector(log2(ITEMS)-1 downto 0);
    DATA_IN  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    WRITE    : in  std_logic;

    -- Read interface
    RD_ADDR  : in  std_logic_vector(log2(ITEMS)-1 downto 0);
    DATA_OUT : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DATA_VLD : out std_logic;
    READ     : in  std_logic;
    PIPE_EN  : in  std_logic
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of BUF_MEM is

  signal gnd_item : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal mem_do   : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal reg_do   : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal reg_dv   : std_logic;

-- ----------------------------------------------------------------------------
begin

-- for XST synthesis, conecting port to constrained signal
gnd_item <= (others => '0');

BRAM_MEM : if (LUT_MEMORY = false) generate

  memory : entity work.SDP_BMEM(behavioral)
    generic map (
      DATA_WIDTH => DATA_WIDTH,
      ITEMS      => ITEMS,
      OUTPUT_REG => OUTPUT_REG,
      DEBUG      => false
    )
    port map (
      -- Interface A - write
      CLKA     => CLK,
      RSTA     => RESET,
      WEA      => WRITE,
      ADDRA    => WR_ADDR,
      DIA      => DATA_IN,

      -- Interface B - read
      CLKB     => CLK,
      RSTB     => RESET,
      REB      => READ,
      ADDRB    => RD_ADDR,
      DOB      => DATA_OUT,
      DOB_DV   => DATA_VLD,
      PIPE_ENB => PIPE_EN
    );

end generate;

LUT_MEM : if (LUT_MEMORY = true) generate

  memory : entity work.DP_DISTMEM
    generic map (
      DATA_WIDTH => DATA_WIDTH,
      ITEMS      => ITEMS
    )
    port map (
      WCLK  => CLK,
      WE    => WRITE,
      ADDRA => WR_ADDR,
      DI    => DATA_IN,
      DOA   => open,

      ADDRB => RD_ADDR,
      DOB   => mem_do
    );

    LUT_NO_OUTREG : if (OUTPUT_REG = false) generate
      DATA_VLD <= READ;
      DATA_OUT <= mem_do;
    end generate;

    LUT_GEN_OUTREG : if (OUTPUT_REG = true) generate
      -- register distmem's data out
      reg_dop: process(CLK)
      begin
        if (CLK'event AND CLK = '1') then
           if (PIPE_EN = '1') then
              reg_do <= mem_do;
           end if;
        end if;
      end process;

      -- register data valid signal
      reg_dvp: process(CLK)
      begin
        if (CLK'event AND CLK = '1') then
           if (RESET = '1') then
              reg_dv <= '0';
           elsif (PIPE_EN = '1') then
              reg_dv <= READ;
           end if;
        end if;
      end process;

      DATA_VLD <= reg_dv;
      DATA_OUT <= reg_do;
    end generate;

end generate;

end architecture;
