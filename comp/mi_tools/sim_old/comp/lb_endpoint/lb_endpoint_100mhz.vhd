--
-- lb_endpoint_100mhz.vhd: Internal Bus End Point Component
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.lb_pkg.all; -- Internal Bus package
use work.math_pack.all; -- Math Pack

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ENDPOINT_100 is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0);
      LIMIT            : std_logic_vector(31 downto 0);
      BUFFER_EN        : boolean
   );
   port(
      -- Common Interface
      RESET         : in std_logic;

      -- Local Bus Interface
      LB_CLK        : in std_logic;
      LB_DWR        : in std_logic_vector(15 downto 0);
      LB_BE         : in std_logic_vector(1 downto 0);
      LB_ADS_N      : in std_logic;
      LB_RD_N       : in std_logic;
      LB_WR_N       : in std_logic;
      LB_DRD        : out std_logic_vector(15 downto 0);
      LB_RDY_N      : out std_logic;
      LB_ERR_N      : out std_logic;
      LB_ABORT_N    : in  std_logic;

      -- User Component Interface
      CLK           : in  std_logic;
      MI32_DWR      : out std_logic_vector(31 downto 0);           -- Input Data
      MI32_ADDR     : out std_logic_vector(31 downto 0);           -- Address
      MI32_RD       : out std_logic;                               -- Read Request
      MI32_WR       : out std_logic;                               -- Write Request
      MI32_BE       : out std_logic_vector(3  downto 0);           -- Byte Enable
      MI32_DRD      : in  std_logic_vector(31 downto 0);           -- Output Data
      MI32_ARDY     : in  std_logic;                               -- Address Ready
      MI32_DRDY     : in  std_logic                                -- Data Ready
  );
end entity LB_ENDPOINT_100;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ENDPOINT_100_ARCH of LB_ENDPOINT_100 is

    constant ADDR_WIDTH : integer:= log2(LIMIT);

    -- Abort (lb2adc reset)
    signal lb_endpoint_reset        : std_logic;

    -- Read/Write Address decoder and counter signals
    signal aux_addr            : std_logic_vector(31 downto 0);
    signal addr_match          : std_logic;
    signal ads_cnt             : std_logic;
    signal addr_cnt            : std_logic_vector(31 downto 0);
    signal addr_cnt_en         : std_logic;
    signal addr_match_reg      : std_logic;

    -- User component signals generation
    signal wr_reg              : std_logic;
    signal in_cnt              : std_logic;
    signal dwr_low_reg         : std_logic_vector(15 downto 0);
    signal be_low_reg          : std_logic_vector(1 downto 0);
    signal drd_mux             : std_logic_vector(15 downto 0);
    signal drd_mux_sel         : std_logic_vector(1 downto 0);
    signal drd_high_reg        : std_logic_vector(15 downto 0);
    signal drdy_pipe           : std_logic;
    signal ardy_pipe           : std_logic;

    -- Buffer signals
    signal shr_dwr             : std_logic_vector(15 downto 0);
    signal shr_be              : std_logic_vector(1 downto 0);
    signal shr_wr_n            : std_logic;
    signal shr_rd_n            : std_logic;
    signal shr_vld             : std_logic;
    signal shr_read            : std_logic;
    signal mi32_rd_out         : std_logic;
    signal mi32_wr_out         : std_logic;
    signal mi32_ardy_aux           : std_logic;

begin
-- ----------------------------------------------------------------------------
-- RESET GENERATION
-- ----------------------------------------------------------------------------
-- LB2ADC RESET generation
lb_endpoint_reset <= RESET or not LB_ABORT_N;

-- ----------------------------------------------------------------------------
-- ARDY GENERATION (solve problem when ardy is always '1')
-- ----------------------------------------------------------------------------
mi32_ardy_aux <= MI32_ARDY and (mi32_rd_out or mi32_wr_out);


-- ----------------------------------------------------------------------------
-- ADDRESS DECODER
-- ----------------------------------------------------------------------------
aux_addr      <= LB_DWR & addr_cnt(15 downto 0);
addr_match    <= '1' when aux_addr(31 downto ADDR_WIDTH) = BASE_ADDR(31 downto ADDR_WIDTH) else '0';

-- register addr_match_reg ----------------------------------------------------
addr_match_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         addr_match_reg <= '0';
      else
         if (LB_ADS_N = '0' and ads_cnt = '1') then
           addr_match_reg <= addr_match;
         end if;
         if (LB_ADS_N = '0' and ads_cnt = '0') then
           addr_match_reg <= '0';
         end if;
      end if;
   end if;
end process;

-- ads_cnt counter ------------------------------------------------------------
ads_counterp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         ads_cnt <= '0';
      elsif (LB_ADS_N = '0') then
         ads_cnt <= not ads_cnt;
      end if;
   end if;
end process;

-- ----------------------------------------------------------------------------
-- ADDRESS REGISTER AND ADDRESS COUNTER
-- ----------------------------------------------------------------------------
-- addr_cnt counter -----------------------------------------------------------
addr_cntp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         addr_cnt <= (others => '0');
      else
         if (LB_ADS_N = '0' and ads_cnt = '0') then
            addr_cnt(15 downto 0) <= LB_DWR;
         end if;
         if (LB_ADS_N = '0' and ads_cnt = '1') then
            addr_cnt(31 downto 16) <= LB_DWR;
         end if;
         if (addr_cnt_en = '1') then
            addr_cnt <= addr_cnt + 4;
         end if;
      end if;
   end if;
end process;


-- --------------------------------------------------------------------------
-- MI32_DRD and MI32_DRDY PART
-- --------------------------------------------------------------------------

-- drd_high registers -------------------------------------------------------
drd_high_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         drd_high_reg <= (others => '0');
      elsif (MI32_DRDY = '1') then
        drd_high_reg <= MI32_DRD(31 downto 16);
      end if;
   end if;
end process;

drd_mux_sel <= MI32_DRDY & drdy_pipe;
-- When no drd drd_mux must be 0 due to switch (drd is ored from all ports)
-- multiplexor drd_mux ------------------------------------------------------
drd_muxp: process(drd_mux_sel, drd_high_reg, MI32_DRD)
begin
   case drd_mux_sel is
      when "10" => drd_mux <= MI32_DRD(15 downto 0);
      when "01" => drd_mux <= drd_high_reg;
      when others => drd_mux <= (others => '0');
   end case;
end process;

-- drdy pipe ----------------------------------------------------------------
drdy_pipep: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         drdy_pipe  <= '0';
      else
         drdy_pipe  <= MI32_DRDY;
      end if;
   end if;
end process;

-- ardy pipe ----------------------------------------------------------------
ardy_pipep: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         ardy_pipe  <= '0';
      else
         ardy_pipe  <= mi32_ardy_aux;
      end if;
   end if;
end process;



-- ----------------------------------------------------------------------------
-- ENDPOINT WITH NO WRITE BUFFER
-- ----------------------------------------------------------------------------
BUFFER_NOT_EN_GEN : if (not BUFFER_EN) generate

-- register wr_reg ------------------------------------------------------------
wr_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         wr_reg <= '0';
      else
         if (LB_WR_N = '0') then
           wr_reg <= '1';
         end if;
         if (LB_ADS_N = '0') then
           wr_reg <= '0';
         end if;
      end if;
   end if;
end process;

-- in_cnt ---------------------------------------------------------------------
in_cnt_cntp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         in_cnt <= '0';
      elsif (LB_RD_N = '0' or LB_WR_N = '0') then
        in_cnt <= not in_cnt;
      end if;
   end if;
end process;

-- data_be_low registers ------------------------------------------------------
data_be_low_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         dwr_low_reg  <= (others => '0');
         be_low_reg   <= (others => '0');
      elsif ((LB_WR_N = '0' or LB_RD_N = '0') and in_cnt = '0') then
        dwr_low_reg <= LB_DWR;
        be_low_reg  <= LB_BE;
      end if;
   end if;
end process;


MI32_DWR            <= LB_DWR & dwr_low_reg;
MI32_BE             <= LB_BE  & be_low_reg;

MI32_ADDR(ADDR_WIDTH-1 downto 0)   <= addr_cnt(ADDR_WIDTH-1 downto 0);
MI32_ADDR(31 downto ADDR_WIDTH)    <= (others => '0');

addr_cnt_en         <= mi32_ardy_aux;
MI32_RD             <= in_cnt and not LB_RD_N and addr_match_reg;
MI32_WR             <= in_cnt and not LB_WR_N and addr_match_reg;
mi32_rd_out         <= in_cnt and not LB_RD_N and addr_match_reg;
mi32_wr_out         <= in_cnt and not LB_WR_N and addr_match_reg;
LB_DRD   <= drd_mux;
LB_RDY_N <= not ((MI32_DRDY or drdy_pipe) or ( (mi32_ardy_aux or ardy_pipe) and wr_reg));
LB_ERR_N <= '1';


end generate;


-- ----------------------------------------------------------------------------
-- ENDPOINT WITH WRITE BUFFER
-- ----------------------------------------------------------------------------
BUFFER_EN_GEN : if (BUFFER_EN) generate

-- ----------------------------------------------------------------------------
LB_ENDPOINT_BUFFER_U : entity work.LB_ENDPOINT_BUFFER
   port map (
      -- Common Interface
      CLK           => LB_CLK,
      RESET         => lb_endpoint_reset,

      -- Input Interface
      ADDR_SEL      => addr_match_reg,
      DATA_IN       => LB_DWR,
      BE_IN         => LB_BE,
      WR_IN         => LB_WR_N,
      RD_IN         => LB_RD_N,

      --Output Interface
      DATA_OUT      => shr_dwr,
      BE_OUT        => shr_be,
      WR_OUT        => shr_wr_n,
      RD_OUT        => shr_rd_n,
      DATA_OUT_VLD  => shr_vld,
      BUFFER_RD     => shr_read
      );


-- register wr_reg ------------------------------------------------------------
wr_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         wr_reg <= '0';
      else
         if (shr_wr_n = '0' and shr_vld = '1') then
           wr_reg <= '1';
         end if;
         if (LB_ADS_N = '0') then
           wr_reg <= '0';
         end if;
      end if;
   end if;
end process;

-- in_cnt -----------------------------------------------------------
in_cntp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         in_cnt <= '0';
      else
         if (shr_vld = '1' and in_cnt='0') then
           in_cnt <= '1';
         end if;
         if  (shr_vld = '1' and in_cnt='1' and mi32_ardy_aux = '1') then
           in_cnt <= '0';
         end if;
      end if;
   end if;
end process;

-- data_be_low registers ------------------------------------------------------
data_be_low_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         dwr_low_reg  <= (others => '0');
         be_low_reg   <= (others => '0');
      elsif ((shr_rd_n = '0' or shr_wr_n = '0') and shr_vld = '1' and in_cnt = '0') then
        dwr_low_reg <= shr_dwr;
        be_low_reg  <= shr_be;
      end if;
   end if;
end process;

shr_read      <= '1' when in_cnt = '0' or mi32_ardy_aux = '1' else '0';
MI32_DWR            <= shr_dwr & dwr_low_reg;
MI32_BE             <= shr_be & be_low_reg;
MI32_ADDR(ADDR_WIDTH-1 downto 0)   <= addr_cnt(ADDR_WIDTH-1 downto 0);
MI32_ADDR(31 downto ADDR_WIDTH)    <= (others => '0');
addr_cnt_en    <= mi32_ardy_aux;
MI32_RD             <= in_cnt and not shr_rd_n and shr_vld and addr_match_reg;
MI32_WR             <= in_cnt and not shr_wr_n and shr_vld and addr_match_reg;
mi32_rd_out         <= in_cnt and not shr_rd_n and shr_vld and addr_match_reg;
mi32_wr_out         <= in_cnt and not shr_wr_n and shr_vld and addr_match_reg;
LB_DRD   <= drd_mux;
LB_RDY_N <= not ((MI32_DRDY or drdy_pipe) or ( (mi32_ardy_aux or ardy_pipe) and wr_reg));
LB_ERR_N <= '1';
end generate;

end architecture LB_ENDPOINT_100_ARCH;
