--
-- lb_endpoint_50mhz.vhd: Internal Bus End Point Component
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
entity LB_ENDPOINT_50 is
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
end entity LB_ENDPOINT_50;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ENDPOINT_50_ARCH of LB_ENDPOINT_50 is


    constant ADDR_WIDTH : integer:= log2(LIMIT);

    -- Abort (lb2adc reset)
    signal lb_endpoint_reset        : std_logic;

    -- Read/Write Address decoder and counter signals
    signal aux_addr            : std_logic_vector(31 downto 0);
    signal addr_match          : std_logic;
    signal ads_cnt             : std_logic;
    signal addr_reg            : std_logic_vector(31 downto 0);
    signal addr_match_reg      : std_logic;
    signal addr_cnt50_we       : std_logic;
    signal addr_cnt50          : std_logic_vector(31 downto 0);

    -- User component signals generation
    signal wr_reg              : std_logic;
    signal in_cnt              : std_logic;
    signal dwr_low_reg         : std_logic_vector(15 downto 0);
    signal be_low_reg          : std_logic_vector(1 downto 0);
    signal drd_mux             : std_logic_vector(15 downto 0);
    signal drd_mux_sel         : std_logic_vector(1 downto 0);

    -- Buffer signals
    signal shr_dwr     : std_logic_vector(15 downto 0);
    signal shr_be       : std_logic_vector(1 downto 0);
    signal shr_wr_n     : std_logic;
    signal shr_rd_n     : std_logic;
    signal shr_vld : std_logic;
    signal shr_read           : std_logic;

    signal reg1_rd              : std_logic;
    signal reg1_wr              : std_logic;
    signal reg2_rd              : std_logic;
    signal reg2_wr              : std_logic;
    signal dwr1_reg             : std_logic_vector(31 downto 0);
    signal be1_reg              : std_logic_vector(3 downto 0);
    signal drdy_reg50           : std_logic;
    signal drd_reg50            : std_logic_vector(31 downto 0);
    signal ardy_reg50           : std_logic;
    signal first_reg            : std_logic;
    signal first_reg_pipe       : std_logic;

    signal drdy_cnt             : std_logic;
    signal lb_drd_reg           : std_logic_vector(15 downto 0);
    signal lb_rdy_n_reg         : std_logic;
    signal mi32_rd_out          : std_logic;
    signal mi32_wr_out          : std_logic;
    signal mi32_ardy_aux            : std_logic;

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
aux_addr      <= LB_DWR & addr_reg(15 downto 0);
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
-- addr_reg -------------------------------------------------------------------
addr_regp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         addr_reg <= (others => '0');
      else
         if (LB_ADS_N = '0' and ads_cnt = '0') then
            addr_reg(15 downto 0) <= LB_DWR;
         end if;
         if (LB_ADS_N = '0' and ads_cnt = '1') then
            addr_reg(31 downto 16) <= LB_DWR;
         end if;
      end if;
   end if;
end process;

-- addr_cnt50 counter ---------------------------------------------------------
addr_cnt50p: process(lb_endpoint_reset, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (lb_endpoint_reset = '1') then
         addr_cnt50 <= (others => '0');
      else
         if (addr_cnt50_we = '0') then
            addr_cnt50 <= addr_reg;
         end if;
         if (mi32_ardy_aux = '1') then
            addr_cnt50 <= addr_cnt50 + 4;
         end if;
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------
-- MI32_DRD and MI32_DRDY PART
-- --------------------------------------------------------------------------
-- drdy_cnt -----------------------------------------------------------------
drdy_cntp: process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         drdy_cnt <= '0';
      elsif (drdy_reg50 = '1') then
        drdy_cnt <= not drdy_cnt;
      end if;
   end if;
end process;

drd_mux_sel <= drdy_reg50 & drdy_cnt;
-- When no drd drd_mux must be 0 due to switch (drd is ored from all ports)
-- multiplexor drd_mux ------------------------------------------------------
drd_muxp: process(drd_mux_sel, drd_reg50)
begin
   case drd_mux_sel is
      when "10" => drd_mux <= drd_reg50(15 downto 0);
      when "11" => drd_mux <= drd_reg50(31 downto 16);
      when others => drd_mux <= (others => '0');
   end case;
end process;


-- ----------------------------------------------------------------------------
-- ENDPOINT WITH NO WRITE BUFFER
-- ----------------------------------------------------------------------------
BUFFER_NOT_EN_GEN : if (not BUFFER_EN) generate

-- register wr_reg ------------------------------------------------------------
-- Used for rdy_n generation (ardy and rdy_n)
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

-- in_cnt -----------------------------------------------------------
-- Used for writing data_low or data_high
in_cntp: process(lb_endpoint_reset, LB_CLK)
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
      elsif ( (LB_WR_N = '0' or LB_RD_N = '0') and in_cnt = '0') then
         dwr_low_reg <= LB_DWR;
         be_low_reg  <= LB_BE;
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------
-- LB CLK Registers
-- --------------------------------------------------------------------------
LB_RDY_N <= lb_rdy_n_reg;
LB_DRD   <= lb_drd_reg;
LB_ERR_N <= '1';

process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         reg1_rd      <= '0';
         reg1_wr      <= '0';
         reg2_rd      <= '0';
         reg2_wr      <= '0';
         dwr1_reg     <= (others => '0');
         be1_reg      <= (others => '0');
         lb_drd_reg   <= (others => '0');
         lb_rdy_n_reg <= '1';
      else
         if (in_cnt='1') then
            dwr1_reg   <= LB_DWR & dwr_low_reg;
            be1_reg    <= LB_BE  & be_low_reg;
         end if;
         reg1_rd      <= not LB_RD_N and addr_match_reg;
         reg1_wr      <= not LB_WR_N and addr_match_reg;
         reg2_rd      <= reg1_rd;
         reg2_wr      <= reg1_wr;
         lb_rdy_n_reg <= not (drdy_reg50 or (ardy_reg50 and wr_reg));
         lb_drd_reg   <= drd_mux;
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------
-- User CLK Registers
-- --------------------------------------------------------------------------
MI32_ADDR(31 downto ADDR_WIDTH)    <= (others => '0');
MI32_ADDR(ADDR_WIDTH-1 downto 0)   <= addr_cnt50(ADDR_WIDTH-1 downto 0);


process(lb_endpoint_reset, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (lb_endpoint_reset = '1') then
         MI32_RD            <= '0';
         MI32_WR            <= '0';
         mi32_rd_out        <= '0';
         mi32_wr_out        <= '0';
         MI32_DWR           <= (others => '0');
         MI32_BE            <= (others => '0');
         ardy_reg50    <= '0';
         drdy_reg50    <= '0';
         drd_reg50     <= (others => '0');
         addr_cnt50_we <= '0';
      else
         MI32_RD            <= reg2_rd;
         MI32_WR            <= reg2_wr;
         mi32_rd_out        <= reg2_rd;
         mi32_wr_out        <= reg2_wr;
         MI32_DWR           <= dwr1_reg;
         MI32_BE            <= be1_reg;
         ardy_reg50    <= mi32_ardy_aux;
         drdy_reg50    <= MI32_DRDY;
         drd_reg50     <= MI32_DRD;
         addr_cnt50_we <= LB_ADS_N; -- Write address into 50Mhz addr counter
      end if;
   end if;
end process;
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

-- first_reg ------------------------------------------------------------------
first_regp: process(lb_endpoint_reset, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (lb_endpoint_reset = '1') then
         first_reg <= '0';
      else
         if (LB_ADS_N = '0') then
            first_reg <= '1';
         end if;
         if (reg2_rd = '1' or reg2_wr='1') then
            first_reg <= '0';
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
         if (shr_vld = '1' and in_cnt='0' and (ardy_reg50 = '1' or first_reg = '1' or first_reg_pipe='1')) then
           in_cnt <= '1';
         end if;
         if (shr_vld = '1' and in_cnt='1') then
           in_cnt <= '0';
         end if;
      end if;
   end if;
end process;

-- user_comp_in registers -----------------------------------------------------
user_comp_in_regp: process(lb_endpoint_reset, LB_CLK)
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

shr_read      <= '1' when in_cnt = '1' or ardy_reg50 = '1' or first_reg = '1' or first_reg_pipe='1' else '0';

-- --------------------------------------------------------------------------
-- LB CLK Registers
-- --------------------------------------------------------------------------
LB_RDY_N <= lb_rdy_n_reg;
LB_DRD   <= lb_drd_reg;
LB_ERR_N <= '1';

process(lb_endpoint_reset, LB_CLK)
begin
   if (LB_CLK'event AND LB_CLK = '1') then
      if (lb_endpoint_reset = '1') then
         reg1_rd      <= '0';
         reg1_wr      <= '0';
         reg2_rd      <= '0';
         reg2_wr      <= '0';
         dwr1_reg     <= (others => '0');
         be1_reg      <= (others => '0');
         lb_drd_reg   <= (others => '0');
         lb_rdy_n_reg <= '1';
      else
         if (in_cnt='1') then
            dwr1_reg <= shr_dwr & dwr_low_reg;
            be1_reg  <= shr_be  & be_low_reg;
         end if;
         reg1_rd      <= not shr_rd_n and addr_match_reg and shr_vld;
         reg1_wr      <= not shr_wr_n and addr_match_reg and shr_vld;
         reg2_rd      <= reg1_rd;
         reg2_wr      <= reg1_wr;
         lb_rdy_n_reg <= not (drdy_reg50 or (ardy_reg50 and wr_reg));
         lb_drd_reg   <= drd_mux;
      end if;
   end if;
end process;

-- --------------------------------------------------------------------------
-- User CLK Registers
-- --------------------------------------------------------------------------
MI32_ADDR(ADDR_WIDTH-1 downto 0)   <= addr_cnt50(ADDR_WIDTH-1 downto 0);
MI32_ADDR(31 downto ADDR_WIDTH)    <= (others => '0');

process(lb_endpoint_reset, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (lb_endpoint_reset = '1') then
         MI32_RD            <= '0';
         MI32_WR            <= '0';
         mi32_rd_out        <= '0';
         mi32_wr_out        <= '0';
         MI32_DWR           <= (others => '0');
         MI32_BE            <= (others => '0');
         ardy_reg50    <= '0';
         drdy_reg50    <= '0';
         drd_reg50     <= (others => '0');
         addr_cnt50_we <= '0';
      else
         MI32_RD            <= reg2_rd;
         MI32_WR            <= reg2_wr;
         mi32_rd_out        <= reg2_rd;
         mi32_wr_out        <= reg2_wr;
         if (mi32_ardy_aux = '1' or first_reg = '1') then
            MI32_DWR           <= dwr1_reg;
            MI32_BE            <= be1_reg;
         end if;
         first_reg_pipe <= first_reg;
         addr_cnt50_we <= LB_ADS_N; -- Write address into 50Mhz addr counter
         ardy_reg50    <= mi32_ardy_aux;
         drdy_reg50    <= MI32_DRDY;
         drd_reg50     <= MI32_DRD;
      end if;
   end if;
end process;

end generate;


end architecture LB_ENDPOINT_50_ARCH;
