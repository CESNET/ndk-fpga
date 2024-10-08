-- mi_reg.vhd
-- # Copyright (C) 2014 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use ieee.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MI_REG is
   generic (
      --! Data width mi_data
      MI_WIDTH    : integer := 32;
      --! Register data width
      DATA_WIDTH   : integer := 32;
      --! inter/exter register
      INTER       : boolean := true;
      --! mi read enable
      MI_RD_EN    : boolean := true;
      --! mi write enable
      MI_WR_EN    : boolean := true;
      --! usr write port enable
      USR_WR_EN   : boolean := true;
      --! reset enable
      RST_EN      : boolean := true;
      --! be enable
      BE_EN       : boolean := true;
      --! inicial value
      constant INICIAL     : std_logic_vector;
      --! number of register
      NUM_REG     : integer
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data output
      DATA_OUT : out  std_logic_vector(MI_WIDTH - 1 downto 0);
      --! Enable from decoder
      DEC_EN   : in std_logic;

      --! MI32 input interface -------------------------------------------------
      --! Input Data
      MI_DWR                        : in  std_logic_vector(MI_WIDTH-1 downto 0);
      --! Read Request
      MI_RD                         : in  std_logic;
      --! Write Request
      MI_WR                         : in  std_logic;
      --! Byte Enable
      MI_BE                         : in  std_logic_vector(MI_WIDTH/8-1  downto 0);
      --! Output Data
      MI_DRD                        : out std_logic_vector(MI_WIDTH-1 downto 0);
      --! Address Ready
      MI_ARDY                       : out std_logic;
      --! Data Ready
      MI_DRDY                       : out std_logic;

      MI_RD_OUT                     : out std_logic;
      MI_WR_OUT                     : out std_logic;
      USR_DATA_IN                   : in  std_logic_vector(MI_WIDTH-1 downto 0);
      USR_DATA_EN                   : in  std_logic;

      EXTER_ARDY                    : in  std_logic
   );
end MI_REG;

architecture full of MI_REG is
   signal rst_reg       : std_logic;
   signal data_reg_out  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_reg_in   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rd_dec_en     : std_logic;
   signal wr_dec_en     : std_logic;
   signal reg_wr_en     : std_logic;
   signal be_p          : std_logic_vector(MI_WIDTH/8-1 downto 0);
begin
   --! generate inter register
   GEN_INTER_REG : if (INTER = true) generate
   begin
      --! when RESET is enbale
      GEN_RESET_ON : if (RST_EN = true) generate
      begin
         rst_reg <= RESET;
      end generate;

       --! when RESET is disable
      GEN_RESET_OFF : if (RST_EN = false) generate
      begin
         rst_reg <= '0';
      end generate;

      --! ARDY when MI_RD and MI_WR are enabled
      GEN_ARDY_RDON_WRON: if (MI_RD_EN = true and MI_WR_EN = true) generate
      begin
         --! when signal from decoder is true
         rd_dec_en <= MI_RD AND DEC_EN;
         wr_dec_en <= MI_WR AND DEC_EN;
         --! gen ardy, drdy
         MI_ARDY <= rd_dec_en or wr_dec_en;
         MI_DRDY <= rd_dec_en;
         --! RD and WR for user
         MI_RD_OUT <= rd_dec_en;
         MI_WR_OUT <= wr_dec_en;
         --! DRD data
         MI_DRD(DATA_WIDTH-1 downto 0)        <= data_reg_out;
         MI_DRD(MI_WIDTH-1 downto DATA_WIDTH) <= (others => '0');
      end generate;

      --! ARDY when MI_RD is disable and MI_WR is enbale
      GEN_ARDY_RDOFF_WRON: if (MI_RD_EN = false and MI_WR_EN = true) generate
      begin
         --! when signal from decoder is true
         wr_dec_en <= MI_WR AND DEC_EN;
         rd_dec_en <= '0';
         --! gen ardy, drdy
         MI_ARDY <= wr_dec_en;
         MI_DRDY <= '0';
         --! RD and WR for user
         MI_RD_OUT <= 'U';
         MI_WR_OUT <= wr_dec_en;
         --! DRD data
         MI_DRD    <= (others => '0');
      end generate;

      --! ARDY when MI_RD is enable and MI_WR is disable
      GEN_ARDY_RDON_WROFF: if (MI_RD_EN = true and MI_WR_EN = false) generate
      begin
         --! when signal from decoder is true
         rd_dec_en <= MI_RD AND DEC_EN;
         wr_dec_en <= '0';
         --! gen ardy, drdy
         MI_ARDY <= rd_dec_en;
         MI_DRDY <= rd_dec_en;
         --! RD and WR for user
         MI_RD_OUT <= rd_dec_en;
         MI_WR_OUT <= 'U';
         --! DRD data
         MI_DRD(DATA_WIDTH-1 downto 0)        <= data_reg_out;
         GEN_FINISH_DRD: if MI_WIDTH /= DATA_WIDTH generate
            MI_DRD(MI_WIDTH-1 downto DATA_WIDTH) <= (others => '0');
         end generate;
      end generate;

      --! ARDY when MI_RD and MI_WR is disable
      GEN_ARDY_RDOFF_WROFF: if (MI_RD_EN = false and MI_WR_EN = false) generate
      begin
         --! when signal from decoder is true
         --!
         --! gen ardy, drdy
         MI_ARDY <= '0';
         MI_DRDY <= '0';
         --! RD and WR for user
         MI_RD_OUT <= 'U';
         MI_WR_OUT <= 'U';
         --! DRD data
         MI_DRD    <= (others => '-');
      end generate;

      --! control write data to register when MI_WR and USR_WR are enabled
      GEN_REGIN_DAT_MIWRON_USRWRON: if (MI_WR_EN = true and USR_WR_EN = true) generate
      begin
         --! switch data
         data_reg_in <= MI_DWR(DATA_WIDTH-1 downto 0) when wr_dec_en = '1' else
                        USR_DATA_IN(DATA_WIDTH-1 downto 0);
         --! control write enable
         reg_wr_en <= wr_dec_en or USR_DATA_EN;
      end generate;

      --! control write data to register when MI_WR is enbale and USR_WR is disable
      GEN_REGIN_DAT_MIWRON_USRWROff: if (MI_WR_EN = true and USR_WR_EN = false) generate
      begin
         --! switch data
         data_reg_in <= MI_DWR(DATA_WIDTH-1 downto 0);
         --! control write enable
         reg_wr_en <= wr_dec_en;
      end generate;

      --! control write data to register when MI_WR is disable and USR_WR is enable
      GEN_REGIN_DAT_MIWROFF_USRWRON: if (MI_WR_EN = false and USR_WR_EN = true) generate
      begin
         --! switch data
         data_reg_in <= USR_DATA_IN(DATA_WIDTH-1 downto 0);
         --! control write enable
         reg_wr_en <= USR_DATA_EN;
      end generate;

      --! control write data to register when MI_WR and USR_WR are disable
      GEN_REGIN_DAT_MIWROFF_USRWROFF: if (MI_WR_EN = false and USR_WR_EN = false) generate
      begin
        data_reg_out <= INICIAL(DATA_WIDTH-1+MI_WIDTH*(NUM_REG-1) downto 0+MI_WIDTH*(NUM_REG-1));
      end generate;


      GEN_BE : if(MI_WR_EN = true) generate
      begin
         be : process(wr_dec_en, MI_BE)
         begin
            if(wr_dec_en = '0') then
               be_p <= (others => '1');
            else
               be_p <= MI_BE;
            end if;
         end process;
      end generate;

      GEN_BE_NO : if(MI_WR_EN = false) generate
      begin
         be_p <= (others => '1');
      end generate;

      GEN_REG: if (MI_WR_EN = true or USR_WR_EN = true) generate
      begin
         --! conect register
         BE_REG_inst : entity work.BE_REG
         generic map (
            DATA_WIDTH  => DATA_WIDTH,
            MI_WIDTH => MI_WIDTH,
            BE_ENABLE   => BE_EN,
            NUM_REG     => NUM_REG,
            INICIAL    => INICIAL
        )
         port map (
            --! Clock input
            CLK        => CLK,
            --! Reset input
            RESET      => rst_reg,
            --! BE signal
            BE         => be_p,
            --! in data
            DATA       => data_reg_in,
            --! enable
            ENABLE     => reg_wr_en,
            --! data out
            P          => data_reg_out
         );
      end generate;

      --! output data
      DATA_OUT(DATA_WIDTH-1 downto 0) <= data_reg_out;
      GEN_FINISH_DATA_OUT: if MI_WIDTH /= DATA_WIDTH generate
         DATA_OUT(MI_WIDTH-1 downto DATA_WIDTH) <= (others => '0');
      end generate;
   end generate;

   --! generate exter register
   GEN_EXTER_REG : if (INTER = false) generate
   begin
       --! ARDY when MI_RD and MI_WR are enabled
      EXTERN_ARDY_RDON_WRON: if (MI_RD_EN = true and MI_WR_EN = true) generate
      begin
         --! when signal from decoder is true
         MI_RD_OUT <= MI_RD AND DEC_EN;
         MI_WR_OUT <= MI_WR AND DEC_EN;
         --! DRD data
         MI_DRD    <= USR_DATA_IN;
      end generate;

      --! ARDY when MI_RD is disable and MI_WR is enbale
      EXTERN_ARDY_RDOFF_WRON: if (MI_RD_EN = false and MI_WR_EN = true) generate
      begin
         --! when signal from decoder is true
         MI_WR_OUT <= MI_WR AND DEC_EN;
         MI_RD_OUT <= 'U';
         --! DRD data
         MI_DRD    <= (others => '-');
      end generate;

      --! ARDY when MI_RD is enable and MI_WR is disable
      EXTERN_ARDY_RDON_WROFF: if (MI_RD_EN = true and MI_WR_EN = false) generate
      begin
         --! when signal from decoder is true
         MI_RD_OUT <= MI_RD AND DEC_EN;
         MI_WR_OUT <= 'U';
         --! DRD data
         MI_DRD    <= USR_DATA_IN;
      end generate;

      --! ARDY when MI_RD and MI_WR is disable
      EXTERN_ARDY_RDOFF_WROFF: if (MI_RD_EN = false and MI_WR_EN = false) generate
      begin
         MI_RD_OUT <= 'U';
         MI_WR_OUT <= 'U';
         --! DRD data
         MI_DRD    <= (others => '-');
      end generate;

      DATA_OUT <= MI_DWR;
      MI_ARDY <= EXTER_ARDY;
      MI_DRDY <= USR_DATA_EN;
   end generate;

end full;

