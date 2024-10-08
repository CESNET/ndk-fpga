-- MI_register_array.vhd
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

--! register data type
use work.REG_PACK.all;

entity MI_REGISTER_ARRAY is
   generic (
      --! Data width mi_data
      MI_WIDTH       : integer := 32;
      --! MI addres data width
      MI_ADDR_WIDTH  : integer := 32;
      --! MI pipe
      MI_PIPE        : boolean := true;
      --! addres first register in array
      --! width must be (MI_ADDR_WIDTH-1 downto 0)
      constant FIRST_ADDR  : std_logic_vector;
      --! significant bits of the address
      SIGN_BITS_ADDR : integer;
      --! number of regiters
      NUM_REGS       : integer := 1;
      --! initialization values for registers,
      --! width must be (NUM_REGS*MI_WIDTH-1 downto 0)
      constant INICIAL     : std_logic_vector;
      --! registers generic data (array)
      --! range must be (1 to NUM_REGS)
      --! sample connections in /sim/testbench.vhd
      GENER_REGS : REG_TYPE_ARRAY;
      DEVICE     : string := "7SERIES"
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;

      --! MI32 input interface -------------------------------------------------
      --! Input Data
      MI_DWR                        : in  std_logic_vector(MI_WIDTH-1 downto 0);
      --! addres
      MI_ADDR                       : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
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

      --! registers Data output
      REG_DATA_OUT                  : out std_logic_vector((NUM_REGS*MI_WIDTH)-1 downto 0);
      --! MI_WR signals
      REG_WR_OUT                    : out std_logic_vector(NUM_REGS-1 downto 0);
      --! MI_RD signals
      REG_RD_OUT                    : out std_logic_vector(NUM_REGS-1 downto 0);
      --! users data input
      REG_DATA_IN                   : in std_logic_vector((NUM_REGS*MI_WIDTH)-1 downto 0);
      --! users we signal
      REG_WE_IN                     : in std_logic_vector(NUM_REGS-1 downto 0);
      --! MI_ARDY signal from extern register
      REG_ARDY_IN                   : in std_logic_vector(NUM_REGS-1 downto 0)
   );
end MI_REGISTER_ARRAY;

architecture full of MI_REGISTER_ARRAY is
   signal dec_out : std_logic_vector(NUM_REGS-1 downto 0);
   signal mux_drd_in   : std_logic_vector((NUM_REGS*MI_WIDTH)-1 downto 0);
   signal mux_drd_out  : std_logic_vector(MI_WIDTH-1 downto 0);
   signal mux_ardy_in  : std_logic_vector(NUM_REGS-1 downto 0);
   signal mux_ardy_out : std_logic_vector(0 downto 0);
   signal mux_drdy_in  : std_logic_vector(NUM_REGS-1 downto 0);
   signal mux_drdy_out : std_logic_vector(0 downto 0);

   signal mi_dwr_pipe   : std_logic_vector(MI_WIDTH-1 downto 0);
   signal mi_addr_pipe  : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
   signal mi_be_pipe    : std_logic_vector(MI_WIDTH/8-1 downto 0);
   signal mi_rd_pipe    : std_logic;
   signal mi_wr_pipe    : std_logic;
   signal mi_ardy_pipe  : std_logic;
   signal mi_drd_pipe   : std_logic_vector(MI_WIDTH-1 downto 0);
   signal mi_drdy_pipe  : std_logic;

begin
   assert (MI_ADDR'length = FIRST_ADDR'length) report "range of signal FIRST_ADDR must be (MI_ADDR_WIDTH-1 downto 0)" severity failure;
   assert (INICIAL'length = NUM_REGS*MI_WIDTH) report "range of signal INICIAL must be (NUM_REGS*MI_WIDTH-1 downto 0)" severity failure;
   assert (MI_ADDR'length >= SIGN_BITS_ADDR) report "SIGN_BITS_ADDR must be less or equal than MI_ADDR" severity failure;
   assert (GENER_REGS'length = NUM_REGS) report "SIGN_BITS_ADDR must be less or equal than MI_ADDR" severity failure;

   --! generate mi pipe
   MI_PIPE_inst : entity work.MI_PIPE
   generic map (
      DATA_WIDTH  => MI_WIDTH,
      ADDR_WIDTH  => MI_ADDR_WIDTH,
      USE_OUTREG  => MI_PIPE,
      FAKE_PIPE   => not MI_PIPE,
      DEVICE      => DEVICE
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK    => CLK,
      RESET  => RESET,

      -- Input MI interface ---------------------------------------------------
      IN_DWR      => MI_DWR,
      IN_ADDR     => MI_ADDR,
      IN_BE       => MI_BE,
      IN_RD       => MI_RD,
      IN_WR       => MI_WR,
      IN_ARDY     => MI_ARDY,
      IN_DRD      => MI_DRD,
      IN_DRDY     => MI_DRDY,

      -- Output MI interface --------------------------------------------------
      OUT_DWR     => mi_dwr_pipe,
      OUT_ADDR    => mi_addr_pipe,
      OUT_BE      => mi_be_pipe,
      OUT_RD      => mi_rd_pipe,
      OUT_WR      => mi_wr_pipe,
      OUT_ARDY    => mi_ardy_pipe,
      OUT_DRD     => mi_drd_pipe,
      OUT_DRDY    => mi_drdy_pipe
   );

   --! decode addres
   process(mi_addr_pipe)
   begin
      dec_out <= (others => '0');

      for i in 0 to (NUM_REGS-1) loop
         if (mi_addr_pipe(SIGN_BITS_ADDR-1 downto 0) = std_logic_vector(resize(unsigned(FIRST_ADDR)+(i*4),SIGN_BITS_ADDR))) then
            dec_out(i) <= '1';
         end if;
      end loop;
   end process;

   --! generate mux MI_DRD
   MUX_DRD_inst : entity work.GEN_MUX_ONEHOT
   generic map(
      DATA_WIDTH  => MI_WIDTH,
      MUX_WIDTH   => NUM_REGS
   )
   port map(
      DATA_IN     => mux_drd_in,
      SEL         => dec_out,
      DATA_OUT    => mux_drd_out
   );

   --! generate mux MI_ARDY
   MUX_ARDY_inst : entity work.GEN_MUX_ONEHOT
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => NUM_REGS
   )
   port map(
      DATA_IN     => mux_ardy_in,
      SEL         => dec_out,
      DATA_OUT    => mux_ardy_out
   );

   --! generate mux MI_DRDY
   MUX_DRDY_inst : entity work.GEN_MUX_ONEHOT
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => NUM_REGS
   )
   port map(
      DATA_IN     => mux_drdy_in,
      SEL         => dec_out,
      DATA_OUT    => mux_drdy_out
   );

   mi_drd_pipe <= mux_drd_out;
   mi_ardy_pipe <= mux_ardy_out(0);
   mi_drdy_pipe <= mux_drdy_out(0);

   --! connect registers
   GEN_REGS: for I in 1 to NUM_REGS generate
   begin
      MI_REG_inst : entity work.MI_REG
      generic map (
         --! Data width mi_data
         MI_WIDTH => MI_WIDTH,
         --! Register data width
         DATA_WIDTH => GENER_REGS(I).DATA_WIDTH,
         --! inter/exter register
         INTER => GENER_REGS(I).INTER,
         --! mi read enable
         MI_RD_EN => GENER_REGS(I).MI_RD_EN,
         --! mi write enable
         MI_WR_EN => GENER_REGS(I).MI_WR_EN,
         --! usr write port enable
         USR_WR_EN => GENER_REGS(I).USR_WR_EN,
         --! reset enable
         RST_EN => GENER_REGS(I).RST_EN,
         --! be enable
         BE_EN => GENER_REGS(I).BE_EN,
         --! nicial value
         INICIAL => INICIAL,
         NUM_REG => I
      )
      port map (
         --! Clock input
         CLK => CLK,
         --! Reset input
         RESET => RESET,
         --! Data output
         DATA_OUT => REG_DATA_OUT(MI_WIDTH-1+((I-1)*MI_WIDTH) downto (I-1)*MI_WIDTH),
         --! Enable from decoder
         DEC_EN => dec_out(I-1),

         --! MI32 input interface -------------------------------------------------
         --! Input Data
         MI_DWR => mi_dwr_pipe,
         --! Read Request
         MI_RD  => mi_rd_pipe,
         --! Write Request
         MI_WR  => mi_wr_pipe,
         --! Byte Enable
         MI_BE  => mi_be_pipe,
         --! Output Data
         MI_DRD => mux_drd_in(MI_WIDTH-1+((I-1)*MI_WIDTH) downto (I-1)*MI_WIDTH),
         --! Address Ready
         MI_ARDY => mux_ardy_in(I-1),
         --! Data Ready
         MI_DRDY => mux_drdy_in(I-1),

         MI_RD_OUT => REG_RD_OUT(I-1),
         MI_WR_OUT => REG_WR_OUT(I-1),
         USR_DATA_IN => REG_DATA_IN(MI_WIDTH-1+((I-1)*MI_WIDTH) downto (I-1)*MI_WIDTH),
         USR_DATA_EN => REG_WE_IN(I-1),
         EXTER_ARDY => REG_ARDY_IN(I-1)
      );
   end generate GEN_REGS;
end architecture;
