-- np_lutram.vhd: Generic N-port distributed LUT memory
-- Copyright (C) 2017 CESNET
-- Author(s): Václav Hummel <xhumme00@cesnet.cz>
--            Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Generic N-port distributed LUT memory
entity NP_LUTRAM is
  generic(
    DATA_WIDTH  : integer := 1;
    ITEMS       : integer := 64;
    WRITE_PORTS : integer := 1;
    READ_PORTS  : integer := 3;
    DEVICE      : string  := "7SERIES"
  );
  port(
    DI          : in  slv_array_t(WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    WE          : in  std_logic_vector(WRITE_PORTS-1 downto 0);
    WCLK        : in  std_logic;
    ADDRA       : in  slv_array_t(WRITE_PORTS-1 downto 0)(LOG2(ITEMS)-1 downto 0);
    ADDRB       : in  slv_array_t(READ_PORTS-1 downto 0)(LOG2(ITEMS)-1 downto 0);
    DOB         : out slv_array_t(READ_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0)
  );
end entity;

architecture behavioral of NP_LUTRAM is

   signal memi_addr  : slv_array_t(0 to WRITE_PORTS-1)(READ_PORTS*log2(ITEMS)-1 downto 0);
   signal memi_do   : slv_array_t(0 to WRITE_PORTS-1)(READ_PORTS*DATA_WIDTH-1 downto 0);
   signal mem_dob     : slv_array_2d_t(0 to WRITE_PORTS-1)(0 to READ_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal mem_dob_reord  : slv_array_2d_t(0 to READ_PORTS-1)(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal mux_sel     : slv_array_t(0 to READ_PORTS-1)(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal addra_onehot   : slv_array_t(0 to WRITE_PORTS-1)(ITEMS-1 downto 0);
   signal addra_onehot_reord   : slv_array_t(0 to ITEMS-1)(WRITE_PORTS-1 downto 0);
   signal reg_sels_we : std_logic_vector(ITEMS-1 downto 0);
   signal reg_sels_in : slv_array_t(0 to ITEMS-1)(max(log2(WRITE_PORTS),1)-1 downto 0) := (others => (others => '0'));
   signal reg_sels    : slv_array_t(0 to ITEMS-1)(max(log2(WRITE_PORTS),1)-1 downto 0) := (others => (others => '0'));

begin

   addra_onehotg: for i in 0 to WRITE_PORTS-1 generate
      addra_onehoti: entity work.bin2hot
      generic map(
         DATA_WIDTH => log2(ITEMS)
      )
      port map(
         EN => WE(i),
         INPUT => ADDRA(i),
         OUTPUT => addra_onehot(i)
      );
   end generate;

   addra_onehot_reordg: for i in 0 to ITEMS-1 generate
      addra_onehot_reordgg: for j in 0 to WRITE_PORTS-1 generate
         addra_onehot_reord(i)(j) <= addra_onehot(j)(i);
      end generate;
   end generate;

   dma_states_muxg: for i in 0 to ITEMS-1 generate

      -- becouse modelsim withnout parameter -novopt generate error
      -- with this construction. Solution of this problem is add
      -- slice size.
      -- reg_sels_we(i) <= or(addra_onehot_reord(i));
      reg_sels_we(i) <= or(addra_onehot_reord(i)(WRITE_PORTS-1 downto 0));

      reg_sels_ini: entity work.gen_enc
      generic map(
         ITEMS => WRITE_PORTS,
         DEVICE => DEVICE
      )
      port map(
         DI => addra_onehot_reord(i),
         ADDR => reg_sels_in(i)
      );
   end generate;

   reg_selsg: for i in 0 to ITEMS-1 generate
      reg_selsp: process(WCLK)
      begin
         if (WCLK'event and WCLK = '1') then
            if (reg_sels_we(i) = '1') then
               reg_sels(i) <= reg_sels_in(i);
            end if;
         end if;
      end process;
   end generate;

   mux_selg: for i in 0 to READ_PORTS-1 generate
      mux_seli: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => max(log2(WRITE_PORTS),1),
         MUX_WIDTH => ITEMS
      )
      port map(
         DATA_IN => slv_array_ser(reg_sels, ITEMS, max(log2(WRITE_PORTS),1)),
         SEL => ADDRB(i),
         DATA_OUT => mux_sel(i)
      );
   end generate;

   memg: for i in 0 to WRITE_PORTS-1 generate

      memi_addrg: for j in 0 to READ_PORTS-1 generate
         memi_addr(i)((j+1)*log2(ITEMS)-1 downto j*log2(ITEMS)) <= ADDRB(j);
      end generate;

      lutram_i : entity work.GEN_LUTRAM
      generic map (
         DATA_WIDTH         => DATA_WIDTH,
         ITEMS              => ITEMS,
         RD_PORTS           => READ_PORTS,
         RD_LATENCY         => 0,
         WRITE_USE_RD_ADDR0 => false,
         MLAB_CONSTR_RDW_DC => true,
         DEVICE             => DEVICE
      )
      port map (
         CLK     => WCLK,
         WR_EN   => WE(i),
         WR_ADDR => ADDRA(i),
         WR_DATA => DI(i),
         RD_ADDR => memi_addr(i),
         RD_DATA => memi_do(i)
      );

      mem_dog: for j in 0 to READ_PORTS-1 generate
         mem_dob(i)(j) <= memi_do(i)((j+1)*DATA_WIDTH-1 downto j*DATA_WIDTH);
      end generate;
   end generate;

   mem_dob_reordg: for i in 0 to READ_PORTS-1 generate
      mem_dob_reordgg: for j in 0 to WRITE_PORTS-1 generate
         mem_dob_reord(i)(j) <= mem_dob(j)(i);
      end generate;
   end generate;

   muxg: for i in 0 to READ_PORTS-1 generate
      muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         MUX_WIDTH => WRITE_PORTS
      )
      port map(
         DATA_IN => slv_array_ser(mem_dob_reord(i), WRITE_PORTS, DATA_WIDTH),
         SEL => mux_sel(i),
         DATA_OUT => DOB(i)
      );
   end generate;

end architecture;
