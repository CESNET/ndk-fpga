-- np_lutram_pro.vhd: Generic N-port distributed memory
-- Copyright (C) 2018 CESNET
-- Author(s): Václav Hummel <xhumme00@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use IEEE.math_real.all;
use work.math_pack.all;
use work.type_pack.all;

entity NP_LUTRAM_PRO is
   generic(
      DATA_WIDTH : integer := 64; -- any possitive value
      ITEMS      : integer := 64;  -- any possitive value
      WRITE_PORTS: integer := 8;
      READ_PORTS : integer := 8;
      DEVICE     : string := "ULTRASCALE"
   );
   port(
      -- Registered
      DI         : in  slv_array_t(WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
      -- Registered
      WE         : in  std_logic_vector(WRITE_PORTS-1 downto 0);
      WCLK       : in  std_logic;
      WCLKN      : in  std_logic; -- has to be CLK_MULT*WCLK, same source
      WRESET     : in  std_logic; -- !! MUST BE SYNCHRONISED ON rising_edge(WCLK) !!
      -- Registered
      ADDRA      : in  slv_array_t(WRITE_PORTS-1 downto 0)(LOG2(ITEMS)-1 downto 0);
      -- Registered
      ADDRB      : in  slv_array_t(READ_PORTS-1 downto 0)(LOG2(ITEMS)-1 downto 0);
      -- Registered, DOB is valid 2 clock cycles after ADDRB
      DOB        : out slv_array_t(READ_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0)
  );
end entity;

architecture behavioral of NP_LUTRAM_PRO is

   constant CLK_MULT : integer := 2;

   constant WRITE_PORTS_EXT : integer := integer(ceil(real(WRITE_PORTS)/real(CLK_MULT)))*CLK_MULT;
   constant READ_PORTS_EXT : integer := integer(ceil(real(READ_PORTS)/real(CLK_MULT)))*CLK_MULT;

   signal reg1_di         : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal reg1_we         : std_logic_vector(WRITE_PORTS-1 downto 0);
   signal reg1_addra      : slv_array_t(0 to WRITE_PORTS-1)(LOG2(ITEMS)-1 downto 0);
   signal reg1_addrb      : slv_array_t(0 to READ_PORTS-1)(LOG2(ITEMS)-1 downto 0);

   signal reg1_di_ext : slv_array_t(0 to WRITE_PORTS_EXT-1)(DATA_WIDTH-1 downto 0);
   signal reg1_we_ext : std_logic_vector(WRITE_PORTS_EXT-1 downto 0);
   signal reg1_addra_ext : slv_array_t(0 to WRITE_PORTS_EXT-1)(LOG2(ITEMS)-1 downto 0);
   signal reg1_addrb_ext : slv_array_t(0 to READ_PORTS_EXT-1)(LOG2(ITEMS)-1 downto 0);

   signal reg2_we_ext : std_logic_vector(WRITE_PORTS_EXT-1 downto 0);
   signal reg2_addra_ext : slv_array_t(0 to WRITE_PORTS_EXT-1)(LOG2(ITEMS)-1 downto 0);
   signal reg2_addrb_ext : slv_array_t(0 to READ_PORTS_EXT-1)(LOG2(ITEMS)-1 downto 0);

   signal reg2_addra_onehot   : slv_array_t(0 to WRITE_PORTS_EXT-1)(ITEMS-1 downto 0);
   signal reg2_addra_onehot_reord   : slv_array_t(0 to ITEMS-1)(WRITE_PORTS_EXT-1 downto 0);
   signal reg2_addra_onehot_reord_red   : slv_array_t(0 to ITEMS-1)(WRITE_PORTS_EXT/CLK_MULT-1 downto 0);

   signal reg2_sels_we : std_logic_vector(ITEMS-1 downto 0);
   signal reg2_sels : slv_array_t(0 to ITEMS-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0) :=
                      (others => (others => '0'));

   signal reg3_sels : slv_array_t(0 to ITEMS-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0) :=
                      (others => (others => '0'));

   signal reg1_mux_sel     : slv_array_t(0 to READ_PORTS_EXT-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0);
   signal reg2_mux_sel     : slv_array_t(0 to READ_PORTS_EXT-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0);
   signal reg3_mux_sel     : slv_array_t(0 to READ_PORTS_EXT-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0);
   signal reg4_mux_sel     : slv_array_t(0 to READ_PORTS_EXT-1)(max(log2(WRITE_PORTS_EXT/CLK_MULT),1)-1 downto 0);

   signal reg3_dob_ext : slv_array_2d_t(0 to WRITE_PORTS_EXT/CLK_MULT-1)(0 to READ_PORTS_EXT-1)(DATA_WIDTH-1 downto 0);
   signal reg4_dob_ext : slv_array_2d_t(0 to WRITE_PORTS_EXT/CLK_MULT-1)(0 to READ_PORTS_EXT-1)(DATA_WIDTH-1 downto 0);
   signal reg4_dob_ext_reord : slv_array_2d_t(0 to READ_PORTS_EXT-1)(0 to WRITE_PORTS_EXT/CLK_MULT-1)(DATA_WIDTH-1 downto 0);
   signal reg4_dob_ext_mux_out : slv_array_t(0 to READ_PORTS_EXT-1)(DATA_WIDTH-1 downto 0);

begin

   -- Extend
   reg1_di_extg: for i in 0 to WRITE_PORTS_EXT-1 generate
      reg1_di_extgg: if i < WRITE_PORTS generate
         reg1_di_ext(i) <= DI(i);
         reg1_we_ext(i) <= WE(i);
         reg1_addra_ext(i) <= ADDRA(i);
      end generate;
      reg1_di_extggg: if i >= WRITE_PORTS generate
         reg1_di_ext(i) <= (others => '0');
         reg1_we_ext(i) <= '0';
         reg1_addra_ext(i) <= (others => '0');
      end generate;
   end generate;

   reg1_addrb_extg: for i in 0 to READ_PORTS_EXT-1 generate
      reg1_addrb_extgg: if i < READ_PORTS generate
         reg1_addrb_ext(i) <= ADDRB(i);
      end generate;
      reg1_addrb_extggg: if i >= READ_PORTS generate
         reg1_addrb_ext(i) <= (others => '0');
      end generate;
   end generate;

   -- Register
   reg2_di_extp: process(WCLK)
   begin
      if (WCLK'event and WCLK = '1') then
         if (WRESET = '1') then
            reg2_we_ext <= (others => '0');
         else
            reg2_we_ext <= reg1_we_ext;
         end if;
         reg2_addra_ext <= reg1_addra_ext;
         reg2_addrb_ext <= reg1_addrb_ext;
      end if;
   end process;

   reg2_addra_onehotg: for i in 0 to WRITE_PORTS_EXT-1 generate
      reg2_addra_onehoti: entity work.bin2hot
      generic map(
         DATA_WIDTH => log2(ITEMS)
      )
      port map(
         EN => reg2_we_ext(i),
         INPUT => reg2_addra_ext(i),
         OUTPUT => reg2_addra_onehot(i)
      );
   end generate;

   reg2_addra_onehot_reordg: for i in 0 to ITEMS-1 generate
      reg2_addra_onehot_reordgg: for j in 0 to WRITE_PORTS_EXT-1 generate
         reg2_addra_onehot_reord(i)(j) <= reg2_addra_onehot(j)(i);
      end generate;
   end generate;

   reg2_addra_onehot_reord_redg: for i in 0 to ITEMS-1 generate
      reg2_addra_onehot_reord_redgg: for j in 0 to WRITE_PORTS_EXT/CLK_MULT-1 generate
         reg2_addra_onehot_reord_red(i)(j) <= or reg2_addra_onehot_reord(i)((j+1)*CLK_MULT-1 downto j*CLK_MULT);
      end generate;
   end generate;

   reg2_selsg: for i in 0 to ITEMS-1 generate

      reg2_sels_we(i) <= or reg2_addra_onehot_reord(i);

   end generate;

   reg2_sels_pr : process (reg2_addra_onehot_reord_red)
   begin
      for i in 0 to ITEMS-1 loop
         reg2_sels(i) <= (others => '0');
         for e in WRITE_PORTS_EXT/CLK_MULT-1 downto 0 loop
            if (reg2_addra_onehot_reord_red(i)(e)='1') then
                reg2_sels(i) <= std_logic_vector(resize_left(to_unsigned(e,log2(WRITE_PORTS_EXT/CLK_MULT)),reg2_sels(i)'length));
            end if;
         end loop;
      end loop;
   end process;

   reg3_selsg: for i in 0 to ITEMS-1 generate
      reg3_selsp: process(WCLK)
      begin
         if (WCLK'event and WCLK = '1') then
            if (reg2_sels_we(i) = '1') then
               reg3_sels(i) <= reg2_sels(i);
            end if;
         end if;
      end process;
   end generate;

   reg1_mux_selg: for i in 0 to READ_PORTS_EXT-1 generate
      reg1_mux_seli: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => max(log2(WRITE_PORTS_EXT/CLK_MULT),1),
         MUX_WIDTH => ITEMS
      )
      port map(
         DATA_IN => slv_array_ser(reg3_sels, ITEMS, max(log2(WRITE_PORTS_EXT/CLK_MULT),1)),
         SEL => reg2_addrb_ext(i),
         DATA_OUT => reg2_mux_sel(i)
      );
   end generate;

   reg2_mux_selp: process(WCLK)
   begin
      if (WCLK'event and WCLK = '1') then
         reg3_mux_sel <= reg2_mux_sel;
         reg4_mux_sel <= reg3_mux_sel;
      end if;
   end process;

   memg: for i in 0 to WRITE_PORTS_EXT/CLK_MULT-1 generate
      memi: entity work.NP_LUTRAM_FIXED
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         ITEMS => ITEMS,
         WRITE_PORTS => CLK_MULT,
         READ_PORTS => READ_PORTS_EXT,
         DEVICE => DEVICE
      )
      port map(
         DI => reg1_di_ext(i*CLK_MULT to (i+1)*CLK_MULT-1),
         WE => reg1_we_ext((i+1)*CLK_MULT-1 downto i*CLK_MULT),
         WCLK  => WCLK,
         WCLKN => WCLKN,
         WRESET => WRESET,
         ADDRA => reg1_addra_ext(i*CLK_MULT to (i+1)*CLK_MULT-1),
         ADDRB => reg1_addrb_ext,
         DOB => reg3_dob_ext(i)
      );
   end generate;

   reg4_dob_extp: process(WCLK)
   begin
      if (WCLK'event and WCLK = '1') then
         reg4_dob_ext <= reg3_dob_ext;
      end if;
   end process;

   reg4_dob_ext_reordg: for i in 0 to READ_PORTS_EXT-1 generate
      reg4_dob_ext_reordgg: for j in 0 to WRITE_PORTS_EXT/CLK_MULT-1 generate
         reg4_dob_ext_reord(i)(j) <= reg4_dob_ext(j)(i);
      end generate;
   end generate;

   muxg: for i in 0 to READ_PORTS_EXT-1 generate
      muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         MUX_WIDTH => WRITE_PORTS_EXT/CLK_MULT
      )
      port map(
         DATA_IN => slv_array_ser(reg4_dob_ext_reord(i), WRITE_PORTS_EXT/CLK_MULT, DATA_WIDTH),
         SEL => reg3_mux_sel(i),
         DATA_OUT => reg4_dob_ext_mux_out(i)
      );
   end generate;

   dobg: for i in 0 to READ_PORTS-1 generate
      DOB(i) <= reg4_dob_ext_mux_out(i);
   end generate;

end architecture;
