--! tsu_cv2_core.vhd: core component of GPS synchronized timestamp unit
--! Copyright (C) 2009 CESNET
--! Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>, Jakub Cabal <jakubcabal@gmail.com>
--!
--! SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TSU_CV2_CORE is
   generic (
      REGISTER_TS_OUTPUT : boolean := false;
      DEVICE             : string  := "ULTRASCALE"
   );
   port (
      -- =============================================
      -- Clock and reset signals for MI_32 interface
      -- =============================================

      MI32_CLK       : in  std_logic;
      MI32_RESET     : in  std_logic;

      -- ================================
      -- In / Out SW interface via MI_32
      -- ================================
      DWR            : in  std_logic_vector(31 downto 0);
      ADDR           : in  std_logic_vector(31 downto 0);
      RD             : in  std_logic;
      WR             : in  std_logic;
      BE             : in  std_logic_vector(3 downto 0);
      DRD            : out std_logic_vector(31 downto 0);
      ARDY           : out std_logic;
      DRDY           : out std_logic;

      -- Input PPS_N signal
      PPS_N          : in  std_logic;

      -- ===============
      -- TSU core clock
      -- ===============

      TSU_CORE_CLK   : in  std_logic;
      TSU_CORE_RESET : in  std_logic;

      -- =========================
      -- Output pacodag interface
      -- =========================

      TS             : out std_logic_vector(63 downto 0);
      -- timestamp is valid (one cycle), depends on INTA reg
      TS_DV          : out std_logic
   );
end TSU_CV2_CORE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture BEHAVIORAL of TSU_CV2_CORE is

   --! Register signals
   signal reg_realtime                 : std_logic_vector(95 downto 0);
   signal incr_value                   : std_logic_vector(38 downto 0);
   signal reg_pulsepsec                : std_logic_vector(95 downto 0);
   signal reg_write                    : std_logic;
   signal core_reg_ts_dv               : std_logic;
   signal second_reg_realtime          : std_logic_vector(63 downto 0);
   signal second_reg_ts_dv             : std_logic;

   --! Direction of data flow
   signal core_reg_mi_data_input       : std_logic_vector(95 downto 0);

   --! Common MI32 register
   signal core_reg_mi_data_low         : std_logic_vector(31 downto 0);
   signal core_reg_mi_data_middle      : std_logic_vector(31 downto 0);
   signal core_reg_mi_data_high        : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_low           : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_middle        : std_logic_vector(31 downto 0);
   signal mi_reg_mi_data_high          : std_logic_vector(31 downto 0);

   --! MI32 control register
   signal mi_reg_cntrl                 : std_logic_vector(2 downto 0);

   --! MUX select signals
   signal sel_reg_rtr_rd               : std_logic;
   signal sel_reg_rtr_wr               : std_logic;
   signal sel_reg_incr_val_rd          : std_logic;
   signal sel_reg_incr_val_wr          : std_logic;
   signal sel_reg_pulsepsec_wr         : std_logic;
   signal sel_reg_mi_data_low          : std_logic;
   signal sel_reg_mi_data_middle       : std_logic;
   signal sel_reg_mi_data_high         : std_logic;
   signal sel_reg_cntrl                : std_logic;
   signal sel_reg_inta                 : std_logic;

   --! Write enable signals
   signal reg_rtr_we_0                 : std_logic;
   signal reg_incr_val_we              : std_logic;
   signal core_reg_mi_data_low_we      : std_logic;
   signal core_reg_mi_data_middle_we   : std_logic;
   signal core_reg_mi_data_high_we     : std_logic;
   signal mi_reg_ts_dv_we              : std_logic;
   signal mi_reg_cntrl_we              : std_logic;
   signal mi_reg_mi_data_low_we        : std_logic;
   signal mi_reg_mi_data_middle_we     : std_logic;
   signal mi_reg_mi_data_high_we       : std_logic;
   signal pps_wr_en                    : std_logic;

   --! DSP48 signals
   signal add_result                   : std_logic_vector(95 downto 0);

   --! MI32 slave signals
   signal tsu_dwr                      : std_logic_vector(31 downto 0);
   signal tsu_addr                     : std_logic_vector(31 downto 0);
   signal tsu_be                       : std_logic_vector(3 downto 0);
   signal tsu_rd                       : std_logic;
   signal tsu_wr                       : std_logic;
   signal tsu_drd                      : std_logic_vector(31 downto 0);
   signal tsu_ardy                     : std_logic;
   signal tsu_drdy                     : std_logic;
   signal tsu_drdy_r                   : std_logic;

   --! DRD and DRDY MUX
   signal drd_mux                      : std_logic_vector(31 downto 0);
   signal core_reg_mi_data_low_drdy    : std_logic;
   signal core_reg_mi_data_middle_drdy : std_logic;
   signal core_reg_mi_data_high_drdy   : std_logic;

begin

   -- ----------------------------------------------------------------------------
   --                            ASYNC MI32
   -- ----------------------------------------------------------------------------

   mi_async_i : entity work.MI_ASYNC
   generic map (
      RAM_TYPE => "AUTO",
      DEVICE   => DEVICE
   )
   port map (
      --! Master interface
      CLK_M     => MI32_CLK,
      RESET_M   => MI32_RESET,
      MI_M_DWR  => DWR,
      MI_M_ADDR => ADDR,
      MI_M_BE   => BE,
      MI_M_RD   => RD,
      MI_M_WR   => WR,
      MI_M_DRD  => DRD,
      MI_M_ARDY => ARDY,
      MI_M_DRDY => DRDY,

      --! Slave interface
      CLK_S     => TSU_CORE_CLK,
      RESET_S   => TSU_CORE_RESET,
      MI_S_DWR  => tsu_dwr,
      MI_S_ADDR => tsu_addr,
      MI_S_BE   => tsu_be,
      MI_S_RD   => tsu_rd,
      MI_S_WR   => tsu_wr,
      MI_S_DRD  => tsu_drd,
      MI_S_ARDY => tsu_ardy,
      MI_S_DRDY => tsu_drdy
   );

   -- ----------------------------------------------------------------------------
   --                            TSU CORE CLK DOMAIN
   -- ----------------------------------------------------------------------------

   --! If REGISTER_TS_OUTPUT is set to TRUE - register TS and TS_DV for one more time
   registered_ts : if REGISTER_TS_OUTPUT = true generate
      registered_ts_process : process(TSU_CORE_CLK)
      begin
         if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
            second_reg_realtime <= reg_realtime(95 downto 32);
            second_reg_ts_dv <= core_reg_ts_dv;
         end if;
      end process;

      TS    <= second_reg_realtime;
      TS_DV <= second_reg_ts_dv;
   end generate registered_ts;

   --! Else connect them directly to output
   not_registered_ts : if REGISTER_TS_OUTPUT = false generate
      TS    <= reg_realtime(95 downto 32);
      TS_DV <= core_reg_ts_dv;
   end generate not_registered_ts;

   -- -------------------------------------------------------
   --! TS_DV register (if set, timestamp is assumed as valid) (INTA register)
   --! mi -> tsu_core
   core_ts_dv_register : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (TSU_CORE_RESET = '1') then
            core_reg_ts_dv <= '0';
         elsif (mi_reg_ts_dv_we = '1' and tsu_be(0) = '1') then
            core_reg_ts_dv <= tsu_dwr(0); --!mi_reg_ts_dv;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------------
   --   BASIC THREE RESISTERS OF THE TIMESTAMP UNIT WHICH PRESERVE TIME INFORMATION
   -- --------------------------------------------------------------------------------

   -- -------------------------------------------------------
   --! RTR (real-time register)
   reg_rtr : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if (reg_rtr_we_0 = '1') then
            reg_realtime <= mi_reg_mi_data_high & mi_reg_mi_data_middle & mi_reg_mi_data_low;
         else
            reg_realtime <= add_result;
         end if;
      end if;
   end process;

   tsu_adder : entity work.tsu_adder
   port map (
      CLK        => TSU_CORE_CLK,
      RESET      => TSU_CORE_RESET,
      REG_RTR_WE => reg_rtr_we_0,
      REG_RTR    => reg_realtime,
      INCR_VALUE => incr_value,
      ADD_RESULT => add_result
   );

   -- --------------------------------------------------------------------------------
   --! INCR_REG - Incremental value register
   reg_incr_value : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (reg_incr_val_we = '1') then
            incr_value <= mi_reg_mi_data_middle(6 downto 0) & mi_reg_mi_data_low;
         end if;
      end if;
   end process reg_incr_value;

   -- -------------------------------------------------------
   --! PPS_REG (puls per second register). Due to inverted
   --! PPS_N signal we save RTR on descending edge of PPS_N
   reg_pulseps : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (PPS_N = '0' and pps_wr_en = '1') then
            reg_pulsepsec <= reg_realtime;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! Register for enabling write into reg_pulseps register
   reg_pps_en : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         pps_wr_en <= PPS_N;
      end if;
   end process;

   -- --------------------------------------------------------------------------------
   --! Write into control register indicator
   reg_write_req : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (mi_reg_cntrl_we = '1') then
            reg_write <= '1';
         else
            reg_write <= '0';
         end if;
      end if;
   end process reg_write_req;

   -- --------------------------------------------------------------------------------
   --! Choose register by address in reg_cntrl
   select_register : process(mi_reg_cntrl)
   begin
      --! Implicit values of select
      sel_reg_rtr_rd <= '0';
      sel_reg_rtr_wr <= '0';
      sel_reg_incr_val_rd <= '0';
      sel_reg_incr_val_wr <= '0';
      sel_reg_pulsepsec_wr <= '0';

      case (mi_reg_cntrl) is
         when "000" => sel_reg_incr_val_rd <= '1';    --! MI data  -> INCR_VAL
         when "001" => sel_reg_rtr_rd <= '1';         --! MI data  -> RTR
         when "100" => sel_reg_incr_val_wr <= '1';    --! INCR_VAL -> MI data
         when "101" => sel_reg_rtr_wr <= '1';         --! RTR      -> MI data
         when "111" => sel_reg_pulsepsec_wr <= '1';   --! REG_PPS  -> MI data
         when others => null;
      end case;

   end process select_register;

   -- --------------------------------------------------------------------------------
   --! Set write enable into register
     reg_rtr_we_0            <= sel_reg_rtr_rd and reg_write;
     reg_incr_val_we         <= sel_reg_incr_val_rd and reg_write;

   -- -------------------------------------------------------
   --! MI32 common data register low
   core_reg_mi_common_data_low : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (core_reg_mi_data_low_we = '1') then
            core_reg_mi_data_low <= core_reg_mi_data_input(31 downto 0);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! MI32 common data register middle
   core_reg_mi_common_data_middle : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (core_reg_mi_data_middle_we = '1') then
            core_reg_mi_data_middle <= core_reg_mi_data_input(63 downto 32);
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! MI32 common data register high
   core_reg_mi_common_data_high : process(TSU_CORE_CLK)
   begin
      if (TSU_CORE_CLK'event and TSU_CORE_CLK = '1') then
         if (core_reg_mi_data_high_we = '1') then
            core_reg_mi_data_high <= core_reg_mi_data_input(95 downto 64);
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------------
   --! Write to core_reg_mi_common_data mux
   to_core_reg_mi_common_data_mux : process(mi_reg_cntrl(1 downto 0), incr_value, reg_realtime, reg_pulsepsec)
   begin
      core_reg_mi_data_input <= (others => '0');

      case (mi_reg_cntrl(1 downto 0)) is
         when "00" => core_reg_mi_data_input(38 downto 0) <= incr_value;  --! INCR_VAL -> MI data
         when "01" => core_reg_mi_data_input <= reg_realtime;             --! RTR      -> MI data
         when "11" => core_reg_mi_data_input <= reg_pulsepsec;            --! REG_PPS  -> MI data
         when others => null;
      end case;
   end process;

   -- ----------------------------------------------------------------------------
   --                              MI32 CLK DOMAIN
   -- ----------------------------------------------------------------------------

   -- -------------------------------------------------------
   --! Register for control where data from/to MI32 bus should go, CNTRL_REG
   mi_reg_control : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if (mi_reg_cntrl_we = '1') then
            if (tsu_be(0) = '1') then mi_reg_cntrl <= tsu_dwr(2 downto 0); end if;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! MI32 common data register low
   mi_reg_mi_common_data_low : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if (mi_reg_mi_data_low_we = '1') then
            for i in 0 to tsu_be'high loop
               if tsu_be(i) = '1' then
                  mi_reg_mi_data_low(8*i+7 downto 8*i) <= tsu_dwr(8*i+7 downto 8*i);
               end if;
            end loop;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! MI32 common data register middle
   mi_reg_mi_common_data_middle : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if (mi_reg_mi_data_middle_we = '1') then
            for i in 0 to tsu_be'high loop
               if tsu_be(i) = '1' then
                  mi_reg_mi_data_middle(8*i+7 downto 8*i) <= tsu_dwr(8*i+7 downto 8*i);
               end if;
            end loop;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   --! MI32 common data register high
   mi_reg_mi_common_data_high : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if (mi_reg_mi_data_high_we = '1') then
            for i in 0 to tsu_be'high loop
               if tsu_be(i) = '1' then
                  mi_reg_mi_data_high(8*i+7 downto 8*i) <= tsu_dwr(8*i+7 downto 8*i);
               end if;
            end loop;
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------
   --                            ARDY MUX
   -- ----------------------------------------------------------------------------

   --! Mux for ARDY signal
   tsu_ardy <= tsu_rd or tsu_wr;

   -- ----------------------------------------------------------------------------
   --                            DRDY MUX
   -- ----------------------------------------------------------------------------

   --! DRDY signal for read from register
   drdy_mux : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         core_reg_mi_data_low_drdy    <= tsu_rd and sel_reg_mi_data_low;
         core_reg_mi_data_middle_drdy <= tsu_rd and sel_reg_mi_data_middle;
         core_reg_mi_data_high_drdy   <= tsu_rd and sel_reg_mi_data_high;
      end if;
   end process;

   --! Register MI.DRDY (data output)
   reg_mi32_drdy : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         if TSU_CORE_RESET = '1' then
            tsu_drdy   <= '0';
            tsu_drdy_r <= '0';
         else
            tsu_drdy_r <= tsu_rd;
            tsu_drdy   <= tsu_drdy_r;
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------
   --                            DRD REGISTER
   -- ----------------------------------------------------------------------------

   --! Register MI.DRD (data output)
   reg_mi32_drd : process(TSU_CORE_CLK)
   begin
      if (rising_edge(TSU_CORE_CLK)) then
         tsu_drd <= drd_mux;
      end if;
   end process;

   mux_mi32_drd : process(core_reg_mi_data_low_drdy, core_reg_mi_data_low, core_reg_mi_data_middle_drdy, core_reg_mi_data_middle,
                          core_reg_mi_data_high_drdy, core_reg_mi_data_high)
   begin
      if core_reg_mi_data_low_drdy = '1' then
         drd_mux <= core_reg_mi_data_low;
      elsif core_reg_mi_data_middle_drdy = '1' then
         drd_mux <= core_reg_mi_data_middle;
      elsif core_reg_mi_data_high_drdy = '1' then
         drd_mux <= core_reg_mi_data_high;
      else
         drd_mux <= (others => '0');
      end if;
   end process;

   -- --------------------------------------------------------------------------------
   --! Choose register by address in MI32.ADDR
   select_demux : process(tsu_addr)
   begin
      --! Implicit values of select
      sel_reg_mi_data_low <= '0';
      sel_reg_mi_data_middle <= '0';
      sel_reg_mi_data_high <= '0';
      sel_reg_cntrl <= '0';
      sel_reg_inta <= '0';

      case (tsu_addr(8-1 downto 0)) is --! Only the lowest 8 bits are considered
         when X"00" => sel_reg_mi_data_low <= '1';       --! Low part of common mi32 data register
         when X"04" => sel_reg_mi_data_middle <= '1';    --! Middle part of common mi32 data register
         when X"08" => sel_reg_mi_data_high <= '1';      --! High part of common mi32 data register
         when X"0C" => sel_reg_cntrl <= '1';             --! MI32 control register
         when X"14" => sel_reg_inta <= '1';              --! INTA register selected
         when others => null;
      end case;

   end process select_demux;

   -- --------------------------------------------------------------------------------
   --! Set write enable into register
   mi_reg_mi_data_low_we      <= sel_reg_mi_data_low and tsu_wr;
   mi_reg_mi_data_middle_we   <= sel_reg_mi_data_middle and tsu_wr;
   mi_reg_mi_data_high_we     <= sel_reg_mi_data_high and tsu_wr;
   mi_reg_cntrl_we            <= sel_reg_cntrl and tsu_wr;
   mi_reg_ts_dv_we            <= sel_reg_inta and tsu_wr;

   core_reg_mi_data_low_we    <= (sel_reg_rtr_wr or sel_reg_incr_val_wr or sel_reg_pulsepsec_wr) and reg_write;
   core_reg_mi_data_middle_we <= (sel_reg_rtr_wr or sel_reg_incr_val_wr or sel_reg_pulsepsec_wr) and reg_write;
   core_reg_mi_data_high_we   <= (sel_reg_rtr_wr or sel_reg_pulsepsec_wr) and reg_write;

end architecture;
