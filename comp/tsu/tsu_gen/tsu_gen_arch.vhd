-- tsu_gen_arch.vhd
--!
--! @file
--! \brief Architecture of GPS synchronized timestamp unit
--! \author Lukas Kekely <kekely@cesnet.cz>, Jakub Cabal <jakubcabal@gmail.com>
--! \date 2012
--!
--! @section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! Package containing max function.
use work.math_pack.all;

--! \brief Architecture of GPS synchronized timestamp unit
architecture BEHAVIORAL of TSU_GEN is

   --! \name TSU core signals
   signal tsu_core_pps_n                : std_logic;
   signal tsu_core_drdy                 : std_logic;
   signal tsu_core_ardy                 : std_logic;
   signal tsu_core_drd                  : std_logic_vector(31 downto 0);
   signal tsu_dwr                       : std_logic_vector(31 downto 0);
   signal tsu_addr                      : std_logic_vector(31 downto 0);
   signal tsu_be                        : std_logic_vector(3 downto 0);
   signal tsu_rd                        : std_logic;
   signal tsu_wr                        : std_logic;

   --! \name Register signals
   signal mi_detect_pps_reg0            : std_logic;
   signal mi_detect_pps_reg1            : std_logic;
   signal state_bits                    : std_logic_vector(31 downto 0);
   signal reg_src                       : std_logic_vector(31 downto 0);
   signal det_clk                       : std_logic;
   signal mi_clk_ref_now                : std_logic;
   signal mi_clk_ref_old                : std_logic;
   signal detect_pps_reg                : std_logic;
   signal detect_pps_reset              : std_logic_vector(3 downto 0);
   signal detect_pps_reset_zeros        : std_logic;
   signal sync_detect_pps_reset_zeros   : std_logic;
   signal sig_clk_sel                   : std_logic_vector(max(CLK_SEL_WIDTH-1,0) downto 0);
   signal sig_pps_sel                   : std_logic_vector(max(PPS_SEL_WIDTH-1,0) downto 0);
   signal sync_sig_pps_sel              : std_logic_vector(max(PPS_SEL_WIDTH-1,0) downto 0);

   --! \name CLK counters
   signal mi_clk_ref_cnt                : std_logic_vector(5 downto 0);
   signal clk_ref_cnt                   : std_logic_vector(3 downto 0) := "0000";
   signal clk_ref_xor                   : std_logic;

   --! \name MUX select signals
   signal sel_state_reg                 : std_logic;
   signal sel_pps_mux_cntrl             : std_logic;
   signal sel_freq                      : std_logic;
   signal sel_tsu_core_clk_mux_cntrl    : std_logic;
   signal sel_src                       : std_logic;

   --! \name Write enable signals
   signal reg_pps_mux_cntrl_we          : std_logic;
   signal reg_tsu_core_clk_mux_cntrl_we : std_logic;

   --! \name DRDY signals
   signal detect_drdy                   : std_logic;
   signal freq_drdy                     : std_logic;
   signal src_drdy                      : std_logic;
   signal clk_mux_drdy                  : std_logic;
   signal pps_mux_drdy                  : std_logic;
   signal mi_drd_mux                    : std_logic_vector(31 downto 0);

   --! \name Fractional part to ns conversion signals
   signal ts_from_tsu_core              : std_logic_vector(63 downto 0);
   signal ts_to_ts_ns                   : std_logic_vector(63 downto 0);

    signal mi_rd_int                    : std_logic;
    signal mi_cs_filter                 : std_logic;
    signal reg_mi_busy                  : std_logic := '0';

begin
   --! \name

   --! \brief Instance of core unit of whole timestamp unit
   --! \details There are registers for counting real-time inside.
   tsu_cv2_core_i : entity work.TSU_CV2_CORE
     generic map (
       REGISTER_TS_OUTPUT => false,
       DEVICE             => DEVICE
     ) port map (
       MI32_CLK       => MI_CLK,
       MI32_RESET     => MI_RESET,

       DWR            => tsu_dwr,
       ADDR           => tsu_addr,
       RD             => tsu_rd,
       WR             => tsu_wr,
       BE             => tsu_be,
       DRD            => tsu_core_drd,
       ARDY           => tsu_core_ardy,
       DRDY           => tsu_core_drdy,

       PPS_N          => tsu_core_pps_n,
       TSU_CORE_CLK   => CLK,
       TSU_CORE_RESET => RESET,

       TS             => ts_from_tsu_core,
       TS_DV          => TS_DV
     );

    mi_rd_int <= MI_RD and not reg_mi_busy;

    mi_cs_filter <= sel_state_reg or sel_pps_mux_cntrl or sel_freq or sel_tsu_core_clk_mux_cntrl or sel_src;

   CORE_MI32_FILTER : process(MI_CLK)
   begin
      if (rising_edge(MI_CLK)) then
         tsu_dwr  <= MI_DWR;
         tsu_addr <= MI_ADDR;
         tsu_be   <= MI_BE;
         if (mi_cs_filter or (tsu_core_ardy and (tsu_rd or tsu_wr))) = '1' then
            tsu_rd <= '0';
            tsu_wr <= '0';
         else
            tsu_rd <= mi_rd_int;
            tsu_wr <= MI_WR;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
-- TIMESTAMP FORMAT CONVERT - FRACTIONAL TO NANOSECOND
-- ----------------------------------------------------------------------------

   ts_format_convertor: entity work.tsu_convertor
   generic map(
      TS_MULT_SMART_DSP => TS_MULT_SMART_DSP,
      TS_MULT_USE_DSP   => TS_MULT_USE_DSP
   )
   port map(
      CLK   => CLK,
      RESET => RESET,
      TS    => ts_from_tsu_core,
      TS_NS => ts_to_ts_ns
   );

   TS    <= ts_from_tsu_core;
   TS_NS <= ts_to_ts_ns;

-- --------------------------------------------------------
--         Detection of active source clk signals
-- --------------------------------------------------------

   --! Detection of active main clock
   clk_det_cnt_cv : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         clk_ref_cnt <= clk_ref_cnt + '1';
      end if;
   end process;

   --! Reclock main clock detection to MI32 clock
   --! Open-loop
   clk_ref_reclock: entity work.ASYNC_OPEN_LOOP
   generic map(
      IN_REG  => false,    --! We do not use!
      TWO_REG => false
   )
   port map(
      ACLK     => CLK,
      BCLK     => MI_CLK,
      ARST     => RESET,
      BRST     => MI_RESET,
      ADATAIN  => clk_ref_cnt(3),
      BDATAOUT => mi_clk_ref_now
   );

   --! OLD_REF_CLK Register
   old_ref_clk : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         mi_clk_ref_old  <= mi_clk_ref_now;
      end if;
   end process;

   clk_ref_xor <= mi_clk_ref_now xor mi_clk_ref_old;

   --! MI32 clock counter for main clock detection
   clk_det_cnt_cv_mi : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         if (clk_ref_xor = '1') then
            mi_clk_ref_cnt <= (others => '0');
         else
            mi_clk_ref_cnt <= mi_clk_ref_cnt + '1';
         end if;
      end if;
   end process;

   --! Main clock detection register
   clk_detect_register : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         if (mi_clk_ref_cnt(5) = '1') then
            det_clk <= '0';
         else
            if (clk_ref_xor = '1') then
               det_clk <= '1';
            end if;
         end if;
      end if;
   end process;

-- --------------------------------------------------------
--         Processing of PPS_N signal
-- --------------------------------------------------------

   tsu_pps_processing : entity work.tsu_pps_processing
   port map (
      CLK              => CLK,
      RESET            => RESET,
      PPS_N            => PPS_N,
      DETECT_PPS_RESET => sync_detect_pps_reset_zeros,
      CORE_PPS_N       => tsu_core_pps_n,
      DETECT_PPS       => detect_pps_reg
   );

   --! Reclocks PPS detection register to MI32 frequency
   --! Open-loop
   detect_reclock: entity work.ASYNC_OPEN_LOOP
   generic map(
      IN_REG  => false,    --! We do not use!
      TWO_REG => false
   )
   port map(
      ACLK     => CLK,
      BCLK     => MI_CLK,
      ARST     => RESET,
      BRST     => MI_RESET,
      ADATAIN  => detect_pps_reg,
      BDATAOUT => mi_detect_pps_reg1
   );

-- ----------------------------------------------------------------------------
--                              MI CLK DOMAIN
-- ----------------------------------------------------------------------------

   --! \brief Address register for mux to choose source PPS signal controlled by SW, SEL_PPS register
   pps_sel_gen : if PPS_SEL_WIDTH > 0 generate
      pps_mux_cntrl_reg : process(MI_CLK)
      begin
         if (MI_CLK'event and MI_CLK = '1') then
            if (MI_RESET = '1') then
               sig_pps_sel  <= (others => '0');
            elsif (reg_pps_mux_cntrl_we = '1' and MI_BE(0) = '1') then
               sig_pps_sel  <= MI_DWR(max(PPS_SEL_WIDTH-1,0) downto 0);
            end if;
         end if;
      end process;

      --! Synchronize sig_pps_sel to TSU clock domain
      bus_handshake_pps_sel: entity work.ASYNC_BUS_HANDSHAKE
      generic map (
         DATA_WIDTH => max(PPS_SEL_WIDTH,0)
      )
      port map (
         --! A clock domain
         ACLK       => MI_CLK,
         ARST       => MI_RESET,
         ADATAIN    => sig_pps_sel,
         ASEND      => '1',
         AREADY     => open,

         --! B clock domain
         BCLK       => CLK,
         BRST       => RESET,
         BDATAOUT   => sync_sig_pps_sel,
         BLOAD      => '1',
         BVALID     => open
      );
   end generate;
   no_pps_sel_gen : if PPS_SEL_WIDTH <= 0 generate
      sig_pps_sel <= "0";
      sync_sig_pps_sel <= "0";
   end generate;
   PPS_SEL <= sync_sig_pps_sel;

   --! \brief Address register for mux to choose source CLK signal controlled by SW, SEL_CLK register
   clk_sel_gen : if CLK_SEL_WIDTH > 0 generate
      clk_mux_cntrl_reg : process(MI_CLK)
      begin
         if (MI_CLK'event and MI_CLK = '1') then
            if (MI_RESET = '1') then
               sig_clk_sel  <= (others => '0');
            elsif (reg_tsu_core_clk_mux_cntrl_we = '1' and MI_BE(0) = '1') then
               sig_clk_sel <= MI_DWR(CLK_SEL_WIDTH-1 downto 0);
            end if;
         end if;
      end process;
   end generate;
   no_clk_sel_gen : if CLK_SEL_WIDTH <= 0 generate
      sig_clk_sel <= "0";
   end generate;
   CLK_SEL <= sig_clk_sel;

   --! MI32-accessible register to get the number of CLK and PPS sources
   reg_src <= CLK_SRC & PPS_SRC;

   --! Detects PPS source change
   detect_pps_reset_p : process(MI_CLK)
   begin
      if MI_CLK'event and MI_CLK = '1' then
         if MI_RESET = '1' then
            detect_pps_reset <= (others => '0');
         else
            if reg_pps_mux_cntrl_we = '1' and MI_BE(0) = '1' then
               detect_pps_reset <= "0001";
            elsif detect_pps_reset /= "0000" then
               detect_pps_reset <= detect_pps_reset + 1;
            end if;
         end if;
      end if;
   end process;

   --! Detects PPS reset zeros
   detect_pps_reset_zeros_p : process(MI_CLK)
   begin
      if MI_CLK'event and MI_CLK = '1' then
         if detect_pps_reset = "0000" then
            detect_pps_reset_zeros <= '0';
         else
            detect_pps_reset_zeros <= '1';
         end if;
      end if;
   end process;

   --! Synchronize detect_pps_reset_zeros to tsu clock domain
   detect_pps_reset_reclock: entity work.ASYNC_RESET
   generic map(
      TWO_REG => false
   )
   port map(
      CLK        => CLK,
      ASYNC_RST  => detect_pps_reset_zeros,
      OUT_RST(0) => sync_detect_pps_reset_zeros
   );

-- --------------------------------------------------------
--         DRDY, DRD, ARDY
-- --------------------------------------------------------

   --! DRDY signal for read from register
   ardy_drdy_detect_pps_n : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         freq_drdy   <= mi_rd_int and sel_freq;
         detect_drdy <= mi_rd_int and sel_state_reg;
         src_drdy    <= mi_rd_int and sel_src;
         pps_mux_drdy<= mi_rd_int and sel_pps_mux_cntrl;
         clk_mux_drdy<= mi_rd_int and sel_tsu_core_clk_mux_cntrl;
      end if;
   end process;

   --! Register MI.DRDY (data output)
   reg_mi32_drdy : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         if MI_RESET = '1' then
            MI_DRDY <= '0';
         else
            MI_DRDY <= freq_drdy or detect_drdy or tsu_core_drdy or src_drdy or pps_mux_drdy or clk_mux_drdy;
         end if;
      end if;
   end process;

   --! Register MI.DRD (data output)
   reg_mi32_drd : process(MI_CLK)
   begin
      if (MI_CLK'event and MI_CLK = '1') then
         MI_DRD <= mi_drd_mux;
      end if;
   end process;

   mux_mi32_drd : process(CLK_FREQ,state_bits,reg_src,sig_pps_sel,sig_clk_sel,tsu_core_drd,
                          freq_drdy,detect_drdy,src_drdy,pps_mux_drdy,clk_mux_drdy)
   begin
      if freq_drdy = '1' then
         mi_drd_mux <= CLK_FREQ;
      elsif detect_drdy = '1' then
         mi_drd_mux <= state_bits;
      elsif src_drdy = '1' then
         mi_drd_mux <= reg_src;
      elsif pps_mux_drdy = '1' then
         mi_drd_mux <= (31 downto max(PPS_SEL_WIDTH,1) => '0') & sig_pps_sel;
      elsif clk_mux_drdy = '1' then
         mi_drd_mux <= (31 downto max(CLK_SEL_WIDTH,1) => '0') & sig_clk_sel;
      else
         mi_drd_mux <= tsu_core_drd;
      end if;
   end process;

    mi_busy_p: process(MI_CLK)
    begin
        if rising_edge(MI_CLK) then
            if (MI_RESET = '1') then
                reg_mi_busy <= '0';
            elsif tsu_core_drdy = '1' then
                reg_mi_busy <= '0';
            elsif (tsu_rd and tsu_core_ardy) = '1' then
                reg_mi_busy <= '1';
            end if;
        end if;
    end process;

   --! State registers in the unit connected to mi32
   state_bits <= X"0000000" & "00" & det_clk & mi_detect_pps_reg1;

   --! Mux for ARDY signal
   MI_ARDY <= (mi_cs_filter and (mi_rd_int or MI_WR)) or tsu_core_ardy;

   --! \brief Choose register by address in MI32.ADDR
   --! \details Address space: \n
   --! 0x10 = State register, detection of clk and pps activity (R) \n
   --! 0x18 = PPS source multiplexor address (RW) \n
   --! 0x1C = Actual TSU clock frequency (R) \n
   --! 0x20 = TSU clock source multiplexor address (RW) \n
   --! 0x24 = Number of available CLK and PPS sources (R) \n
   select_demux : process(MI_ADDR)
   begin
      --! Implicit values of select
      sel_state_reg              <= '0';
      sel_pps_mux_cntrl          <= '0';
      sel_freq                   <= '0';
      sel_tsu_core_clk_mux_cntrl <= '0';
      sel_src                    <= '0';

      case (MI_ADDR(7 downto 0)) is
         when X"10" => sel_state_reg <= '1';               --! State register (detects clk and pps sources)
         when X"18" => sel_pps_mux_cntrl <= '1';           --! PPS source multiplexor address
         when X"1C" => sel_freq <= '1';                    --! TSU frequency
         when X"20" => sel_tsu_core_clk_mux_cntrl <= '1';  --! tsu_core clk select
         when X"24" => sel_src <= '1';
         when others => null;
      end case;
   end process;

   --! Set write enable into register
   reg_pps_mux_cntrl_we          <= sel_pps_mux_cntrl and MI_WR;
   reg_tsu_core_clk_mux_cntrl_we <= sel_tsu_core_clk_mux_cntrl and MI_WR;

end architecture;
