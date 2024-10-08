-- mfb_merger_old.vhd: MFB+MVB bus merger
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------
-- Merges two input MVB+MFB interfaces in one output interface
-- Contains input FIFOs and output PIPEs.

-- This architecture has not been verified, as it is not supposed to be used.
-- Use architecture FULL instead!

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture OLD of MFB_MERGER is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    constant INPUT_FIFOXM_SIZE : integer := max(MVB_ITEMS,MFB_REGIONS)*INPUT_FIFO_SIZE;
    constant SOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant MFB_DATA_WIDTH    : integer := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_FIFOXM_WIDTH  : integer := MFB_DATA_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+2;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- Extended RX MFB signals
    signal RX_MFB_DATA_ext    : slv_array_t(1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal RX_MFB_SOF_ext     : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);
    signal RX_MFB_EOF_ext     : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);
    signal RX_MFB_SOF_POS_ext : slv_array_t(1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal RX_MFB_EOF_POS_ext : slv_array_t(1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal RX_MFB_VLD_ext     : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);
    signal RX_MFB_SRC_RDY_ext : std_logic_vector(1 downto 0);
    signal RX_MFB_DST_RDY_ext : std_logic_vector(1 downto 0);

    -- input MVB FIFOXM interface
    signal mvb_in_fifoxm_di    : slv_array_t(1 downto 0)(MVB_ITEMS*(HDR_WIDTH+1)-1 downto 0);
    signal mvb_in_fifoxm_wr    : slv_array_t(1 downto 0)(MVB_ITEMS-1 downto 0);
    signal mvb_in_fifoxm_full  : std_logic_vector(1 downto 0);
    signal mvb_in_fifoxm_do    : slv_array_t(1 downto 0)(MVB_ITEMS*(HDR_WIDTH+1)-1 downto 0);
    signal mvb_in_fifoxm_rd    : slv_array_t(1 downto 0)(MVB_ITEMS-1 downto 0);
    signal mvb_in_fifoxm_empty : slv_array_t(1 downto 0)(MVB_ITEMS-1 downto 0);

    signal mvb_in_fifoxm_do_hdr     : slv_array_2d_t(1 downto 0)(MVB_ITEMS-1 downto 0)(HDR_WIDTH-1 downto 0);
    signal mvb_in_fifoxm_do_payload : slv_array_t(1 downto 0)(MVB_ITEMS-1 downto 0);

    -- input MFB FIFOXM interface
    signal mfb_in_fifoxm_di    : slv_array_t(1 downto 0)(MFB_REGIONS*MFB_FIFOXM_WIDTH-1 downto 0);
    signal mfb_in_fifoxm_wr    : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_in_fifoxm_full  : std_logic_vector(1 downto 0);
    signal mfb_in_fifoxm_do    : slv_array_t(1 downto 0)(MFB_REGIONS*MFB_FIFOXM_WIDTH-1 downto 0);
    signal mfb_in_fifoxm_rd    : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_in_fifoxm_empty : slv_array_t(1 downto 0)(MFB_REGIONS-1 downto 0);

    signal mfb_in_fifoxm_do_data    : slv_array_2d_t(1 downto 0)(MFB_REGIONS-1 downto 0)(MFB_DATA_WIDTH-1 downto 0);
    signal mfb_in_fifoxm_do_sof_pos : slv_array_2d_t(1 downto 0)(MFB_REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal mfb_in_fifoxm_do_eof_pos : slv_array_2d_t(1 downto 0)(MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal mfb_in_fifoxm_do_sof     : slv_array_t   (1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_in_fifoxm_do_eof     : slv_array_t   (1 downto 0)(MFB_REGIONS-1 downto 0);

    -- switch
    signal switch_fifoxm_di    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_wr    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_full  : std_logic;
    signal switch_fifoxm_do    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_rd    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_empty : std_logic_vector(MVB_ITEMS-1 downto 0);

    -- MVB switching signals
    signal new_switch : std_logic;
    signal switch_reg : std_logic;

    -- MFB switching signals
    signal cont_pac     : std_logic;
    signal cont_pac_reg : std_logic;

    -- output MVB PIPE rx interface
    signal mvb_out_pipe_rx_hdr     : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal mvb_out_pipe_rx_vld     : std_logic_vector(MVB_ITEMS          -1 downto 0);
    signal mvb_out_pipe_rx_src_rdy : std_logic;
    signal mvb_out_pipe_rx_dst_rdy : std_logic;

    -- output MFB PIPE rx interface
    signal mfb_out_pipe_rx_data    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mfb_out_pipe_rx_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_out_pipe_rx_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_out_pipe_rx_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal mfb_out_pipe_rx_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal mfb_out_pipe_rx_src_rdy : std_logic;
    signal mfb_out_pipe_rx_dst_rdy : std_logic;

    ---------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- RX MFB extention unit
    -- -------------------------------------------------------------------------

    rx0_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS     => MFB_REGIONS   ,
        REGION_SIZE => MFB_REG_SIZE  ,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,

        REGION_AUX_EN => True        ,
        BLOCK_AUX_EN  => False       ,
        ITEM_AUX_EN   => False
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA       => RX0_MFB_DATA   ,
        RX_SOF_POS    => RX0_MFB_SOF_POS,
        RX_EOF_POS    => RX0_MFB_EOF_POS,
        RX_SOF        => RX0_MFB_SOF    ,
        RX_EOF        => RX0_MFB_EOF    ,
        RX_SRC_RDY    => RX0_MFB_SRC_RDY,
        RX_DST_RDY    => RX0_MFB_DST_RDY,

        TX_DATA       => RX_MFB_DATA_ext   (0),
        TX_SOF_POS    => RX_MFB_SOF_POS_ext(0),
        TX_EOF_POS    => RX_MFB_EOF_POS_ext(0),
        TX_SOF        => RX_MFB_SOF_ext    (0),
        TX_EOF        => RX_MFB_EOF_ext    (0),
        TX_REGION_VLD => RX_MFB_VLD_ext    (0),
        TX_SRC_RDY    => RX_MFB_SRC_RDY_ext(0),
        TX_DST_RDY    => RX_MFB_DST_RDY_ext(0)
    );

    rx1_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS     => MFB_REGIONS   ,
        REGION_SIZE => MFB_REG_SIZE  ,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,

        REGION_AUX_EN => True        ,
        BLOCK_AUX_EN  => False       ,
        ITEM_AUX_EN   => False
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA       => RX1_MFB_DATA   ,
        RX_SOF_POS    => RX1_MFB_SOF_POS,
        RX_EOF_POS    => RX1_MFB_EOF_POS,
        RX_SOF        => RX1_MFB_SOF    ,
        RX_EOF        => RX1_MFB_EOF    ,
        RX_SRC_RDY    => RX1_MFB_SRC_RDY,
        RX_DST_RDY    => RX1_MFB_DST_RDY,

        TX_DATA       => RX_MFB_DATA_ext   (1),
        TX_SOF_POS    => RX_MFB_SOF_POS_ext(1),
        TX_EOF_POS    => RX_MFB_EOF_POS_ext(1),
        TX_SOF        => RX_MFB_SOF_ext    (1),
        TX_EOF        => RX_MFB_EOF_ext    (1),
        TX_REGION_VLD => RX_MFB_VLD_ext    (1),
        TX_SRC_RDY    => RX_MFB_SRC_RDY_ext(1),
        TX_DST_RDY    => RX_MFB_DST_RDY_ext(1)
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input MVB fifoxms
    -- -------------------------------------------------------------------------

    mvb_input_fifoxm_in_gen : for i in 0 to MVB_ITEMS-1 generate
        mvb_in_fifoxm_di(0)((HDR_WIDTH+1)*i+HDR_WIDTH+1-1 downto (HDR_WIDTH+1)*i+1) <= RX0_MVB_HDR(HDR_WIDTH*(i+1)-1 downto HDR_WIDTH*i);
        mvb_in_fifoxm_di(0)((HDR_WIDTH+1)*i) <= RX0_MVB_PAYLOAD(i);

        mvb_in_fifoxm_di(1)((HDR_WIDTH+1)*i+HDR_WIDTH+1-1 downto (HDR_WIDTH+1)*i+1) <= RX1_MVB_HDR(HDR_WIDTH*(i+1)-1 downto HDR_WIDTH*i);
        mvb_in_fifoxm_di(1)((HDR_WIDTH+1)*i) <= RX1_MVB_PAYLOAD(i);
    end generate;

    mvb_in_fifoxm_wr(0) <= RX0_MVB_SRC_RDY and RX0_MVB_VLD;
    RX0_MVB_DST_RDY     <= not mvb_in_fifoxm_full(0);

    mvb_in_fifoxm_wr(1) <= RX1_MVB_SRC_RDY and RX1_MVB_VLD;
    RX1_MVB_DST_RDY     <= not mvb_in_fifoxm_full(1);

    mvb_input_fifoxm_gen : for i in 0 to 1 generate
        mvb_input_fifoxm_i : entity work.FIFOX_MULTI
        generic map(
            DATA_WIDTH     => HDR_WIDTH+1      ,
            ITEMS          => INPUT_FIFOXM_SIZE,
            WRITE_PORTS    => MVB_ITEMS        ,
            READ_PORTS     => MVB_ITEMS        ,
            RAM_TYPE       => "AUTO"           ,
            SAFE_READ_MODE => false            ,
            DEVICE         => DEVICE
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => mvb_in_fifoxm_di   (i),
            WR     => mvb_in_fifoxm_wr   (i),
            FULL   => mvb_in_fifoxm_full (i),
            DO     => mvb_in_fifoxm_do   (i),
            RD     => mvb_in_fifoxm_rd   (i),
            EMPTY  => mvb_in_fifoxm_empty(i)
        );
    end generate;

    mvb_input_fifoxm_out_gen : for i in 0 to 1 generate
        mvb_input_fifoxm_out_gen : for e in 0 to MVB_ITEMS-1 generate
            mvb_in_fifoxm_do_hdr(i)(e)     <= mvb_in_fifoxm_do(i)((HDR_WIDTH+1)*e+HDR_WIDTH+1-1 downto (HDR_WIDTH+1)*e+1);
            mvb_in_fifoxm_do_payload(i)(e) <= mvb_in_fifoxm_do(i)((HDR_WIDTH+1)*e);
        end generate;
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input MFB fifoxms
    -- -------------------------------------------------------------------------

    mfb_input_fifoxm_in_gen : for i in 0 to 1 generate
        mfb_input_fifoxm_in_i_gen : for e in 0 to MFB_REGIONS-1 generate
            mfb_in_fifoxm_di(i)(MFB_FIFOXM_WIDTH*(e+1)-1 downto MFB_FIFOXM_WIDTH*e)
                    <= RX_MFB_DATA_ext(i)(MFB_DATA_WIDTH*(e+1)-1 downto MFB_DATA_WIDTH*e)
                     & RX_MFB_SOF_POS_ext(i)(SOF_POS_WIDTH*(e+1)-1 downto SOF_POS_WIDTH*e)
                     & RX_MFB_EOF_POS_ext(i)(EOF_POS_WIDTH*(e+1)-1 downto EOF_POS_WIDTH*e)
                     & RX_MFB_SOF_ext(i)(e)
                     & RX_MFB_EOF_ext(i)(e);
            mfb_in_fifoxm_wr(i)(e) <= RX_MFB_VLD_ext(i)(e) and RX_MFB_SRC_RDY_ext(i);
        end generate;
        RX_MFB_DST_RDY_ext(i) <= not mfb_in_fifoxm_full(i);
    end generate;

    mfb_input_fifoxm_gen : for i in 0 to 1 generate
        mfb_input_fifoxm_i : entity work.FIFOX_MULTI
        generic map(
            DATA_WIDTH     => MFB_FIFOXM_WIDTH ,
            ITEMS          => INPUT_FIFOXM_SIZE,
            WRITE_PORTS    => MFB_REGIONS      ,
            READ_PORTS     => MFB_REGIONS      ,
            RAM_TYPE       => "AUTO"           ,
            SAFE_READ_MODE => false            ,
            DEVICE         => DEVICE
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => mfb_in_fifoxm_di   (i),
            WR     => mfb_in_fifoxm_wr   (i),
            FULL   => mfb_in_fifoxm_full (i),
            DO     => mfb_in_fifoxm_do   (i),
            RD     => mfb_in_fifoxm_rd   (i),
            EMPTY  => mfb_in_fifoxm_empty(i)
        );
    end generate;

    mfb_input_fifoxm_out_gen : for i in 0 to 1 generate
        mfb_input_fifoxm_out_i_gen : for e in 0 to MFB_REGIONS-1 generate
            mfb_in_fifoxm_do_data(i)(e)    <= mfb_in_fifoxm_do(i)(MFB_FIFOXM_WIDTH*e+MFB_DATA_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+1+1-1 downto MFB_FIFOXM_WIDTH*e+SOF_POS_WIDTH+EOF_POS_WIDTH+1+1);
            mfb_in_fifoxm_do_sof_pos(i)(e) <= mfb_in_fifoxm_do(i)(MFB_FIFOXM_WIDTH*e+SOF_POS_WIDTH+EOF_POS_WIDTH+1+1-1 downto MFB_FIFOXM_WIDTH*e+EOF_POS_WIDTH+1+1);
            mfb_in_fifoxm_do_eof_pos(i)(e) <= mfb_in_fifoxm_do(i)(MFB_FIFOXM_WIDTH*e+EOF_POS_WIDTH+1+1-1 downto MFB_FIFOXM_WIDTH*e+1+1);
            mfb_in_fifoxm_do_sof(i)(e)     <= mfb_in_fifoxm_do(i)(MFB_FIFOXM_WIDTH*e+1);
            mfb_in_fifoxm_do_eof(i)(e)     <= mfb_in_fifoxm_do(i)(MFB_FIFOXM_WIDTH*e);
        end generate;
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB sending
    -- -------------------------------------------------------------------------

    -- input selecting logic + sending of mvb data
    mvb_sending_pr : process(all)
        variable switch_i : integer;
        variable mvb_ptr  : integer;
        variable switched : boolean;
    begin
        -- default values
        mvb_out_pipe_rx_hdr     <= (others => 'X');
        mvb_out_pipe_rx_vld     <= (others => '0');
        mvb_out_pipe_rx_src_rdy <= '0';

        switch_fifoxm_di <= (others => '0');
        switch_fifoxm_wr <= (others => '0');

        mvb_in_fifoxm_rd <= (others => (others => '0'));

        -- init variables
        switch_i := 1 when switch_reg='1' else 0;

        switched := false;
        mvb_ptr := 0;

        -- for each output item
        for i in 0 to MVB_ITEMS-1 loop
            if (mvb_in_fifoxm_empty(switch_i)(mvb_ptr)='1') then -- switch when current input has no mvb data
                switch_i := 1 when switch_i=0 else 0;
                exit when switched=true;
                mvb_ptr  := 0; -- read the other input from item 0
                switched := true;
            end if;

            -- set signals
            mvb_out_pipe_rx_hdr(HDR_WIDTH*(i+1)-1 downto HDR_WIDTH*i)
                    <= mvb_in_fifoxm_do_hdr(switch_i)(mvb_ptr);

            mvb_out_pipe_rx_vld(i)  <= not mvb_in_fifoxm_empty(switch_i)(mvb_ptr);
            if (mvb_in_fifoxm_empty(switch_i)(mvb_ptr)='0') then -- mvb_out_pipe_rx_src_rdy <= or mvb_out_pipe_rx_vld
                mvb_out_pipe_rx_src_rdy <= '1';
            end if;

            switch_fifoxm_di(i) <= '1' when switch_i=1 else '0';
            switch_fifoxm_wr(i) <= '1' when mvb_in_fifoxm_empty(switch_i)(mvb_ptr)='0' and mvb_out_pipe_rx_dst_rdy='1' and mvb_in_fifoxm_do_payload(switch_i)(mvb_ptr)='1' else '0'; -- write if header has payload

            mvb_in_fifoxm_rd(switch_i)(mvb_ptr) <= mvb_out_pipe_rx_dst_rdy;

            exit when mvb_in_fifoxm_empty(switch_i)(mvb_ptr)='1'; -- exit when not even this input has data
            mvb_ptr := mvb_ptr+1;
        end loop;

        new_switch <= '1' when switch_i=0 else '0'; -- switch again after reading one word
    end process;

    -- switch register
    switch_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (switch_fifoxm_full='0' and mvb_out_pipe_rx_dst_rdy='1') then
                switch_reg <= new_switch;
            end if;

            if (RESET='1') then
                switch_reg <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Switch decision fifoxm
    -- -------------------------------------------------------------------------

    switch_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH     => 1          ,
        ITEMS          => MVB_ITEMS*4,
        WRITE_PORTS    => MVB_ITEMS  ,
        READ_PORTS     => MVB_ITEMS  ,
        RAM_TYPE       => "AUTO"     ,
        SAFE_READ_MODE => false      ,
        DEVICE         => DEVICE
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => switch_fifoxm_di   ,
        WR     => switch_fifoxm_wr   ,
        FULL   => switch_fifoxm_full ,
        DO     => switch_fifoxm_do   ,
        RD     => switch_fifoxm_rd   ,
        EMPTY  => switch_fifoxm_empty
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MFB sending
    -- -------------------------------------------------------------------------

    -- send MFB regions based on switc infromation from switch_fifoxm
    mfb_sending_pr : process (all)
    -- Each output region can only have 1 SOF or 1 EOF.
    -- When MFB_REG_SIZE>1 then this limitation can lower the bus throughput!
        variable mfb_ptr       : i_array_t(1 downto 0);
        variable ptr1          : integer;
        variable sw_ptr        : integer;
        variable sof           : std_logic;
        variable eof           : std_logic;
        variable switch_i      : integer;
    begin
        -- default values
        mfb_out_pipe_rx_data     <= (others => 'X');
        mfb_out_pipe_rx_sof      <= (others => '0');
        mfb_out_pipe_rx_eof      <= (others => '0');
        mfb_out_pipe_rx_sof_pos  <= (others => 'X');
        mfb_out_pipe_rx_eof_pos  <= (others => 'X');

        mfb_out_pipe_rx_src_rdy  <= '0';

        switch_fifoxm_rd <= (others => '0');
        mfb_in_fifoxm_rd <= (others => (others => '0'));

        cont_pac <= '0';

        -- init variables
        mfb_ptr  := (others => 0);
        sw_ptr   := 0;
        sof      := not cont_pac_reg;
        eof      := '0';
        switch_i := 1 when switch_fifoxm_empty(sw_ptr)='1' else 0;

        -- for each output region
        for i in 0 to MFB_REGIONS-1 loop
            exit when sw_ptr=MVB_ITEMS; -- no more mvb items
            exit when switch_fifoxm_empty(sw_ptr)='1'; -- no more mvb items
            switch_i := 1 when switch_fifoxm_do(sw_ptr)='1' else 0;
            exit when mfb_in_fifoxm_empty(switch_i)(mfb_ptr(switch_i))='1'; -- wait for mfb data
            eof      := '1' when mfb_in_fifoxm_do_eof(switch_i)(mfb_ptr(switch_i))='1' and (sof='0' or mfb_in_fifoxm_do_sof_pos(switch_i)(mfb_ptr(switch_i)) <= mfb_in_fifoxm_do_eof_pos(switch_i)(mfb_ptr(switch_i))) else '0';

            -- set output region
            mfb_out_pipe_rx_data(MFB_DATA_WIDTH*(i+1)-1 downto MFB_DATA_WIDTH*i) <= mfb_in_fifoxm_do_data(switch_i)(mfb_ptr(switch_i));

            mfb_out_pipe_rx_sof(i) <= sof;
            mfb_out_pipe_rx_eof(i) <= eof; -- always should be '1' before loop break

            mfb_out_pipe_rx_sof_pos(SOF_POS_WIDTH*(i+1)-1 downto SOF_POS_WIDTH*i) <= mfb_in_fifoxm_do_sof_pos(switch_i)(mfb_ptr(switch_i));
            mfb_out_pipe_rx_eof_pos(EOF_POS_WIDTH*(i+1)-1 downto EOF_POS_WIDTH*i) <= mfb_in_fifoxm_do_eof_pos(switch_i)(mfb_ptr(switch_i));

            if (mfb_in_fifoxm_empty(switch_i)(mfb_ptr(switch_i))='0') then
                mfb_out_pipe_rx_src_rdy <= '1';
            end if;

            if (eof='1') then -- packet ends in this region
                if (mfb_in_fifoxm_do_sof(switch_i)(mfb_ptr(switch_i))='0' or mfb_in_fifoxm_do_sof_pos(switch_i)(mfb_ptr(switch_i))<=mfb_in_fifoxm_do_eof_pos(switch_i)(mfb_ptr(switch_i))) then -- new packet does not start in this region
                    mfb_in_fifoxm_rd(switch_i)(mfb_ptr(switch_i)) <= mfb_out_pipe_rx_dst_rdy; -- only actually read when out PIPE is ready
                    mfb_ptr(switch_i) := mfb_ptr(switch_i)+1;
                end if;
                switch_fifoxm_rd(sw_ptr) <= mfb_out_pipe_rx_dst_rdy; -- only actually read when out PIPE is ready
                cont_pac <= '0';
                sof := '1';
                sw_ptr := sw_ptr+1;
            else -- packet does not end
                cont_pac <= '1';
                sof := '0';
                mfb_in_fifoxm_rd(switch_i)(mfb_ptr(switch_i)) <= mfb_out_pipe_rx_dst_rdy; -- only actually read when out PIPE is ready
                mfb_ptr(switch_i) := mfb_ptr(switch_i)+1;
            end if;
        end loop;
    end process;

    -- packet continued to this mfb word
    cont_pac_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (mfb_out_pipe_rx_dst_rdy='1') then
                cont_pac_reg <= cont_pac;
            end if;

            if (RESET='1') then
                cont_pac_reg <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB out PIPE
    -- -------------------------------------------------------------------------

    mvb_out_pipe_i : entity work.MVB_PIPE
    generic map(
        ITEMS          => MVB_ITEMS,
        ITEM_WIDTH     => HDR_WIDTH,
        FAKE_PIPE      => false    ,
        USE_DST_RDY    => true     ,
        DEVICE         => DEVICE
    )
    port map(
        CLK           => CLK  ,
        RESET         => RESET,

        RX_DATA       => mvb_out_pipe_rx_hdr    ,
        RX_VLD        => mvb_out_pipe_rx_vld    ,
        RX_SRC_RDY    => mvb_out_pipe_rx_src_rdy,
        RX_DST_RDY    => mvb_out_pipe_rx_dst_rdy,

        TX_DATA       => TX_MVB_HDR    ,
        TX_VLD        => TX_MVB_VLD    ,
        TX_SRC_RDY    => TX_MVB_SRC_RDY,
        TX_DST_RDY    => TX_MVB_DST_RDY
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MFB out PIPE
    -- -------------------------------------------------------------------------

    mfb_out_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS        => MFB_REGIONS   ,
        REGION_SIZE    => MFB_REG_SIZE  ,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        FAKE_PIPE      => false         ,
        USE_DST_RDY    => true          ,
        DEVICE         => DEVICE
    )
    port map(
        CLK           => CLK  ,
        RESET         => RESET,

        RX_DATA       => mfb_out_pipe_rx_data   ,
        RX_SOF_POS    => mfb_out_pipe_rx_sof_pos,
        RX_EOF_POS    => mfb_out_pipe_rx_eof_pos,
        RX_SOF        => mfb_out_pipe_rx_sof    ,
        RX_EOF        => mfb_out_pipe_rx_eof    ,
        RX_SRC_RDY    => mfb_out_pipe_rx_src_rdy,
        RX_DST_RDY    => mfb_out_pipe_rx_dst_rdy,

        TX_DATA       => TX_MFB_DATA   ,
        TX_SOF_POS    => TX_MFB_SOF_POS,
        TX_EOF_POS    => TX_MFB_EOF_POS,
        TX_SOF        => TX_MFB_SOF    ,
        TX_EOF        => TX_MFB_EOF    ,
        TX_SRC_RDY    => TX_MFB_SRC_RDY,
        TX_DST_RDY    => TX_MFB_DST_RDY
    );

    -- -------------------------------------------------------------------------

end architecture;
