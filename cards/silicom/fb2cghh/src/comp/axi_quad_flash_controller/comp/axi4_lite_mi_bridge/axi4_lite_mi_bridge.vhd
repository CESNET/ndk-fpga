-- axi4_lite_mi_bridge.vhd: Control unit for merging AXI protocol and MI32 protocol
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- This component is bridge unit between MI32 protocol and AXI Quad SPI protocol.
-- To keep code simple, there is used 3-state FSM. Idle state is switching states
-- between reading and writing state based on input MI flags.
-- The link to AXI Quad SPI IP core is following:
-- https://docs.xilinx.com/r/en-US/pg153-axi-quad-spi/AXI-Quad-SPI-v3.2-LogiCORE-IP-Product-Guide
entity AXI4_LITE_MI_BRIDGE is
    generic(
        -- Address width of AXI
        G_AXI_ADDR_WIDTH : integer := 7;
        -- 9th bit to determine if the request is for this component or not
        G_MI_ADDR_WIDTH  : integer := 8;
        -- Data width of AXI
        G_AXI_DATA_WIDTH : integer := 32
        
        );
    port(
        CLK         : in  std_logic;
        RST         : in  std_logic;

        -- Write Address Channel ports
        AWADDR      : out std_logic_vector(G_AXI_ADDR_WIDTH - 1 downto 0);
        AWVALID     : out std_logic; 
        AWREADY     : in  std_logic;

        -- Write Data Channel ports 
        WDATA       : out std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
        WSTRB       : out std_logic_vector((G_AXI_DATA_WIDTH/8)-1 downto 0);
        WVALID      : out std_logic;
        WREADY      : in  std_logic;

        -- Write Response Channel ports
        BRESP       : in  std_logic_vector(1 downto 0);
        BVALID      : in  std_logic;
        BREADY      : out std_logic;

        -- Read Address Channel ports
        ARADDR      : out std_logic_vector(G_AXI_ADDR_WIDTH - 1 downto 0); 
        ARVALID     : out std_logic; 
        ARREADY     : in  std_logic; 

        -- Read Data Channel ports 
        RDATA       : in  std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
        RRESP       : in  std_logic_vector(1 downto 0);
        RVALID      : in  std_logic;
        RREADY      : out std_logic;

        -- MI32 protocol signals 
        AXI_MI_ADDR : in  std_logic_vector(G_MI_ADDR_WIDTH - 1 downto 0);
        AXI_MI_DWR  : in  std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
        AXI_MI_WR   : in  std_logic;
        AXI_MI_RD   : in  std_logic;
        AXI_MI_BE   : in  std_logic_vector((G_AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_MI_ARDY : out std_logic;
        AXI_MI_DRD  : out std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
        AXI_MI_DRDY : out std_logic
    );
end entity;

architecture FULL of AXI4_LITE_MI_BRIDGE is

    type t_fsm_axi_bridge is (
                            st_idle,        -- waiting for MI request 
                            st_wr_response, -- response to WR flag
                            st_rd_response  -- response to RD flag
                            );       

    -- Control logic (FSM)
    signal state, next_state: t_fsm_axi_bridge := st_idle;
    signal awvalid_reg_d      : std_logic :='0';
    signal awvalid_reg_q      : std_logic :='0';
    signal wvalid_reg_d       : std_logic :='0';
    signal wvalid_reg_q       : std_logic :='0';
    signal arvalid_reg_d      : std_logic :='0';
    signal arvalid_reg_q      : std_logic :='0';

    signal bvalid_reg_d       : std_logic;
    signal bvalid_reg_q       : std_logic;

begin

    WSTRB   <= AXI_MI_BE;
    WDATA   <= AXI_MI_DWR;

    AXI_MI_DRD <= RDATA;

    AWADDR  <= AXI_MI_ADDR(6 downto 0);
    ARADDR  <= AXI_MI_ADDR(6 downto 0);
    
    AWVALID <= AXI_MI_WR when awvalid_reg_q = '1' else '0';
    WVALID  <= AXI_MI_WR when wvalid_reg_q  = '1' else '0';
    ARVALID <= AXI_MI_RD when arvalid_reg_q = '1' else '0';

    process (clk)
    begin 
        if rising_edge(clk) then
            if RST = '1' then
                state             <= st_idle;
                awvalid_reg_q     <= '0';
                wvalid_reg_q      <= '0';
                arvalid_reg_q     <= '0';
                bvalid_reg_q      <= '0';
            else
                state             <= next_state;
                awvalid_reg_q     <= awvalid_reg_d;
                wvalid_reg_q      <= wvalid_reg_d;
                arvalid_reg_q     <= arvalid_reg_d;
                bvalid_reg_q      <= bvalid_reg_d;
            end if;
        end if;
    end process;  
   
    --delay register
    bvalid_reg_d <= BVALID;

    fsm_p: process (state, AXI_MI_WR, AXI_MI_RD,AWREADY, ARREADY, WREADY, BVALID, RVALID, RRESP, bvalid_reg_q,
                    awvalid_reg_q, wvalid_reg_q, arvalid_reg_q, BRESP)
    begin
        next_state      <= state;
        awvalid_reg_d   <= awvalid_reg_q;
        wvalid_reg_d    <= wvalid_reg_q;
        arvalid_reg_d   <= arvalid_reg_q;
        BREADY          <= '0';
        AXI_MI_ARDY     <= '0';
        AXI_MI_DRDY     <= '0';
        RREADY          <= '0';
        
        case (state) is
            when st_idle     =>
                awvalid_reg_d <= '0';
                wvalid_reg_d  <= '0';
                
                --Request for write
                if AXI_MI_WR = '1' then 
                    next_state    <= st_wr_response;
                    awvalid_reg_d <= '1';
                    wvalid_reg_d  <= '1';
                end if;

                --Request for read
                if AXI_MI_RD = '1' then
                    next_state    <= st_rd_response;
                    arvalid_reg_d <= '1';
                end if;

            when st_wr_response =>
                -- AXI protocol 
                BREADY  <= '1';
                if AWREADY = '1' then
                    awvalid_reg_d <= '0';
                end if;

                if WREADY = '1' then
                    wvalid_reg_d  <= '0';
                end if;

                -- Write process is done, ready for new data 
                if BVALID = '1' and BRESP /= "11"  then
                    next_state      <= st_idle;
                    AXI_MI_ARDY     <= '1';
                end if;
            
            when st_rd_response =>
                -- AXI protocol
                RREADY      <= '1';

                if ARREADY = '1' then 
                    arvalid_reg_d <= '0';
                end if;
                
                -- Read process is done, back to st_idle
                if RVALID = '1' and RRESP /= "11" then
                    next_state  <= st_idle;
                    AXI_MI_DRDY <= '1';
                    AXI_MI_ARDY <= '1';
                end if;
                
            when others      =>
                next_state <= st_idle;
        end case;
    end process;
    
end architecture;