-- frame_lng_check.vhd: MFB Frame length check
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_FRAME_LNG_CHECK is
generic(
    REGIONS     : natural := 4; -- any possitive value
    REGION_SIZE : natural := 8; -- any possitive value
    BLOCK_SIZE  : natural := 8; -- any possitive value
    ITEM_WIDTH  : natural := 8; -- any possitive value
    META_WIDTH  : natural := 8; -- any possitive value
    LNG_WIDTH   : natural := 14; -- width of length signals
    REG_BITMAP  : std_logic_vector(4-1 downto 0) := "1111"
);
port(
    -- =========================================================================
    -- CLOCK AND RESET
    -- =========================================================================
    CLK            : in  std_logic;
    RESET          : in  std_logic;
    -- =========================================================================
    -- INPUT MAX/MIN LENGTH INTERFACE
    -- =========================================================================
    FRAME_LNG_MAX  : in  std_logic_vector(LNG_WIDTH-1 downto 0);
    FRAME_LNG_MIN  : in  std_logic_vector(LNG_WIDTH-1 downto 0);
    -- =========================================================================
    -- INPUT MFB INTERFACE
    -- =========================================================================
    RX_DATA        : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_META        : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    RX_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
    RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
    RX_SRC_RDY     : in  std_logic;
    RX_DST_RDY     : out std_logic;
    -- =========================================================================
    -- OUTPUT MFB INTERFACE
    -- =========================================================================
    TX_DATA        : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_META        : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
    TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
    TX_SRC_RDY     : out std_logic;
    TX_DST_RDY     : in  std_logic;
    -- Error flag of maximum length, it is set from the MFB region where the
    -- frame length exceeds the specified maximum. It's valid when TX_SRC_RDY=1.
    TX_LNG_MAX_ERR : out std_logic_vector(REGIONS-1 downto 0);
    -- Error flag of minimum length, it is valid when TX_SRC_RDY=1 and TX_EOF=1.
    TX_LNG_MIN_ERR : out std_logic_vector(REGIONS-1 downto 0);
    -- Error flag of length overflow, it is valid when TX_SRC_RDY=1 and TX_EOF=1.
    TX_LNG_OVF_ERR : out std_logic_vector(REGIONS-1 downto 0);
    -- Frame length in MFB items is valid when is TX_SRC_RDY=1, value description:
        -- TX_EOF=1: Total length of ending frame..
        -- TX_EOF=0: Length of current frame calculated to end of current region.
    TX_FRAME_LNG   : out std_logic_vector(REGIONS*LNG_WIDTH-1 downto 0)
);
end entity;

architecture FULL of MFB_FRAME_LNG_CHECK is

   constant DATA_WIDTH   : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_SIZE : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_SIZE : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

   signal s_fl_data              : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_fl_meta              : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_fl_sof_pos           : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal s_fl_eof_pos           : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal s_fl_sof               : std_logic_vector(REGIONS-1 downto 0);
   signal s_fl_eof               : std_logic_vector(REGIONS-1 downto 0);
   signal s_fl_cof               : std_logic_vector(REGIONS-1 downto 0);
   signal s_fl_src_rdy           : std_logic;
   signal s_fl_temp_lng          : std_logic_vector(REGIONS*LNG_WIDTH-1 downto 0);
   signal s_fl_frame_lng         : std_logic_vector(REGIONS*LNG_WIDTH-1 downto 0);

   signal s_temp_lng_arr         : slv_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_frame_lng_arr        : slv_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_temp_lng_over_max    : std_logic_vector(REGIONS-1 downto 0);
   signal s_frame_lng_over_max   : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_frame             : std_logic_vector(REGIONS-1 downto 0);
   signal s_lng_over_max         : std_logic_vector(REGIONS-1 downto 0);

   signal s_lng_max_err          : std_logic_vector(REGIONS-1 downto 0);
   signal s_lng_max_err_last     : std_logic_vector(REGIONS downto 0);

   signal s_lng_below_min        : std_logic_vector(REGIONS-1 downto 0);
   signal s_lng_min_err          : std_logic_vector(REGIONS-1 downto 0);
   signal s_lng_ovf_err          : std_logic_vector(REGIONS-1 downto 0);

   signal s_frame_lng            : slv_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);

   signal s_reg1_data            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_reg1_meta            : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_reg1_sof_pos         : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal s_reg1_eof_pos         : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal s_reg1_sof             : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_eof             : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_src_rdy         : std_logic;

   signal s_reg1_adapter_err     : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_lng_max_err     : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_lng_min_err     : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_lng_ovf_err     : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_frame_len       : slv_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);

begin

    -- =========================================================================
    --  STAGE 1
    -- =========================================================================

    mfb_frame_lng_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE,
        ITEM_WIDTH     => ITEM_WIDTH,
        META_WIDTH     => META_WIDTH,
        LNG_WIDTH      => LNG_WIDTH,
        REG_BITMAP     => REG_BITMAP(3-1 downto 0),
        SATURATION     => True,
        IMPLEMENTATION => "parallel" -- "serial", "parallel"
    )
    port map(
        -- CLOCK AND RESET
        CLK          => CLK,
        RESET        => RESET,
        -- RX MFB INTERFACE
        RX_DATA      => RX_DATA,
        RX_META      => RX_META,
        RX_SOF_POS   => RX_SOF_POS,
        RX_EOF_POS   => RX_EOF_POS,
        RX_SOF       => RX_SOF,
        RX_EOF       => RX_EOF,
        RX_SRC_RDY   => RX_SRC_RDY,
        RX_DST_RDY   => RX_DST_RDY,
        -- TX MFB INTERFACE
        TX_DATA      => s_fl_data,
        TX_META      => s_fl_meta,
        TX_SOF_POS   => s_fl_sof_pos,
        TX_EOF_POS   => s_fl_eof_pos,
        TX_SOF       => s_fl_sof,
        TX_EOF       => s_fl_eof,
        TX_COF       => s_fl_cof,
        TX_TEMP_LNG  => s_fl_temp_lng, -- Frame length in items calculated to end of current region, valid when is SRC_RDY and not EOF
        TX_FRAME_LNG => s_fl_frame_lng, -- Frame length in items, valid when is SRC_RDY and EOF
        TX_FRAME_OVF => s_lng_ovf_err,
        TX_SRC_RDY   => s_fl_src_rdy,
        TX_DST_RDY   => TX_DST_RDY
    );

    -- =========================================================================
    --  STAGE 2
    -- =========================================================================

    -- -------------------------------------------------------------------------
    --  DETECT FRAMES WITH LENGHT OVER MAXIMUM VALUE
    -- -------------------------------------------------------------------------

    s_temp_lng_arr  <= slv_array_downto_deser(s_fl_temp_lng,REGIONS,LNG_WIDTH);
    s_frame_lng_arr <= slv_array_downto_deser(s_fl_frame_lng,REGIONS,LNG_WIDTH);

    -- detect lenght over max
    lng_over_max_g : for r in 0 to REGIONS-1 generate
        s_is_frame(r)           <= s_fl_sof(r) or s_fl_cof(r) or s_fl_eof(r);
        s_temp_lng_over_max(r)  <= '1' when (unsigned(s_temp_lng_arr(r)) >= unsigned(FRAME_LNG_MAX)) else '0';
        s_frame_lng_over_max(r) <= '1' when (unsigned(s_frame_lng_arr(r)) > unsigned(FRAME_LNG_MAX)) else '0';
        s_lng_over_max(r)       <= (s_temp_lng_over_max(r) and s_is_frame(r) and not s_fl_eof(r)) or (s_fl_eof(r) and s_frame_lng_over_max(r));
    end generate;

    -- distribution lenght max error to end of frame
    lng_max_err_g : for r in 0 to REGIONS-1 generate
        s_lng_max_err(r)        <= s_lng_over_max(r) or s_lng_max_err_last(r);
        s_lng_max_err_last(r+1) <= '0' when (s_fl_eof(r) = '1') else s_lng_max_err(r);
    end generate;

    lng_max_err_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_lng_max_err_last(0) <= '0';
            elsif (s_fl_src_rdy = '1' and TX_DST_RDY = '1') then
                s_lng_max_err_last(0) <= s_lng_max_err_last(REGIONS);
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  DETECT FRAMES WITH LENGHT BELOW MINIMUM VALUE
    -- -------------------------------------------------------------------------

    lng_min_err_g : for r in 0 to REGIONS-1 generate
        s_lng_below_min(r) <= '1' when (unsigned(s_frame_lng_arr(r)) < unsigned(FRAME_LNG_MIN)) else '0';
        s_lng_min_err(r)   <= s_lng_below_min(r) and s_fl_eof(r);
    end generate;

    -- -------------------------------------------------------------------------
    --  GENERATE FRAME LENGHT OUTPUT VALUE
    -- -------------------------------------------------------------------------

    frame_lng_g : for r in 0 to REGIONS-1 generate
        s_frame_lng(r) <= s_frame_lng_arr(r) when (s_fl_eof(r) = '1') else s_temp_lng_arr(r);
    end generate;

    -- =========================================================================
    --  OUTPUT REGISTERS
    -- =========================================================================

    reg1_g : if REG_BITMAP(3) generate
        reg1_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_DST_RDY = '1') then
                    s_reg1_data        <= s_fl_data;
                    s_reg1_meta        <= s_fl_meta;
                    s_reg1_sof_pos     <= s_fl_sof_pos;
                    s_reg1_eof_pos     <= s_fl_eof_pos;
                    s_reg1_sof         <= s_fl_sof;
                    s_reg1_eof         <= s_fl_eof;
                    s_reg1_lng_max_err <= s_lng_max_err;
                    s_reg1_lng_min_err <= s_lng_min_err;
                    s_reg1_lng_ovf_err <= s_lng_ovf_err;
                    s_reg1_frame_len   <= s_frame_lng;
                end if;
            end if;
        end process;

        reg1_vld_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_reg1_src_rdy <= '0';
                elsif (TX_DST_RDY = '1') then
                    s_reg1_src_rdy <= s_fl_src_rdy;
                end if;
            end if;
        end process;
    end generate;

    no_reg1_g : if not REG_BITMAP(3) generate
        s_reg1_data        <= s_fl_data;
        s_reg1_meta        <= s_fl_meta;
        s_reg1_sof_pos     <= s_fl_sof_pos;
        s_reg1_eof_pos     <= s_fl_eof_pos;
        s_reg1_sof         <= s_fl_sof;
        s_reg1_eof         <= s_fl_eof;
        s_reg1_lng_max_err <= s_lng_max_err;
        s_reg1_lng_min_err <= s_lng_min_err;
        s_reg1_lng_ovf_err <= s_lng_ovf_err;
        s_reg1_frame_len   <= s_frame_lng;
        s_reg1_src_rdy     <= s_fl_src_rdy;
    end generate;

    -- -------------------------------------------------------------------------
    --  OUTPUTS PORTS
    -- -------------------------------------------------------------------------

    TX_DATA    <= s_reg1_data;
    TX_META    <= s_reg1_meta;
    TX_SOF_POS <= s_reg1_sof_pos;
    TX_EOF_POS <= s_reg1_eof_pos;
    TX_SOF     <= s_reg1_sof;
    TX_EOF     <= s_reg1_eof;
    TX_SRC_RDY <= s_reg1_src_rdy;

    TX_LNG_MAX_ERR <= s_reg1_lng_max_err;
    TX_LNG_MIN_ERR <= s_reg1_lng_min_err;
    TX_LNG_OVF_ERR <= s_reg1_lng_ovf_err;
    TX_FRAME_LNG   <= slv_array_ser(s_reg1_frame_len,REGIONS,LNG_WIDTH);

end architecture;
