-- tx_dma_pcie_trans_buffer.vhd: this is a specially made component to buffer PCIe transactions
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--            David Benes      <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:
use work.math_pack.all;
use work.type_pack.all;

-- This component instantiaties data buffer for every channel.Each buffer consists from an array of
-- BRAMs which total to the size of the input MFB bus in bytes, i.e. 32 \* *MFB_REGIONS*. This buffer
-- architecture has been chosen because of the address alignment to individual bytes for the
-- incoming PCIe transactions. This also causes the largest resource footprint this entity has in
-- the TX DMA Calypte controller. Since one array of BRAMs can contain much more data than the
-- largest packet able to be transmitted on a channel, the BRAM array is shared between multiple
-- channels. The amount  of channels sharing one array depends on :vhdl:genconstant:`POINTER_WIDTH`
-- and :vhdl:genconstant:`MFB_REGIONS` generic parameters. The extent of buffer sharing is shown
-- in the following table:
--
-- +--------------------+---------------------------+---------------------+
-- | BRAM Size          |           2048 B          |        4096 B       |
-- +--------------------+---------------------------+---------------------+
-- | BRAM Type          | RAMB16 (AMD)/M20K (Intel) |     RAMB36 (AMD)    |
-- +====================+=============+=============+==========+==========+
-- | MFB_REGIONS        | 1           | 2           | 1        | 2        |
-- +--------------------+-------------+-------------+----------+----------+
-- | BRAMs per array    | 32          | 64          | 32       | 64       |
-- +--------------------+-------------+-------------+----------+----------+
-- | Channels per array | up to 8     | up to 16    | up to 16 | up to 32 |
-- +--------------------+-------------+-------------+----------+----------+
--
-- .. NOTE:: Requiring more channels than the maximum amount per array results in an instantiation
--           of multiple BRAM arrays.
--
-- On the output, there is a standard RAM reading interface for multiple channels. Upon setting the
-- address on the :vhdl:portsignal:`RD_ADDR`, an index of a channel on :vhdl:portsignal:`RD_CHAN` and
-- asserting :vhdl:portsignal:`RD_EN`, the
-- core asserts :vhdl:portsignal:`RD_DATA_VLD` 1 or more clock periods later when valid data are
-- available on the :vhdl:portsignal:`RD_DATA` output port.
--
entity TX_DMA_PCIE_TRANS_BUFFER is
    generic (
        DEVICE : string := "ULTRASCALE";

        -- Total number of DMA Channels within this DMA Endpoint
        CHANNELS : natural := 8;

        -- Input MFB interface
        MFB_REGIONS     : natural := 2;
        MFB_REGION_SIZE : natural := 1;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 32;

        -- Determines the number of bytes that can be stored in the buffer.
        -- The amount of bytes equals 2\*\*POINTER_WIDTH
        POINTER_WIDTH          : natural := 16;
        -- If true, each port of the TDPs (used by the 2,1,8,32 MFB configuration) is controlled by
        -- separate interfaces
        SPLIT_READ_PORTS       : boolean := FALSE;
        -- If true, the read data are aligned according to the lower bits of the RD_ADDR input
        READ_BARREL_SHIFTER_EN : b_array_t(1 downto 0) := (TRUE, TRUE)
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- Input MFB bus (quasi BRAM writing interface)
        -- =========================================================================================
        PCIE_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        PCIE_MFB_META    : in  slv_array_t(MFB_REGIONS -1 downto 0)(((MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1)-1 downto 0);
        PCIE_MFB_SOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        PCIE_MFB_SRC_RDY : in  std_logic;

        -- =========================================================================================
        -- Output reading interface for port A of the TDP or the single read port of the SDP
        -- =========================================================================================
        RD_CHAN_A     : in  std_logic_vector(log2(CHANNELS) -1 downto 0);
        RD_DATA_A     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RD_ADDR_A     : in  std_logic_vector(POINTER_WIDTH -1 downto 0);
        RD_EN_A       : in  std_logic;
        RD_DATA_VLD_A : out std_logic;

        -- =========================================================================================
        -- Output reading interface for port B
        --
        -- Unused if SPLIT_READ_PORTS=FALSE or MFB configuration is (1,1,8,32)
        -- =========================================================================================
        RD_CHAN_B     : in  std_logic_vector(log2(CHANNELS) -1 downto 0);
        RD_DATA_B     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0) := (others => '0');
        RD_ADDR_B     : in  std_logic_vector(POINTER_WIDTH -1 downto 0);
        RD_EN_B       : in  std_logic;
        RD_DATA_VLD_B : out std_logic := '0'
    );
end entity;

architecture FULL of TX_DMA_PCIE_TRANS_BUFFER is

    constant MFB_LENGTH      : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    -- Number of Dwords in MFB word (equal as the nummber of items)
    constant MFB_DWORDS      : natural := MFB_LENGTH/MFB_ITEM_WIDTH;
    -- Number of bytes in MFB word
    constant MFB_BYTES       : natural := MFB_LENGTH/8;
    -- The Address is restricted by BAR_APERTURE (IP_core setting)
    constant BUFFER_DEPTH    : natural := (2**POINTER_WIDTH)/(MFB_LENGTH/8);
    -- Number of input registers
    constant BRAM_REG_NUM    : natural := 2;
    -- Number of registers between BRAMs and barrel shifter
    constant INP_REG_NUM     : natural := 1;
    constant IS_INTEL_DEV    : boolean := (DEVICE = "STRATIX10" or DEVICE = "AGILEX");
    -- a maximum depth of a BRAM block (in 1B items) depends on a vendor
    constant MAX_BRAM_DEPTH  : natural := tsel(IS_INTEL_DEV, 2048, 4096);
    -- The amount of channels that fits to one array
    constant CHANS_PER_ARRAY : natural := minimum(CHANNELS, MAX_BRAM_DEPTH/BUFFER_DEPTH);
    -- Number of memory arrays since one array can contain multiple channels
    constant MEM_ARRAYS      : natural := CHANNELS/CHANS_PER_ARRAY;

    -- =============================================================================================
    -- Defining ranges for meta signal
    -- =============================================================================================
    constant META_IS_DMA_HDR_W : natural := 1;
    constant META_PCIE_ADDR_W  : natural := 62;
    constant META_CHAN_NUM_W   : natural := log2(CHANNELS);
    constant META_BE_W         : natural := (MFB_LENGTH/MFB_REGIONS)/8;

    constant META_IS_DMA_HDR_O : natural := 0;
    constant META_PCIE_ADDR_O  : natural := META_IS_DMA_HDR_O + META_IS_DMA_HDR_W;
    constant META_CHAN_NUM_O   : natural := META_PCIE_ADDR_O + META_PCIE_ADDR_W;
    constant META_BE_O         : natural := META_CHAN_NUM_O + META_CHAN_NUM_W;

    subtype META_IS_DMA_HDR is natural range META_IS_DMA_HDR_O + META_IS_DMA_HDR_W -1 downto META_IS_DMA_HDR_O;
    subtype META_PCIE_ADDR  is natural range   META_PCIE_ADDR_O + META_PCIE_ADDR_W -1 downto META_PCIE_ADDR_O;
    subtype META_CHAN_NUM   is natural range     META_CHAN_NUM_O + META_CHAN_NUM_W -1 downto META_CHAN_NUM_O;
    subtype META_BE         is natural range                 META_BE_O + META_BE_W -1 downto META_BE_O;

    subtype META_MEM_ARR_IDX is natural range log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) + META_CHAN_NUM_O -1 downto log2(CHANS_PER_ARRAY) + META_CHAN_NUM_O;

    -- Input register
    signal pcie_mfb_data_inp_reg    : slv_array_t(INP_REG_NUM downto 0)(PCIE_MFB_DATA'range);
    signal pcie_mfb_meta_inp_reg    : slv_array_2d_t(INP_REG_NUM downto 0)(MFB_REGIONS -1 downto 0)(((MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1)-1 downto 0);
    signal pcie_mfb_sof_inp_reg     : slv_array_t(INP_REG_NUM downto 0)(PCIE_MFB_SOF'range);
    signal pcie_mfb_src_rdy_inp_reg : std_logic_vector(INP_REG_NUM downto 0);

    -- counter of the address for each valid word following the beginning of the transaction
    signal addr_cntr_pst            : unsigned(META_PCIE_ADDR_W -1 downto 0);
    signal addr_cntr_nst            : unsigned(META_PCIE_ADDR_W -1 downto 0);

    -- Stores the index of the packet that get currently stored
    signal chan_num_reg             : std_logic_vector(META_CHAN_NUM_W -1 downto 0);
    signal chan_num_next            : std_logic_vector(META_CHAN_NUM_W -1 downto 0);

    -- control of the amount of shift on the writing barrel shifters
    signal wr_shift_sel             : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(MFB_LENGTH/32) -1 downto 0);

    signal wr_be_bram_bshifter      : slv_array_t(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0);
    signal wr_be_bram_demux         : slv_array_2d_t(MEM_ARRAYS -1 downto 0)(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0);
    signal wr_addr_bram_by_shift    : slv_array_2d_t(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/32) -1 downto 0)(log2(BUFFER_DEPTH*CHANS_PER_ARRAY) -1 downto 0);
    signal wr_data_bram_bshifter    : slv_array_t(MFB_REGIONS - 1 downto 0)(MFB_LENGTH -1 downto 0);

    signal mem_arr_idx_reg          : std_logic_vector(log2(MEM_ARRAYS) -1 downto 0);
    signal mem_arr_idx_next         : std_logic_vector(log2(MEM_ARRAYS) -1 downto 0);

    signal rd_en_bram_demux         : slv_array_t(MEM_ARRAYS -1 downto 0)(MFB_REGIONS -1 downto 0);
    signal rd_data_bram_mux         : slv_array_t(MFB_REGIONS -1 downto 0)(MFB_LENGTH -1 downto 0);
    signal rd_data_bram             : slv_array_2d_t(MEM_ARRAYS -1 downto 0)(MFB_REGIONS - 1 downto 0)(MFB_LENGTH -1 downto 0);
    signal rd_addr_bram_by_shift    : slv_array_2d_t(MFB_REGIONS -1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0)(log2(BUFFER_DEPTH*CHANS_PER_ARRAY) -1 downto 0);

    -- ================= --
    -- 2 regions support --
    -- ================= --
    -- Meta array
    signal pcie_mfb_meta_arr        : slv_array_t(MFB_REGIONS - 1 downto 0)((MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1-1 downto 0);

    -- Converter signal: PCIE_MFB_DATA'length/32 => PCIE_MFB_DATA'length/ 8
    -- Address the item in a BRAM for each byte for each region
    signal wr_addr_bram_by_multi    : slv_array_2d_t(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0)(log2(BUFFER_DEPTH*CHANS_PER_ARRAY) -1 downto 0);

    -- Read/Write Address - TDP
    signal rw_addr_bram_by_mux      : slv_array_3d_t(MEM_ARRAYS - 1 downto 0)(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0)(log2(BUFFER_DEPTH*CHANS_PER_ARRAY) -1 downto 0);

    -- Read data valid - TDP
    signal rd_data_valid_arr        : std_logic_vector(MFB_REGIONS - 1 downto 0);

    -- Read enable per memory array per BRAM port
    signal rd_en_pch                : slv_array_t(MEM_ARRAYS - 1 downto 0)(MFB_REGIONS - 1 downto 0);

    -- Meta signal for whole MFB word
    signal pcie_meta_be_per_port  : slv_array_t(MFB_REGIONS - 1 downto 0)(MFB_LENGTH/8 - 1 downto 0);

    -- BRAM registers
    signal wr_be_bram_demux_reg      : slv_array_3d_t(BRAM_REG_NUM downto 0)(MEM_ARRAYS -1 downto 0)(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/8) -1 downto 0);
    signal wr_addr_bram_by_shift_reg : slv_array_3d_t(BRAM_REG_NUM downto 0)(MFB_REGIONS - 1 downto 0)((PCIE_MFB_DATA'length/32) -1 downto 0)(log2(BUFFER_DEPTH*CHANS_PER_ARRAY) -1 downto 0);
    signal wr_data_bram_shifter_reg  : slv_array_2d_t(BRAM_REG_NUM downto 0)(MFB_REGIONS - 1 downto 0)(MFB_LENGTH -1 downto 0);

    signal addr_sel                 : slv_array_t(MEM_ARRAYS -1 downto 0)(MFB_REGIONS - 1 downto 0);

    -- =============================================================================================
    -- DEBUG signals (verification or ILA)
    -- =============================================================================================
    signal wr_addr_collision_detected : slv_array_t(MEM_ARRAYS -1 downto 0)(MFB_BYTES -1 downto 0);
    signal rdwr_collision_detected    : slv_array_2d_t(MEM_ARRAYS -1 downto 0)(MFB_REGIONS -1 downto 0)(MFB_BYTES -1 downto 0);

begin

    assert (
        (MFB_REGIONS = 2 and SPLIT_READ_PORTS)
        or (MFB_REGIONS = 1 and (not SPLIT_READ_PORTS))
        or (MFB_REGIONS = 2 and (not SPLIT_READ_PORTS))
        )
        report "TX_DMA_PCIE_TRANS_BUFFER: The configuration with split ports is only allowed for a 2-region setting!"
        severity FAILURE;

    -- =============================================================================================
    -- Input shift registers
    -- =============================================================================================
    pcie_mfb_data_inp_reg   (0) <= PCIE_MFB_DATA;
    pcie_mfb_meta_inp_reg   (0) <= PCIE_MFB_META;
    pcie_mfb_sof_inp_reg    (0) <= PCIE_MFB_SOF;
    pcie_mfb_src_rdy_inp_reg(0) <= PCIE_MFB_SRC_RDY;

    inp_shift_reg_mult_g: if (INP_REG_NUM > 0) generate
        input_shift_reg_g: for i in 0 to (INP_REG_NUM - 1) generate
            input_shift_reg_p : process (CLK) is
            begin
                if rising_edge(CLK) then
                    if (RESET = '1') then
                        pcie_mfb_src_rdy_inp_reg(i + 1) <= '0';
                    else
                        pcie_mfb_data_inp_reg   (i + 1) <= pcie_mfb_data_inp_reg   (i);
                        pcie_mfb_meta_inp_reg   (i + 1) <= pcie_mfb_meta_inp_reg   (i);
                        pcie_mfb_sof_inp_reg    (i + 1) <= pcie_mfb_sof_inp_reg    (i);
                        pcie_mfb_src_rdy_inp_reg(i + 1) <= pcie_mfb_src_rdy_inp_reg(i);
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    -- Meta array
    pcie_mfb_meta_arr   <= pcie_mfb_meta_inp_reg(INP_REG_NUM);

    -- =============================================================================================
    -- Assertions for verification
    -- =============================================================================================

    -- psl assert_captured_dma_header :
    --      assert forall it in {0 to (MFB_REGIONS -1)} :
    --      always ((not (PCIE_MFB_SRC_RDY = '1' or PCIE_MFB_META(it)(META_BE) /= (META_BE_W -1 downto 0 => '0'))) or
    --              (PCIE_MFB_META(it)(META_IS_DMA_HDR) = "0")) abort(RESET) @rising_edge(CLK)
    --      report "TX_DMA_PCIE_TRANS_BUFFER: captured DMA header on region  to_string(it) Danger of data overwrite!";

    -- =============================================================================================
    -- Address storage
    -- =============================================================================================
    addr_cntr_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                addr_cntr_pst <= (others => '0');
                chan_num_reg  <= (others => '0');
            else
                addr_cntr_pst <= addr_cntr_nst;
                chan_num_reg  <= chan_num_next;
            end if;
        end if;
    end process;

    addr_cntr_nst_logic_p : process (all) is
    begin
        addr_cntr_nst <= addr_cntr_pst;
        chan_num_next <= chan_num_reg;

        -- Increment the address for a next word by 8 (the number of DWs in the
        -- word) to be written to the BRAMs.  When the new packet arrives, its
        -- address is stored and incremented by one region size

        -- Be careful! The number '8' is only correct for one region
        if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
            -- Address Increment
            -- +16 (amount of DWs for two regions)
            addr_cntr_nst <= addr_cntr_pst + MFB_REGIONS*MFB_BLOCK_SIZE;

            -- Last SOF - Higher takes
            for i in 0 to (MFB_REGIONS - 1) loop
                if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(i) = '1') then
                    -- First SOF does +16, the second makes +8
                    -- When second SOF is present, this automatically takes the address from the
                    -- second region and adds increment of 8 to that. If there is only one SOF and
                    -- particularly in the first region, then increment by 16 because the frame
                    -- continues in the next word.
                    addr_cntr_nst   <= unsigned(pcie_mfb_meta_arr(i)(META_PCIE_ADDR)) + (MFB_REGIONS - i)*MFB_BLOCK_SIZE;
                    chan_num_next   <= pcie_mfb_meta_arr(i)(META_CHAN_NUM);
                end if;
            end loop;
        end if;
    end process;

    -- =============================================================================================
    -- META(BE) select
    -- =============================================================================================
    -- This process selects which bytes are enabled in which BS based on the SOF status in the second region
    meta_be_g: if (MFB_REGIONS = 1) generate
        pcie_meta_be_per_port(0) <= pcie_mfb_meta_arr(0)(META_BE);
    else generate
        meta_sel_p : process (all)
        begin
            if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(1) = '1') then
                pcie_meta_be_per_port(0) <= (META_BE_W -1 downto 0 => '0') & pcie_mfb_meta_arr(0)(META_BE);
                pcie_meta_be_per_port(1) <= pcie_mfb_meta_arr(1)(META_BE) & (META_BE_W -1 downto 0 => '0');
            else
                -- The problem is that we only get half the information in metadata for each region
                pcie_meta_be_per_port(0) <= pcie_mfb_meta_arr(1)(META_BE) & pcie_mfb_meta_arr(0)(META_BE);
                pcie_meta_be_per_port(1) <= (others => '0');
            end if;
        end process;
    end generate;

    -- =============================================================================================
    -- Data shift - Port A
    -- =============================================================================================
    -- This process controls the shift of the input word and the corresponding byte enable signal to it.
    -- When beginning of a transaction is captured, the shift is taken directly from the current address,
    -- but when it continues, then select shift from the counter of addresses.

    -- The previous "2 downto 0" is specification of address - now generic for more regions
    -- The address system here is divided into two parts due to the dual-port BRAM configuration
    wr_bshifter_0_ctrl_p : process (all) is
        variable pcie_mfb_meta_addr_v : std_logic_vector(META_PCIE_ADDR_W -1 downto 0);
    begin
        wr_shift_sel(0) <= (others => '0');

        if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
            if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(0) = '1') then
                pcie_mfb_meta_addr_v    := pcie_mfb_meta_arr(0)(META_PCIE_ADDR);
                wr_shift_sel(0)         <= pcie_mfb_meta_addr_v(log2(MFB_DWORDS) - 1  downto 0);
            else
                -- Shared address when the processing is in the middle of a frame - last saved address
                wr_shift_sel(0)         <= std_logic_vector(addr_cntr_pst(log2(MFB_DWORDS) - 1 downto 0));
            end if;
        end if;
    end process;

    -- Data - Port A
    wr_data_barrel_shifter_0_i: entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => MFB_REGIONS*MFB_BLOCK_SIZE,
        BLOCK_SIZE => MFB_ITEM_WIDTH,
        SHIFT_LEFT => TRUE
    )
    port map (
        DATA_IN  => pcie_mfb_data_inp_reg(INP_REG_NUM),
        DATA_OUT => wr_data_bram_bshifter(0),
        SEL      => wr_shift_sel(0)
    );

    -- Byte enable - port A
    wr_be_barrel_shifter_0_i: entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => MFB_REGIONS*MFB_BLOCK_SIZE,
        BLOCK_SIZE => 4,
        SHIFT_LEFT => TRUE
    )
    port map (
        DATA_IN  => pcie_meta_be_per_port(0),
        DATA_OUT => wr_be_bram_bshifter(0),
        SEL      => wr_shift_sel(0)
    );

    -- =============================================================================================
    -- Data shift - Port B
    -- =============================================================================================
    -- This packet starts at the beginning of the second region, so we need to correct the address
    -- by the number of DWords in region

    tworeg_bs_g: if (MFB_REGIONS = 2) generate
        wr_bshifter_1_ctrl_p : process (all) is
            variable pcie_mfb_meta_addr_v : std_logic_vector(META_PCIE_ADDR_W -1 downto 0);
        begin
            wr_shift_sel(1) <= (others => '0');

            if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
                if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(1) = '1') then
                    -- The '+8' is MFB_BLOCK_SIZE (same as length of a REGION in Dwords) and is
                    -- only used when the SOF is in the second region
                    -- NOTE: that -8 can be a source of error. Was +8 previously.
                    pcie_mfb_meta_addr_v    := std_logic_vector(unsigned(pcie_mfb_meta_arr(1)(META_PCIE_ADDR)) - 8);
                    wr_shift_sel(1)         <= pcie_mfb_meta_addr_v(log2(MFB_DWORDS) - 1  downto 0);
                end if;
            end if;
        end process;

        -- Data - Port B
        wr_data_barrel_shifter_1_i: entity work.BARREL_SHIFTER_GEN
        generic map (
            BLOCKS     => MFB_REGIONS*MFB_BLOCK_SIZE,
            BLOCK_SIZE => MFB_ITEM_WIDTH,
            SHIFT_LEFT => TRUE
        )
        port map (
            DATA_IN  => pcie_mfb_data_inp_reg(INP_REG_NUM),
            DATA_OUT => wr_data_bram_bshifter(1),
            SEL      => wr_shift_sel(1)
        );

        -- Byte enable - port B
        wr_be_barrel_shifter_1_i: entity work.BARREL_SHIFTER_GEN
        generic map (
            BLOCKS     => MFB_REGIONS*MFB_BLOCK_SIZE,
            BLOCK_SIZE => 4,
            SHIFT_LEFT => TRUE
        )
        port map (
            DATA_IN  => pcie_meta_be_per_port(1),
            DATA_OUT => wr_be_bram_bshifter(1),
            SEL      => wr_shift_sel(1)
        );
    end generate;

    -- =============================================================================================
    -- Address correction
    -- =============================================================================================
    -- This process increments the address on the lowest DWords when shift occurs.
    -- That means that when data are shifted on the input, the rotation causes higher DWs to appear
    -- on the lower positions.
    -- Writing on the same address could cause the overwrite of data already stored in lower BRAMs.

    -- Possibilites:
    --     SOF(0) SOF(1)   PORTS
    -- 1)    0      0       A A
    -- 2)    0      1       A B  -- Illegal combination in this case
    -- 3)    1      0       A A
    -- 4)    1      1       A B

    -- Port A
    wr_addr_correction_a_p : process (all) is
        variable pcie_mfb_meta_addr_v : std_logic_vector(META_PCIE_ADDR_W -1 downto 0);
        variable buff_addr_v          : std_logic_vector(log2(BUFFER_DEPTH) -1 downto 0);
        variable chan_addr_v          : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
    begin
        wr_addr_bram_by_shift(0) <= (others => (others => '0'));

        if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
            if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(0) = '1') then
                -- Pass address to variable
                pcie_mfb_meta_addr_v := pcie_mfb_meta_arr(0)(META_PCIE_ADDR);
                buff_addr_v          := pcie_mfb_meta_addr_v(log2(BUFFER_DEPTH)+log2(MFB_DWORDS) -1 downto log2(MFB_DWORDS));
                chan_addr_v          := pcie_mfb_meta_arr(0)(log2(CHANS_PER_ARRAY) + META_CHAN_NUM_O -1 downto META_CHAN_NUM_O);

                wr_addr_bram_by_shift(0) <= (others => (chan_addr_v & buff_addr_v));

                -- Increment address in bytes that have been rotated
                for i in 0 to ((MFB_LENGTH/32) -1) loop
                    if (i < unsigned(pcie_mfb_meta_addr_v(log2(MFB_DWORDS) - 1 downto 0))) then
                        wr_addr_bram_by_shift(0)(i) <= chan_addr_v & std_logic_vector(unsigned(buff_addr_v) + 1);
                    end if;
                end loop;
            else
                buff_addr_v := std_logic_vector(addr_cntr_pst(log2(BUFFER_DEPTH) + log2(MFB_DWORDS) -1 downto log2(MFB_DWORDS)));
                chan_addr_v := chan_num_reg(log2(CHANS_PER_ARRAY) -1 downto 0);

                wr_addr_bram_by_shift(0) <= (others => (chan_addr_v & buff_addr_v));

                -- Increment address in bytes that have been rotated
                for i in 0 to ((MFB_LENGTH/32) -1) loop
                    if (i < addr_cntr_pst(log2(MFB_DWORDS) - 1 downto 0)) then
                        wr_addr_bram_by_shift(0)(i) <= chan_addr_v & std_logic_vector(unsigned(buff_addr_v) + 1);
                    end if;
                end loop;
            end if;
        end if;
    end process;

    -- Port B
    wr_addr_correction_b_g: if (MFB_REGIONS = 2) generate
        wr_addr_correction_b_p : process (all) is
            variable pcie_mfb_meta_addr_v : std_logic_vector(META_PCIE_ADDR_W -1 downto 0);
            variable buff_addr_v          : std_logic_vector(log2(BUFFER_DEPTH) -1 downto 0);
            variable chan_addr_v          : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
        begin
            wr_addr_bram_by_shift(1) <= (others => (others => '0'));

            if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
                if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(1) = '1') then
                    -- Pass address to variable
                    pcie_mfb_meta_addr_v := pcie_mfb_meta_arr(1)(META_PCIE_ADDR);
                    buff_addr_v          := pcie_mfb_meta_addr_v(log2(BUFFER_DEPTH)+log2(MFB_DWORDS) -1 downto log2(MFB_DWORDS));
                    chan_addr_v          := pcie_mfb_meta_arr(1)(log2(CHANS_PER_ARRAY) + META_CHAN_NUM_O -1 downto META_CHAN_NUM_O);

                    wr_addr_bram_by_shift(1) <= (others => (chan_addr_v & buff_addr_v));

                    -- Increment address in bytes that has been overflowed
                    for i in 0 to ((MFB_LENGTH/32) -1) loop
                        if (i < unsigned(pcie_mfb_meta_addr_v(log2(MFB_DWORDS) - 1 downto 0))) then
                            wr_addr_bram_by_shift(1)(i) <= chan_addr_v & std_logic_vector(unsigned(buff_addr_v) + 1);
                        end if;
                    end loop;
                    -- else is not the case - the first port will handle it
                end if;
            end if;
        end process;
    end generate;

    -- =============================================================================================
    -- Channel index store
    -- =============================================================================================
    -- Demultiplexer is based on value of META(Channel)
    -- Last value of the Channel is stored
    -- TODO: It should be taken into consideration that this storing process should be removed
    -- because the channel number is already extracted in METADATA_EXTRACTOR and the index of a
    -- channel is held through the duration of a whole packet.
    mem_arr_indx_hold_g: if (MEM_ARRAYS > 1) generate
        mem_arr_idx_hold_reg_p : process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    mem_arr_idx_reg <= (others => '0');
                else
                    mem_arr_idx_reg <= mem_arr_idx_next;
                end if;
            end if;
        end process;

        -- This FSM stores a part of a channel number to determine the memory array
        -- to which the data ought to be send. It stores channel number for the last
        -- valid SOF in the word.
        mem_arr_idx_hold_nst_logic_p : process (all) is
            variable mem_arr_idx_v : std_logic_vector(log2(CHANNELS) -1 downto 0);
        begin
            mem_arr_idx_next <= mem_arr_idx_reg;

            -- Higher takes
            if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
                for i in 0 to (MFB_REGIONS - 1) loop
                    if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(i) = '1') then

                        mem_arr_idx_v    := pcie_mfb_meta_arr(i)(META_CHAN_NUM);
                        mem_arr_idx_next <= mem_arr_idx_v(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY));

                    end if;
                end loop;
            end if;
        end process;

        -- =============================================================================================
        -- Demultiplexers - Byte enable
        -- =============================================================================================
        -- Possibilites:
        --     SOF(0) SOF(1)
        -- 1)    0      0   - Port A handles whole MFB word = Last valid channel is used
        -- 2)    0      1   - Port A handles first region, Second region is dispatched by port B (illegal for incoming data)
        -- 3)    1      0   - Port A handles whole MFB word = Current channel is used
        -- 4)    1      1   - Port A handles first region, Second region is dispatched by port B
        wr_bram_data_demux_p : process (all) is
        begin
            wr_be_bram_demux <= (others => (others => (others => '0')));

            for i in 0 to (MFB_REGIONS - 1) loop
                if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
                    if (pcie_mfb_sof_inp_reg(INP_REG_NUM)(i) = '1') then
                        wr_be_bram_demux(to_integer(unsigned(pcie_mfb_meta_arr(i)(META_MEM_ARR_IDX))))(i) <= wr_be_bram_bshifter(i);
                    else
                        wr_be_bram_demux(to_integer(unsigned(mem_arr_idx_reg)))(i)                        <= wr_be_bram_bshifter(i);
                    end if;
                end if;
            end loop;
        end process;
    else generate

        wr_bram_data_demux_p : process (all) is
        begin
            wr_be_bram_demux <= (others => (others => (others => '0')));

            for i in 0 to (MFB_REGIONS - 1) loop
                if (pcie_mfb_src_rdy_inp_reg(INP_REG_NUM) = '1') then
                    wr_be_bram_demux(0)(i) <= wr_be_bram_bshifter(i);
                end if;
            end loop;
        end process;
    end generate;

    -- =============================================================================================
    -- Registers between BARREL_SHIFTERs and BRAMs
    -- =============================================================================================
    wr_be_bram_demux_reg(0)      <= wr_be_bram_demux;
    wr_addr_bram_by_shift_reg(0) <= wr_addr_bram_by_shift;
    wr_data_bram_shifter_reg (0) <= wr_data_bram_bshifter;

    bram_input_reg_mult_g: if (BRAM_REG_NUM > 0) generate
        bram_input_reg_g : for i in 0 to BRAM_REG_NUM - 1 generate
            bram_input_reg_p : process (CLK) is
            begin
                if rising_edge(CLK) then
                    wr_be_bram_demux_reg     (i + 1) <= wr_be_bram_demux_reg     (i);
                    wr_addr_bram_by_shift_reg(i + 1) <= wr_addr_bram_by_shift_reg(i);
                    wr_data_bram_shifter_reg (i + 1) <= wr_data_bram_shifter_reg (i);
                end if;
            end process;
        end generate;
    end generate;

    -- =============================================================================================
    -- BRAM - One region
    -- =============================================================================================
    -- One region
    sdp_bram_g: if (MFB_REGIONS = 1) generate
        brams_for_channels_g : for mem_arr_idx in 0 to (MEM_ARRAYS -1) generate
            brams_per_byte : for wbyte in 0 to ((MFB_LENGTH/8) -1) generate
                sdp_bram_be_i : entity work.SDP_BRAM_BE
                generic map (
                    BLOCK_ENABLE   => false,
                    -- allow individual bytes to be assigned
                    BLOCK_WIDTH    => 8,
                    -- each BRAM allows to write a single DW
                    DATA_WIDTH     => 8,
                    -- the depth of the buffer
                    ITEMS          => BUFFER_DEPTH*CHANS_PER_ARRAY,
                    COMMON_CLOCK   => TRUE,
                    OUTPUT_REG     => FALSE,
                    METADATA_WIDTH => 0,
                    DEVICE         => DEVICE
                )
                port map (
                    WR_CLK      => CLK,
                    WR_RST      => RESET,
                    WR_EN       => wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(0)(wbyte),
                    WR_BE       => (others => '1'),
                    WR_ADDR     => wr_addr_bram_by_shift_reg(BRAM_REG_NUM)(0)(wbyte/4),
                    WR_DATA     => wr_data_bram_shifter_reg(BRAM_REG_NUM)(0)(wbyte*8 +7 downto wbyte*8),

                    RD_CLK      => CLK,
                    RD_RST      => RESET,
                    RD_EN       => '1',
                    RD_PIPE_EN  => rd_en_bram_demux(mem_arr_idx)(0),
                    RD_META_IN  => (others => '0'),
                    RD_ADDR     => rd_addr_bram_by_shift(0)(wbyte),
                    RD_DATA     => rd_data_bram(mem_arr_idx)(0)(wbyte*8 +7 downto wbyte*8),
                    RD_META_OUT => open,
                    RD_DATA_VLD => open
                );
            end generate;
        end generate;
    end generate;

    -- =============================================================================================
    -- BRAM - Two regions
    -- =============================================================================================
    tdp_bram_g: if (MFB_REGIONS = 2) generate

        -- Convert address of a DWORD to an address of each individual byte
        -- This is used for address multiplexing
        addr_multi_regions_g : for rgn in 0 to MFB_REGIONS - 1 generate
            -- Iterate over bytes of a region
            addr_multi_bytes_g : for wbyte in 0 to ((MFB_LENGTH/8) -1) generate
                wr_addr_bram_by_multi(rgn)(wbyte) <= wr_addr_bram_by_shift_reg(BRAM_REG_NUM)(rgn)(wbyte/4);
            end generate;
        end generate;

        -- Address Select
        -- First port controlled by Byte Enable
        -- Second port is controlled by the second region's SOF
        -- The first bit in Byte Enable is enough to decide whether read to write
        -- OPT: ORing the whole signal can be logically intensive. This could be done.
        -- in the beginning by oring only 4 first bits because there is a FBE portion which
        -- always has to have at least 1 bit set to 1.
        addr_sel_g: for ch in 0 to (MEM_ARRAYS -1) generate
            addr_sel(ch)(0) <= or wr_be_bram_demux_reg(BRAM_REG_NUM)(ch)(0);
            addr_sel(ch)(1) <= or wr_be_bram_demux_reg(BRAM_REG_NUM)(ch)(1);
        end generate;

        -- The Address Multiplexer - Choose between Write and Read Port
        addr_mux_chans_g : for ch in 0 to (MEM_ARRAYS -1) generate
            addr_mux_regions_g : for rgn in 0 to (MFB_REGIONS -1) generate
                addr_mux_p : process (all)
                begin
                    -- Default assignment
                    rw_addr_bram_by_mux(ch)(rgn)  <= (others => (others => '0'));

                    if (addr_sel(ch)(rgn) = '1') then
                        rw_addr_bram_by_mux(ch)(rgn) <= wr_addr_bram_by_multi(rgn);
                    else
                        rw_addr_bram_by_mux(ch)(rgn) <= rd_addr_bram_by_shift(rgn);
                    end if;
                end process;
            end generate;
        end generate;

        -- Read enable - Write port priority
        rd_en_ch_g : for ch in 0 to (MEM_ARRAYS -1) generate
            rd_en_reg_g : for rgn in 0 to (MFB_REGIONS -1) generate
                -- Read enable per channel
                rd_en_pch(ch)(rgn) <= rd_en_bram_demux(ch)(rgn) and (not addr_sel(ch)(rgn));
            end generate;
        end generate;

        brams_for_channels_g : for mem_arr_idx in 0 to (MEM_ARRAYS -1) generate
            tdp_bram_be_g : for wbyte in 0 to ((MFB_LENGTH/8) -1) generate

                tdp_bram_be_i : entity work.DP_BRAM_BEHAV
                generic map (
                    DATA_WIDTH => 8,
                    ITEMS      => CHANS_PER_ARRAY*BUFFER_DEPTH,
                    OUTPUT_REG => FALSE,
                    RDW_MODE_A => "WRITE_FIRST",
                    RDW_MODE_B => "WRITE_FIRST"
                )
                port map (
                    CLK => CLK,
                    RST => RESET,

                    -- =======================================================================
                    -- Port A
                    -- =======================================================================
                    PIPE_ENA => '1',
                    REA      => rd_en_pch(mem_arr_idx)(0),
                    WEA      => wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(0)(wbyte),
                    ADDRA    => rw_addr_bram_by_mux(mem_arr_idx)(0)(wbyte),
                    DIA      => wr_data_bram_shifter_reg(BRAM_REG_NUM)(0)(wbyte*8 +7 downto wbyte*8),
                    DOA      => rd_data_bram(mem_arr_idx)(0)(wbyte*8 +7 downto wbyte*8),
                    DOA_DV   => open,

                    -- =======================================================================
                    -- Port B
                    -- =======================================================================
                    PIPE_ENB => '1',
                    REB      => rd_en_pch(mem_arr_idx)(1),
                    WEB      => wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(1)(wbyte),
                    ADDRB    => rw_addr_bram_by_mux(mem_arr_idx)(1)(wbyte),
                    DIB      => wr_data_bram_shifter_reg(BRAM_REG_NUM)(1)(wbyte*8 +7 downto wbyte*8),
                    DOB      => rd_data_bram(mem_arr_idx)(1)(wbyte*8 +7 downto wbyte*8),
                    DOB_DV   => open
                );

                -- DEBUG process for simulation
                wr_addr_collision_detection_p : process (all) is
                begin

                    wr_addr_collision_detected(mem_arr_idx)(wbyte) <= '0';
                    rdwr_collision_detected(mem_arr_idx)(0)(wbyte) <= '0';
                    rdwr_collision_detected(mem_arr_idx)(1)(wbyte) <= '0';

                    -- dual concurrent write on the same address
                    if (wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(0)(wbyte) = '1' and
                        wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(1)(wbyte) = '1' and
                        rw_addr_bram_by_mux(mem_arr_idx)(0)(wbyte) = rw_addr_bram_by_mux(mem_arr_idx)(1)(wbyte)
                    ) then
                        wr_addr_collision_detected(mem_arr_idx)(wbyte) <= '1';
                    end if;

                    -- concurrent read and write on port A
                    if (wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(0)(wbyte) = '1' and
                        rd_en_pch(mem_arr_idx)(0) = '1'
                    ) then
                        rdwr_collision_detected(mem_arr_idx)(0)(wbyte) <= '1';
                    end if;

                    -- concurrent read and write on port B
                    if (wr_be_bram_demux_reg(BRAM_REG_NUM)(mem_arr_idx)(1)(wbyte) = '1' and
                        rd_en_pch(mem_arr_idx)(1) = '1'
                    ) then
                        rdwr_collision_detected(mem_arr_idx)(1)(wbyte) <= '1';
                    end if;
                end process;
            end generate;
        end generate;

        rd_vld_p : process (CLK)
        begin
            if rising_edge(CLK) then

                rd_data_valid_arr   <= (others => '0');

                for ch in 0 to (MEM_ARRAYS -1) loop
                    for rgn in 0 to (MFB_REGIONS - 1) loop
                        if (rd_en_pch(ch)(rgn) = '1') then
                            rd_data_valid_arr(rgn) <= '1';
                        end if;
                    end loop;
                end loop;
            end if;
        end process;
    end generate;

    -- =============================================================================================
    -- Demulitplexors
    -- =============================================================================================
    split_port_logic_g : if (SPLIT_READ_PORTS and MFB_REGIONS = 2) generate

        bram_demux_p : process (all) is
        begin
            rd_en_bram_demux                                                                                                               <= (others => (others => '0'));
            rd_en_bram_demux(to_integer(unsigned(RD_CHAN_A(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(0) <= RD_EN_A;
            rd_en_bram_demux(to_integer(unsigned(RD_CHAN_B(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(1) <= RD_EN_B;

            rd_data_bram_mux    <= (others => (others => '0'));
            rd_data_bram_mux(0) <= rd_data_bram(to_integer(unsigned(RD_CHAN_A(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(0);
            rd_data_bram_mux(1) <= rd_data_bram(to_integer(unsigned(RD_CHAN_B(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(1);
        end process;

        RD_DATA_VLD_A <= rd_data_valid_arr(0);
        RD_DATA_VLD_B <= rd_data_valid_arr(1);

        rd_barrel_shifter_a_g : if (READ_BARREL_SHIFTER_EN(0)) generate
            rd_data_barrel_shifter_a_i : entity work.BARREL_SHIFTER_GEN
            generic map (
                -- The Reading side is addressable by bytes so the number of blocks is 4 times more than on the
                -- reading side
                BLOCKS     => MFB_BYTES,
                BLOCK_SIZE => 8,
                SHIFT_LEFT => FALSE
            )
            port map (
                DATA_IN  => rd_data_bram_mux(0),
                DATA_OUT => RD_DATA_A,
                SEL      => RD_ADDR_A(log2(MFB_BYTES) - 1 downto 0)
            );

            rd_addr_recalc_p : process (all) is
                variable chan_addr_a_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
            begin
                chan_addr_a_v            := RD_CHAN_A(log2(CHANS_PER_ARRAY) -1 downto 0);
                rd_addr_bram_by_shift(0) <= (others => chan_addr_a_v & RD_ADDR_A(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES)));

                for i in 0 to ((MFB_LENGTH/8) -1) loop
                    if (i < unsigned(RD_ADDR_A(log2(MFB_BYTES) - 1 downto 0))) then
                        rd_addr_bram_by_shift(0)(i) <= chan_addr_a_v & std_logic_vector(unsigned(RD_ADDR_A(log2(BUFFER_DEPTH) + log2(MFB_BYTES) -1 downto log2(MFB_BYTES))) + 1);
                    end if;
                end loop;
            end process;
        else generate
            RD_DATA_A <= rd_data_bram_mux(0);

            rd_addr_recalc_p : process (all) is
                variable chan_addr_a_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
            begin
                chan_addr_a_v            := RD_CHAN_A(log2(CHANS_PER_ARRAY) -1 downto 0);
                rd_addr_bram_by_shift(0) <= (others => chan_addr_a_v & RD_ADDR_A(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES)));
            end process;
        end generate;

        rd_barrel_shifter_b_g : if (READ_BARREL_SHIFTER_EN(1)) generate
            rd_data_barrel_shifter_b_i : entity work.BARREL_SHIFTER_GEN
            generic map (
                -- The Reading side is addressable by bytes so the number of blocks is 4 times more than on the
                -- reading side
                BLOCKS     => MFB_BYTES,
                BLOCK_SIZE => 8,
                SHIFT_LEFT => FALSE
            )
            port map (
                DATA_IN  => rd_data_bram_mux(1),
                DATA_OUT => RD_DATA_B,
                SEL      => RD_ADDR_B(log2(MFB_BYTES) - 1 downto 0)
            );

            rd_addr_recalc_p : process (all) is
                variable chan_addr_b_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
            begin
                chan_addr_b_v            := RD_CHAN_B(log2(CHANS_PER_ARRAY) -1 downto 0);
                rd_addr_bram_by_shift(1) <= (others => chan_addr_b_v & RD_ADDR_B(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES)));

                for i in 0 to ((MFB_LENGTH/8) -1) loop
                    if (i < unsigned(RD_ADDR_B(log2(MFB_BYTES) - 1 downto 0))) then
                        rd_addr_bram_by_shift(1)(i) <= chan_addr_b_v & std_logic_vector(unsigned(RD_ADDR_B(log2(BUFFER_DEPTH) + log2(MFB_BYTES) -1 downto log2(MFB_BYTES))) + 1);
                    end if;
                end loop;
            end process;
        else generate
            RD_DATA_B <= rd_data_bram_mux(1);

            rd_addr_recalc_p : process (all) is
                variable chan_addr_b_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
            begin
                chan_addr_b_v            := RD_CHAN_B(log2(CHANS_PER_ARRAY) -1 downto 0);
                rd_addr_bram_by_shift(1) <= (others => chan_addr_b_v & RD_ADDR_B(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES)));
            end process;
        end generate;
    else generate
        bram_demux_p : process (all) is
        begin
            rd_en_bram_demux                                                                                                            <= (others => (others => '0'));
            rd_en_bram_demux(to_integer(unsigned(RD_CHAN_A(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY))))) <= (others => RD_EN_A);
        end process;

        rd_data_demux_g : if (MFB_REGIONS = 1) generate

            rd_data_vld_reg_p : process (CLK) is
            begin
                if (rising_edge(CLK)) then
                    RD_DATA_VLD_A <= RD_EN_A;
                end if;
            end process;

            rd_data_bram_mux(0) <= rd_data_bram(to_integer(unsigned(RD_CHAN_A(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(0);
        else generate

            rd_data_demux_p : process (all)
            begin
                rd_data_bram_mux <= (others => (others => '0'));
                RD_DATA_VLD_A    <= '0';

                for i in 0 to MFB_REGIONS - 1 loop
                    if (rd_data_valid_arr(i) = '1') then
                        rd_data_bram_mux(0) <= rd_data_bram(to_integer(unsigned(RD_CHAN_A(log2(MEM_ARRAYS) + log2(CHANS_PER_ARRAY) -1 downto log2(CHANS_PER_ARRAY)))))(i);
                        RD_DATA_VLD_A       <= '1';
                    end if;
                end loop;
            end process;
        end generate;

        rd_barrel_shifter_g : if (READ_BARREL_SHIFTER_EN(0)) generate
            rd_data_barrel_shifter_i : entity work.BARREL_SHIFTER_GEN
            generic map (
                BLOCKS     => MFB_BYTES,
                -- The Reading side is addressable by bytes so the number of blocks is 4 times more than on the
                -- reading side
                BLOCK_SIZE => 8,
                SHIFT_LEFT => FALSE
            )
            port map (
                DATA_IN  => rd_data_bram_mux(0),
                DATA_OUT => RD_DATA_A,
                SEL      => RD_ADDR_A(log2(MFB_BYTES) - 1 downto 0)
            );

            rd_addr_recalc_g : for rgn in 0 to (MFB_REGIONS -1) generate
                rd_addr_recalc_p : process (all) is
                    variable chan_addr_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
                begin
                    chan_addr_v                := RD_CHAN_A(log2(CHANS_PER_ARRAY) -1 downto 0);
                    rd_addr_bram_by_shift(rgn) <= (others => (chan_addr_v & RD_ADDR_A(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES))));

                    for i in 0 to ((MFB_LENGTH/8) -1) loop
                        if (i < unsigned(RD_ADDR_A(log2(MFB_BYTES) - 1 downto 0))) then
                            rd_addr_bram_by_shift(rgn)(i) <= chan_addr_v & std_logic_vector(unsigned(RD_ADDR_A(log2(BUFFER_DEPTH) + log2(MFB_BYTES) -1 downto log2(MFB_BYTES))) + 1);
                        end if;
                    end loop;
                end process;
            end generate;
        else generate
            RD_DATA_A <= rd_data_bram_mux(0);

            rd_addr_recalc_p : process (all) is
                variable chan_addr_v : std_logic_vector(log2(CHANS_PER_ARRAY) -1 downto 0);
            begin
                chan_addr_v           := RD_CHAN_A(log2(CHANS_PER_ARRAY) -1 downto 0);
                rd_addr_bram_by_shift <= (others => (others => (chan_addr_v & RD_ADDR_A(log2(BUFFER_DEPTH)+log2(MFB_BYTES) -1 downto log2(MFB_BYTES)))));
            end process;
        end generate;
    end generate;
end architecture;
