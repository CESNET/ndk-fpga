---------------------------------------------------------------------
----                                                             ----
----  I2C Master Core - generic control ports; top level         ----
----                                                             ----
----                                                             ----
----  Author: Richard Herveille                                  ----
----          richard@asics.ws                                   ----
----          www.asics.ws                                       ----
----                                                             ----
----  Adaptation for the Liberouter project:                     ----
----          Stepan Friedl                                      ----
----          friedl@liberouter.org                              ----
----                                                             ----
----  Downloaded from: http://www.opencores.org/projects/i2c/    ----
----                                                             ----
---------------------------------------------------------------------
----                                                             ----
---- Copyright (C) 2000 Richard Herveille                        ----
----                    richard@asics.ws                         ----
----                                                             ----
---- This source file may be used and distributed without        ----
---- restriction provided that this copyright statement is not   ----
---- removed from the file and that any derivative work contains ----
---- the original copyright notice and the associated disclaimer.----
----                                                             ----
----     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ----
---- EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ----
---- TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ----
---- FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ----
---- OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ----
---- INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ----
---- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ----
---- GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ----
---- BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ----
---- LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ----
---- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ----
---- OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ----
---- POSSIBILITY OF SUCH DAMAGE.                                 ----
----                                                             ----
---------------------------------------------------------------------

--  CVS Log
--
--  $Id$
--
--  $Date$
--  $Revision$
--  $Author$
--  $Locker:  $
--  $State: Exp $
--
-- Change History:
--               $Log: i2c_master_top.vhd,v $
--               Revision 1.7  2004/03/14 10:17:03  rherveille
--               Fixed simulation issue when writing to CR register
--
--               Revision 1.6  2003/08/09 07:01:13  rherveille
--               Fixed a bug in the Arbitration Lost generation caused by delay on the (external) sda line.
--               Fixed a potential bug in the byte controller's host-acknowledge generation.
--
--               Revision 1.5  2003/02/01 02:03:06  rherveille
--               Fixed a few 'arbitration lost' bugs. VHDL version only.
--
--               Revision 1.4  2002/12/26 16:05:47  rherveille
--               Core is now a Multimaster I2C controller.
--
--               Revision 1.3  2002/11/30 22:24:37  rherveille
--               Cleaned up code
--
--               Revision 1.2  2001/11/10 10:52:44  rherveille
--               Changed PRER reset value from 0x0000 to 0xffff, conform specs.
--
-- SF 2009/03/13: Internal registers to DWR(DRD) mapping:
--  bit 63                         bit32                                 bit0
--  RESERVED|RESERVED| TXR/RXR | CR/SR  |RESERVED|   CTR   | PRERhi  | PRERlo

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;

entity i2c_master_top is
	generic (
	   PRER_INIT : unsigned(15 downto 0) := (others => '1')
	);
	port (
		-- master clock input, up to 250MHz
		CLK       : in  std_logic;
		-- synchronous active high reset
		RST_SYNC  : in  std_logic;
		-- asynchronous reset, active HIGH
		RST_ASYNC : in  std_logic;

		-- ===========
		-- generic bus
		-- ===========

		--  Byte enables for Write operation
		BE        : in  std_logic_vector( 7 downto 0);
		-- Databus input
		DWR       : in  std_logic_vector(63 downto 0);
		-- Databus output
		DRD       : out std_logic_vector(63 downto 0);
		-- Write enable input
		WEN       : in  std_logic;
		-- interrupt output signal
		INT       : out std_logic;

		-- ===========
		-- i2c lines
		-- ===========

		-- i2c clock line input
		SCL_PAD_I     : in  std_logic;
		-- i2c clock line output
		SCL_PAD_O     : out std_logic;
		-- i2c clock line output enable, active low
		SCL_PADOEN_O  : out std_logic;
		-- i2c data line input
		SDA_PAD_I     : in  std_logic;
		-- i2c data line output
		SDA_PAD_O     : out std_logic;
		-- i2c data line output enable, active low
		SDA_PADOEN_O  : out std_logic
	);
end entity i2c_master_top;

architecture structural of i2c_master_top is
	component i2c_master_byte_ctrl is
	port (
		clk    : in std_logic;
		rst    : in std_logic; -- synchronous active high reset (WISHBONE compatible)
		nReset : in std_logic;	-- asynchornous active low reset (FPGA compatible)
		ena    : in std_logic; -- core enable signal

		clk_cnt : in unsigned(15 downto 0);	-- 4x SCL

		-- input signals
		start,
		stop,
		read,
		write,
		ack_in : std_logic;
		din    : in std_logic_vector(7 downto 0);

		-- output signals
		cmd_ack  : out std_logic;
		ack_out  : out std_logic;
		i2c_busy : out std_logic;
		i2c_al   : out std_logic;
		dout     : out std_logic_vector(7 downto 0);

		-- i2c lines
		scl_i   : in std_logic;  -- i2c clock line input
		scl_o   : out std_logic; -- i2c clock line output
		scl_oen : out std_logic; -- i2c clock line output enable, active low
		sda_i   : in std_logic;  -- i2c data line input
		sda_o   : out std_logic; -- i2c data line output
		sda_oen : out std_logic  -- i2c data line output enable, active low
	);
	end component i2c_master_byte_ctrl;

	-- registers
	signal prer : unsigned(15 downto 0);             -- clock prescale register
	signal ctr  : std_logic_vector(7 downto 0);      -- control register
	signal txr  : std_logic_vector(7 downto 0);      -- transmit register
	signal rxr  : std_logic_vector(7 downto 0);      -- receive register
	signal cr   : std_logic_vector(7 downto 0);      -- command register
	signal sr   : std_logic_vector(7 downto 0);      -- status register

	-- internal reset signal
	signal rst_i : std_logic;

	-- internal acknowledge signal
	signal iack_o : std_logic;

	-- done signal: command completed, clear command register
	signal done : std_logic;

	-- command register signals
	signal sta, sto, rd, wr, ack, iack : std_logic;

	signal core_en : std_logic;                      -- core enable signal
	signal ien     : std_logic;                      -- interrupt enable signal

	-- status register signals
	signal irxack, rxack : std_logic;                -- received aknowledge from slave
	signal tip           : std_logic;                -- transfer in progress
	signal irq_flag      : std_logic;                -- interrupt pending flag
	signal i2c_busy      : std_logic;                -- i2c bus busy (start signal detected)
	signal i2c_al, al    : std_logic;                -- arbitration lost

begin
	-- generate internal reset signal
	rst_i <= not RST_ASYNC;

	-- assign DRD
        DRD <= X"0000" & rxr & sr & X"00" & ctr & std_logic_vector(prer);

        ctr(5 downto 0) <= (others => '0');

	-- generate registers (CR, SR see below)
	gen_regs: process(rst_i, CLK)
	begin
	    if (rst_i = '0') then
	      prer   <= PRER_INIT;
	      ctr(6) <= '0';
	      ctr(7) <= '0';
	      txr    <= (others => '0');
	    elsif (CLK'event and CLK = '1') then
	      if (RST_SYNC = '1') then
	        prer   <= PRER_INIT;
	        ctr(6) <= '0';
	        ctr(7) <= '0';
	        txr    <= (others => '0');
	      elsif (WEN = '1') then
	         if core_en = '0' then
	            if BE(0) = '1' then   --
	               prer(7 downto 0) <= unsigned(DWR(7 downto 0));
	            end if;
	            if BE(1) = '1' then   --
	               prer(15 downto 8) <= unsigned(DWR(15 downto 8));
	            end if;
	         end if;
	         if BE(2) =  '1' then
	            ctr(6) <= DWR(22);
	            ctr(7) <= DWR(23);
	         end if;
	         if BE(5) =  '1' then
	            txr  <= DWR(47 downto 40);
	         end if;
	      end if;
	    end if;
	end process gen_regs;

	-- generate command register
	gen_cr: process(rst_i, CLK)
	begin
	    if (rst_i = '0') then
	        cr <= (others => '0');
	    elsif (CLK'event and CLK = '1') then
	        if (RST_SYNC = '1') then
	            cr <= (others => '0');
	        elsif (WEN = '1') then
	            if ( (core_en = '1') and (BE(4) = '1') ) then
	                -- only take new commands when i2c core enabled
	                -- pending commands are finished
	                cr <= DWR(39 downto 32);
	            end if;
	        else
	            if (done = '1' or i2c_al = '1') then
	               cr(7 downto 4) <= (others => '0'); -- clear command bits when command done or arbitration lost
	            end if;

	            cr(2 downto 1) <= (others => '0');   -- reserved bits, always '0'
	            cr(0) <= '0';                        -- clear IRQ_ACK bit
	        end if;
	    end if;
	end process gen_cr;

	-- decode command register
	sta  <= cr(7);
	sto  <= cr(6);
	rd   <= cr(5);
	wr   <= cr(4);
	ack  <= cr(3);
	iack <= cr(0);

	-- decode control register
	core_en <= ctr(7);
	ien     <= ctr(6);

	-- hookup byte controller block
	byte_ctrl: i2c_master_byte_ctrl port map (
		clk      => CLK,
		rst      => RST_SYNC,
		nReset   => rst_i,
		ena      => core_en,
		clk_cnt  => prer,
		start    => sta,
		stop     => sto,
		read     => rd,
		write    => wr,
		ack_in   => ack,
		i2c_busy => i2c_busy,
		i2c_al   => i2c_al,
		din      => txr,
		cmd_ack  => done,
		ack_out  => irxack,
		dout     => rxr,
		scl_i    => SCL_PAD_I,
		scl_o    => SCL_PAD_O,
		scl_oen  => SCL_PADOEN_O,
		sda_i    => SDA_PAD_I,
		sda_o    => SDA_PAD_O,
		sda_oen  => SDA_PADOEN_O
	);


	-- status register block + interrupt request signal
	st_irq_block : block
	begin
	    -- generate status register bits
	    gen_sr_bits: process (CLK, rst_i)
	    begin
	        if (rst_i = '0') then
	          al       <= '0';
	          rxack    <= '0';
	          irq_flag <= '0';
	        elsif (CLK'event and CLK = '1') then
	          if (RST_SYNC = '1') then
	            al       <= '0';
	            rxack    <= '0';
	            irq_flag <= '0';
	          else
	            al       <= i2c_al or (al and not sta);
	            rxack    <= irxack;

	            -- interrupt request flag is always generated
	            irq_flag <= (done or i2c_al or irq_flag) and not iack;
	          end if;
	        end if;
	    end process gen_sr_bits;

	    -- Generate TIP flag (no flip-flop to be as fast as possible)
	    tip      <= (rd or wr);

	    -- generate interrupt request signals
	    gen_irq: process (CLK, rst_i)
	    begin
	        if (rst_i = '0') then
	          INT <= '0';
	        elsif (CLK'event and CLK = '1') then
	          if (RST_SYNC = '1') then
	            INT <= '0';
	          else
	            -- interrupt signal is only generated when IEN (interrupt enable bit) is set
	            INT <= irq_flag and ien;
	          end if;
	        end if;
	    end process gen_irq;

	    -- assign status register bits
	    sr(7)          <= rxack;
	    sr(6)          <= i2c_busy;
	    sr(5)          <= al;
	    sr(4 downto 2) <= (others => '0'); -- reserved
	    sr(1)          <= tip;
	    sr(0)          <= irq_flag;
	end block;

end architecture structural;
