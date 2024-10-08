import nfb
import time

FTILE_RSFEC_BASES = {25: 0x6000, 50: 0x6200, 100: 0x6600, 200: 0x6E00, 400: 0x7E00}
# See https://www.intel.com/content/www/us/en/docs/programmable/683023/22-2/ethernet-hard-ip-core-csrs.html
FTILE_ETH_BASES =  {10: 0x1000, 25: 0x1000, 50: 0x2000, 40: 0x3000, 100: 0x3000, 200: 0x4000, 400: 0x5000, 0: 0x3000 }
ETH_LANES       =  {10: 1, 25: 1, 50: 4, 40: 4, 100: 20, 200: 8, 400: 16, 0: 4}
FEC_NONE        = 0
FEC_FIRECODE    = 1
FEC_CL91        = 2
FEC_CL134       = 3
FEC_ETC         = 4
FEC_MODE_STR    = {0: 'No FEC', 1: 'Firecode (CL 74)', 2: '2:RS(528,514) (Clause 91)', 3: 'RS(544,514) (Clause 134)', 4: 'Ethernet Technology Consortium RS(272,258)', 5: 'Reserved/Unknown', 6: 'Reserved/Unknown',  7: 'Reserved/Unknown'}


def drp_read(regs, reg, page=0, verbose=False):
     reg = reg >> 2
     cmd = (page << 4) + 0
     # Write DRP address 
     regs.write32(0x18014,reg)
     # Set page & start the operation
     regs.write32(0x18018, cmd)
     # Get the result
     time.sleep(0.001)
     val = regs.read32(0x18010)
     if verbose:
         print('Reading reg {:08x}, page {:d}, cmd {:08x}, value {:08x}'.format(reg, page, cmd, val))
     return val

def drp_write(comp, reg, val, page=0):
     reg = reg >> 2
     cmd = (page << 4) + 1
     # Write value 
     comp.write32(0x18010,val)
     # Write DRP address 
     comp.write32(0x18014,reg)
     # Set page & start the operation
     #print('Writing reg {:08x}, cmd {:08x}'.format(reg, cmd))
     comp.write32(0x18018, cmd)
     time.sleep(0.001) # !!!!!!!!!!!!!!!

def drp_read_drc(regs, reg, page=0, verbose=False):
     cmd = (page << 4) + 0
     # Write DRP address 
     regs.write32(0x18014,reg)
     # Set page & start the operation
     regs.write32(0x18018, cmd)
     # Get the result
     time.sleep(0.001)
     val = regs.read32(0x18010)
     if verbose:
         print('Reading reg {:08x}, page {:d}, cmd {:08x}, value {:08x}'.format(reg, page, cmd, val))
     return val

def drp_write_drc(comp, reg, val, page=0):
     cmd = (page << 4) + 1
     # Write value 
     comp.write32(0x18010,val)
     # Write DRP address 
     comp.write32(0x18014,reg)
     # Set page & start the operation
     #print('Writing reg {:08x}, cmd {:08x}'.format(reg, cmd))
     comp.write32(0x18018, cmd)
     time.sleep(0.001) # !!!!!!!!!!!!!!!     


def bit(val, b):
    """
    Return value of bit val[b]
    """
    return (val & (2**b)) >> b

def bits(val, start, count):
    """
    Return value of bits val[start:start+count]
    """
    hi_bit = start + count
    return (val >> start) & ((1 << count) - 1)


class ftile_rsfec():
    # For base addresses see https://www.intel.com/content/www/us/en/docs/programmable/683023/22-1/fec-and-transceiver-control-and-status.html
    def __init__(self, pcsregs, base=0x7e00, lanes = 16, mode=FEC_CL134):
        self.base = base
        self.comp = pcsregs
        self.page = 0
        self.lanes = lanes
        self.mode = mode

    def read(self, reg, lane=0):
        # Get offset to PCS lane
        addr = self.base + lane * 0x200 + reg
        #print('Reading lane {} reg {:08x}, addr {:08x}'.format(lane, reg, addr))
        return drp_read(self.comp, addr, 0)

    def read64(self, reg, lane=0):
        # Get offset to PCS lane
        addr = self.base + lane * 0x200 + reg 
        #print('Reading lane {} reg {:08x}, addr {:08x}'.format(lane, reg, addr))
        lo = drp_read(self.comp, addr,   0)
        hi = drp_read(self.comp, addr+4, 0)
        return (hi<<32)+lo

    def write(self, reg, val, lane=0):
        # Get offset to PCS lane
        addr = self.base + lane * 0x200 + reg
        drp_write(self.comp, addr, val, 0)

    def snapshot(self, lane):
        self.write(0x1e0, 1, lane)
        self.write(0x1e0, 0, lane)

    def clear_stats(self):
        for lane in range(0, self.lanes):
            self.write(0x1e0, 0x10, lane)

class ftile_pma():
    def __init__(self, pcsregs, lanes = 8):
        self.comp = pcsregs
        self.lanes = lanes

    def read(self, reg, lane=0):
        return drp_read(self.comp, reg, lane+1)

    def write(self, reg, val, lane=0):
        # Get offset to PCS lane
        drp_write(self.comp, reg, val, lane+1)

    def cpi_request(self, data, option, lane, opcode):
        #  See https://www.intel.com/content/www/us/en/docs/programmable/683872/22-4-4-3-0/fgt-attribute-access-method.html
        # Get transceiver index 
        index = self.read(0xffffc, lane) ## !!!! Not working after design boot !!! Why???????????????????????????????????????????????????????????????
        print(f'Phy lane readout {index:08x}')
        index &= 0x00000003
        val = (data << 16)  + (option << 12) + (index << 8) + (opcode)
        print(f'CPI req {lane}, phy lane {index}, value {val:08x}')
        self.write(0x9003c, val,  lane)
        # poll 0x90040 until bit 14 = 0 and bit 15 = option[3]
        ref = 0x8000 if (option&0x8) else 0x0000
        readout = self.read(0x90040, lane)
        print(f'CPI status: {readout:08x}')
        while (readout & 0xC000) != ref:
            readout = self.read(0x90040, lane)
            print(f'CPI status: {readout:08x}')

    def set_pma_loop(self, enable):
        val = 0x6 if enable else 0x0
        for lane in range(self.lanes):
             self.cpi_request(val,0xA, lane, 0x40)
             self.cpi_request(val,0x2, lane, 0x40)
     
    def set_lane_media_mode(self, lane, media=0x14):
        # See ttk_helper_ftile.tcl
        self.cpi_request(data=media, option=0xA, lane=lane, opcode=0x64)
        self.cpi_request(data=media, option=0x2, lane=lane, opcode=0x64)

    def set_mode(self, mode=0x14):
        for lane in range(self.lanes):
            #print('Setting mode {} for lane {}'.format(mode, lane))
            self.set_lane_media_mode(lane, mode)



class ftile_pcs():
    def __init__(self, pcsregs, base, lanes = 20):
        self.base = base
        self.comp = pcsregs
        self.lanes = lanes

    def read(self, reg):
        # Get offset to PCS 
        addr = self.base + (reg - 0x1000)
        val = drp_read(self.comp, addr, 0)
        #print('Reading PCS reg {:08x}, addr {:08x}, value = {:08x}'.format(reg, addr, val))
        return val

    def read64(self, reg):
        # Get offset to PCS 
        addr = self.base + (reg - 0x1000)
        lo = drp_read(self.comp, addr,   0)
        hi = drp_read(self.comp, addr+4, 0)
        return (hi<<32)+lo

    def write(self, reg, val):
        addr = self.base + (reg - 0x1000)
        drp_write(self.comp, addr, val, 0)

    def snapshot(self):
        self.write(0x1000, 3)
        self.write(0x1000, 0)

    def clear_stats(self):
        # Reset RX stats
        self.write(0x1278, 1)
        self.write(0x1278, 0)
        # Reset TX stats
        self.write(0x1274, 1)
        self.write(0x1274, 0)
      

class ftile_eth():

    def __init__(self, pcsregs):
        self.comp = pcsregs
        # Decode Ethernet mode from register 0x100
        config = drp_read(pcsregs, 0x100, 0)
        self.lanes = bits(config, 21, 4)
        self.modulation = 'PAM-4' if bit(config, 9) else 'NRZ'
        speed = bits(config, 5, 3)
        self.speed = \
            10  if speed == 0 else\
            25  if speed == 1 else\
            40  if speed == 2 else\
            50  if speed == 3 else\
            100 if speed == 4 else\
            200 if speed == 5 else\
            400 if speed == 6 else\
            0
        # Assign PMA
        self.pma = ftile_pma(pcsregs, self.lanes)
        # Assign PCS 
        pcsbase = FTILE_ETH_BASES[self.speed]
        pcslanes = ETH_LANES[self.speed]
        self.pcs = ftile_pcs(pcsregs, pcsbase, pcslanes)
        # Assign RS-FEC
        self.rsfec = None
        fec_mode = bits(config, 10, 3)
        fec_base = 0
        if self.speed in FTILE_RSFEC_BASES:
            fec_base = FTILE_RSFEC_BASES[self.speed]
            if fec_mode: 
                self.rsfec = ftile_rsfec(pcsregs, fec_base, self.speed//25, fec_mode)
        self.print_config()

    def print_config(self):
        config = drp_read(self.comp, 0x100, 0)
        fec_mode = bits(config, 10, 3)
        fec_base = 0
        if self.speed in FTILE_RSFEC_BASES:
            fec_base = FTILE_RSFEC_BASES[self.speed]    
        print(f'\nEth init: config = {config:08x}, speed = {self.speed}, modulation : {self.modulation}, lanes = {self.lanes}, rsfec mode = "{FEC_MODE_STR[fec_mode]}", base = {fec_base:04x}')

    def read(self, reg):
        #print('Reading Eth reg {:08x}'.format(reg))
        return drp_read(self.comp, reg, 0)

    def read64(self, reg):
        lo = drp_read(self.comp, addr,   0)
        hi = drp_read(self.comp, addr+4, 0)
        return (hi<<32)+lo

    def write(self, reg, val):
        # Get offset to PCS lane
        addr = reg
        drp_write(self.comp, addr, val, 0)

    def set_rxreset(self):
        self.write(0x108, 4)
        
    def clr_rxreset(self):
        self.write(0x108, 0)

    def set_reset(self):
        self.write(0x108, 6)
        time.sleep(0.5)
        
    def clr_reset(self):
        self.write(0x108, 0)
        time.sleep(0.5)

    def pma_loopback(self, enable):
        self.set_rxreset()
        self.pma.set_pma_loop(enable)
        self.clr_rxreset()
        time.sleep(0.1)

dev = nfb.open(path='0')
nodes = dev.fdt_get_compatible("netcope,pcsregs")

eths = [] 
for i, node in enumerate(nodes):
    comp = dev.comp_open(node)
    eth = ftile_eth(comp)
    eths.append(eth)

