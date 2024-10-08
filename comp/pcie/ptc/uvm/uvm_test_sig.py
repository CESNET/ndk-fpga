import sys
import re


def modelsim_handle(items):
    # First stage: fetch information about signals.
    # This is done by catching output of the 'describe' commands into a temporary file
    if len(sys.argv) > 1 and sys.argv[1] == '--fetch_info':
        print('set filename "uvm_test_sig.pydesc.txt"; set fileId [open $filename "w"]')
        for item in items:
            if isinstance(item, str):
                pass
            else:
                item.query_description()

        print('close $fileId')
    # Second stage: parse informations from temporary file
    # and issue the commands for adding signals to the wave
    else:
        desc = open("uvm_test_sig.pydesc.txt")
        for item in items:
            if isinstance(item, str):
                # Interpret as raw Tcl command
                print(item)
            else:
                item.parse_description(desc)
                item.add_wave()


# Not so pretty and sophisticated function for adding signals to the wave window
def add_wave(path, name=None):
    cmd = 'add wave'
    if isinstance(path, list):
        cmd += ' -group { ' + (name if name else '') + ' }'
        cmd += ' ' + " ".join(path) + ''
    else:
        if name is None:
            cmd += ' {' + path + '}'
        else:
            cmd += ' {' + (name if name else '') + ' {' + path + '}}'
    print(cmd)

# Escape square brackets


def escape_sb(string):
    return string.replace("[", "\\[").replace("]", "\\]")


class Bus:
    items = []

    def __init__(self, path, suffix=''):
        self.path = path
        self.suffix = suffix

    def add_wave(self, file):
        pass

    def parse_description(self, file):
        pass

    def query_description(self):
        pass

    def query_nested_width(self, file):
        self.nested_width = []
        ln = file.readline()
        # INFO: Automatically parsed nested arrays is currently not fully supported
        m = re.search(r'Array\(.*\) \[length (.*)\] of', ln)
        while m:
            self.nested_width.append(int(m[1]))
            ln = file.readline()
            m = re.search(r'Array\(.*\) \[length (.*)\] of', ln)

        # Consume empty line
        ln = file.readline()
        assert ln.strip() == ""


class MVB(Bus):
    def query_description(self):
        print(f'puts $fileId [describe "{self.path}MVB_DATA{escape_sb(self.suffix)}"]')

    def add_wave(self, prefix=None):
        offset = 0
        for j in range(self.mvb_items):
            for i, item in enumerate(self.items):
                name, width = item
                if name is not None:
                    add_wave(f'{self.path}MVB_DATA{self.suffix}[{offset + width - 1}:{offset}]', (prefix if prefix is not None else self.path.split('/')[-1]) + name + str(j))
                offset += width

        add_wave(f'{self.path}MVB_VLD{self.suffix}')
        add_wave(f'{self.path}MVB_SRC_RDY{self.suffix}')
        add_wave(f'{self.path}MVB_DST_RDY{self.suffix}')

    def parse_description(self, file):
        self.query_nested_width(file)

        item_width = sum([width for name, width in self.items])
        self.total_width = self.nested_width[-1]

        self.mvb_items = self.total_width // item_width

        assert self.total_width % item_width == 0


class MVB_HDR(Bus):
    def query_description(self):
        print(f'puts $fileId [describe "{self.path}MVB_HDR_DATA{escape_sb(self.suffix)}"]')

    def add_wave(self, prefix=None):
        offset = 0
        for j in range(self.mvb_items):
            for i, item in enumerate(self.items):
                name, width = item
                if name is not None:
                    add_wave(f'{self.path}MVB_HDR_DATA{self.suffix}[{offset + width - 1}:{offset}]', (prefix if prefix is not None else self.path.split('/')[-1]) + name + str(j))
                offset += width

        add_wave(f'{self.path}MVB_VLD{self.suffix}')

    def parse_description(self, file):
        self.query_nested_width(file)

        item_width = sum([width for name, width in self.items])
        self.total_width = self.nested_width[-1]

        self.mvb_items = self.total_width // item_width
        assert self.total_width % item_width == 0


class MFB(Bus):
    def show_divided(self, parts):
        self.parts = parts
        return self

    def query_description(self):
        print(f'puts $fileId [describe "{self.path}MFB_DATA{escape_sb(self.suffix)}"]')

    def parse_description(self, file):
        self.query_nested_width(file)
        #l = file.readline()
        #m = re.search(r'Array\(.*\) \[length (.*)\] of', l)
        #self.total_width = int(m[1])
        self.total_width = self.nested_width[-1]

        # Consume rest of lines
        #l = file.readline()
        #l = file.readline()

    def add_wave(self):
        if not hasattr(self, 'parts'):
            self.parts = 1
        width = self.total_width // self.parts
        for offset in range(self.parts):
            add_wave(f'{self.path}MFB_DATA{self.suffix}[{offset * width + width - 1}:{offset * width}]')
        add_wave(f'{self.path}MFB_SOF{self.suffix}')
        add_wave(f'{self.path}MFB_EOF{self.suffix}')
        add_wave(f'{self.path}MFB_SRC_RDY{self.suffix}')
        add_wave(f'{self.path}MFB_DST_RDY{self.suffix}')


# Define user MVB data subitems
class DMAUpHdr(MVB):
    items = list(zip(
        ['length', 'type', 'firstib', 'lastib', 'tag', 'unitid', 'addr', 'vfid', 'relaxed'],
        [11, 1, 2, 2, 8, 8, 64, 8, 1],
    ))


class DMADownHdr(MVB):
    items = list(zip(
        ['length', 'completed', None, 'tag', 'unit'],
        [11, 1, 4, 8, 8]
    ))


class RQHdr(MVB_HDR):
    items = list(zip(
        ['length', 'at', 'snoop', 'relaxed', 'ep', 'td', 'padd_0', 'tag_8', 'tc', 'tag_9', 'type_n', 'fmt', 'firstbe', 'lastbe', 'tag', 'req_id', 'global_id'],
        [10, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 4, 4, 8, 16, 64]
    ))


class RCHdr(MVB_HDR):
    items = list(zip(
        ['length', 'at', 'snoop', 'relaxed', 'ep', 'td', 'padd_0', 'tag_8', 'tc', 'tag_9', 'const', 'byte_cnt', 'bcm', 'complete_st', 'completer_id', 'low_addr', 'const_2', 'tag', 'req_id'],
        [10, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8, 12, 1, 3, 16, 7, 1, 8, 16],
    ))


# Create list of requested signals / buses
path_dma = 'sim:/testbench/DUT_U/VHDL_DUT_U/'
#path_app = 'sim:/fpga/usp_i/application_core_i/'
items = [
    DMAUpHdr(path_dma + 'UP_', '[0]'),
    RQHdr(path_dma + 'RQ_'),
    DMADownHdr(path_dma + 'DOWN_', '[0]'),
    MFB(path_dma + 'DOWN_', '[0]').show_divided(8),
    RCHdr(path_dma + 'RC_'),
    # MFB(path_app + 'DMA_TX_').show_divided(8),
    # Raw Tcl command(s)
    "proc sim_post_run {} {wave zoom range 9us 11.5us}"
]

if __name__ == "__main__":
    modelsim_handle(items)
