# switch.py: SW Abstraction/Golden Reference Model of the Switch component
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import asyncio
from functools import partial
from math import ceil, log2

import hdr_info
from scapy.all import Ether


# wrapper ensuring proper calling of a function (a/sync)
async def asyncio_wrapper(function, *args, **kwargs):
    if asyncio.iscoroutinefunction(function):
        return await function(*args, **kwargs)
    else:
        return await asyncio.to_thread(function, *args, **kwargs)


# auxiliary lambdas for 'int <-> bytes' conversion
def reg2int(b):
    return int.from_bytes(b, "little")


def int2reg(i, w):
    return int.to_bytes(i, w, "little")


class SwitchAddrSpace:
    """ Software representation (internal) of switch address space. """

    #   name                  : (addr, bytes)
    _regs = {
        "M_NUM_META_REGS"     : (0x00, 4),
        "M_NUM_DATA_REGS"     : (0x04, 4),
        "M_VERSION"           : (0x08, 4),
        "M_NUM_ACTIONS"       : (0x0c, 4),
        "M_NUM_PORTS"         : (0x10, 4),
        "M_NUM_MATS_PER_PORT" : (0x14, 4),
        "M_MAT_CFGS"          : (0x18, 0), # design-dependent length
        "CSR"                 : (0x00, 0),
        "IN_ADDR"             : (0x00, 0),
        "IN_DATA"             : (0x00, 0),
        "IN_MASK"             : (0x00, 0),
        "IN_ACTION"           : (0x00, 0),
        "OUT_DATA"            : (0x00, 0),
        "OUT_MASK"            : (0x00, 0),
        "OUT_ACTION"          : (0x00, 0),
    }

    #   name                  : bit position
    _csr_fields = {
        "OP_ACTIVATE"         : 0x00000001,
        "OP_CONFIGURE"        : 0x00000002,
        "OP_SOFT_RESET"       : 0x00000004,
        "OP_WRITE"            : 0x00000008,
        "OP_READ"             : 0x00000010,
        "CAP_READ"            : 0x80000000,
    }

    def __init__(self):
        self.w          = 4
        self.regs       = __class__._regs.copy()
        self.csr_fields = __class__._csr_fields.copy()
        self.read_f     = None
        self.write_f    = None
        self.meta_info  = None
        self.mat_cfgs   = None
        self.cap_read   = True

    def _parse_mat_cfgs(self, mat_cfgs, num_mats_per_port):
        reg_idx, mats = 0, []
        try:
            for _ in range(num_mats_per_port):
                mat = {}
                for attr in ["num_fields", "num_items"]:
                    mat[attr] = reg2int(mat_cfgs[self.w*reg_idx:self.w*(reg_idx+1)])
                    reg_idx += 1
                mat["fields"] = []
                for _ in range(mat["num_fields"]):
                    field = {}
                    for attr in ["protocol", "range_high", "range_low"]:
                        field[attr] = reg2int(mat_cfgs[self.w*reg_idx:self.w*(reg_idx+1)])
                        reg_idx += 1
                    mat["fields"].append(field)
                mats.append(mat)
            return mats
        except IndexError:
            raise Exception("Invalid MATs configuration!")

    async def read(self, addr: int, count: int) -> bytes:
        assert self.read_f is not None, "Read function handle not initialized!"
        return await self.read_f(addr, count)

    async def read_reg(self, name: str, *, strip: bool = False) -> bytes:
        reg = await self.read(*self.regs[name])
        return reg.strip(b'\00') if strip else reg

    async def write(self, addr: int, data: bytes) -> None:
        assert self.write_f is not None, "Write function handle not initialized!"
        await self.write_f(addr, data)

    async def write_reg(self, name: str, data: bytes) -> None:
        addr, size = self.regs[name]
        await self.write(addr, data+(bytes(size-len(data))))

    async def send_cmd(self, cmd, max_retries=100, wait_only=False) -> bool:
        async def _wait_for_rdy(self, flag, max_retries, fake) -> bool:
            if not fake:
                for _ in range(max_retries):
                    if not (reg2int(await self.read_reg("CSR")) & flag):
                        break
                else:
                    return False
            return True

        flag = self.csr_fields["OP_"+cmd]
        if not (await _wait_for_rdy(self, flag, max_retries, cmd not in ["WRITE", "READ"])):
            return False
        if wait_only:
            return True
        await self.write_reg("CSR", int2reg(flag, self.w))
        return await _wait_for_rdy(self, flag, max_retries, cmd not in ["READ"])

    async def init(self, *, read_f=None, write_f=None) -> None:
        # initialize R/W function handles
        assert read_f is not None and write_f is not None, "Enter valid R/W functions!"
        self.read_f             = partial(asyncio_wrapper, read_f)
        self.write_f            = partial(asyncio_wrapper, write_f)

        # save immutable meta information internally
        def meta_sel(x):
            return x.startswith("M_") and x != "M_MAT_CFGS"

        self.meta_info          = dict([(r, reg2int(await self.read_reg(r))) for r in self.regs if meta_sel(r)])
        n_meta                  = self.meta_info["M_NUM_META_REGS"]
        n_data                  = self.meta_info["M_NUM_DATA_REGS"]
        n_mats_pp               = self.meta_info["M_NUM_MATS_PER_PORT"]
        self.regs["M_MAT_CFGS"] = (0x18, self.w*(n_meta-len(self.meta_info)))
        self.mat_cfgs           = self._parse_mat_cfgs(await self.read_reg("M_MAT_CFGS"), n_mats_pp)
        # construct representation of the address space
        reg_counts              = iter([1, 1, n_data, n_data, 1, n_data, n_data, 1])
        addr_tmp                = sum(self.regs["M_MAT_CFGS"])
        for reg in filter(lambda x : not x.startswith("M_"), list(self.regs)):
            reg_size       = self.w*next(reg_counts)
            self.regs[reg] = (addr_tmp, reg_size)
            addr_tmp      += reg_size
        # adjust address space with respect to read capability
        if not (reg2int(await self.read_reg("CSR")) & self.csr_fields["CAP_READ"]):
            self.regs = {k: v for k, v in self.regs.items() if not k.startswith("OUT_")}
            self.cap_read = False

    def _dbg_dump_reg(self, name: str, addr: int, value) -> str:
        def _dbg_str(name, addr, value) -> str:
            if type(value) is not int:
                if type(value) is bytes:
                    value = reg2int(value)
                else:
                    return ''
            return f'{addr:#0{10}x} : {name: <20} = {value:#0{10}x} ({value})\n'
        if type(value) is int or len(value) == self.w:
            report = _dbg_str(name, addr, value)
        else:
            report    = ""
            rest, idx = value, 0
            while len(rest) > 0:
                report   += _dbg_str(name+str(idx), addr+idx*self.w, rest[:self.w])
                rest, idx = rest[self.w:], idx+1
        return report

    async def _dbg_dump_reg_async(self, name: str) -> str:
        return self._dbg_dump_reg(name, self.regs[name][0], await self.read_reg(name))

    def dbg_dump_meta(self) -> str:
        report = "< META_REGISTERS >\n"
        # design-independent meta information
        for reg in self.meta_info:
            report += self._dbg_dump_reg(reg, self.regs[reg][0], self.meta_info[reg])
        # design-dependent meta information (set of available MATs)
        reg_addr = self.regs["M_MAT_CFGS"][0]
        for mat_idx, mat_info in enumerate(self.mat_cfgs):
            report += f'\tMAT #{mat_idx}:\n'
            for attr, value in mat_info.items():
                report += self._dbg_dump_reg(attr, reg_addr, value)
                reg_addr += self.w
            for field_idx, field_info in enumerate(mat_info["fields"]):
                report += f'\t\tFIELD #{field_idx} ({get_field_info_str(*field_info.values())}):\n'
                for attr, value in field_info.items():
                    report += self._dbg_dump_reg(attr, reg_addr, value)
                    reg_addr += self.w
        return report

    async def dbg_dump_csr(self) -> str:
        report = "< CSR >\n"
        report += await self._dbg_dump_reg_async("CSR")
        return report

    async def dbg_dump_in(self) -> str:
        report = "< INPUT REGISTERS >\n"
        for reg in filter(lambda x : x.startswith("IN_"), list(self.regs)):
            report += await self._dbg_dump_reg_async(reg)
        return report

    async def dbg_dump_out(self) -> str:
        report = "< OUTPUT REGISTERS >\n"
        for reg in filter(lambda x : x.startswith("OUT_"), list(self.regs)):
            report += await self._dbg_dump_reg_async(reg)
        return report

    async def dbg_dump_all(self) -> str:
        report  = ""
        report += self.dbg_dump_meta()
        report += await self.dbg_dump_csr()
        report += await self.dbg_dump_in()
        report += await self.dbg_dump_out()
        return report

    def __getitem__(self, key):
        return self.regs[key]


class Switch:
    """ Software API main component. """

    class Rule:
        """ Software abstraction of a rule. """

        def __init__(self, data: bytes = None, mask: bytes = None, action: bytes = None):
            self.dict = {'data': data, 'mask': mask, 'action': action}

        def __getitem__(self, key):
            return self.dict[key]

        def __setitem__(self, key, value):
            self.dict[key] = value

        def __iter__(self):
            return iter(self.dict)

        def __str__(self):
            return str(self.dict)

        def fw_delete(self) -> 'Rule':
            """ Sets fields to achieve deletion in FW. """
            self['data'], self['mask'], self['action'] = b'\x01', b'\x00', b'\x00'
            return self

        def is_deleted(self) -> bool:
            """ Checks whether FW data are deleted. """
            data, mask = reg2int(self['data']), reg2int(self['mask'])
            return mask | data != mask

        def __bool__(self):
            if not self['data'] or not self['mask'] or not self['action']:
                return False
            return not self.is_deleted()

        def clear(self) -> None:
            """ Clear rule fields. """
            self.dict = {k: None for k in self}

        def sanitize(self) -> None:
            """ Clear rule fields when invalid or deleted. """
            if not self:
                self.clear()

        def copy(self, rule: 'Rule' = None) -> 'Rule':
            """ Copy rule (create new/overwrite). """
            if rule is None:
                cp = self.__class__()
                return cp.copy(self)
            else:
                self.dict = {k: v for k, v in rule.dict.items()}
                return self

        def match(self, mv: bytes) -> bool:
            """ Match vector against rule. """
            data = reg2int(self['data'])
            mask = reg2int(self['mask'])
            mvec = reg2int(mv)
            return self if not self else data & mask == mvec & mask

    def __init__(self, *, grm=False):
        """ Constructor.
            Params
            ------
                grm ... mirror fw rules within sw
        """
        self.grm  = grm
        self.regs = SwitchAddrSpace()

    def _mat_addr(self, mat: int, addr: int) -> bytes:
        """ Build MAT rule address. """
        mat_sel = mat << (self.regs.w*8 - ceil(log2(self.num_mats)))
        return int2reg(mat_sel | addr, self.regs.w)

    async def init(self, *, read_f=None, write_f=None) -> None:
        """ Initialize the API.
            Params
            ------
                read_f  ... low-level read function handle
                write_f ... low-level write function handle
        """
        # initialize SwitchAddrSpace object
        await self.regs.init(read_f=read_f, write_f=write_f)
        # save useful configuration info
        self.version           = self.regs.meta_info["M_VERSION"]
        self.num_actions       = self.regs.meta_info["M_NUM_ACTIONS"]
        self.num_ports         = self.regs.meta_info["M_NUM_PORTS"]
        self.num_mats_per_port = self.regs.meta_info["M_NUM_MATS_PER_PORT"]
        self.num_mats          = self.num_ports * self.num_mats_per_port
        self.mat_cfgs          = self.regs.mat_cfgs

        # provide user-friendly way of MATs indexing -> self.mats[port_idx][mat_idx]
        def subrange(sr_idx, width):
            return [width*sr_idx+j for j in range(width)]

        self.mats = [subrange(port, self.num_mats_per_port) for port in range(self.num_ports)]
        # mirror MATs depths in FW
        self.mats_items = [mat_cfg["num_items"] for mat_cfg in self.mat_cfgs]*self.num_ports
        # enable Golden Reference Model
        self.fw = [[self.Rule() for _ in range(items)] for items in self.mats_items] if self.grm else None

    def _check_addr(func):
        """ Check address validity. """
        async def wrapper(self, mat, addr, *args, **kwargs):
            if not isinstance(mat, int) or not (0 <= mat < self.num_mats):
                raise ValueError(f"Invalid MAT selector: {mat}. Should be in range <0, {self.num_mats})")
            if not isinstance(addr, int) or not (0 <= addr < self.mats_items[mat]):
                raise ValueError(f"Invalid MAT address: {addr}. Should be in range <0, {self.mats_items[mat]})")
            return await func(self, mat, addr, *args, **kwargs)
        return wrapper

    def _check_rule(func):
        """Check rule validity. """
        async def wrapper(self, rule, *args, **kwargs):
            if not isinstance(rule, self.Rule):
                raise ValueError(f"Invalid rule: {rule}.")
            action = reg2int(rule['action'])
            if action >= self.num_actions:
                raise ValueError(f"Invalid action: {action}. Should be in range <0, {self.num_actions})")
            for field in rule:
                if rule[field] is None:
                    raise ValueError(f"Invalid rule: {rule}. Field '{field}' should not be {rule[field]}!")
            return await func(self, rule, *args, **kwargs)
        return wrapper

    @_check_addr
    async def write_addr(self, mat: int, addr: int) -> None:
        """ Write address to firmware.

            Params
            ------
                mat  ... MAT index
                addr ... MAT rule address
        """
        await self.regs.write_reg("IN_ADDR", self._mat_addr(mat, addr))

    @_check_rule
    async def write_rule(self, rule: 'Switch.Rule') -> None:
        """ Write rule to firmware (rule only).

            Params
            ------
                rule ... Rule object
        """
        for field in rule:
            await self.regs.write_reg("IN_"+field.upper(), rule[field])

    async def write(self, mat: int, addr: int, rule: 'Switch.Rule', write_rule: bool = True) -> bool:
        """ Write rule to firmware.

            Params
            ------
                mat        ... MAT index
                addr       ... MAT rule address
                rule       ... Rule object
                write_rule ... write rule? (optimization for clear methods)

            Returns
            -------
                bool       ... operation successful
        """
        await self.write_addr(mat, addr)
        if write_rule:
            await self.write_rule(rule)
        if (ret := await self.regs.send_cmd("WRITE")) and self.grm:
            if not rule:
                self.fw[mat][addr].clear()
            else:
                self.fw[mat][addr].copy(rule)
        return ret

    async def read(self, mat: int, addr: int, *, grm_read: bool = True, strip: bool = False) -> 'Switch.Rule':
        """ Read rule from firmware.

            Params
            ------
                mat         ... MAT index
                addr        ... MAT rule address
                grm_read    ... read from software mirror instead?
                strip       ... trim leading zero bytes

            Returns
            -------
                Switch.Rule ... rule read from firmware/mirror
        """
        if self.grm and grm_read:
            return self.fw[mat][addr].copy()
        rule = self.Rule()
        if self.regs.cap_read:
            await self.write_addr(mat, addr)
            if (await self.regs.send_cmd("READ")):
                for field in rule:
                    rule[field] = await self.regs.read_reg("OUT_"+field.upper(), strip=strip)
            rule.sanitize()
        return rule

    # TODO: delete_rule based on the rule -> using grm with hashing
    async def delete(self, mat: int, addr: int, write_rule: bool = True) -> bool:
        """ Delete rule in firmware.

            Params
            ------
                mat        ... MAT index
                addr       ... MAT rule address
                write_rule ... write rule? (optimization for clear methods)

            Returns
            -------
                bool       ... operation successful
        """
        return await self.write(mat, addr, self.Rule().fw_delete(), write_rule)

    async def clear_mat(self, mat: int, write_rule: bool = True) -> bool:
        """ Clear MAT.

            Params
            ------
                mat        ... MAT index
                write_rule ... write rule? (optimization for clear_all)

            Returns
            -------
                bool       ... operation successful
        """
        ret = True
        for addr in range(self.mats_items[mat]):
            if not (ret := await self.delete(mat, addr, write_rule and addr == 0x00)):
                break
        return ret

    async def clear_all(self) -> bool:
        """ Clear all MATs.

            Returns
            -------
                bool ... operation successful
        """
        ret = True
        for mat in range(self.num_mats):
            if not (ret := await self.clear_mat(mat, mat == 0)):
                break
        return ret

    async def dbg_dump_mat(self, mat: int, *, grm_read: bool = True) -> str:
        """ Report active MAT rules.

            Params
            ------
                mat      ... MAT index
                grm_read ... read from software mirror instead?

            Returns
            -------
                str      ... representation of MAT address space
        """
        report    = f"MAT #{mat}\n"
        mat_items = self.mats_items[mat]
        addr_w    = ceil(log2(mat_items)/4)+2
        for addr in range(mat_items):
            rule = await self.read(mat, addr, grm_read=grm_read)
            if rule:
                report += f"{addr:#0{addr_w}x} : {rule}\n"
        return report

    async def dbg_dump_all(self, *, grm_read: bool = True) -> str:
        """ Report active rules from all MATs.

            Params
            ------
                grm_read ... read from software mirror instead?

            Returns
            -------
                str      ... representation of MATs' address spaces
        """
        report = ""
        for mat in range(self.num_mats):
            report += await self.dbg_dump_mat(mat, grm_read=grm_read)
        return report

    async def soft_reset(self):
        """ Carry out software reset of addressable registers. """
        await self.regs.send_cmd("SOFT_RESET")

    async def start_traffic(self):
        """ Switch to active mode (see SWITCH_CONTROLLER). """
        await self.regs.send_cmd("ACTIVATE")

    async def stop_traffic(self):
        """ Switch to configuration mode (see SWITCH_CONTROLLER). """
        await self.regs.send_cmd("CONFIGURE")

    async def wait(self):
        """ Wait for completion of write operation. """
        return await self.regs.send_cmd("WRITE", wait_only=True)

    async def config(self, cfg: dict) -> bool:
        """ Configure the switch.

            Params
            ------
                cfg  ... JSON-like configuration object (see cocotb_test.py: testbench.init)

            Returns
            -------
                bool ... operation successful
        """
        for mat, mat_cfg in cfg.items():
            for addr, rule in mat_cfg.items():
                if not await self.write(int(mat), int(addr), self.Rule(*[bytes(r) for r in rule])):
                    return False
        return True

    def predict(self, frame: Ether, port: int) -> int:
        """ Predict output port for a given frame.

            Params
            ------
                frame ... input frame (in scapy.all.Ether format)
                port  ... input port

            Returns
            -------
                int   ... output port prediction
        """
        if not self.grm or port >= self.num_ports:
            return -1
        action = None
        for mat_pidx, mat in enumerate(self.fw[port*self.num_mats_per_port:(port+1)*self.num_mats_per_port]):
            match_vector = bytes()
            # TODO: add support for multiple fields/byte-unaligned fields
            for field in self.mat_cfgs[mat_pidx]['fields']:
                protocol       = field['protocol']
                protocol_class = hdr_info.get_protocol_class(protocol)
                if protocol_class not in frame:
                    continue
                field_range = (field['range_high'], field['range_low'])
                field_id    = hdr_info.get_field_id(protocol, *field_range)
                fld, val    = frame[protocol_class].getfield_and_val(field_id)
                val_decode  = fld.i2m(frame, val)
                if type(val_decode) is int:
                    field_width = ceil((field_range[0]+1 - field_range[1])/8)
                    val_decode  = int2reg(val_decode, field_width)
                match_vector   += val_decode

            for rule in filter(lambda r : bool(r), mat):
                if rule.match(match_vector):
                    action = reg2int(rule['action'])

            if action is not None:
                return action

        return 0
