class RAM:
    def __init__(self, capacity):
        self._mem = bytearray(capacity)

    def wint(self, addr, integer, byte_count, byteorder="little"):
        self.w(addr, list(integer.to_bytes(byte_count, byteorder=byteorder)))

    def rint(self, addr, byte_count, byteorder="little"):
        return int.from_bytes(self.r(addr, byte_count), byteorder=byteorder)

    def w(self, addr, byte):
        self._mem[addr: addr + len(byte)] = byte

    def r(self, addr, byte_count):
        return self._mem[addr: addr + byte_count]
