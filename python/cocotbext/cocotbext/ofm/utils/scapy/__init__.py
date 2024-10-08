import sys
import builtins

# disable warnings from Scapy
__stderr = sys.stderr
sys.stderr = None
from scapy.all import TCP, Ether, IP, Raw, raw # noqa
sys.stderr = __stderr
del __stderr


def s2b(pkt):
    return bytes(raw(pkt))


def simple_tcp_bytes(len=64, src=None, dst=None):
    pkt = Ether() / IP(src=src, dst=dst) / TCP() / "GET /index.html HTTP/1.0 \n\n"
    pkt = pkt / Raw(" " * (len - builtins.len(pkt)))
    return s2b(pkt)
