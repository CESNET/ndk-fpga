# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import asyncio
import atexit
import logging
import threading

logger = logging.getLogger(__name__)

try:
    import pyshark as _pyshark
    from pyshark.capture.inmem_capture import InMemCapture as _InMemCapture

    class _OfflineInMemCapture(_InMemCapture):
        """InMemCapture normally asks tshark to do a live capture ('-i -'),
        which spawns dumpcap and requires cap_net_raw/cap_net_admin. Force
        tshark into offline read mode ('-r -') instead: it parses the exact
        same pcap stream fed over stdin, but never touches dumpcap, so it
        also works without raw-capture privileges."""

        def get_parameters(self, packet_count=None):
            params = super(_InMemCapture, self).get_parameters(packet_count=packet_count)
            params += ['-r', '-']
            return params

except ImportError as e:
    logger.debug(f"pyshark not available, packet parsing disabled: {e}")
    _pyshark = None

pyshark_capture = None
pyshark_loop = None
pyshark_thread = None

# Seconds to wait for tshark to parse a single packet
PYSHARK_TIMEOUT = 20


def _pyshark_thread_main(ready):
    """Runs a dedicated event loop for pyshark, since the cocotb/simulator
    thread has no asyncio event loop of its own to drive one."""
    global pyshark_capture, pyshark_loop

    pyshark_loop = asyncio.new_event_loop()
    asyncio.set_event_loop(pyshark_loop)
    pyshark_capture = _OfflineInMemCapture(eventloop=pyshark_loop)
    ready.set()
    pyshark_loop.run_forever()
    pyshark_loop.close()


def pyshark_available() -> bool:
    """True while pyshark_parse() can decode packets: pyshark is installed
    and no parse has failed yet."""
    return _pyshark is not None


def pyshark_start():
    """Starts the pyshark worker thread and its event loop ahead of time, so
    the first real pyshark_parse() call isn't slowed down by it. The tshark
    subprocess itself is still spawned lazily, on the first parsed packet."""
    global pyshark_thread

    if _pyshark is None or pyshark_loop is not None:
        return

    ready = threading.Event()
    pyshark_thread = threading.Thread(target=_pyshark_thread_main, args=(ready,), daemon=True)
    pyshark_thread.start()
    ready.wait()
    atexit.register(pyshark_stop)


def pyshark_stop(timeout: float = 5):
    """Terminates the tshark subprocess and the worker thread. Called
    automatically at interpreter exit; a later pyshark_parse() starts them
    again."""
    global pyshark_capture, pyshark_loop, pyshark_thread

    if pyshark_loop is None:
        return

    future = asyncio.run_coroutine_threadsafe(pyshark_capture.close_async(), pyshark_loop)
    try:
        future.result(timeout)
    except Exception as e:
        logger.warning(f"pyshark: closing tshark failed: {e!r}")
    pyshark_loop.call_soon_threadsafe(pyshark_loop.stop)
    pyshark_thread.join(timeout)

    pyshark_capture = None
    pyshark_loop = None
    pyshark_thread = None


def pyshark_parse(pkt: bytes, timeout: float = PYSHARK_TIMEOUT):
    """Returns the packet decoded by tshark, or None when pyshark is not
    available. Any failure (tshark missing, crashed or stuck for longer than
    $timeout seconds) is logged and disables further parsing."""
    global _pyshark

    if _pyshark is None:
        return

    pyshark_start()

    # The inner timeout makes pyshark close a stuck tshark, the outer one
    # also covers a tshark that does not even start.
    future = asyncio.run_coroutine_threadsafe(pyshark_capture.parse_packets_async([pkt], timeout=timeout), pyshark_loop)
    try:
        p_pkts = future.result(timeout + 5)
    except Exception as e:
        future.cancel()
        logger.error(f"pyshark: parsing failed, packet parsing disabled: {e!r}")
        pyshark_stop()
        _pyshark = None
        return

    if not p_pkts:
        return
    return p_pkts[0]
