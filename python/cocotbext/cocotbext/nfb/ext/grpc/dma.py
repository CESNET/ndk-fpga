# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import queue
import logging
from threading import Event

import cocotbext.ofm.utils

import nfb.ext.protobuf.v1.dma_pb2 as dma_pb2
import nfb.ext.protobuf.v1.dma_pb2_grpc as dma_pb2_grpc


class DmaRequest():
    def __init__(self, rq):
        self.rq = rq
        self.event = Event()

    def set(self, data):
        self.rq.data = data
        self.event.set()

    def wait(self):
        self.event.wait()
        return self.rq.data


class DmaServicer(dma_pb2_grpc.DmaServicer):
    def __init__(self, ram):
        self._log = logging.getLogger(__name__)
        self._ram = ram
        self._bind = False
        self._req_queue = None

    def RqStream(self, request_iterator, context):
        if self._req_queue is not None:
            self._log.warning(f"Another context on Dma.RqStream is already active, ignoring current: {context.peer()}")
            return

        self._log.info(f"Using new Dma.RqStream context: {context.peer()}")

        self._bind = True
        self._req_queue = queue.Queue(10)
        self._ram.connect(self._req_queue)

        context.add_callback(self._logout)

        while self._bind:
            req = self._req_queue.get()
            if req is not None:
                yield req.rq
                resp = next(request_iterator)
                if req.rq.type == dma_pb2.DmaOperation.DMA_READ:
                    req.set(resp.data)
                else:
                    req.set(bytes())

        self._req_queue = None
        self._ram.close()
        self._log.info(f"Closing Dma.RqStream context: {context.peer()}")

    def _logout(self):
        self._bind = False
        if self._req_queue is not None:
            self._req_queue.put(None)

    def Logout(self, request_iterator, context):
        self._logout()


class RAM(cocotbext.ofm.utils.RAM):
    def __init__(self):
        self._rq = None
        self._log = logging.getLogger(__name__)

    def connect(self, request_queue):
        self._rq = request_queue

    def close(self):
        self._rq = None

    def w(self, addr, data):
        if self._rq is None:
            self._log.error(f"Dma client for RAM access not connected: write {len(data)}B to {addr:0x}")
            return

        resp = DmaRequest(dma_pb2.DmaRequest(type=dma_pb2.DmaOperation.DMA_WRITE, addr=addr, nbyte=len(data), data=bytes(data)))
        self._rq.put(resp)

    def r(self, addr, byte_count):
        if self._rq is None:
            self._log.error(f"Dma client for RAM access not connected: read {byte_count}B from {addr:0x}")
            return bytes(byte_count)

        resp = DmaRequest(dma_pb2.DmaRequest(type=dma_pb2.DmaOperation.DMA_READ, addr=addr, nbyte=byte_count, data=None))
        self._rq.put(resp)
        return resp.wait()
