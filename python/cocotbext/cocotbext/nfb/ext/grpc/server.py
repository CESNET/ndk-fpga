# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import time
import logging
import socket

import grpc
import cocotb

from concurrent import futures
from threading import Thread

from .nfb import NfbServicer
from .dma import DmaServicer

import nfb.ext.protobuf.v1.nfb_pb2_grpc as nfb_pb_grpc
import nfb.ext.protobuf.v1.dma_pb2_grpc as dma_pb_grpc


class NfbDmaThreadedGrpcServer:
    def __init__(self, ram, dev, addr="127.0.0.1", port=50051):
        super().__init__()
        self._log = logging.getLogger(__name__)

        self._port = port

        self._nfb_reciver = dev if isinstance(dev, nfb_pb_grpc.NfbServicer) else NfbServicer(dev)
        self._dma_reciver = ram if isinstance(ram, dma_pb_grpc.DmaServicer) or ram is None else DmaServicer(ram)

        self._server = grpc.server(futures.ThreadPoolExecutor())
        self._server.add_insecure_port(f"{addr}:{port}")
        nfb_pb_grpc.add_NfbServicer_to_server(self._nfb_reciver, self._server)
        if self._dma_reciver:
            dma_pb_grpc.add_DmaServicer_to_server(self._dma_reciver, self._server)

        self._thread = Thread(target=self._run)
        self._thread_terminate = False

    def _run(self):
        self._server.start()

        if cocotb.regression_manager is not None:
            while not cocotb.regression_manager._tearing_down and not self._thread_terminate:
                time.sleep(0.1)

        if isinstance(self._dma_reciver, DmaServicer):
            self._dma_reciver._logout()
        if isinstance(self._nfb_reciver, NfbServicer):
            self._nfb_reciver.resp_force()
        self._server.stop(2.0)
        self._server.wait_for_termination()

    def path(self):
        addr = socket.gethostname()
        dma = "+dma_vas" if self._dma_reciver else ""
        return f"libnfb-ext-grpc.so:grpc{dma}:{addr}:{self._port}"

    def start(self):
        self._thread.start()
        self._log.info(f"gRPC server started, listening on {self._port}. Device string: {self.path()}")

    def close(self):
        self._thread_terminate = True

    def __enter__(self):
        self.start()

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()
