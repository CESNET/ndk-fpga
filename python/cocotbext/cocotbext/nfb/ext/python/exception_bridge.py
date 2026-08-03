# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.

"""cocotb CancelledError policy for the libnfb Python exception bridge."""

from __future__ import annotations

import functools
import threading
from asyncio import CancelledError
from typing import Callable, TypeVar

import cocotb
from nfb.ext.python import ExceptionBridgeBase, get_exception_bridge
from nfb.ext.python.shim import set_exception_bridge

R = TypeVar("R")


class ExceptionBridge(ExceptionBridgeBase):
    """Stash CancelledError across libnfb C so the cocotb bridge can re-raise."""

    def __init__(self) -> None:
        self._tls = threading.local()

    def pending(self) -> bool:
        return getattr(self._tls, "exc", None) is not None

    def intercept(self, exc: BaseException) -> bool:
        if isinstance(exc, CancelledError):
            self._tls.exc = exc
            return True
        return False

    def raise_if_cancelled(self) -> None:
        exc = getattr(self._tls, "exc", None)
        if exc is not None:
            self._tls.exc = None
            raise exc

    def clear(self) -> None:
        self._tls.exc = None


def install_exception_bridge() -> ExceptionBridge:
    """Register a process-wide ExceptionBridge if none is set yet."""
    exc_bridge = get_exception_bridge()
    if exc_bridge is None:
        exc_bridge = ExceptionBridge()
        set_exception_bridge(exc_bridge)
    return exc_bridge


def bridge(func: Callable[..., R]) -> Callable[..., R]:
    """Drop-in for ``cocotb.task.bridge`` that re-raises a stashed CancelledError."""

    @functools.wraps(func)
    def guarded(*args, **kwargs):
        try:
            result = func(*args, **kwargs)
            br = get_exception_bridge()
            if br is not None:
                br.raise_if_cancelled()
            return result
        except BaseException:
            br = get_exception_bridge()
            if br is not None:
                br.clear()
            raise

    return cocotb.task.bridge(guarded)
