# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.

"""cocotb CancelledError policy for the libnfb Python exception bridge."""

from __future__ import annotations

import functools
import threading
from asyncio import CancelledError
from typing import Callable, Coroutine, ParamSpec, TypeVar

import cocotb
import cocotb.task
from cocotb._base_triggers import Trigger
from nfb.ext.python import ExceptionBridgeBase, get_exception_bridge
from nfb.ext.python.shim import set_exception_bridge

P = ParamSpec("P")
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


def bridge(func: Callable[P, R]) -> Callable[P, Coroutine[Trigger, None, R]]:
    """Drop-in for ``cocotb.task.bridge`` that re-raises a stashed CancelledError.

    Also refuses to even start *func* if the dispatching task is already flagged
    for cancellation, since dispatching it would just strand the bridge thread in
    ``event.wait()`` forever. Relies on the private ``_must_cancel`` flag, as
    there's no public API for this; skips the check if that attribute is ever
    removed/renamed upstream rather than fail outright.
    """

    @functools.wraps(func)
    def guarded(*args, **kwargs):
        try:
            task = cocotb.task.current_task()
        except RuntimeError:
            task = None
        if task is not None and getattr(task, "_must_cancel", False):
            raise CancelledError()

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
