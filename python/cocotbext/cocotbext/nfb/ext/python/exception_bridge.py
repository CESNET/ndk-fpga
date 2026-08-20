# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.

"""cocotb CancelledError policy for the libnfb Python exception bridge."""

from __future__ import annotations

import functools
import logging
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

logger = logging.getLogger(__name__)


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


def _pending_threads() -> list:
    try:
        from cocotb._bridge import pending_threads

        return pending_threads
    except ImportError:
        # For the cocotb <2.1
        return cocotb._scheduler_inst._pending_threads  # type: ignore[attr-defined]


def _dispatch_daemonic(func: Callable[..., R], *args, **kwargs) -> Coroutine[Trigger, None, R]:
    """Locally-owned copy of cocotb's internal executor-thread dispatch, with ``daemon=True``
    added to the executor thread it creates.

    Upstream's thread isn't daemonic, so if its Task never resumes (e.g. the
    simulator stopped scheduling after a fatal failure elsewhere while this call was
    in flight), the thread blocks in ``event.wait()`` forever and keeps the process
    alive. Scoped to this module's ``bridge()`` only, rather than monkey-patching
    ``cocotb.Scheduler`` process-wide. Falls back to plain ``cocotb.task.bridge()`` if
    the private internals it copies are ever missing/renamed upstream.
    """
    try:
        from cocotb._bridge import external_waiter
        from cocotb._outcomes import capture

        pending = _pending_threads()
        waiter = external_waiter()

        def execute_external() -> None:
            waiter._outcome = capture(func, *args, **kwargs)
            waiter.thread_done()

        async def wrapper() -> R:
            thread = threading.Thread(
                group=None,
                target=execute_external,
                name=func.__qualname__ + "_thread",
                daemon=True,
            )
            waiter.thread = thread
            pending.append(waiter)
            await waiter.event.wait()
            return waiter.result  # raises if there was an exception

        return wrapper()
    except (ImportError, AttributeError):
        logger.warning(
            "cocotb internals used to make the bridge thread daemonic are unavailable "
            "(cocotb version mismatch?); falling back to cocotb.task.bridge(), whose "
            "thread can strand the process if the task never resumes.",
            exc_info=True,
        )
        return cocotb.task.bridge(func)(*args, **kwargs)


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

    def wrapper(*args, **kwargs) -> Coroutine[Trigger, None, R]:
        return _dispatch_daemonic(guarded, *args, **kwargs)

    # Not @functools.wraps(guarded): its typeshed stub would make type checkers see
    # wrapper() as returning R directly instead of a Coroutine (same pitfall as
    # bridge_safe_asynccontextmanager in cocotbext.ofm.utils.bridge_safe). Copy
    # the introspection metadata by hand instead.
    wrapper.__name__ = func.__name__
    wrapper.__qualname__ = func.__qualname__
    wrapper.__doc__ = func.__doc__
    setattr(wrapper, "__wrapped__", func)
    return wrapper
