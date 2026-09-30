# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.

"""Async context manager whose cleanup may survive a bridge() call safely on cancel.

Use only when a context manager's `finally:` makes a blocking bridge() call (ours
or cocotb.task.bridge()) - such a call can strand its OS thread forever if resumed
after the scheduler stops servicing tasks. Everything else: use plain
contextlib.asynccontextmanager, it's simpler and runs cleanup synchronously.
"""

import asyncio
import logging
from contextlib import _AsyncGeneratorContextManager
from typing import AsyncGenerator, Callable, TypeVar

import cocotb

T = TypeVar("T")

logger = logging.getLogger(__name__)

# Kept referenced so GC doesn't drive one more step of an abandoned generator -
# that step could re-dispatch the very bridge() call we just detached from.
_abandoned_generators = []

# Tags an exception instance once we've logged it, so a single exception unwinding
# through several nested bridge-safe managers (e.g. the three in `async with (uem_inst(us),
# uem_inst(ur), finalize_stats(nfb))`) is only reported once, not once per manager.
_LOGGED_ATTR = "_bridge_safe_logged"


class _BridgeSafeAsyncGeneratorContextManager(_AsyncGeneratorContextManager[T]):
    async def __aexit__(self, typ, value, traceback):
        if typ is None:
            return await super().__aexit__(typ, value, traceback)

        if issubclass(typ, asyncio.CancelledError):
            if value is not None and not getattr(value, _LOGGED_ATTR, False):
                try:
                    setattr(value, _LOGGED_ATTR, True)
                except AttributeError:
                    pass  # some BaseExceptions don't allow arbitrary attributes; skip dedup, not logging
        _abandoned_generators.append(self.gen)
        cocotb.start_soon(self._best_effort_close())
        return False

    async def _best_effort_close(self):
        try:
            await self.gen.aclose()
        except asyncio.CancelledError:
            raise
        except BaseException:
            logger.debug("best-effort cleanup after cancellation didn't complete", exc_info=True)


def bridge_safe_asynccontextmanager(
    func: Callable[..., AsyncGenerator[T, None]],
) -> Callable[..., _BridgeSafeAsyncGeneratorContextManager[T]]:
    """Like ``contextlib.asynccontextmanager``, but on cancellation detaches instead
    of resuming the generator - safe if its ``finally:`` calls bridge().

    Behaves exactly like the standard decorator on any non-cancellation exit. Only
    guards ``__aexit__``; a bridge() call already in flight during ``__aenter__``
    can't be rescued the same way.
    """
    def helper(*args, **kwds) -> _BridgeSafeAsyncGeneratorContextManager[T]:
        return _BridgeSafeAsyncGeneratorContextManager(func, args, kwds)

    # Not @functools.wraps(func): its typeshed stub would undo the precise typing
    # above. Copy introspection metadata by hand instead.
    helper.__name__ = func.__name__
    helper.__qualname__ = func.__qualname__
    helper.__doc__ = func.__doc__
    setattr(helper, "__wrapped__", func)
    return helper
