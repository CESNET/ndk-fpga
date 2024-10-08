from cocotbext.ofm.mi.drivers import MIMasterDriver, MISlaveDriver


class MIMasterDriverTB(MIMasterDriver):
    """Driver derived from MIMasterDriver intended for MI Pipe Test."""

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

    async def _send_thread(self) -> None:
        """Function for generating a thread for testing with cocotb testbench."""

        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                if transaction[0] == "wr":
                    await self.write(int.from_bytes(transaction[1][0:4], 'little'), transaction[1], sync=True)
                elif transaction[0] == "rd":
                    await self.read(int.from_bytes(transaction[1][0:4], 'little'), len(transaction[1]), sync=True)
                else:
                    raise RuntimeError("Invalid testcase")

                if event:
                    event.set()
                if callback:
                    callback(transaction)


class MISlaveDriverTB(MISlaveDriver):
    """Driver derived from MISlaveDriver intended for MI Pipe Test."""

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

    async def _send_thread(self) -> None:
        """Function for generating a thread for testing with cocotb testbench."""

        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                if transaction[0] == "wr":
                    pass

                elif transaction[0] == "rd":
                    await self.write(transaction[1], sync=True)

                else:
                    raise RuntimeError("Invalid testcase")

                if event:
                    event.set()
                if callback:
                    callback(transaction)
