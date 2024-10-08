# File: build_adapter.py
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
# Copyright: (C) 2024 CESNET, z.s.p.o.

"""
Description: Abstract class describing behaviour of generic build adapter.
"""

from abc import ABC, abstractmethod
from comp_settings.config_transform import NdkXBuildConfig


class NdkXBuildAdapter(ABC):
    @abstractmethod
    def run_set_generics(
        self,
        comb_id: int,
    ):
        pass

    @abstractmethod
    def run_tool(self):
        pass

    @abstractmethod
    def run_report(self) -> bool:
        pass


class NdkXBuildRunner(ABC):
    def __init__(
        self,
        config: NdkXBuildConfig,
    ) -> None:
        self.config: NdkXBuildConfig = config

    @abstractmethod
    def run(self):
        pass

    @abstractmethod
    def report(self):
        pass
