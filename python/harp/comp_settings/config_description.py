# File: config_description.py
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
# Copyright: (C) 2024 CESNET, z.s.p.o.

"""
Pydantic classes describing structure of NdkXBuild TOML config file.
"""

from pydantic import BaseModel, Field, model_validator, AfterValidator
from typing import Annotated, Union, List, Optional, Dict
from typing_extensions import Self
from enum import Enum


def check_range(
    v: str,
):
    ldict = {}
    cmd = f"rng = {v}"
    exec(cmd, globals(), ldict)
    rng = ldict["rng"]

    assert isinstance(rng, range), "String is not a valid range!"
    return v


TOMLStringRange = Annotated[str, AfterValidator(check_range)]
TOMLDirectValue = Union[int, str, bool, List[Union[int, str, bool]]]


class TOMLGenericSettingType(str, Enum):
    CONSTANT = "const"
    LIST = "list"
    GENERATOR = "gen"


def _execute_inline_code(
    code_str,
):
    ldict = {}
    try:
        cmd = f"var = {code_str}"
        exec(cmd, globals(), ldict)
    except BaseException:
        raise ValueError(f"Failed to execute code: \"{cmd}\"")
    return ldict["var"]


class TOMLExcludeWhen(BaseModel):
    generic: str
    value: str

    @model_validator(mode="after")
    def validate_lambda(self) -> Self:
        lmbda = _execute_inline_code(self.value)

        if not callable(lmbda):
            raise ValueError("Generator value must be a function")

        if not isinstance(lmbda(42), bool):
            raise ValueError("Generator value (function) must return boolean value")

        self.value = lmbda
        return self


class TOMLGenericSetting(BaseModel):
    type: Annotated[TOMLGenericSettingType, Field(default=TOMLGenericSettingType.CONSTANT)]
    value: TOMLDirectValue
    range: Optional[str] = Field(None)
    exclude_when: Optional[TOMLExcludeWhen] = Field(None)

    @model_validator(mode="after")
    def validate_type(self) -> Self:
        if self.type == TOMLGenericSettingType.CONSTANT:
            if self.range is not None:
                raise ValueError(
                    "Range is specified for generic setting of type constant or list")
        elif self.type == TOMLGenericSettingType.LIST:
            if self.range is not None:
                raise ValueError(
                    "Range is specified for generic setting of type constant or list")

            if not isinstance(self.value, list):
                raise ValueError("Generic of type list must be of type list (wait what?)")
        elif self.type == TOMLGenericSettingType.GENERATOR:
            if not isinstance(self.value, str) or self.range is None:
                raise ValueError(
                    "Generator value must be a string and range must be specified")

            # Lamda function validation
            lmbda = _execute_inline_code(self.value)

            if not callable(lmbda):
                raise ValueError("Generator value must be a function")

            if not isinstance(lmbda(42), int):
                raise ValueError("Generator value (function) must return an integer")

            self.value = lmbda

            # Range validation
            rng = _execute_inline_code(self.range)

            try:
                _ = (e for e in rng)
            except TypeError:
                raise ValueError("Range of generator must be valid python iterable!")

            self.range = rng

        return self


TOMLUnionSetting = Union[TOMLGenericSetting, TOMLDirectValue]


class TOMLCombination(BaseModel):
    name: str
    description: Optional[str] = Field(default=None)
    settings: List[Union[str, List[str]]]
    tests: Optional[List[str]] = Field(default=None)


class TOMLVerRndSetting(BaseModel):
    tests_allowed: List[str]
    amount: float


class TOMLVerSettings(BaseModel):
    tests: List[str]


class TOMLVer(BaseModel):
    settings: TOMLVerSettings
    rnd: Optional[TOMLVerRndSetting] = Field(None)
    combinations: List[TOMLCombination]


class TOMLSynthSettings(BaseModel):
    combinations: List[TOMLCombination]


class TOMLBuildSystem(BaseModel):
    synth_folder: str = Field(default="synth")
    ver_folder: str = Field(default="uvm")
    ver_fdo_file: str = Field(default="top_level.fdo")


class TOMLGenerics(BaseModel):
    asserts: List[str]


class NdkXBuildTOML(BaseModel):
    settings: Dict[str, Dict[str, TOMLUnionSetting]]
    ver_settings: Optional[Dict[str, Dict[str, TOMLUnionSetting]]] = Field(default=None)
    synth_settings: Optional[Dict[str, Dict[str, TOMLUnionSetting]]] = Field(default=None)
    ver: TOMLVer
    synth: TOMLSynthSettings
    build_system: Optional[TOMLBuildSystem] = Field(default=TOMLBuildSystem())
    generics: Optional[TOMLGenerics] = Field(default=None)
