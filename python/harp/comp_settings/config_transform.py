# File: config_transform.py
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
# Copyright: (C) 2024 CESNET, z.s.p.o.

"""
Classes and functions, which assist in generating combinations
of entity generics settings.
"""

from .config_description import (
    TOMLUnionSetting,
    TOMLGenericSetting,
    TOMLGenericSettingType,
    TOMLDirectValue,
    NdkXBuildTOML,
    TOMLCombination
)
from typing import Dict, List, Optional, Tuple
import pandas as pd
import logging
import re

_global_logger = logging.getLogger("NdkXBuild(ConfigTransform)")


def cartesian_product(dfs: List[pd.DataFrame]) -> pd.DataFrame:
    """
    Perform a cartesian product on a list of DataFrames.

    Parameters:
    *dfs : Tuple[pd.DataFrame]
        The DataFrames to perform the cartesian product on.

    Returns:
    pd.DataFrame
        The resulting DataFrame after performing the cartesian product.
    """

    if len(dfs) == 1:
        r = dfs[0].copy(True)
        return r
    elif len(dfs) == 0:
        raise ValueError("Can't merge zero data frames!")

    # Check for unique column names across all DataFrames
    all_columns = set()
    for df in dfs:
        columns = set(df.columns)
        if not columns.isdisjoint(all_columns):
            raise ValueError("All DataFrames must have unique column names")
        all_columns.update(columns)

    # Initialize the result with the first DataFrame
    result = dfs[0].copy(True)
    result["_key"] = 1

    for df in dfs[1:]:
        # Add a key column for the merge
        df["_key"] = 1
        # Perform the cross join and drop the key column
        result = pd.merge(result, df, on='_key')

    result = result.drop(["_key"], axis=1)

    return result


class NdkXBuildConfig:
    def __init__(
        self,
        toml_conf: NdkXBuildTOML,
    ):
        # keys - setting name, values - pandas dataframes of all combinations
        self.default_generics = pd.DataFrame.from_dict(
            {k: [v] for k, v in toml_conf.settings["default"].items()})
        self.settings = {
            k: NdkXBuildSetting.get_setting_values(
                v,
                self.default_generics) for k,
            v in toml_conf.settings.items()}
        self.ver_settings = {
            k: NdkXBuildSetting.get_setting_values(
                v,
                self.default_generics) for k,
            v in toml_conf.ver_settings.items()} if toml_conf.ver_settings else None
        self.synth_settings = {
            k: NdkXBuildSetting.get_setting_values(
                v,
                self.default_generics) for k,
            v in toml_conf.synth_settings.items()} if toml_conf.synth_settings else None
        self.ver_combinations = [
            NdkXBuildCombination(
                comb,
                self.settings,
                self.ver_settings,
                self.default_generics) for comb in toml_conf.ver.combinations]
        self.synth_combinations = [
            NdkXBuildCombination(
                comb,
                self.settings,
                self.ver_settings,
                self.default_generics) for comb in toml_conf.synth.combinations]

        if toml_conf.generics:
            self.assert_filter(toml_conf.generics.asserts)

    def assert_filter(
        self,
        asserts: List[str],
    ):
        for comb in self.ver_combinations:
            for a in asserts:
                ares = comb.generics_df.eval(a)
                comb.generics_df = comb.generics_df[ares]

    def debug_print(self):
        for comb in self.ver_combinations:
            print(comb.generics_df)

        for comb in self.synth_combinations:
            print(comb.generics_df)


def transform_list(
    input_list,
):
    prefix = []
    to_generate = []

    for el in input_list:
        if isinstance(el, str):
            prefix.append(el)
        else:
            to_generate.append(el)

    if len(prefix) == 0:
        raise ValueError(
            "Prefix must not be empty! If you wish to have no common combination, use \"\".")

    def remove_empty_strings(nested_list):
        return [[item for item in inner_list if item != ""]
                for inner_list in nested_list]

    rwip = [prefix]
    final_result = []

    for bi in to_generate:
        result = [sublist_a + [elem_b] for sublist_a in rwip for elem_b in bi]
        final_result.extend(result)
        rwip.extend(result)
        rwip = remove_empty_strings(result)
        rwip = [list(x) for x in set(tuple(x) for x in rwip) if x]

    return remove_empty_strings(rwip)


class NdkXBuildCombination:
    def __init__(
        self,
        toml_comb: TOMLCombination,
        settings: Dict[str, pd.DataFrame],
        additional_settings: Dict[str, pd.DataFrame],
        defaults: pd.DataFrame,
    ) -> None:

        _global_logger.debug(f"Generating combination {toml_comb.name}")
        self.generics_df = self.get_combination_generics(
            toml_comb.settings, settings, additional_settings, defaults)
        self.fill_defaults(self.generics_df, defaults)
        self.name = toml_comb.name
        self.description = toml_comb.description
        self.tests = toml_comb.tests

    @classmethod
    def fill_defaults(
        cls,
        gen_df: pd.DataFrame,
        defaults: pd.DataFrame,
    ):
        for dcol in defaults.columns:
            if dcol not in gen_df.columns:
                gen_df[dcol] = defaults[dcol][0]

    @classmethod
    def _search_setting(
        cls,
        setting_name: str,
        settings: Dict[str, pd.DataFrame],
        ver_settings: Optional[Dict[str, pd.DataFrame]],
    ):
        if setting_name in settings:
            return settings[setting_name]
        elif ver_settings is not None and setting_name in ver_settings:
            return ver_settings[setting_name]
        else:
            raise KeyError(
                f"Setting '{setting_name}' not found in settings or ver_settings.")

    @classmethod
    def _get_range(
        cls,
        comb_str: str,
    ) -> Tuple[str, Optional[int], Optional[int]]:
        """Parses range from combination name specification."""

        pattern = r'^(.*?)(\[(\d+)(:(\d+))?\])?$'

        # Use re.match to apply the pattern
        match = re.match(pattern, comb_str)

        if match:
            left_part = match.group(1)
            start_number = match.group(3)
            end_number = match.group(5)

            # Check if indices are valid
            if start_number is None:
                return left_part, None, None
            elif start_number is not None and end_number is None:
                return left_part, int(start_number), int(start_number) + 1
            elif start_number is not None and end_number is not None:
                return left_part, int(start_number), int(end_number)
            else:
                raise ValueError(f"Invalid combination format \"{comb_str}\"!")
        else:
            # Invalid format if the pattern does not match
            raise ValueError(f"Invalid combination format \"{comb_str}\"!")

    @classmethod
    def _get_comb_ranges(
        cls,
        partial_combinations: List[List[str]]
    ) -> List[List[Tuple[str, Optional[int], Optional[int]]]]:
        """Parses partial combination slices."""

        return [[cls._get_range(key) for key in setlist]
                for setlist in partial_combinations]

    @classmethod
    def get_combination_generics(
        cls,
        setting_list: List[str],
        settings: Dict[str, pd.DataFrame],
        ver_settings: Optional[Dict[str, pd.DataFrame]],
        defaults: pd.DataFrame,
    ):
        """Transforms combination into pandas dataframe containing all possible
        generic settings."""

        settings_to_apply = [x for x in setting_list]
        partial_combinations = transform_list(settings_to_apply)
        partial_combinations = cls._get_comb_ranges(partial_combinations)

        partial_comb_dfs = list()
        # Iterate through the setting list and check both dictionaries for the
        # keys
        for setlist in partial_combinations:
            partial_comb = []
            for key, _, _ in setlist:
                partial_comb.append(
                    NdkXBuildCombination._search_setting(
                        key, settings, ver_settings).copy(True))

            partial_comb_dfs.append(partial_comb)

        # Filter out unwanted rows in dfs
        filtered_dfs = list()
        for i, setlist in enumerate(partial_comb_dfs):
            partial_list = []
            for df_i, df in enumerate(setlist):
                _, start_ind, end_ind = partial_combinations[i][df_i]
                if start_ind is None:
                    partial_list.append(df)
                else:
                    partial_list.append(df.iloc[start_ind:end_ind])
            filtered_dfs.append(partial_list)

        partial_combinations = [cartesian_product(x) for x in filtered_dfs]
        for x in partial_combinations:
            cls.fill_defaults(x, defaults)

        return pd.concat(partial_combinations,
                         ignore_index=True).drop_duplicates()


class NdkXBuildSetting:
    @classmethod
    def check_generic_presence(
        cls,
        generics: List[str],
        defaults: List[str],
    ):
        for gen_name in generics:
            # Skip type - fake generic
            if gen_name == "type":
                continue
            if gen_name not in defaults:
                raise ValueError(
                    f"Generic {gen_name} not in default settings!")

    @classmethod
    def get_setting_values(
        cls,
        generics: Dict[str, TOMLUnionSetting],
        defaults: Dict[str, TOMLDirectValue],
    ) -> pd.DataFrame:
        NdkXBuildSetting.check_generic_presence(
            generics.keys(), defaults.keys())
        # Generate generic values
        if "type" in generics.keys():
            if generics["type"] == "list":
                generics.pop("type")
                return pd.DataFrame.from_dict(generics)
            else:
                raise ValueError("Unknown type of setting!")
        else:
            generics_values = [
                NdkXBuildGeneric.generate_values(
                    gname,
                    values) for gname,
                values in generics.items()]
            # Create cartesian product of values
            return cartesian_product(generics_values)


class NdkXBuildGeneric:
    @classmethod
    def generate_values(
        cls,
        name: str,
        setting: TOMLUnionSetting
    ) -> pd.DataFrame:
        values = None

        if isinstance(setting, TOMLGenericSetting):
            # Generate possible values
            if setting.type == TOMLGenericSettingType.CONSTANT:
                values = [setting.value]
            elif setting.type == TOMLGenericSettingType.LIST:
                values = setting.value
            elif setting.type == TOMLGenericSettingType.GENERATOR:
                values = [setting.value(x) for x in setting.range]
            else:
                raise ValueError(
                    f"Incorrect value of generic type, got {setting.type}")
        else:
            # Constant
            values = [setting]

        return pd.DataFrame(values, columns=[name])
