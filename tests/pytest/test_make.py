# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>

import os
import re
import pytest


def pytest_generate_tests(metafunc):
    funcarglist = metafunc.cls.params[metafunc.function.__name__]
    argnames = sorted(funcarglist[0])
    metafunc.parametrize(
        argnames, [[funcargs[name] for name in argnames] for funcargs in funcarglist]
    )


#basepath = '../../'
basepath = './'


def get_makefiles():
    return os.popen(f'cd {basepath}; grep --include Makefile "all: comp" -Rl ./* | grep "synth/Makefile"').read().split("\n")


class TestClass:
    # a map specifying multiple argument sets for a test method
    tools = [
        'quartus',
        'vivado',
        'nvc',
    ]
    params = {
        "test_make": [dict(makefile=mf, tool=tool) for tool in tools for mf in get_makefiles() if mf]
    }

    def test_make(self, tool, makefile):
        makepath = basepath + makefile
        synth_params = {
            'quartus': 'SYNTH=quartus',
            'vivado': 'SYNTH=vivado',
            'nvc': 'TARGET=nvc',
        }
        synth = synth_params[tool]

        ret = os.system(f'make {synth} -C $(dirname {makepath}) > {makepath}-{tool}-makerun.log 2> {makepath}-{tool}-makerun_err.log')
        if ret:
            error = self.parse_error_log(makefile, makepath, tool, synth)
            pytest.fail(error, False)

    def parse_error_log(self, makefile, makepath, tool, synth):
        makepath = basepath + makefile

        error = os.popen(f'cat {makepath}-{tool}-makerun.log | grep -i error | head -n1').read()

        # Try to get error from second log
        if not error:
            err_pattern = 'Fatal|Error' if tool == 'nvc' else 'ERROR'
            error = os.popen(f'cat {makepath}-{tool}-makerun_err.log | grep -i -E "{err_pattern}" | head -n1').read()
            if not error:
                error = os.popen(f'cat {makepath}-{tool}-makerun_err.log | head -n1').read()

        fail = None
        ue = re.match('.*instantiates undefined entity "(.*)".*', error)
        if ue:
            pytest.skip(f'Undefined entity: {ue.groups()[0]}')

        if re.match('.*design library "(.*)" does not contain primary unit "vcomponents".*', error):
            pytest.skip(error)
        if re.match("Specified part could not be found.", error):
            pytest.skip(error)
        if re.match("Part name (.*)is invalid.", error):
            pytest.skip(error)

        if re.match('.*crc32_ethernet.*doesn\'t exists!.*', error):
            pytest.skip('crc32 is not in this repository')

        if re.match('.*build/Makefile: No such file or directory', error):
            fail = f"bad path in Makefile: {makepath}"
        else:
            fail = error
        return fail
