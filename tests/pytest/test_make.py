#!/usr/bin/python3
import os
import re
import pytest


def pytest_generate_tests(metafunc):
    funcarglist = metafunc.cls.params[metafunc.function.__name__]
    argnames = sorted(funcarglist[0])
    metafunc.parametrize(
        argnames, [[funcargs[name] for name in argnames] for funcargs in funcarglist]
    )


class TestClass:
    # a map specifying multiple argument sets for a test method
    basepath = '../../'
    makefiles = os.popen(f'cd {basepath}; grep --include Makefile "all: comp" -Rl comp/*').read().split("\n")
    params = {
        "test_make": [dict(makefile=x, synth='quartus') for x in makefiles if x] +
                     [dict(makefile=x, synth='vivado') for x in makefiles if x],
    }

    def test_make(self, makefile, synth):
        makepath = TestClass.basepath + makefile
        ret = os.system(f'make SYNTH={synth} -C $(dirname {makepath}) > {makepath}_{synth}_makerun.log 2> {makepath}_{synth}_makerun_err.log')
        if ret:
            error = self.parse_error_log(makefile, synth)
            pytest.fail(error)

    def parse_error_log(self, makefile, synth):
        makepath = TestClass.basepath + makefile

        err_pattern = 'Error' if synth == 'quartus' else 'ERROR'
        error = os.popen(f'cat {makepath}_{synth}_makerun.log | grep {err_pattern} | head -n1').read()

        # Try to get error from second log
        if not error:
            error = os.popen(f'cat {makepath}_{synth}_makerun_err.log | grep ERROR | head -n1').read()

        ue = re.match('.*instantiates undefined entity "(.*)".*', error)
        if ue:
            pytest.skip(f'Undefined entity: {ue.groups()[0]}')

        if re.match('.*design library "(.*)" does not contain primary unit "vcomponents".*', error):
            pytest.skip(error)

        if re.match('.*crc32_ethernet.*doesn\'t exists!.*', error):
            pytest.skip('crc32 is not in this repository')
