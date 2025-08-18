# coverage_reporter.py: Generates a Nested Data Reporting compatible JSON coverage report (see https://plugins.jenkins.io/nested-data-reporting/) based on a UCDB coverage input file
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

import argparse
import os
import subprocess
import re
import json


def get_total_coverage_from_report(report: str) -> int | None:
    search_result = re.search(pattern=r'Total coverage \(filtered view\): (\d+)%', string=report)
    if search_result:
        return int(search_result.group(1))
    else:
        return None


def get_code_coverage(input_filepath: str) -> int:
    report = subprocess.run(args=['vcover', 'report', '-summary', '-precision', '0', '-codeAll', '-instance=/testbench.', input_filepath], capture_output=True)
    assert report.returncode == 0, 'An error occurred while executing the `vcover` command.'
    cove_coverage = get_total_coverage_from_report(report=report.stdout.decode())
    assert cove_coverage, 'An error occurred while parsing the code coverage value from the report.'
    return cove_coverage


def get_functional_coverage(input_filepath: str) -> int | None:
    report = subprocess.run(args=['vcover', 'report', '-summary', '-precision', '0', '-cvg', input_filepath], capture_output=True)
    assert report.returncode == 0, 'An error occurred while executing the `vcover` command.'
    return get_total_coverage_from_report(report=report.stdout.decode())


def get_assertion_coverage(input_filepath: str) -> int | None:
    report = subprocess.run(args=['vcover', 'report', '-summary', '-precision', '0', '-assert', input_filepath], capture_output=True)
    assert report.returncode == 0, 'An error occurred while executing the `vcover` command.'
    return get_total_coverage_from_report(report=report.stdout.decode())


def get_json_string(component_name: str, code_coverage: int, functional_coverage: int | None, assertion_coverage: int | None) -> str:
    if not functional_coverage:
        functional_coverage = 0
    if not assertion_coverage:
        assertion_coverage = 0

    to_json = {
        'id': 'coverage_report',
        'items': [
            {
                'id': component_name,
                'name': component_name,
                'result': {
                    'Code': code_coverage,
                    'Functional': functional_coverage,
                    'Assertion': assertion_coverage
                }
            }
        ]
    }

    return json.dumps(obj=to_json, indent=2)


def main(input_filepath: str, output_filepath: str, component_name: str):
    assert os.path.isfile(path=input_filepath), 'The input UCDB file does not exist.'

    code_coverage = get_code_coverage(input_filepath=input_filepath)
    functional_coverage = get_functional_coverage(input_filepath=input_filepath)
    assertion_coverage = get_assertion_coverage(input_filepath=input_filepath)
    json_string = get_json_string(component_name=component_name, code_coverage=code_coverage, functional_coverage=functional_coverage, assertion_coverage=assertion_coverage)

    if output_filepath:
        with open(file=output_filepath, mode='w') as output_file:
            output_file.write(json_string)
    else:
        print(json_string)


if __name__ == '__main__':
    argument_parser = argparse.ArgumentParser()
    argument_parser.add_argument('-i', '--input', type=str, help='Path to the input UCDB file.', required=True)
    argument_parser.add_argument('-n', '--name', type=str, help='The component name.', required=True)
    argument_parser.add_argument('-o', '--output', type=str, help='Path to the output JSON file for the coverage report. If not specified, it will be written to standard output.', default=None)
    arguments = argument_parser.parse_args()

    main(input_filepath=arguments.input, output_filepath=arguments.output, component_name=arguments.name)
