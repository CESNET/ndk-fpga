# gitlab_runner.py: Verible GitLab stage runner script. To waive linter violations, see this: https://github.com/chipsalliance/verible/tree/master/verible/verilog/tools/lint#waiving-lint-violations-lint-waiver
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

import argparse
import os
import gitlab
import subprocess
import sys


class Server:
    '''
    Represents the GitLab server.
    '''

    def __init__(self, api_token_name: str = 'VERIBLE_API_TOKEN'):
        # Get environment variables
        private_token = os.environ.get(api_token_name)
        server_url = os.environ.get('CI_SERVER_URL')
        project_id = os.environ.get('CI_PROJECT_ID')
        merge_request_id = os.environ.get('CI_MERGE_REQUEST_IID')
        assert private_token, 'The private token environment variable is not set.'
        assert server_url, 'Environment variable `CI_SERVER_URL` is not set.'
        assert project_id, 'Environment variable `CI_PROJECT_ID` is not set.'
        assert merge_request_id, 'Environment variable `CI_MERGE_REQUEST_IID` is not set.'

        # Get GitLab API handles
        self.gl = gitlab.Gitlab(url=server_url, private_token=private_token)
        self.project = self.gl.projects.get(id=project_id)
        self.merge_request = self.project.mergerequests.get(id=merge_request_id)

    def get_modified_source_paths(self, extensions: tuple[str, ...] = ('.sv',)) -> list[str]:
        '''
        Returns paths to modified source files with specific extensions.
        '''

        paths = []
        changes = self.merge_request.changes()['changes']
        for change in changes:
            path = change['new_path']
            if path.endswith(extensions):
                paths.append(path)
        return paths


class Linter:
    '''
    Represents the Verible linter.
    '''

    def __init__(self, rules_config_path: str = os.path.join(os.path.dirname(__file__), 'rules')):
        self.rules_config_path = rules_config_path

    def get_linter_output(self, path: str) -> str | None:
        '''
        Runs the Verible linter and returns its output, if any.
        '''

        output = subprocess.run(args=['verible-verilog-lint', '--ruleset=none', f'--rules_config={self.rules_config_path}', path], capture_output=True)
        if output.returncode != 0:
            return output.stderr.decode()
        else:
            return None


def main():
    server = Server()
    linter = Linter()

    trigger = False
    paths = server.get_modified_source_paths()
    for path in paths:
        output = linter.get_linter_output(path=path)
        if output:
            trigger = True
            print(('-' * 150) + f'\n{output}')

    if trigger:
        print('-' * 150)
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == '__main__':
    argparse.ArgumentParser(
        description='Verible GitLab stage runner script. To waive linter violations, see this:\n'
                    'https://github.com/chipsalliance/verible/tree/master/verible/verilog/tools/lint'
                    '#waiving-lint-violations-lint-waiver.',
        formatter_class=argparse.RawTextHelpFormatter
    ).parse_args()
    main()
