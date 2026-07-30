#!/usr/bin/env python3

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import os
import re
import shutil
import subprocess
import argparse
from datetime import datetime


def generate_test_template(
    path: str = os.getcwd(),
    entity: str | None = None,
    ndk_fpga_path: str | None = None,
    name: str | None = None,
    email: str | None = None,
    company: str = "CESNET z. s. p. o.",
    license: str = "BSD-3-Clause",
):
    """
    Generates a generic cocotb test template.

    Args:
        path: The location where the test folder will be generated.
        entity: The name of the VHDL entity for which the test will be generated. If not specified, the entity is found automatically.
                If multiple entities are found, the user will be prompted to choose one.
        ndk_fpga_path: The path to the parent folder of ndk-fpga. If not specified, it is found automatically.
        name: The name of the author displayed in headers. Collected from Git if not specified.
        email: The email of the author displayed in headers. Collected from Git if not specified.
        company: Author company displayed in headers.
        license: License displayed in headers.
    """

    os.chdir(path)

    if os.path.exists("cocotb"):
        if input("Cocotb folder already exists. Do you want to overwrite it? (y/n) ") != "y":
            print("No changes have been performed.")
            return
        shutil.rmtree("cocotb")

    if entity is None:
        entities = list()

        for dirpath, dirnames, filenames in os.walk(os.getcwd()):
            for filename in filenames:
                if filename.endswith(".vhd"):
                    vhdl_file    = open(filename, "r")
                    vhdl_code    = vhdl_file.read()
                    entity_names = re.findall("entity[ ]+[_0-9a-zA-Z]+ is", vhdl_code)

                    for entity_name in entity_names:
                        entities.append(entity_name.split(" ")[1])

                    vhdl_file.close()

        if len(entities) == 0:
            print("No VHDL files or entities found!")
            return
        elif len(entities) == 1:
            entity = entities[0]
        else:
            entity_enum = "Multiple VHDL entities found:\n"

            for i in range(len(entities)):
                entity_enum += f"[{i}]: {entities[i]}\n"

            entity_enum += "Choose for which entity is the test to be generated: "

            while True:
                try:
                    entity = entities[int(input(entity_enum))]
                    break
                except (ValueError, IndexError):
                    print("An error occured. Choose again.")

    if name is None:
        name  = subprocess.run(['git', 'config', '--global', 'user.name'], capture_output=True, text=True, check=True).stdout.strip("\n")

    if email is None:
        email = subprocess.run(['git', 'config', '--global', 'user.email'], capture_output=True, text=True, check=True).stdout.strip("\n")

    if ndk_fpga_path is None:
        ndk_fpga_path = path
        prev_path = path

        while os.path.basename(ndk_fpga_path) != "ndk-fpga":
            ndk_fpga_path = os.path.dirname(ndk_fpga_path)

            if ndk_fpga_path == prev_path:
                print("NDK-FPGA parent folder not found!")
                return

            prev_path = ndk_fpga_path

    templates_path = os.path.join(ndk_fpga_path, "build", "scripts", "cocotb", "templates")
    ndk_fpga_path_rel = os.path.relpath(os.path.dirname(ndk_fpga_path), path)

    os.mkdir("cocotb")
    os.chdir(os.path.join(path, "cocotb"))

    test_file_template = open(f"{templates_path}/cocotb_test.py", "r")
    test_file_contents = test_file_template.read()
    test_file_template.close()

    test_file_contents = re.sub("% ", "%% ", test_file_contents)

    test_file = open("cocotb_test.py", "w+")
    test_file.write(test_file_contents % (license, datetime.now().year, company, name, email))
    test_file.close()

    makefile_template = open(f"{templates_path}/Makefile", "r")
    makefile_contents = makefile_template.read()
    makefile_template.close()

    makefile = open("Makefile", "w+")
    makefile.write(makefile_contents % (license, datetime.now().year, company, name, email, entity.lower(), ndk_fpga_path_rel))
    makefile.close()

    test_sig_template = open(f"{templates_path}/cocotb_test_sig.fdo", "r")
    test_sig_contents = test_sig_template.read()
    test_sig_template.close()

    test_sig = open("cocotb_test_sig.fdo", "w+")
    test_sig.write(test_sig_contents % (license, datetime.now().year, company, name, email, entity.lower()))
    test_sig.close()

    pyproject_template = open(f"{templates_path}/pyproject.toml", "r")
    pyproject_contents = pyproject_template.read()
    pyproject_template.close()

    pyproject = open("pyproject.toml", "w+")
    pyproject.write(pyproject_contents % (entity.lower()))
    pyproject.close()

    print("Test template successfully generated.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="Cocotb Test Template Generator",
        description="Generates cocotb test template for a VHDL entity.",
    )

    parser.add_argument("-p", "--path", default=os.getcwd(), help="The location where the test folder will be generated. If not specified, the current working directory is chosen.")
    parser.add_argument("-e", "--entity", default=None, help="The name of the VHDL entity for which the test will be generated. If not specified, the entity is found automatically")
    parser.add_argument("-nfp", "--ndk_fpga_path", default=None, help="The path to the parent folder of ndk-fpga. If not specified, it is found automatically.")
    parser.add_argument("-n", "--name", default=None, help="The name of the author displayed in headers. Collected from Git if not specified.")
    parser.add_argument("-m", "--email", default=None, help="The email of the author displayed in headers. Collected from Git if not specified.")
    parser.add_argument("-c", "--company", default="CESNET z. s. p. o.", help="Author company displayed in headers. CESNET z. s. p. o. if not specified.")
    parser.add_argument("-l", "--license", default="BSD-3-Clause", help=" License displayed in headers. BSD-3-Clause if not specified.")
    args = parser.parse_args()

    generate_test_template(args.path, args.entity, args.ndk_fpga_path, args.name, args.email, args.company, args.license)
