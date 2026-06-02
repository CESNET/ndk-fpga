#!/bin/sh
python3 -m venv venv-doc
source ./venv-doc/bin/activate
pip install -r requirements.txt
make html
