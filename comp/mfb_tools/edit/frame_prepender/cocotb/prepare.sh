#!/bin/sh

ROOT_PATH=../../../../..

PKG_COCOTBEXT=$ROOT_PATH/python/cocotbext/

# Python virtual environment
python -m venv venv-prepender
source venv-prepender/bin/activate

python -m pip install setuptools
python -m pip install $PKG_COCOTBEXT

echo ""
echo "Now activate environment with:"
echo "source venv-prepender/bin/activate"
