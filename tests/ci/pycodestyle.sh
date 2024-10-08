#! /bin/sh

flake8 --extend-exclude "ver_settings.py,synth_settings.py" --statistics --extend-ignore=T201,T202,B902,F821,E501,E203,E221,E261,E265,E266
