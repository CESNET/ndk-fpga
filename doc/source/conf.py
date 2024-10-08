# -- Path setup --------------------------------------------------------------
import os
import sys
sys.path.append(os.path.abspath("./_ext"))

import sphinx_rtd_theme
from pathlib import Path
from datetime import date
from git import Repo

current_year = date.today().year
git_repo = Repo(search_parent_directories=True)
git_branch = git_repo.active_branch.name
git_sha = git_repo.head.object.hexsha
git_sha_short = git_repo.git.rev_parse(git_sha, short=8)

# -- Project information -----------------------------------------------------

project = 'NDK-FPGA Docs'
copyright = str(current_year) + ', CESNET z.s.p.o.'
author = 'CESNET TMC'
version = 'Git branch: ' + str(git_branch) + ', <br> Git hash: ' + str(git_sha_short)

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    "ndk-fpga",
    "sphinx_rtd_theme",
    "sphinxvhdl.vhdl"
]

vhdl_autodoc_source_path = (Path(__file__).parent.parent.parent).resolve()

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = []


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = "sphinx_rtd_theme"
html_theme_options = {
    'collapse_navigation': True,
    'sticky_navigation': True,
    'navigation_depth': 4,
    'includehidden': True,
    'display_version': True,
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

html_style = 'css/theme_overrides.css'
