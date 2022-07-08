#!/bin/bash

# This is for repeatability - since dependency resolution can depend on
# the order of a set's enumeration, which is randomized in Python >3.6,
# we set a fixed random seed to make this deterministic. This really isn't
# necessary for correctness, but we need it so that the results in the
# paper are reproducible.

export PYTHONHASHSEED=123

thisscript=$(realpath ${0})
thisdir=$(dirname ${thisscript})

${thisdir}/save_graphs.py

