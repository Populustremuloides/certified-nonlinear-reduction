#!/bin/sh
# Use the activated environment; install dependencies once with pip install -e .
set -eu
cd "$(dirname "$0")"
exec python3 -m stable_reduction.cli run "$@"
