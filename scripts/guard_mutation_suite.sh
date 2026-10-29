#!/bin/sh
# Mutation suite for the freeze guards: apply known-bad mutations in a throwaway copy of the tree and
# assert that the source-level landing gate (scripts/lint_sources.sh) rejects each one.
# usage: scripts/guard_mutation_suite.sh [--with-abi] [--only ID,ID] [--keep] [--json FILE]
# Exit 0 only if every mutation is rejected and the restored copy passes again. See docs/campaign/GUARDS.md.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 -I "$here/guard_mutation_suite.py" "$@"
