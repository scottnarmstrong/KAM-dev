#!/bin/sh
# One-command setup of the pinned Python environment of the producer tools (untrusted tooling).
#
#   scripts/setup_python_env.sh [VENV_DIR]      default VENV_DIR: .venv at the repository root
#   PYTHON=python3.13 scripts/setup_python_env.sh
#
# Creates a virtual environment and installs exactly the files of scripts/requirements.txt
# (`--require-hashes`, wheels only), then prints the installed versions. Run the tools with that
# environment's interpreter, e.g. `.venv/bin/python -I scripts/certifier/route_select.py --validate`,
# or `. .venv/bin/activate` and the documented `python3 -I ...` commands. Python >= 3.12 is required
# by the pinned numpy and scipy; the pins are tested with Python 3.13.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
venv=${1:-"$root/.venv"}
py=${PYTHON:-python3}

ver=$("$py" -c 'import sys; print("%d.%d" % sys.version_info[:2])')
case "$ver" in
  3.13) ;;
  3.12|3.1[4-9]) echo "note: Python $ver; the pins are tested with 3.13 (pip stops if a pinned wheel is missing)" >&2 ;;
  *) echo "error: Python $ver; the pinned numpy 2.5.3 and scipy 1.18.1 need Python >= 3.12" >&2; exit 1 ;;
esac

"$py" -m venv "$venv"
"$venv/bin/python" -m pip install --quiet --disable-pip-version-check --require-hashes \
  --only-binary=:all: -r "$root/scripts/requirements.txt"
"$venv/bin/python" -I -c '
import sys, mpmath, numpy, scipy
print("python %s, numpy %s, mpmath %s, scipy %s" % (sys.version.split()[0], numpy.__version__,
                                                     mpmath.__version__, scipy.__version__))'
echo "environment ready: $venv (activate with: . $venv/bin/activate)"
