#!/usr/bin/env python3
"""Rewrite the hashes of the producer tools' requirement files from PyPI (the pinned versions are the input).

    python3 -I scripts/lock_requirements.py            # rewrite the --hash lines for the pinned versions
    python3 -I scripts/lock_requirements.py --check    # exit 1 if a hash list differs from PyPI's

scripts/requirements.txt is the manifest of the producer tools' third-party packages (numpy, mpmath);
scripts/requirements-scipy.txt adds the optional scipy (it includes the core file with `-r`).  Every package is
pinned with `==` and every file PyPI publishes for that version is listed with its sha256, so `pip install
--require-hashes` installs exactly these artifacts on any platform PyPI serves.  To move a pin, edit its version
line and run this script; nothing else in the files changes.  It needs network access to pypi.org.
"""
import json
import os
import re
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
REQS = [os.path.join(HERE, f) for f in ("requirements.txt", "requirements-scipy.txt")]
PIN = re.compile(r"^([A-Za-z0-9_.-]+)==([A-Za-z0-9_.+-]+)")


def pypi_hashes(name, version):
    url = "https://pypi.org/pypi/%s/%s/json" % (name, version)
    with urllib.request.urlopen(url, timeout=60) as fh:
        d = json.load(fh)
    if any(u.get("yanked") for u in d["urls"]):
        raise SystemExit("%s==%s is yanked on PyPI" % (name, version))
    return sorted({u["digests"]["sha256"] for u in d["urls"]})


def render(lines):
    """the file with each pin's hash block regenerated (comments and order kept)."""
    out, skip = [], False
    for ln in lines:
        if skip and ln.startswith("    --hash="):
            continue
        skip = False
        m = PIN.match(ln)
        if not m:
            out.append(ln)
            continue
        hs = pypi_hashes(m.group(1), m.group(2))
        out.append("%s==%s \\" % (m.group(1), m.group(2)))
        out += ["    --hash=sha256:%s%s" % (h, " \\" if i + 1 < len(hs) else "") for i, h in enumerate(hs)]
        skip = True
    return out


def main():
    bad = 0
    for req in REQS:
        name = "scripts/" + os.path.basename(req)
        with open(req, encoding="utf-8") as fh:
            cur = fh.read().splitlines()
        new = render(cur)
        if "--check" in sys.argv:
            ok = new == cur
            bad += not ok
            print("lock_requirements: %s %s" % (name, "matches PyPI" if ok else
                                                "differs from PyPI's hashes for its pins"))
            continue
        with open(req, "w", encoding="utf-8") as fh:
            fh.write("\n".join(new) + "\n")
        print("wrote", name)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
