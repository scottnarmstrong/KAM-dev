#!/usr/bin/env python3
"""Check that the engine stand-ins of the lunar signature file are verbatim copies.

Usage: python3 -I check_so_standins.py ENGINE.lean LUNAR.lean

Every top-level declaration of the lunar file's block "§I.0 STAND-IN" (up to the following
`end KAM.Certificate`) must occur byte for byte, with its docstring, as a blank-line separated
chunk of the engine file. Also reports the line counts of both files (cap 1500) and lines over
100 characters. Exit status 0 iff everything passes.
"""
import re
import sys

DECL = re.compile(r"^(?:noncomputable )?(?:theorem|lemma|def|structure|abbrev|class|inductive|"
                  r"instance) ([^\s({:]+)", re.M)


def chunks(text):
    return [c.strip("\n") for c in text.split("\n\n") if c.strip()]


def main(engine_path, lunar_path):
    engine = open(engine_path, encoding="utf-8").read()
    lunar = open(lunar_path, encoding="utf-8").read()
    start = lunar.index("## §I.0 STAND-IN")
    start = lunar.index("\n\n", start)
    stop = lunar.index("end KAM.Certificate", start)
    engine_chunks = set(chunks(engine))
    ok = True
    names = []
    for c in chunks(lunar[start:stop]):
        m = DECL.search(c)
        if not m:
            continue
        names.append(m.group(1))
        if c not in engine_chunks:
            print(f"NOT VERBATIM: {m.group(1)}")
            ok = False
    print(f"stand-ins checked: {len(names)} ({', '.join(names)})")
    for path, text in ((engine_path, engine), (lunar_path, lunar)):
        lines = text.splitlines()
        long = [i + 1 for i, l in enumerate(lines) if len(l) > 100]
        print(f"{path}: {len(lines)} lines; lines over 100 chars: {long or 'none'}")
        if len(lines) > 1500 or long:
            ok = False
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
