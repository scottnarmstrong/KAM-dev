#!/usr/bin/env python3
"""SO-CSEG: one progress line per torus (modules done / total, heavy done / heavy total) and a projected finish,
from the kbuild driver's logs. Appended to .drafts/PROGRESS.md."""
import datetime
import re

D = "/mnt/HC_Volume_106379410/kam-data/so-cseg/"
out = []
now = datetime.datetime.now()
for w, tsv in (("lower", "kbuild.tsv"), ("upper", "kbuild_lane2.tsv")):
    txt = open(D + "kbuild_%s.out" % w).read()
    hdr = re.findall(r"^(\d+) modules, (\d+) heavy", txt, re.M)
    tot, htot = (int(hdr[-1][0]), int(hdr[-1][1])) if hdr else (0, 0)
    ok = {}
    for kind, m in re.findall(r"^(heavy|light) (\S+) rc=0 ", txt, re.M):
        ok[m] = kind
    done, hdone = len(ok), sum(1 for k in ok.values() if k == "heavy")
    rows = [l.rstrip("\n").split("\t") for l in open(D + "kbuild/" + tsv)]
    rows = [r for r in rows if r[0].startswith("KAM.SpinOrbit.Data.%s" % w.capitalize()) and r[2] == "0"]
    mh = [float(r[3]) for r in rows if r[1] == "heavy"]
    ml = [float(r[3]) for r in rows if r[1] == "light"]
    mh, ml = (sum(mh) / len(mh) if mh else 60), (sum(ml) / len(ml) if ml else 10)
    rem = mh * max(htot - hdone, 0) + ml * max((tot - htot) - (done - hdone), 0)
    eta = now + datetime.timedelta(seconds=rem)
    out.append("%s %s: %d / %d modules (heavy %d / %d), heavy %.0f s, light %.0f s each, projected finish %s"
               % (now.strftime("%m-%d %H:%M"), w, done, tot, hdone, htot, mh, ml, eta.strftime("%m-%d %H:%M")))
with open("/root/code/KAM-inp-sodata3/.drafts/PROGRESS.md", "a") as f:
    f.write("\n".join(out) + "\n")
print("\n".join(out))
