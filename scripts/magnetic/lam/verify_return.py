#!/usr/bin/env python3
"""MAG-LAM return check (run HERE, not on lam): verify_return.py ARCHIVE.tar.zst STAGING
Unpacks the archive into STAGING, checks sha256.txt for every file, that every module of the chain closure not in
done.txt passed (results-run.tsv / built.txt) with its olean sha256 matching the shipped file, and prints the
per-class peak/wall table. Seeding afterwards: copy STAGING/lib and STAGING/ir into KAM-mag/.lake/build (cp -a), then
`lake build --no-build KAM.Magnetic.Data.Mag.Seg.Checks` must be rc 0."""
import collections, hashlib, os, subprocess, sys
sys.path.insert(0, "/mnt/HC_Volume_106379410/kam-mag/KAM-mag/scripts/magnetic")
import mag_lam_pool as L
arc, stg = sys.argv[1:3]
os.makedirs(stg, exist_ok=True)
subprocess.check_call("zstd -dc %s | tar -C %s -xf -" % (arc, stg), shell=True)
subprocess.check_call("cd %s && sha256sum -c --quiet sha256.txt" % stg, shell=True)
root = "/mnt/HC_Volume_106379410/kam-mag/KAM-mag"
order, _, _ = L.closure(root, ["KAM.Magnetic.Data.Mag.Seg.Checks"])
done = {l.strip() for l in open("/mnt/HC_Volume_106379410/kam-data/mag/lam/done.txt")}
rows = {}
for f in ("results-run.tsv", "results-smoke.tsv"):
    p = os.path.join(stg, f)
    if os.path.exists(p):
        for l in open(p):
            r = l.rstrip("\n").split("\t")
            if r[2] == "pass":
                rows[r[0]] = r
need = [m for m in order if m not in done]
miss = [m for m in need if m not in rows]
bad = []
for m in need:
    if m in rows:
        o = os.path.join(stg, "lib", "lean", *m.split(".")) + ".olean"
        if not os.path.exists(o) or hashlib.sha256(open(o, "rb").read()).hexdigest() != rows[m][8]:
            bad.append(m)
tab = collections.defaultdict(list)
for m, r in rows.items():
    tab[L.classify(m) or "other"].append((int(r[4]), float(r[3])))
for c, v in sorted(tab.items()):
    print("%-6s n=%4d peak max %.1f GB  wall sum %.1f h  max %.0f s" % (
        c, len(v), max(p for p, _ in v) / 2 ** 30, sum(w for _, w in v) / 3600, max(w for _, w in v)))
print("need %d, passed %d, missing %d (first %s), olean hash mismatches %d" % (
    len(need), len(need) - len(miss), len(miss), miss[:3], len(bad)))
sys.exit(0 if not miss and not bad else 1)
