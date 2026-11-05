#!/usr/bin/env python3
"""D68: append the 7 magnetic anchors to manifest/frozen-anchors.json (6 definitions SEALED, magnetic_barrier
DRAFT_SORRY), hashing with the guard's own code (scripts/check_frozen_anchors.py: Guard.digest, MARKERS and the
proof-region bounds of Guard.check_theorem_region).  ABI hashes: abi_hashes.py's procedure (`#print` / `#check @`
under pp.all, the same marker split and sha256), elaborated against the overlay .lake/mag-build.

    python3 mag_freeze_manifest.py [--write]
"""
import hashlib, importlib.util, json, os, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cfa", ROOT / "scripts" / "check_frozen_anchors.py")
G = importlib.util.module_from_spec(spec); spec.loader.exec_module(G)
digest = G.Guard.digest
APPROVAL = dict(approved_by="Scott Armstrong", approved_at="2026-11-01",
                approval_ref="owner approval of the magnetic statement ('approve the magnetic statement'), exactly "
                             "docs/explorations/mag/FREEZE-PROPOSAL.md and docs/explorations/mag/draft/*.lean.txt at "
                             "mag-pilot@a48eb432, including the ℝ × ℝ × ℝ state-type exception; docs/DECISIONS.md D68",
                approval_version="1")
SRC = dict(revision="KAM@a48eb432 (mag-pilot) docs/explorations/mag/FREEZE-PROPOSAL.md",
           range=None)
DEFS = [("MagEps", "magEps"), ("MagH0", "magH0"), ("MagAlpha", "magAlpha"), ("MagV", "magV"),
        ("MagField", "magField"), ("MagHamC", "magHamC")]
THM = ("MagneticBarrier", "magnetic_barrier")


def imports(rel):
    return re.findall(r"(?m)^\s*(?:public\s+)?import\s+(KAM\.Frozen\.[A-Za-z0-9_.]+)\s*$", (ROOT / rel).read_text())


def closure(rel):
    seen, todo = [], list(imports(rel))
    while todo:
        m = todo.pop()
        p = m.replace(".", "/") + ".lean"
        if p in seen:
            continue
        seen.append(p)
        todo += imports(p)
    return [dict(path=p, sha256=digest((ROOT / p).read_bytes())) for p in sorted(seen)]


def regions(text):
    pos = [text.index(m) for m in G.MARKERS]
    body_start = text.index("\n", pos[1]) + 1
    body_end = text.rfind("\n", 0, pos[2]) + 1
    return text[:body_start], text[body_end:]


def abi(entries):
    marker = "ABI_HASH_BOUNDARY"
    mods = sorted({".".join(Path(a["path"]).with_suffix("").parts) for a in entries})
    lines = ["import %s" % m for m in mods] + ["set_option pp.all true", "set_option pp.oneline false"]
    for a in entries:
        lines.append('#eval IO.println "%s %s"' % (marker, a["export"]))
        lines.append(("#print %s" if a["kind"] == "definition" else "#check @%s") % a["export"])
    sd = ROOT / ".lake" / "abi-scratch"; sd.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=sd, delete=False) as f:
        f.write("\n".join(lines) + "\n"); tmp = f.name
    ov = ROOT / ".lake" / "mag-build"
    env = os.environ | {"ELAN_NO_OVERRIDE_NOTICE": "1"}
    out = subprocess.run(["lake", "env", "sh", "-c", 'LEAN_PATH="%s:$LEAN_PATH" exec lean --root=%s %s' % (ov, ROOT, tmp)],
                         cwd="/root/code/KAM-inp", capture_output=True, text=True, env=env)
    os.unlink(tmp)
    assert out.returncode == 0, (out.stdout + out.stderr)[-3000:]
    chunks = re.split(r"^%s (\S+)\s*$" % marker, out.stdout, flags=re.M)
    h = {}
    for i in range(1, len(chunks), 2):
        body = re.sub(r"^\S+\.lean:\d+:\d+: ", "", chunks[i + 1].strip(), flags=re.M)
        h[chunks[i]] = hashlib.sha256(body.encode()).hexdigest()
    return h


def entries():
    out = []
    for f, n in DEFS:
        rel = "KAM/Frozen/Magnetic/Defs/%s.lean" % f
        out.append(dict(id="magnetic.%s.v1" % n, kind="definition", author_approval=APPROVAL,
                        source=dict(SRC, range="FREEZE-PROPOSAL §Proposed Lean text, draft/%s.lean.txt" % f),
                        contract=dict(id="magnetic.%s" % n, version="1"), path=rel, export="KAM.Magnetic.%s" % n,
                        split_policy=dict(source_group="magnetic.%s" % n, mode="NOT_SPLIT",
                                          ruling_ref="docs/DECISIONS.md D68"),
                        abi_sha256=None, definition_closure=closure(rel), state="SEALED",
                        full_file_sha256=digest((ROOT / rel).read_bytes())))
    f, n = THM
    rel = "KAM/Frozen/Magnetic/Theorems/%s.lean" % f
    pre, suf = regions((ROOT / rel).read_bytes().decode("utf-8"))
    out.append(dict(id="magnetic.%s.v1" % n, kind="theorem", author_approval=APPROVAL,
                    source=dict(SRC, range="FREEZE-PROPOSAL §Proposed Lean text, draft/%s.lean.txt (headline)" % f),
                    contract=dict(id="magnetic.%s" % n, version="1"), path=rel, export="KAM.Magnetic.%s" % n,
                    split_policy=dict(source_group="magnetic.%s" % n, mode="NOT_SPLIT",
                                      ruling_ref="docs/DECISIONS.md D68"),
                    abi_sha256=None, definition_closure=closure(rel), state="DRAFT_SORRY",
                    implementation=dict(export="KAM.Provider.Magnetic.%s" % n,
                                        module="KAM.Provider.Magnetic.MagneticBarrier"),
                    prefix_sha256=digest(pre), suffix_sha256=digest(suf),
                    draft_allowlist=dict(frozen_paths=[], audit_paths=[])))
    h = abi(out)
    for a in out:
        a["abi_sha256"] = h[a["export"]]
    return out


if __name__ == "__main__":
    es = entries()
    for a in es:
        print(a["id"], a["state"], a["abi_sha256"][:16], len(a["definition_closure"]))
    if "--write" in sys.argv:
        mp = ROOT / "manifest" / "frozen-anchors.json"
        m = json.loads(mp.read_text())
        have = {a["id"] for a in m["anchors"]}
        assert not have & {a["id"] for a in es}
        m["anchors"] += es
        mp.write_text(json.dumps(m, indent=1, ensure_ascii=False) + "\n")
        print("written", len(m["anchors"]), "anchors")
