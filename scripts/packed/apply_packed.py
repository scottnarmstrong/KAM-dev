#!/usr/bin/env python3
"""V2-PACKED-APPLY: one entry point for the packed route of any certificate application (untrusted tooling; it
writes Lean sources that the kernel re-checks, and changes no Lean and no emitter).

Reads an application config (JSON, schema below and in `docs/campaign/design/V2-PACKED-APPLY.md` §3) and the
application's certificate dump (an LG00-format certificate tree, §2), checks the dump against everything the
emitters read (fails closed, naming the missing file or definition), and drives the existing emitters in order:
  cert    `prod_cert_gen.py`  the certificate copy without advice and witnesses (layout `copy` only);
  port    `gen_port.py`       the chain-free proof ported onto the copy (layout `copy` only);
  chains  `jet_prod_gen.py`   the Low and Full jet chains from the mirror caches (§4);
  packed  `gen_packed.py`     the packed modules `<root>.**` (`--stages jet`) at the copy or at the app's own
                              constants (layout `own`: `--pk-root`, `--pk-format`).
and before them, from the app's generator state (§4):
  extract `jet_extract_low.py` the Low and Full chain programs, live slots and leaves (the app's tooling on the path);
  mirror  `jet_low_gen.py`    `--mirror-only`: the bit-exact mirror of each chain (the caches `chains` and `packed` read).
Every step is one Python process under `py_capped.sh` (8 GB, no swap, after the 20 GB anon wait). Nothing is
built: the Lean side is `run_packed.py` (§5), one process at a time under 4 GB.

After the steps: OUT/apply_<T>.json (the commands, the emitted modules, SHA-256 and size of every emitted file), and
with --check=REF a byte-for-byte comparison of every emitted file with REF (the same relative path): `IDENTICAL`
or the list of differences; the module lists (`modules_<T>.json`) are compared too.

Usage: python3 -I scripts/packed/apply_packed.py CONFIG.json [--out=DIR] [--steps=packed] [--check=REF_DIR]
       [--dry-run] [--check-only] [--emitters=DIR]
  --steps    comma-separated subset of the config's `steps` (default: all of them)
  --emitters the directory of the emitters (default: this script's)
  --dry-run  print the commands and run the dump checks only
  --check-only  skip the steps (they ran before into OUT): the manifest and the comparison only
Exit status 0 when every step passed and (with --check) every file is identical.
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# The Lean names the emitters read from the dump and write into the packed modules. They are LG00's today: the
# reader (`gen_cert.py`) and the emitters match these literal names, so an application's dump must use them, and
# the config states them (`names`) so that a mismatch fails here, before any emitter runs (§6 of the design: the
# names a parameterized emitter must take).
EMITTER_NAMES = {
    "namespace": "LG00",            # the dump's namespace is `<namespace>.<tree>` (`gen_packed`: assert)
    "params": "lg00Params",         # Data/Cert.lean
    "box": "lg00Box",
    "cert": "lg00Cert",
    "emb": "lg00Emb",
    "pi": "lg00Pi",
    "gram_inv": "lg00GramInv",
    "tors_inv": "lg00TorsInv",
    "witness": "lg00RW",            # Final/Wit.lean: the route witness (claims bL, bN, bNt, bT)
    "jet": "lg00Jet",               # <package>/Jet.lean: the jet program literal and its slots v0, d1, d2
    "jet_bridge": "lg00Ham_jet",    # <package>/JetBridge.lean: `lg00Cert.ham.jet = lg00Jet`, built by the app
    "field": "LGF",                 # the ledger's number field
    "statement": "lg00_kamTorus",   # <tree>/Main.lean: the torus theorem, copied verbatim into MainJ
}

# The dump: file -> definitions that must be present (`def NAME` / `theorem NAME` at the start of a line).
DUMP_FILES = {
    "Data/Cert.lean": ["params", "box", "cert", "emb", "pi", "gram_inv", "tors_inv"],
    "Data/DCoeffs.lean": [],        # the long rationals `lgD<i>` the certificate names
    "Data/E0.lean": [],             # the embedding's components `lg00Angle<i>_0`, `lg00Action<i>_0`
    "Data/W8.lean": [],             # the Gram inverse witness `lg00Gram<ij>_0`
    "Final/Wit.lean": ["witness"],
    "Main.lean": ["statement"],
    "../Jet.lean": ["jet"],
    "../JetBridge.lean": ["jet_bridge"],
}
# The application's modules the packed assembly imports (design §5), relative to the tree (or, `../`, the package's
# namespace directory). Checked in the `own` layout; in `copy` the port makes them from these.
ASM_IMPORTS = {
    "static": "Final/Static.lean", "embedding": "Final/Embedding.lean", "refined_core": "Final/RefinedCore.lean",
    "freq": "Final/Freq.lean", "ham_bounds": "Balls/HamBounds.lean", "ham_claim": "Final/HamClaim.lean",
    "ham_identity": "../Physical/HamIdentity.lean",
}
STEPS = ("extract", "mirror", "cert", "port", "chains", "packed")
DEF = r"^(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?(?:def|theorem|abbrev)\s+%s\b"


def die(msg):
    sys.exit("apply_packed: " + msg)


def opt(name, default=None):
    for a in sys.argv[1:]:
        if a.startswith(name + "="):
            return a.split("=", 1)[1]
    return default


def check_config(cfg):
    """The config's keys and its names; fails closed on anything the emitters cannot honour."""
    for k in ("application", "tree", "dump", "layout", "names", "steps", "jet"):
        if k not in cfg:
            die("config: missing key %r" % k)
    bad = {k: (v, EMITTER_NAMES.get(k)) for k, v in cfg["names"].items() if EMITTER_NAMES.get(k) != v}
    missing = sorted(set(EMITTER_NAMES) - set(cfg["names"]))
    if bad or missing:
        die("config names differ from the names the emitters read and write (design §6; the emitters are not "
            "parameterized in these yet): %s%s" % (
                ", ".join("%s: %r (emitters: %r)" % (k, a, b) for k, (a, b) in sorted(bad.items())),
                ("; missing: " + ", ".join(missing)) if missing else ""))
    lay = cfg["layout"]
    if lay.get("kind") not in ("copy", "own"):
        die("layout.kind must be `copy` (the certificate copy `<prefix>.<T>.PK`) or `own` (the app's constants)")
    if lay["kind"] == "own" and not lay.get("pk_root"):
        die("layout `own` needs pk_root (e.g. `LG00.{T}.PK`) and pk_format")
    if lay["kind"] == "own" and lay.get("prefix", cfg["names"]["namespace"]) != cfg["names"]["namespace"]:
        die("layout `own` emits at the app's own constants: prefix must be the namespace")
    for s in cfg["steps"]:
        if s not in STEPS:
            die("unknown step %r" % s)
        if s in ("cert", "port") and lay["kind"] != "copy":
            die("step %r makes the certificate copy: layout `copy` only" % s)
        if s in ("extract", "mirror", "chains"):
            for st in ("Low", "Full"):
                c = cfg["jet"].get("chains", {}).get(st, {})
                for k in ("json", "mirror") + (("cut",) if s == "chains" else ()):
                    if k not in c:
                        die("step %r needs jet.chains.%s.%s" % (s, st, k))
                tgt = c.get({"extract": "json", "mirror": "mirror"}.get(s, ""))
                if tgt and os.path.exists(tgt):     # never overwrite an input another worker made
                    die("step %r would write %s, which exists: name a new path in the config" % (s, tgt))
            if s == "extract" and not ("state" in cfg["jet"] and "tooling" in cfg["jet"]):
                die("step `extract` needs jet.state (the generator state) and jet.tooling (its package root)")


def check_dump(cfg):
    """Every file and definition the reader and the emitters read (§2). Returns the list of checked items."""
    root, names = cfg["dump"]["tree"], cfg["names"]
    seen = []
    for rel, roles in DUMP_FILES.items():
        p = os.path.normpath(os.path.join(root, rel))
        if not os.path.isfile(p):
            die("dump: missing %s" % p)
        txt = open(p, encoding="utf-8").read()
        for r in roles:
            if not re.search(DEF % re.escape(names[r]), txt, re.M):
                die("dump: %s does not define %s (%s)" % (p, names[r], r))
        seen.append(rel)
    cert = open(os.path.join(root, "Data/Cert.lean"), encoding="utf-8").read()
    ns = re.search(r"^namespace (\S+)", cert, re.M)
    want = "%s.%s" % (names["namespace"], cfg["tree"])
    if not ns or ns.group(1) != want:
        die("dump: Data/Cert.lean's namespace is %s, not %s" % (ns and ns.group(1), want))
    for role, rel in ASM_IMPORTS.items():         # the chart, the chain-free proofs (§5)
        p = os.path.normpath(os.path.join(root, rel))
        if not os.path.isfile(p):
            die("dump: the packed assembly imports %s (%s): missing" % (p, role))
        seen.append(rel)
    for k in ("low_mirror", "full_mirror"):
        if "packed" in cfg["steps"] and "mirror" not in cfg["steps"] and not os.path.isfile(cfg["jet"][k]):
            die("jet.%s: missing %s (jet_low_gen.py --mirror-only --cache=…, design §4)" % (k, cfg["jet"][k]))
    return seen


def commands(cfg, out, emitters):
    """The emitter commands of the config's steps, in order (each run under py_capped.sh)."""
    t, lay, names, jet = cfg["tree"], cfg["layout"], cfg["names"], cfg["jet"]
    app = cfg["dump"]["package"]
    pre = lay.get("prefix", names["namespace"])
    em = lambda s: os.path.join(emitters, s)
    cmds = []
    for s in cfg["steps"]:
        if s == "extract":          # the chain programs and leaves from the app's generator state (its tooling)
            for st in ("Low", "Full"):
                c = jet["chains"][st]
                cmds.append((s, [em("jet_extract_low.py"), jet["state"], c["json"], jet["tooling"],
                                 "--stage=" + st]))
        elif s == "mirror":         # the bit-exact mirror of each chain (Low ~19 min, Full ~60 min for LG00 T′)
            for st in ("Low", "Full"):
                c = jet["chains"][st]
                cmds.append((s, [em("jet_low_gen.py"), c["json"], "--stage=" + st, "--mirror-only",
                                 "--cache=" + c["mirror"]]))
        elif s == "cert":
            cmds.append((s, [em("prod_cert_gen.py"), out, "--app=" + app, "--tree=" + t, "--prefix=" + pre]))
        elif s == "port":
            a = [em("gen_port.py"), out, "--app=" + app, "--tree=" + t, "--prefix=" + pre,
                 "--prod-gen=" + em("prod_cert_gen.py")]
            if cfg.get("ham") == "ported":      # the copy proves its own Hamiltonian results (no LG00 data)
                a.append("--ham-port")
            sb = cfg.get("port", {}).get("split_balls", [])
            if sb:                              # the ball chunks above the cap, split at their stored halves
                a.append("--split-balls=" + ",".join(str(k) for k in sb))
            cmds.append((s, a))
        elif s == "chains":
            for st in ("Low", "Full"):
                c = jet["chains"][st]
                cmds.append((s, [em("jet_prod_gen.py"), c["json"], c["mirror"], out, "--stage=" + st,
                                 "--prefix=" + pre, "--tree=" + t] + ["--%s=%s" % kv for kv in c["cut"].items()]))
        elif s == "packed":
            a = [em("gen_packed.py"), "--tree", t, "--prefix", pre, "--cert", cfg["dump"]["tree"], "--pkg", out,
                 "--stages", "jet"]
            if cfg.get("ham") == "ported":
                a.append("--ham-ported")
            if "asm_suffix" in cfg:
                a += ["--asm-suffix", cfg["asm_suffix"]]
            if lay["kind"] == "own":
                a += ["--pk-root", lay["pk_root"], "--pk-format", lay["pk_format"]]
            a += ["--jet-low", jet["low_mirror"], "--jet-full", jet["full_mirror"]]
            cmds.append((s, a))
    return cmds


def emitted(out, cfg):
    """The emitted files: the module list of `gen_packed` (with the format module) and every file the copy, the
    port and the chains list; relative paths under OUT."""
    files = []
    t = cfg["tree"]
    ml = os.path.join(out, "modules_%s.json" % t)
    if os.path.exists(ml):
        files += [m[0].replace(".", "/") + ".lean" for m in json.load(open(ml))]
    pre = cfg["layout"].get("prefix", cfg["names"]["namespace"])
    po = os.path.join(out, "ported_%s_%s.json" % (pre, t))
    if os.path.exists(po):
        files += [m.replace(".", "/") + ".lean" for m in json.load(open(po))["modules"]]
    for nm in sorted(os.listdir(out)) if os.path.isdir(out) else []:
        if re.fullmatch(r"modules_(%s_)?(Low|Full)\.txt|cert_%s\.txt" % (t, t), nm):
            files += [m.replace(".", "/") + ".lean" for m in open(os.path.join(out, nm)).read().split()]
    return sorted(set(files))


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    sys.stdout.reconfigure(line_buffering=True)
    if len(sys.argv) < 2 or sys.argv[1].startswith("--"):
        die("usage: apply_packed.py CONFIG.json [--out=DIR] [--steps=…] [--check=REF] [--dry-run]")
    cfg = json.load(open(sys.argv[1]))
    if opt("--steps"):
        cfg["steps"] = [s for s in opt("--steps").split(",") if s]
    out = os.path.abspath(opt("--out", cfg.get("out", "")) or die("no --out and no `out` in the config"))
    emitters = os.path.abspath(opt("--emitters", HERE))
    check_config(cfg)
    if "own" == cfg["layout"]["kind"] and "--pk-root" not in open(os.path.join(emitters, "gen_packed.py")).read():
        die("layout `own` needs gen_packed.py's --pk-root (59ea55407): not in %s" % emitters)
    seen = check_dump(cfg)
    print("dump OK: %s (%s)" % (cfg["dump"]["tree"], ", ".join(seen)))
    cmds = commands(cfg, out, emitters)
    for s, a in cmds:
        print("[%s] py_capped.sh %s" % (s, " ".join(a)))
    if "--dry-run" in sys.argv:
        return 0
    if os.path.isdir(out) and os.listdir(out) and not any(re.fullmatch(r"apply_\w+\.json", nm)
                                                          for nm in os.listdir(out)):
        die("%s is not empty and holds no apply_<T>.json: not an output of this script (never write into a "
            "reference or another worker's package)" % out)
    if opt("--check") and os.path.abspath(opt("--check")) == out:
        die("--out and --check are the same directory")
    os.makedirs(out, exist_ok=True)
    rec = dict(config=sys.argv[1], application=cfg["application"], tree=cfg["tree"], emitters=emitters,
               steps=[], files={})
    prev = os.path.join(out, "apply_%s.json" % cfg["tree"])
    if "--check-only" in sys.argv:          # the steps ran before: only the manifest and the comparison
        rec["steps"] = json.load(open(prev))["steps"] if os.path.exists(prev) else []
        cmds = []
    for s, a in cmds:
        r = subprocess.run(["bash", os.path.join(HERE, "py_capped.sh")] + a, capture_output=True, text=True)
        log = os.path.join(out, "apply_%s_%s.log" % (cfg["tree"], s))
        open(log, "a").write("$ %s\n%s\n--- stderr\n%s\n--- exit %d\n" % (" ".join(a), r.stdout, r.stderr,
                                                                          r.returncode))
        rec["steps"].append(dict(step=s, cmd=a, exit=r.returncode))
        if s == "cert" and not r.returncode:    # prod_cert_gen prints its module list
            mods = [l.strip() for l in r.stdout.splitlines() if re.fullmatch(r"[A-Z]\w*(\.\w+)+", l.strip())]
            open(os.path.join(out, "cert_%s.txt" % cfg["tree"]), "w").write("\n".join(mods) + "\n")
        if r.returncode:
            json.dump(rec, open(os.path.join(out, "apply_%s.json" % cfg["tree"]), "w"), indent=1)
            die("step %s failed (exit %d); log %s\n%s" % (s, r.returncode, log, r.stderr[-2000:]))
        print("[%s] exit 0" % s)
    files = emitted(out, cfg)
    for f in files:
        p = os.path.join(out, f)
        if not os.path.isfile(p):
            die("emitted module list names %s, which is not in %s" % (f, out))
        rec["files"][f] = [sha(p), os.path.getsize(p)]
    print("emitted: %d files, %d bytes" % (len(files), sum(v[1] for v in rec["files"].values())))
    ref = opt("--check")
    ok = True
    if ref:
        diff, miss = [], []
        for f in files:
            q = os.path.join(ref, f)
            if not os.path.isfile(q):
                miss.append(f)
            elif sha(q) != rec["files"][f][0]:
                diff.append(f)
        lists = {}
        for nm in sorted(os.listdir(out)):
            q = os.path.join(ref, nm)
            if re.fullmatch(r"modules_.*\.(json|txt)", nm) and os.path.exists(q):
                lists[nm] = open(os.path.join(out, nm), "rb").read() == open(q, "rb").read()
            elif re.fullmatch(r"ported_.*\.json", nm) and os.path.exists(q):     # its emitter path differs
                lists[nm] = json.load(open(os.path.join(out, nm)))["modules"] == json.load(open(q))["modules"]
        ok = not diff and not miss and all(lists.values())
        rec["check"] = dict(ref=os.path.abspath(ref), compared=len(files), different=diff, missing_in_ref=miss,
                            lists=lists, identical=ok)
        print("check against %s: %d files compared, %d different, %d missing in the reference; lists %s: %s" % (
            ref, len(files), len(diff), len(miss), lists, "IDENTICAL" if ok else "DIFFERENT"))
        for f in (diff + miss)[:20]:
            print("  " + f)
    json.dump(rec, open(os.path.join(out, "apply_%s.json" % cfg["tree"]), "w"), indent=1)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
