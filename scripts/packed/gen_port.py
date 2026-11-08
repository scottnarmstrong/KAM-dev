#!/usr/bin/env python3
"""V2-PACKED-GEN: port the landed, chain-free part of a torus's proof onto the packed route's certificate copy
(untrusted tooling; nothing here is trusted: every ported module is re-checked by the kernel).

The packed route certifies kamx-packed's copy of the certificate (`prod_cert_gen.py`, V2-PACKED-PROD-API §2-3:
`<P>.<T>.Data.Cert`, LG00's certificate with no advice and no witnesses; `CertifiedTorus` does not read them). The
packed stages replace LG00's `Low`, `Full`, `Gram` and `Torsion` stages; the rest of LG00's proof (the static check,
the Hamiltonian balls and bounds, the embedding check, the disc pass `checkHamClaim`, the certified sharp sites
`refinedCoreS`, the frequency facts, the Hamiltonian identity, the model, the window and the confinement form of the
statement) is reused verbatim on the copy: this script copies the closure of those modules from LG00's package
(read only), renamed `LG00` -> `<P>`, with the certificate text of `prod_cert_gen.cert_text`. The closure must not
reach the landed chains or the advice and witness data; it fails closed if it does.

The LG00 modules kamx-packed's `prod_cert_gen.py` lists in `KEEP` (if it defines it) are imported from LG00's
application, not copied (orchestrator, 2026-11-01: the packed packages import `LG00.JetBridge`, whose `lg00Ham_jet`
is proved and built in LG00's application, instead of re-proving it); the renaming is `prod_cert_gen.rename`'s.
Usage: python3 -I scripts/packed/gen_port.py OUT_PKG [--app=APP_ROOT] [--tree=TP] [--prefix=LG00P]
       [--prod-gen=PATH_TO_prod_cert_gen.py]
Prints the ported module list (and writes OUT_PKG/ported_<P>_<T>.json).
"""
import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
IMP = re.compile(r"^public import (\S+)", re.M)
# `Balls.HamBounds` and `Final.HamClaim` are ported only with `--ham-port` (then `--split-balls 38` splits LG00's
# 6 GB ball chunk in two); otherwise the copy imports LG00's own proofs and carries them over (`CertCongr`), which
# drags LG00's whole data, advice included, into the closure.
TREE_ROOTS = ["Final.Static", "Final.Embedding", "Final.RefinedCore", "Final.Freq"]
HAM_ROOTS = ["Balls.HamBounds", "Final.HamClaim"]
SHARED_ROOTS = ["Physical.HamIdentity", "Model"]
CERT_DATA = ("DCoeffs", "E0", "W8", "Cert")


def opt(name, default):
    return next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--%s=" % name)), default)


def load_prod_gen(path):
    spec = importlib.util.spec_from_file_location("prod_cert_gen", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def closure(app, tree, keep=()):
    """The LG00 modules of the chain-free part; fails if it reaches a landed chain or the advice/witness data.
    Modules in `keep` (LG00's own, imported rather than copied: e.g. `LG00.JetBridge`, whose `lg00Ham_jet` is
    proved and built in LG00's application) are neither copied nor traversed; `gen_pkg.py` reuses them."""
    roots = ["LG00.%s.%s" % (tree, r) for r in TREE_ROOTS + (HAM_ROOTS if "--ham-port" in sys.argv else [])] + \
        ["LG00.%s" % r for r in SHARED_ROOTS]
    banned = re.compile(r"^LG00\.%s\.(Low|Full|Gram|Torsion)\." % tree)
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m in keep:
            continue
        seen.add(m)
        if m == "LG00.%s.Data.Cert" % tree:
            continue              # the copy keeps only DCoeffs, E0, W8 (and Ham), see prod_cert_gen.cert_text
        for d in IMP.findall(open(os.path.join(app, *m.split(".")) + ".lean", encoding="utf-8").read()):
            if not d.startswith("LG00."):
                continue
            assert not banned.match(d), "the chain-free part imports a landed chain: %s <- %s" % (d, m)
            if d.startswith("LG00.%s.Data." % tree):
                assert d.split(".")[-1] in CERT_DATA, "the chain-free part imports advice/witness data: %s <- %s" % (
                    d, m)
            stack.append(d)
    return sorted(seen | {"LG00.%s.Data.%s" % (tree, x) for x in CERT_DATA})


def count_balls(text, name):
    """The number of balls in a literal ball list `name` (top-level elements of the outer list)."""
    i = text.index("def %s " % name)
    j = text.find("\nnoncomputable def", i + 5)
    j = j if j > 0 else text.find("\nend ", i)
    body = text[text.index(":=", i) + 2:j]
    depth, n = 0, 0
    for ch in body:
        if ch in "([⟨":
            depth += 1
            if depth == 2:
                n += 1
        elif ch in ")]⟩":
            depth -= 1
    return n


def split_ball_chunk(app, tree, pre, k, rename):
    """Split the ball-pass chunk `k` (`Balls.T<k>`: one `decide` over 200 operations; LG00's `Balls.T38` needs 6 GB)
    into two `decide`s at the boundary of its two stored halves (`lg00BN<k>_1`, the balls of the first operations,
    and `lg00BN<k>_0`, the rest, newest first), and a replacement `T<k>` with the same statement, assembled by
    `ballsRev_step`. No new data: the halves are LG00's own literals. Returns {module: text} for the copy."""
    bdir = os.path.join(app, "LG00", tree, "Balls")
    old = open(os.path.join(bdir, "T%d.lean" % k), encoding="utf-8").read()
    hit = [f for f in sorted(os.listdir(bdir))
           if re.search(r"\bdef lg00BN%d_1 " % k, open(os.path.join(bdir, f), encoding="utf-8").read())]
    assert len(hit) == 1, hit
    ntext = open(os.path.join(bdir, hit[0]), encoding="utf-8").read()
    assert not re.search(r"\bdef lg00BN%d_2 " % k, ntext), "more than two halves"
    m = count_balls(ntext, "lg00BN%d_1" % k)
    st = re.search(r"lg00BR (\d+) lg00BallAcc%d lg00Ops%d = some lg00BallAcc%d" % (k, k, k + 1), " ".join(old.split()))
    rg = re.search(r"Ops `\[(\d+), (\d+)\)` from the checkpoint\.", old)
    start, end = int(st.group(1)), int(rg.group(2))
    assert int(rg.group(1)) == start and 0 < m < end - start, (start, m, end)
    acc, ops, new0, new1 = "lg00BallAcc%d" % k, "lg00Ops%d" % k, "lg00BN%d_0" % k, "lg00BN%d_1" % k
    head = old[:old.index("theorem lg00Balls%d" % k)]
    tail = "\nend LG00.%s\n" % tree

    def part(title, rng, imps=""):
        h = head.replace("chunk %d (generated)" % k, "chunk %d, %s (generated)" % (k, title), 1)
        h = h.replace(rg.group(0), rng, 1)
        return h.replace("module\n\n", "module\n\n" + imps, 1) if imps else h

    note = ("(split in two by V2-PACKED-GEN's `gen_port.py`\nat the boundary of the stored halves `%s`, `%s`; "
            "the unsplit chunk needs 6 GB)" % (new1, new0))
    a = part("first part", "Ops `[%d, %d)` from the checkpoint %s." % (start, start + m, note)) + (
        "theorem lg00Balls%da :\n    lg00BR %d %s (%s.take %d) = some (%s ++ %s) :=\n"
        "  ballsRev_of_chunkOk (by decide +kernel)\n" % (k, start, acc, ops, m, new1, acc)) + tail
    b = part("second part", "Ops `[%d, %d)` from the checkpoint %s." % (start + m, end, note)) + (
        "theorem lg00Balls%db :\n    lg00BR %d (%s ++ %s) (%s.drop %d) =\n      some (%s ++ (%s ++ %s)) :=\n"
        "  ballsRev_of_chunkOk (by decide +kernel)\n" % (k, start + m, new1, acc, ops, m, new0, new1, acc)) + tail
    imps = "public import LG00.%s.Balls.T%da\npublic import LG00.%s.Balls.T%db\n" % (tree, k, tree, k)
    c = part("assembled", "Ops `[%d, %d)` from the checkpoint: the chunk theorem, assembled from its parts\n"
             "`T%da`, `T%db` %s." % (start, end, k, k, note), imps) + (
        "theorem lg00Balls%d :\n    lg00BR %d %s %s = some lg00BallAcc%d := by\n"
        "  have h := (ballsRev_step (k' := %d) lg00Balls%da (by decide +kernel)).trans lg00Balls%db\n"
        "  rw [List.take_append_drop] at h\n"
        "  exact h.trans (by rw [lg00BallAcc%d, lg00BallNew%d, List.append_assoc])\n"
        % (k, start, acc, ops, k + 1, start + m, k, k, k + 1, k)) + tail
    return {"%s.%s.Balls.T%da" % (pre, tree, k): rename(a, pre), "%s.%s.Balls.T%db" % (pre, tree, k): rename(b, pre),
            "%s.%s.Balls.T%d" % (pre, tree, k): rename(c, pre)}


def main():
    out = os.path.abspath(sys.argv[1])
    app = opt("app", "/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00")
    tree, pre = opt("tree", "TP"), opt("prefix", "LG00P")
    pg = opt("prod-gen", os.path.join(HERE, "prod_cert_gen.py"))
    if not os.path.exists(pg):
        pg = "/home/scott/KAM-dev-worktrees/v2-packed/scripts/packed/prod_cert_gen.py"   # kamx-packed's branch
    PG = load_prod_gen(pg)
    keep = set(getattr(PG, "KEEP", ()))       # kamx-packed's choice of the LG00 modules imported, not copied
    mods = closure(app, tree, keep)
    written = []
    for m in mods:
        src = open(os.path.join(app, *m.split(".")) + ".lean", encoding="utf-8").read()
        txt = PG.rename(src, pre)
        if m == "LG00.%s.Data.Cert" % tree:
            txt = PG.cert_text(txt, pre, tree)
        if m == "LG00.%s.Final.Freq" % tree:    # LG00's defect (handoff, errata): the `open` of an absent namespace
            old = "public import %s.Confinement.Main\n" % pre
            if old in txt and "KAM.CertificateSharp.V2.RouteARefinedS" not in txt:
                txt = txt.replace(old, old + "public import KAM.CertificateSharp.V2.RouteARefinedS\n", 1)
        name = pre + m[len("LG00"):]
        dst = os.path.join(out, *name.split(".")) + ".lean"
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if not os.path.exists(dst) or open(dst, encoding="utf-8").read() != txt:
            open(dst, "w", encoding="utf-8").write(txt)
        written.append(name)
    for k in [int(x) for x in opt("split-balls", "").split(",") if x]:
        for name, txt in split_ball_chunk(app, tree, pre, k, PG.rename).items():
            dst = os.path.join(out, *name.split(".")) + ".lean"
            if not os.path.exists(dst) or open(dst, encoding="utf-8").read() != txt:
                open(dst, "w", encoding="utf-8").write(txt)
            if name not in written:
                written.append(name)
    json.dump(dict(app=app, tree=tree, prefix=pre, prod_cert_gen=pg, modules=written, kept=sorted(keep)),
              open(os.path.join(out, "ported_%s_%s.json" % (pre, tree)), "w"), indent=1)
    print("\n".join(written))
    print("%d modules ported" % len(written), file=sys.stderr)


if __name__ == "__main__":
    main()
