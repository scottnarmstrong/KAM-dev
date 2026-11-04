#!/usr/bin/env python3
"""LOCK-DATA: the eight `DK` models of the lock embedding as kernel-checked literals (untrusted tooling).

    python3 -B lock_dk.py GENDIR OUTROOT

`dkAngleModel 2 base.emb base.weight base.piEnc i j` and `dkActionModel … i j` (i, j < 2) are recomputed by every
check that reads `DK` (the frame majorant L, the Gram entries, the embedding row sums); one column of four took
9.4–10.3e9 B in the kernel and a Gram entry (four DK models and their products) was OOM-killed at 10 GB. Each model
is computed once here (mirror: `lock_sofx.build(...).DKc`) and proved equal to its expression by one kernel run:

  DK/Lit{a,p}{i}{j}   the model literal (compact terms, `ZRows`)                                   data
  DK/{A,P}{i}{j}      `dkAngleModel … i j = lockDKa{i}{j}` (resp. action) by `CertModel.eq_of_segBeq`   heavy
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
os.environ.setdefault("OMP_NUM_THREADS", "1")
import lock_cseg as LC    # noqa: E402,F401  (sets the lock backend and the compact term writer in csplit_emit)
import csplit_emit as CE  # noqa: E402
import lock_seg as LSG    # noqa: E402

NS = "KAM.SpinOrbit.Data.LockN65"
EXPR = {"a": "dkAngleModel", "p": "dkActionModel"}


def tac(text):
    """a wrapped tactic line: first line at column 2, continuations at column 4"""
    ls = CE.wrap(text.strip().split(" "), "    ")
    ls[0] = "  " + ls[0].lstrip()
    return ls


def main(gdir, outroot):
    c, _d = LSG.lock_cert(gdir)
    tree = CE.Tree(outroot, "LockN65")
    tree.mod = lambda rel: "%s.%s" % (NS, rel.replace("/", "."))
    base = [NS + ".Cert", NS + ".ZRows", "KAM.CertificateSharp.Kernel.SegDefs", "KAM.SpinOrbit.LunarAssemblyV2"]
    files = {}
    for kind in ("a", "p"):
        for i in range(2):
            for j in range(2):
                m = c.DKc[(kind, i, j)]
                nm = "lockDK%s%d%d" % (kind, i, j)
                lit = "DK/Lit%s%d%d" % (kind, i, j)
                files[lit] = (base, "DK model literal %s%d%d" % (kind, i, j),
                              "The model `%s 2 base.emb base.weight base.piEnc %d %d` (mirror; data)."
                              % (EXPR[kind], i, j), CE.model_defs(nm, m))
                st = "%s 2 base.emb base.weight base.piEnc %d %d = %s :=" % (EXPR[kind], i, j, nm)
                files["DK/%s%d%d" % (kind.upper(), i, j)] = (
                    base + ["%s.DK.Lit%s%d%d" % (NS, kind, i, j)], "DK model %s%d%d" % (kind, i, j),
                    "One kernel run: the `DK` entry equals its literal.",
                    ["theorem lock_dk%s%d%d :" % (kind, i, j)] + CE.wrap(st.split(" "), "    ") +
                    ["  CertModel.eq_of_segBeq (by decide +kernel)"])
                print(nm, "terms", len(m.poly), "deg", m.deg, flush=True)
    # the whole matrix: `dkModels` unfolds (rfl, lazily) to the eight entries, each rewritten to its literal
    ent = lambda i, j: ("dkAngleModel 2 base.emb base.weight base.piEnc %d %d" % (i, j) if i < 2 else
                        "dkActionModel 2 base.emb base.weight base.piEnc %d %d" % (i - 2, j))
    lit = lambda i, j: "lockDK%s%d%d" % ("a" if i < 2 else "p", i % 2, j)
    explicit = "[" + ", ".join("[" + ", ".join("%s" % ent(i, j) for j in range(2)) + "]" for i in range(4)) + "]"
    lits = "[" + ", ".join("[" + ", ".join(lit(i, j) for j in range(2)) + "]" for i in range(4)) + "]"
    body = ["/-- The `DK` matrix of the lock embedding as literals. -/",
            "theorem lock_dkMat :"] + CE.wrap(("dkModels 2 base.emb base.weight base.piEnc = %s := by" % lits).split(" "),
                                             "    ")
    body += tac(("rw [show dkModels 2 base.emb base.weight base.piEnc = %s from rfl]" % explicit))
    body += tac("rw [" + ", ".join("lock_dk%s%d%d" % (k, i, j) for k in "ap" for i in range(2)
                                   for j in range(2)) + "]")
    files["DK/Mat"] = (base + ["%s.DK.%s%d%d" % (NS, k.upper(), i, j) for k in "ap" for i in range(2)
                               for j in range(2)], "the DK matrix",
                       "`dkModels` from its eight kernel-checked entries (no evaluation here).", body)
    pdir = os.path.join(outroot, "KAM", "SpinOrbit", "Data", "LockN65", "DK")
    os.makedirs(pdir, exist_ok=True)
    opens = ["open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith", ""]
    for rel, (imps, title, doc, body) in files.items():
        text = CE.HEADER.format(imports="\n".join("public import " + x for x in sorted(set(imps))),
                                title="The N = 65 lock: %s" % title, doc=doc, ns=NS,
                                body="\n".join(opens + CE.autowrap(body)).rstrip())
        text = text.replace("`scripts/spin_orbit/csplit_emit.py`", "`scripts/spin_orbit/lock_dk.py`")
        text = LC.ZX.whiten_text(text)[0]       # DELTA-LAM-3: whitened `zdecs` rows (lock_zx.py, ZCodeX.lean)
        for k, l in enumerate(text.splitlines()):
            assert len(l) <= 100, (rel, k, l)
        assert text.count("\n") <= 1500, (rel, text.count("\n"))
        open(os.path.join(outroot, "KAM", "SpinOrbit", "Data", "LockN65", rel + ".lean"), "w").write(text)
    print("lock dk", len(files), "modules")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
