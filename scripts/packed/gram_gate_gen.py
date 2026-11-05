#!/usr/bin/env python3
"""V2-PACKED-B2 gate: the packed Gram stage on LG00's own certificate data (untrusted tooling; the kernel
re-checks everything).

Copies, read-only, the literals of LG00's embedding (`lg00Emb`: four real components), its Gram inverse
witness (`lg00GramInv`), its weight `lgD4` and its pi enclosure `lg00Pi` from the `lg00-cert` branch, with
LG00's literal format (`dz`, `tm`, `tr`, `LGF = CertFixed 128`), and writes probes that force

  GramData     the data only (control);
  GramEntry_r_a  `pgEntryOk … r a = true`: one boundary entry (the landed DK model (r, a) against the memo),
               eight probes;
  GramCore     `(gramPackedCore 2 lg00GramInv W cfg book memo (σB - μ)).isSome = true`: the packed core.
Together (`pgEntries_of`, `gramPackedCheck_eq_core`) they decide `checkGramPacked` for the LG00 certificate.
Controls and the decomposition of the core:
  GramCoreGuard     the core's guard alone (`pgGuard`);
  GramCoreNeg       the core with the bound `σ = 1/100` returns `none`;
  GramEntryMut_0_0  the boundary entry (0, 0) against a memo with one mantissa + 1 is rejected;
  GramCoreMut       the core with the memo's entry (0, 0) doubled (real part) returns `none`.
Scaling probes (`docs/campaign/studies/V2-PACKED-B2-GATE/scaling/`): the landed DK models in one declaration
(`GramK2`, `GramK4`, `GramKall`: 2, 4 and 8 entries), one or two alone (`GramE1model`, `GramE3model`: the
model only; `GramE1ok`, `GramE3ok`, `GramK00sep`: with the packing check), the B boundary (`GramBok`, one
entry; `GramBall`, all four) and one norm guard (`GramNormL3`).
The memo (the DK models' mantissas and radii) is computed by the landed mirror `scripts/spin_orbit/sofx_check.py`
(`dkAngleModel`, `dkActionModel`, bit-exact) and re-checked by the kernel entry by entry.

The book (layouts, loads, norm precision) is computed here from the data with the Lean formulas mirrored:
boxes from the keys (the real components' full lattice), one common row stride for every layout, loads
`bK = 2^136`, `bB = 2^132` (generous; the kernel checks them), `lD` from `PGramBook.bD`, the width from
`normOk`. Probes go to $V2P_GATE_DIR (default .lake/v2-packed-gate), outside the sources.
Usage: python3 -I scripts/packed/gram_gate_gen.py [LG00_CERT_DIR]
"""
import json
import os
import re
import subprocess
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "spin_orbit"))
import sofx_arith as A        # noqa: E402
import sofx_check as C        # noqa: E402
import sofx_model as M        # noqa: E402
import sofx_packed as SP      # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.environ.get("V2P_GATE_DIR", os.path.join(ROOT, ".lake", "v2-packed-gate"))
CERT = sys.argv[1] if len(sys.argv) > 1 else "/home/scott/KAM-dev-worktrees/lg00-cert/KAM/LG00Cert"

P = 128
Q = 24
BK = 2 ** 136
BB = 2 ** 132


def dz(x):
    x = int(x)
    return x // 2 if x % 2 == 0 else -(x // 2) - 1


def zz(v):
    return 2 * v if v >= 0 else -2 * v - 1


def grab(path, name):
    s = open(path).read()
    i = s.index("def %s " % name)
    i = s.rindex("\n", 0, i) + 1
    j = s.find("\nnoncomputable def", i + 10)
    k = s.find("\ndef ", i + 10)
    e = s.find("\nend ", i + 10)
    j = min(x for x in (j, k, e) if x > 0)
    return s[i:j].rstrip() + "\n"


def keys(text):
    text = re.sub(r"\s+", " ", text)
    return [(dz(a), dz(b)) for _, a, b in re.findall(r"\b(tm|tr) (\d+) (\d+)", text)]


def box(ks):
    lo = (min(k[0] for k in ks), min(k[1] for k in ks))
    hi = (max(k[0] for k in ks), max(k[1] for k in ks))
    return lo, (hi[0] - lo[0] + 1, hi[1] - lo[1] + 1)


def dense_len(dims, stride):
    return 1 + sum((d - 1) * s for d, s in zip(dims, stride))


def mul_load(Na, Nb, A, B):
    return 2 * (min(Na, Nb) * A * B)


def wceil(w, q, e):
    num, den = w.numerator, w.denominator
    x = num ** e * 2 ** q
    return (x + den ** e - 1) // den ** e


def maxes(w, q, lo, dims, s0):
    rows = max(wceil(w, q, abs(lo[0] + a)) for a in range(dims[0]))
    cols = max(wceil(w, q, abs(lo[1] + b)) for b in range(dims[1]))
    return rows, cols


def main():
    data = os.path.join(CERT, "Data")
    comps = ["lg00Angle0_0", "lg00Angle1_0", "lg00Action0_0", "lg00Action1_0"]
    grams = ["lg00Gram00_0", "lg00Gram01_0", "lg00Gram10_0", "lg00Gram11_0"]
    texts = {nm: grab(os.path.join(data, "E0.lean"), nm) for nm in comps}
    texts.update({nm: grab(os.path.join(data, "W8.lean"), nm) for nm in grams})
    d4 = grab(os.path.join(data, "DCoeffs.lean"), "lgD4")
    cert = os.path.join(data, "Cert.lean")
    emb = grab(cert, "lg00Emb")
    ginv = grab(cert, "lg00GramInv")
    pi = grab(cert, "lg00Pi")
    w = F(51855732311149192643326361867, 50000000000000000000000000000)
    # boxes: the real components on the full lattice (half, its negation, the zero mode)
    kk = [(0, 0)]
    for nm in comps:
        for k in keys(texts[nm]):
            kk += [k, (-k[0], -k[1])]
    loK, dK = box(kk)
    kb = [k for nm in grams for k in keys(texts[nm])] + [(0, 0)]
    loB, dB = box(kb)
    d2 = (2 * dK[0] - 1, 2 * dK[1] - 1)
    lo2 = (2 * loK[0], 2 * loK[1])
    d3 = (dB[0] + d2[0] - 1, dB[1] + d2[1] - 1)
    lo3 = (loB[0] + lo2[0], loB[1] + lo2[1])
    s0 = d3[1]
    st = (s0, 1)
    N1, NB, N2, N3 = (dense_len(dK, st), dense_len(dB, st), dense_len(d2, st), dense_len(d3, st))
    n = 2
    bG = 2 * n * mul_load(N1, N1, BK, BK)
    bE = n * mul_load(NB, N2, BB, bG)
    bD = 2 ** (3 * P) + bE
    lK, lB, lD = BK.bit_length(), BB.bit_length(), bD.bit_length()
    need = []
    for lo, dims, l in ((loK, dK, lK), (loB, dB, lB), (lo3, d3, lD)):
        r, c = maxes(w, Q, lo, dims, s0)
        need.append(max(l + 2, (dims[0] * s0 * 2 ** l * r * c).bit_length() + 1))
    width = max(need)
    # the memo: the landed DK models through the bit-exact mirror
    B = A.FixedB(P)

    def half(nm):
        out = []
        flat = re.sub(r"\s+", " ", texts[nm])
        for kind, a, b, rest in re.findall(r"\b(tm|tr) (\d+) (\d+) (\d+(?: \d+)?)", flat):
            vals = [dz(v) for v in rest.split()]
            if kind == "tm":
                out.append(((dz(a), dz(b)), (vals[0], vals[1])))
            else:
                out.append(((dz(a), dz(b)), (vals[0], 0)))
        return out
    zeros = [0, 0, 202346613640935704422015369371257, -92032393014743591896737119884692]
    K = M.Embedding([-1, -1], [M.RealPoly(zeros[0], half(comps[0])), M.RealPoly(zeros[1], half(comps[1]))],
                    [0, 0], [M.RealPoly(zeros[2], half(comps[2])), M.RealPoly(zeros[3], half(comps[3]))])
    Wm = M.Weight(F(29, 5000), w)
    pe = A.PiEnclosure(1069028584064966747859680373161870783300, 5, 72, 21)
    memo_re, memo_im, memo_rad = [], [], []
    maxm = 0
    for r in range(2 * n):
        rr, ri, rd = [], [], []
        for a in range(n):
            m = C.dkAngleModel(B, n, K, Wm, pe, r, a) if r < n else C.dkActionModel(B, n, K, Wm, pe, r - n, a)
            assert m.deg == 0
            mt = SP.toMants(B, P, m.poly)
            rr.append(mt[0])
            ri.append(mt[1])
            rd.append(F(m.rad, 2 ** P))
            maxm = max([maxm] + [abs(v) for _, v in mt[0] + mt[1]])
        memo_re.append(rr)
        memo_im.append(ri)
        memo_rad.append(rd)
    assert maxm <= BK, "memo mantissa above bK"

    def tl(ts):
        return "[" + ", ".join("tz %d %d %d" % (zz(k[0]), zz(k[1]), zz(v)) for k, v in ts) + "]"

    def wrap_list(expr, ind="    "):
        out, cur = [], ind
        toks = expr.split(", ")
        for t, tok in enumerate(toks):
            piece = tok + (", " if t + 1 < len(toks) else "")
            if len(cur) + len(piece.rstrip()) > 98 and cur.strip():
                out.append(cur.rstrip())
                cur = ind
            cur += piece
        out.append(cur.rstrip())
        return "\n".join(out)
    memo_defs = ""
    for r in range(2 * n):
        for a in range(n):
            memo_defs += "noncomputable def gMre_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (
                r, a, wrap_list(tl(memo_re[r][a])))
            memo_defs += "noncomputable def gMim_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (
                r, a, wrap_list(tl(memo_im[r][a])))
    def rows(pfx):
        return "[" + ", ".join("[" + ", ".join("%s_%d_%d" % (pfx, r, a) for a in range(n)) + "]"
                               for r in range(2 * n)) + "]"
    rads = "[" + ", ".join("[" + ", ".join("(%d / %d : ℚ)" % (q.numerator, q.denominator) for q in memo_rad[r])
                           + "]" for r in range(2 * n)) + "]"
    memo_defs += "noncomputable def gMemo : PGramMemo where\n  re := %s\n  im := %s\n  rad :=\n" % (
        rows("gMre"), rows("gMim")) + wrap_list(rads.replace("], [", "],\n [")) + "\n"
    lay = lambda lo, dims: "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (lo[0], lo[1], dims[0], dims[1], s0, width)
    book = ("noncomputable def gBook : PGramBook where\n  P := %d\n  L1 := %s\n  LB := %s\n"
            "  bK := 2 ^ %d\n  bB := 2 ^ %d\n  q := %d\n  lK := %d\n  lB := %d\n  lD := %d\n" % (
                P, lay(loK, dK), lay(loB, dB), BK.bit_length() - 1, BB.bit_length() - 1, Q, lK, lB, lD))
    fmt = ("abbrev lgP : ℕ := 128\n\nabbrev LGF : Type := CertFixed lgP\n\n"
           "def dz (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)\n\n"
           "abbrev tm (k₀ k₁ re im : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨dz im⟩⟩)\n\n"
           "abbrev tr (k₀ k₁ re : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨0⟩⟩)\n\n"
           "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n\n")
    extra = ("noncomputable def gW : CertWeight := ⟨(29 / 5000 : ℚ), lgD4⟩\n\n"
             "noncomputable def gCfg : ModelConfig LGF := ⟨24, 30, 12, CertFixed.toMant lgP, []⟩\n\n")
    body = fmt + d4 + "\n" + "".join(texts[nm] + "\n" for nm in comps + grams) + emb + "\n" + ginv + \
        "\n" + pi + "\n" + extra + book + "\n" + memo_defs
    head = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.GramBase

/-!
# V2-PACKED-B2 gate probe `%s` (opt-in, not built)

%s

The data are LG00's (branch `lg00-cert`, read-only copies). Generated by
`scripts/packed/gram_gate_gen.py`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.Gate.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

"""
    sig = "((73 / 50 : ℚ) - 1 / 100000)"
    stmts = {"GramData": ("Data-only control.", "True"),
             "GramCore": ("The core of the packed Gram check of the LG00 certificate (everything but the "
                          "boundary entries).",
                          "(gramPackedCore 2 lg00GramInv gW gCfg gBook gMemo\n"
                          "      %s).isSome = true" % sig)}
    for r in range(2 * n):
        for a in range(n):
            stmts["GramEntry_%d_%d" % (r, a)] = (
                "One boundary entry: the landed DK model (%d, %d) against the memo." % (r, a),
                "pgEntryOk 2 lg00Emb gW gCfg lg00Pi gBook gMemo %d %d = true" % (r, a))
    # controls and the decomposition of the core
    memo_rows = lambda sub: "[" + ", ".join("[" + ", ".join(sub.get((r, a), "gMre_%d_%d" % (r, a)) for a in range(n))
                                            + "]" for r in range(2 * n)) + "]"
    mut = [(k, v + 1 if t == 0 else v) for t, (k, v) in enumerate(memo_re[0][0])]
    dbl = [(k, 2 * v) for k, v in memo_re[0][0]]
    extra_defs = {
        "GramEntryMut_0_0": ("noncomputable def gMreMut : List (CertKey × ℤ) :=\n%s\n\n"
                             "noncomputable def gMemoMut : PGramMemo := { gMemo with re := %s }\n" % (
                                 wrap_list(tl(mut)), memo_rows({(0, 0): "gMreMut"}))),
        "GramCoreMut": ("noncomputable def gMreDbl : List (CertKey × ℤ) :=\n%s\n\n"
                        "noncomputable def gMemoDbl : PGramMemo := { gMemo with re := %s }\n" % (
                            wrap_list(tl(dbl)), memo_rows({(0, 0): "gMreDbl"})))}
    stmts.update({
        "GramCoreGuard": ("The guard of the packed core alone (layouts, loads, norms, the memo's and B's packing).",
                          "pgGuard 2 lg00GramInv gW gCfg gBook gMemo = true"),
        "GramCoreNeg": ("Negative control: the packed core with the bound 1/100 returns none.",
                        "(gramPackedCore 2 lg00GramInv gW gCfg gBook gMemo\n      (1 / 100 : ℚ)).isSome = false"),
        "GramEntryMut_0_0": ("Negative control (data): the boundary entry (0, 0) against a memo whose first "
                             "real mantissa is off by one.",
                             "pgEntryOk 2 lg00Emb gW gCfg lg00Pi gBook gMemoMut 0 0 = false"),
        "GramCoreMut": ("Negative control (data): the packed core with the memo's DK entry (0, 0) doubled "
                        "(real part) returns none.",
                        "(gramPackedCore 2 lg00GramInv gW gCfg gBook gMemoDbl\n      %s).isSome = false" % sig)})
    okK = "pcOfPolyOk gCfg.toMant 128 gBook.L1 gBook.bK (dkModel 2 lg00Emb gW lg00Pi %d %d).poly = true"
    allK = ("((List.range %d).all fun r => (List.range 2).all fun a =>\n      pcOfPolyOk gCfg.toMant 128 gBook.L1 "
            "gBook.bK (dkModel 2 lg00Emb gW lg00Pi r a).poly) = true")
    stmts.update({
        "GramK2": ("Scaling: the landed DK models (0, *) and their packing check in one declaration.", allK % 1),
        "GramK4": ("Scaling: the landed DK models (0..1, *) and their packing check in one declaration.", allK % 2),
        "GramKall": ("Scaling: all eight landed DK models and their packing check in one declaration.", allK % 4),
        "GramE1model": ("Scaling: the landed DK model (0, 0) alone.",
                        "(dkModel 2 lg00Emb gW lg00Pi 0 0).poly.terms.length > 0"),
        "GramE3model": ("Scaling: the landed DK model (2, 0) alone.",
                        "(dkModel 2 lg00Emb gW lg00Pi 2 0).poly.terms.length > 0"),
        "GramE1ok": ("Scaling: the landed DK model (0, 0) and its packing check.", okK % (0, 0)),
        "GramE3ok": ("Scaling: the landed DK model (2, 0) and its packing check.", okK % (2, 0)),
        "GramK00sep": ("Scaling: the DK models (0, 0) and (0, 1) with their packing checks, in two declarations.",
                       [("p1", okK % (0, 0)), ("probe", okK % (0, 1))]),
        "GramBok": ("Scaling: the boundary of one entry of B.",
                    "pcOfPolyOk gCfg.toMant 128 gBook.LB gBook.bB (gramInvPoly lg00GramInv 0 1) = true"),
        "GramBall": ("Scaling: the boundary of all four entries of B in one declaration.",
                     "((List.range 2).all fun i => (List.range 2).all fun k =>\n      pcOfPolyOk gCfg.toMant 128 "
                     "gBook.LB gBook.bB (gramInvPoly lg00GramInv i k)) = true"),
        "GramNormL3": ("Scaling: the norm guard of the defects.",
                       "normOk gW gBook.q gBook.lD (gBook.bD 2) gBook.L3 = true")})
    os.makedirs(OUT, exist_ok=True)
    for name, (doc, stmt) in stmts.items():
        words, lines, cur = doc.split(), [], ""
        for wd in words:
            if cur and len(cur) + 1 + len(wd) > 98:
                lines.append(cur)
                cur = wd
            else:
                cur = (cur + " " + wd) if cur else wd
        lines.append(cur)
        txt = head % (name, "\n".join(lines), name) + body + extra_defs.get(name, "")
        thms = stmt if isinstance(stmt, list) else [("probe", stmt)]
        txt += "\nset_option profiler true\nset_option profiler.threshold 1\n"
        for tn, st in thms:
            txt += "\ntheorem %s :\n    %s := by\n  decide +kernel\n" % (tn, st)
        txt += "\nend KAM.CertificateSharp.Packed.Gate.%s\n" % name
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write(txt)
    try:
        commit = subprocess.run(["git", "-C", CERT, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    meta = dict(lg00_cert_commit=commit, memo_terms=sum(len(memo_re[r][a]) + len(memo_im[r][a]) for r in range(2 * n) for a in range(n)),
                memo_max_mantissa_bits=maxm.bit_length(), L1=[loK, dK], LB=[loB, dB], L2=[lo2, d2], L3=[lo3, d3], stride=s0, width=width,
                dense=[N1, NB, N2, N3], loads_log2=dict(bK=136, bB=132, bG=bG.bit_length(), bE=bE.bit_length(),
                                                         bD=bD.bit_length()), l=[lK, lB, lD], q=Q,
                packed_bits=dict(DK=N1 * width, B=NB * width, G=N2 * width, BG=N3 * width))
    with open(os.path.join(OUT, "GramGate.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
