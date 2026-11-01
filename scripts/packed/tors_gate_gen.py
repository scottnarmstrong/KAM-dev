#!/usr/bin/env python3
"""V2-PACKED-B3 gate: the packed torsion stage on LG00's own certificate data (untrusted tooling; the
kernel re-checks everything).

Copies, read-only, LG00's literals from the `lg00-cert` branch:
  - the embedding, Gram witness, weight `lgD4` and pi enclosure (as `gram_gate_gen.py`);
  - the frequency box `lg00Box` (`lgD1`, `lgD2`), the parameters `s`, `σT`, `μ` and the torsion witness
    `lg00TorsInv`;
  - the 20 jet slot models `lg00TMs` read by the torsion (LG00's `Torsion/D0.lean` and `Torsion/V*.lean`:
    the result of the landed `Slp.compose` at `cfgLow`, proved by LG00's `Low` stage as `lg00TMs_eq`).
The memos are computed with the landed mirror (`scripts/spin_orbit/sofx_check.py`: `d2kModel`, `dxhModels`,
`toDeg`; bit-exact) and re-checked by the kernel entry by entry. The book (layouts, loads, norm exponents,
one common row stride and width) follows the Lean formulas of `KAM/CertificateSharp/Packed/Tors.lean`.

Probes (into $V2P_GATE_DIR, default .lake/v2-packed-gate; each with the data it reads):
  TorsData            all data of the core (control: elaboration only);
  TorsD2_r_j_l   (16) `ptD2Ok … r j l = true`: the landed `d2kModel` against the memo;
  TorsA_a_b      (16) `ptAOk … lg00TMs a b = true`: the landed `DX_H ∘ K` entry at degree 0;
  TorsD1_a        (4) `ptD1Ok … lg00TMs a = true`: the landed `DH ∘ K` entry at degree 0;
  TorsCore            `torsPackedCore … = true` (with `eps` from the packed Gram core);
  TorsCoreNeg         the core with `σT - μ` replaced by 1/100 is `false`;
  TorsCoreMut         the core with the memo's entry A(0, 2) doubled is `false`;
  TorsAMut_0_2        the entry A(0, 2) against a memo with one mantissa + 1 is `false`.
`python3 -I scripts/packed/tors_gate_gen.py --toy` prints the toy book of `TorsTests.lean`.
Usage: python3 -I scripts/packed/tors_gate_gen.py [LG00_CERT_DIR]
"""
import json
import os
import re
import subprocess
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gram_gate_gen as G     # noqa: E402  (also puts scripts/spin_orbit on the path)
import sofx_arith as A        # noqa: E402
import sofx_check as C        # noqa: E402
import sofx_model as M        # noqa: E402
import sofx_packed as SP      # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.environ.get("V2P_GATE_DIR", os.path.join(ROOT, ".lake", "v2-packed-gate"))
ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
CERT = ARGS[0] if ARGS else "/home/scott/KAM-dev-worktrees/lg00-cert/KAM/LG00Cert"
P, Q, n = 128, 24, 2


# ---------------------------------------------------------------------------------------------- the book
def win(a, b):
    return ((a[0][0] + b[0][0], a[0][1] + b[0][1]), (a[1][0] + b[1][0] - 1, a[1][1] + b[1][1] - 1))


def tors_book(nn, PP, q, w, L1, LB, LA, bK, bB, bD, bA, bF):
    """The layouts, loads and norm exponents of `PTorsBook` (Lean formulas of `Tors.lean`)."""
    LU0 = ((0, 0), (1, 1))
    LDL = win(L1, LU0)
    LN = win(L1, LB)
    LDG = win(LDL, L1)
    LC = win(LB, LDG)
    LDGi = win(LC, LB)
    LDLB = win(LDL, LB)
    LDN = win(L1, LDGi)
    LAN = win(LA, LN)
    LT = win(LN, LDN)
    LU1 = (tuple(LDN[0][j] - LDLB[0][j] for j in range(2)), tuple(LDN[1][j] - LDLB[1][j] + 1 for j in range(2)))
    LU2 = (tuple(LDN[0][j] - LAN[0][j] for j in range(2)), tuple(LDN[1][j] - LAN[1][j] + 1 for j in range(2)))
    lays = dict(L1=L1, LB=LB, LA=LA, LU0=LU0, LU1=LU1, LU2=LU2, LDL=LDL, LN=LN, LDG=LDG, LC=LC, LDGi=LDGi,
                LDLB=LDLB, LDN=LDN, LAN=LAN, LT=LT)
    for nm in ("LU0", "LU1", "LU2", "LT", "LAN"):
        lo, d = lays[nm]
        assert all(lo[j] <= 0 < lo[j] + d[j] for j in range(2)), nm + " misses the zero key"
    s0 = max(L[1][1] for L in lays.values())
    N = {k: 1 + (L[1][0] - 1) * s0 + (L[1][1] - 1) for k, L in lays.items()}
    ml = lambda a, b, x, y: 2 * min(N[a], N[b]) * x * y
    p3 = 2 ** (3 * PP)
    ld = {}
    ld["aDL"] = nn * ml("L1", "LU0", bD, bF)
    ld["aN"] = nn * ml("L1", "LB", bK, bB)
    ld["aDG"] = 2 * nn * ml("LDL", "L1", ld["aDL"], bK) + 2 * nn * ml("L1", "LDL", bK, ld["aDL"])
    ld["aC"] = nn * ml("LB", "LDG", bB, ld["aDG"])
    ld["aDGi"] = nn * ml("LC", "LB", ld["aC"], bB)
    ld["aDN"] = ml("LDLB", "LU1", nn * ml("LDL", "LB", ld["aDL"], bB), p3) + nn * ml("L1", "LDGi", bK, ld["aDGi"])
    ld["aXN"] = ml("LAN", "LU2", 2 * nn * ml("LA", "LN", bA, ld["aN"]), p3) + ld["aDN"]
    ld["aT"] = 2 * nn * ml("LN", "LDN", ld["aN"], ld["aXN"])
    ld["aY"] = 2 * nn * ml("LA", "LN", bA, ld["aN"])
    norms = dict(lK=("L1", bK), lB=("LB", bB), lD=("L1", bD), lA=("LA", bA), lDL=("LDL", ld["aDL"]),
                 lN=("LN", ld["aN"]), lDG=("LDG", ld["aDG"]), lC=("LC", ld["aC"]), lDGi=("LDGi", ld["aDGi"]),
                 lXN=("LDN", ld["aXN"]))
    ls = {k: max(1, a.bit_length()) for k, (_, a) in norms.items()}
    need = [(2 * ld["aT"]).bit_length(), (2 * ld["aY"]).bit_length()]
    for k, (L, a) in norms.items():
        lo, d = lays[L]
        r, c = G.maxes(w, q, lo, d, s0)
        need += [ls[k] + 2, (d[0] * s0 * 2 ** ls[k] * r * c).bit_length()]
    width = max(need)
    width += (-width) % 8
    return dict(lays=lays, s0=s0, width=width, loads=ld, ls=ls, dense=N,
                b=dict(bK=bK, bB=bB, bD=bD, bA=bA, bF=bF), P=PP, q=q)


def lean_lay(L, s0, width):
    return "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L[0][0], L[0][1], L[1][0], L[1][1], s0, width)


def pow2(x):
    return "2 ^ %d" % (x.bit_length() - 1) if x > 0 and x & (x - 1) == 0 else str(x)


def lean_book(name, bk):
    L, s0, w = bk["lays"], bk["s0"], bk["width"]
    out = "noncomputable def %s : PTorsBook where\n  P := %d\n" % (name, bk["P"])
    for k in ("L1", "LB", "LA", "LU0", "LU1", "LU2"):
        out += "  %s := %s\n" % (k, lean_lay(L[k], s0, w))
    for k in ("bK", "bB", "bD", "bA", "bF"):
        out += "  %s := %s\n" % (k, pow2(bk["b"][k]))
    out += "  q := %d\n" % bk["q"]
    for k in ("lK", "lB", "lD", "lA", "lDL", "lN", "lDG", "lC", "lDGi", "lXN"):
        out += "  %s := %d\n" % (k, bk["ls"][k])
    return out


def toy():
    t = ((-1, -1), (3, 3))
    bk = tors_book(2, 64, 8, F(2), t, t, t, 2 ** 65, 2 ** 65, 1, 2 ** 65, 2 ** 65)
    print(lean_book("tTb", bk))
    print("-- width %d, stride %d, LT dense %d" % (bk["width"], bk["s0"], bk["dense"]["LT"]))


# ---------------------------------------------------------------------------------------------- the data
def grab_any(dirpath, pattern, name):
    for fn in sorted(os.listdir(dirpath)):
        if re.match(pattern, fn):
            s = open(os.path.join(dirpath, fn)).read()
            if re.search(r"\bdef %s\b" % re.escape(name), s):
                return G.grab(os.path.join(dirpath, fn), name)
    raise KeyError(name)


def parse_cc_terms(text):
    flat = re.sub(r"\s+", " ", text)
    out = []
    for kind, a, b, rest in re.findall(r"\b(tm|tr) (\d+) (\d+) (\d+(?: \d+)?)", flat):
        vals = [G.dz(v) for v in rest.split()]
        out.append(((G.dz(a), G.dz(b)), (vals[0], vals[1] if kind == "tm" else 0)))
    return out


def main():
    if "--toy" in sys.argv:
        toy()
        return
    data = os.path.join(CERT, "Data")
    tors = os.path.join(CERT, "Torsion")
    comps = ["lg00Angle0_0", "lg00Angle1_0", "lg00Action0_0", "lg00Action1_0"]
    grams = ["lg00Gram00_0", "lg00Gram01_0", "lg00Gram10_0", "lg00Gram11_0"]
    texts = {nm: G.grab(os.path.join(data, "E0.lean"), nm) for nm in comps}
    texts.update({nm: G.grab(os.path.join(data, "W8.lean"), nm) for nm in grams})
    dco = os.path.join(data, "DCoeffs.lean")
    d4, d1t, d2t = G.grab(dco, "lgD4"), G.grab(dco, "lgD1"), G.grab(dco, "lgD2")
    cert = os.path.join(data, "Cert.lean")
    emb, ginv, pi = G.grab(cert, "lg00Emb"), G.grab(cert, "lg00GramInv"), G.grab(cert, "lg00Pi")
    tinv, boxt = G.grab(cert, "lg00TorsInv"), G.grab(cert, "lg00Box")
    # the jet slot models (degree, terms, radius)
    d0 = open(os.path.join(tors, "D0.lean")).read()
    tms, tms_defs = [], ""
    for i in range(20):
        mdef = G.grab(os.path.join(tors, "D0.lean"), "lg00TMs_%d" % i)
        deg, lst, rad = re.search(r"⟨(\d+), ⟨(lg00TMs_\d+t_\d+)⟩, ⟨(\d+)⟩⟩", re.sub(r"\s+", " ", mdef)).groups()
        ttext = grab_any(tors, r"V\d+\.lean", lst)
        tms.append(M.Model(int(deg), parse_cc_terms(ttext), int(rad)))
        tms_defs += ttext + "\n" + mdef + "\n"
    tms_defs += G.grab(os.path.join(tors, "D0.lean"), "lg00TMs") + "\n"
    assert "lg00TMs" in d0
    # the numbers of the certificate
    rat = lambda txt: F(int(re.search(r"\(\(\((-?\d+)\) : ℤ\) : ℚ\)", txt).group(1)),
                        int(re.search(r"\(\(\((\d+)\) : ℕ\) : ℚ\)", txt).group(1)))
    lgD1, lgD2 = rat(d1t), rat(d2t)
    box = [(lgD1, lgD2), (F(-12961718757584703, 312500312500000), F(0))]
    assert "-12961718757584703 / 312500312500000" in boxt
    s = F(1000001, 1000000)
    sigT_mu = F(21, 100) - F(1, 100000)
    sigB_mu = F(73, 50) - F(1, 100000)
    w = F(51855732311149192643326361867, 50000000000000000000000000000)
    B = A.FixedB(P)

    def half(nm):
        return [(k, (re_, im_)) for k, (re_, im_) in parse_cc_terms(texts[nm])]
    zeros = [0, 0, 202346613640935704422015369371257, -92032393014743591896737119884692]
    K = M.Embedding([-1, -1], [M.RealPoly(zeros[0], half(comps[0])), M.RealPoly(zeros[1], half(comps[1]))],
                    [0, 0], [M.RealPoly(zeros[2], half(comps[2])), M.RealPoly(zeros[3], half(comps[3]))])
    Wm = M.Weight(F(29, 5000), w)
    pe = A.PiEnclosure(1069028584064966747859680373161870783300, 5, 72, 21)

    def entry(m):
        assert m.deg == 0
        mt = SP.toMants(B, P, m.poly)
        assert mt is not None
        return mt[0], mt[1], F(m.rad, 2 ** P)
    # the Gram memo (as gram_gate_gen.py)
    gm = {}
    for r in range(2 * n):
        for a in range(n):
            gm[(r, a)] = entry(C.dkAngleModel(B, n, K, Wm, pe, r, a) if r < n
                               else C.dkActionModel(B, n, K, Wm, pe, r - n, a))
    # the torsion memo
    d2 = [entry(C.d2kModel(B, n, K, Wm, pe, r, j, l)) for r in range(2 * n) for j in range(n) for l in range(n)]
    X = C.dxhModels(B, n, tms)
    ax = [entry(M.toDeg(B, Wm, pe, 0, C.entry(X, a, b, B))) for a in range(2 * n) for b in range(2 * n)]
    d1 = [entry(M.toDeg(B, Wm, pe, 0, C.msGet(tms, a, B))) for a in range(2 * n)]
    mx = lambda es: max([1] + [abs(v) for e in es for _, v in e[0] + e[1]])
    # boxes (the Gram layouts' boxes; the jet slots' keys)
    kk = [(0, 0)]
    for nm in comps:
        for k, _ in parse_cc_terms(texts[nm]):
            kk += [k, (-k[0], -k[1])]
    L1 = G.box(kk)
    LB = G.box([k for nm in grams for k, _ in parse_cc_terms(texts[nm])] + [(0, 0)])
    LA = G.box([k for e in ax + d1 for k, _ in e[0] + e[1]] + [(0, 0)])
    assert all(L1[0][j] <= k[j] < L1[0][j] + L1[1][j] for e in d2 for k, _ in e[0] + e[1] for j in range(2))
    fc = [C_round(s * box[l][0] * 2 ** P) for l in range(n)]
    p2 = lambda x: 2 ** x.bit_length()
    bk = tors_book(n, P, Q, w, L1, LB, LA, 2 ** 136, 2 ** 132, p2(mx(d2)), p2(mx(ax + d1)),
                   p2(max(abs(v) for v in fc)))
    assert mx(gm.values()) <= 2 ** 136
    write_probes(bk, gm, d2, ax, d1, texts, comps, grams, d4, d1t, d2t, emb, ginv, pi, tinv, boxt, tms_defs,
                 sigB_mu, sigT_mu, s)
    try:
        commit = subprocess.run(["git", "-C", CERT, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    meta = dict(lg00_cert_commit=commit, stride=bk["s0"], width=bk["width"],
                layouts={k: [list(v[0]), list(v[1])] for k, v in bk["lays"].items()}, dense=bk["dense"],
                loads_log2={k: v.bit_length() for k, v in bk["loads"].items()}, l=bk["ls"],
                bounds_log2={k: v.bit_length() - 1 for k, v in bk["b"].items()},
                memo_terms=dict(d2=sum(len(e[0]) + len(e[1]) for e in d2), ax=sum(len(e[0]) + len(e[1]) for e in ax),
                                d1=sum(len(e[0]) + len(e[1]) for e in d1)),
                packed_mbit={k: round(v * bk["width"] / 1e6, 2) for k, v in bk["dense"].items()})
    with open(os.path.join(OUT, "TorsGate.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


def C_round(x):
    """`ratRound`: the nearest integer, ties up (⌊x + 1/2⌋)."""
    x = F(x) + F(1, 2)
    return x.numerator // x.denominator


# ---------------------------------------------------------------------------------------------- the probes
def tl(ts):
    return "[" + ", ".join("tz %d %d %d" % (G.zz(k[0]), G.zz(k[1]), G.zz(v)) for k, v in ts) + "]"


def wrap(expr, ind="    "):
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


def qlit(q):
    return "(%d / %d : ℚ)" % (q.numerator, q.denominator)


def write_probes(bk, gm, d2, ax, d1, texts, comps, grams, d4, d1t, d2t, emb, ginv, pi, tinv, boxt, tms_defs,
                 sigB_mu, sigT_mu, s):
    fmt = ("abbrev lgP : ℕ := 128\n\nabbrev LGF : Type := CertFixed lgP\n\n"
           "def dz (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)\n\n"
           "abbrev tm (k₀ k₁ re im : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨dz im⟩⟩)\n\n"
           "abbrev tr (k₀ k₁ re : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨0⟩⟩)\n\n"
           "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n\n"
           "noncomputable def gW : CertWeight := ⟨(29 / 5000 : ℚ), lgD4⟩\n\n"
           "noncomputable def gCfg : ModelConfig LGF := ⟨24, 30, 12, CertFixed.toMant lgP, []⟩\n\n")

    def edef(name, e):
        return ("noncomputable def %s_re : List (CertKey × ℤ) :=\n%s\n\n"
                "noncomputable def %s_im : List (CertKey × ℤ) :=\n%s\n\n"
                "noncomputable def %s : MemoEntry := (%s_re, %s_im, %s)\n\n") % (
                    name, wrap(tl(e[0])), name, wrap(tl(e[1])), name, name, name, qlit(e[2]))
    empty = "([], [], 0)"

    def memo(only=None, sub=None):
        """The torsion memo; `only` keeps one list's entry (others empty), `sub` replaces entry names."""
        sub = sub or {}
        out = ""
        lists = {}
        for kind, es in (("d2", d2), ("ax", ax), ("d1", d1)):
            names = []
            for i, e in enumerate(es):
                nm = "t%s_%d" % (kind, i)
                if only is None or only == (kind, i):
                    out += edef(nm, e)
                    names.append(sub.get(nm, nm))
                else:
                    names.append(empty)
            lists[kind] = names
        out += "noncomputable def tMemo : PTorsMemo where\n"
        for kind in ("d2", "ax", "d1"):
            out += "  %s :=\n%s\n" % (kind, wrap("[" + ", ".join(lists[kind]) + "]"))
        return out
    gmemo = ""
    for (r, a), e in sorted(gm.items()):
        gmemo += "noncomputable def gMre_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, wrap(tl(e[0])))
        gmemo += "noncomputable def gMim_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, wrap(tl(e[1])))
    rows = lambda p: "[" + ", ".join("[" + ", ".join("%s_%d_%d" % (p, r, a) for a in range(n)) + "]"
                                     for r in range(2 * n)) + "]"
    rads = "[" + ", ".join("[" + ", ".join(qlit(gm[(r, a)][2]) for a in range(n)) + "]" for r in range(2 * n)) + "]"
    gmemo += "noncomputable def gMemo : PGramMemo where\n  re := %s\n  im := %s\n  rad :=\n%s\n\n" % (
        rows("gMre"), rows("gMim"), wrap(rads))
    gbook = open(os.path.join(OUT, "GramCore.lean")).read() if os.path.exists(os.path.join(OUT, "GramCore.lean")) \
        else None
    gb = re.search(r"noncomputable def gBook : PGramBook where\n(?:  .*\n)+", gbook).group(0) if gbook else None
    assert gb, "run gram_gate_gen.py first (gBook)"
    tbook = lean_book("tBook", bk)
    head = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsBase

/-!
# V2-PACKED-B3 gate probe `%s` (opt-in, not built)

%s

The data are LG00's (branch `lg00-cert`, read-only copies). Generated by
`scripts/packed/tors_gate_gen.py`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.TGate.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

"""
    gram_data = "".join(texts[nm] + "\n" for nm in grams) + ginv + "\n" + gb + "\n" + gmemo
    emb_data = "".join(texts[nm] + "\n" for nm in comps) + emb + "\n"
    sig_t = "((21 / 100 : ℚ) - 1 / 100000)"
    eps = ("noncomputable def tEps : LGF :=\n  ((gramPackedCore 2 lg00GramInv gW gCfg gBook gMemo\n"
           "    ((73 / 50 : ℚ) - 1 / 100000)).bind gramInvRadius).getD ⟨0⟩\n\n")
    core_data = d4 + "\n" + d1t + "\n" + d2t + "\n" + fmt + pi + "\n" + boxt + "\n" + tinv + "\n" + gram_data + eps + \
        tbook + "\n"
    core = ("torsPackedCore 2 lg00GramInv gW gCfg lg00Box (1000001 / 1000000 : ℚ) tBook gMemo tMemo tEps\n"
            "      lg00TorsInv %s = %s")
    probes = {}
    probes["TorsData"] = ("Data-only control (all data of the core).", core_data + memo(), "True")
    probes["TorsCore"] = ("The core of the packed torsion check of the LG00 certificate (everything but the "
                          "boundary entries); `eps` from the packed Gram core.", core_data + memo(),
                          core % (sig_t, "true"))
    probes["TorsCoreNeg"] = ("Negative control: the core with the bound 1/100 is false.", core_data + memo(),
                             core % ("(1 / 100 : ℚ)", "false"))
    dbl = (([(k, 2 * v) for k, v in ax[2][0]], [(k, 2 * v) for k, v in ax[2][1]], ax[2][2]))
    probes["TorsCoreMut"] = ("Negative control (data): the core with the memo's entry A(0, 2) doubled is false.",
                             core_data + edef("tax_dbl", dbl) + memo(sub={"tax_2": "tax_dbl"}),
                             core % (sig_t, "false"))
    base = d4 + "\n" + fmt + pi + "\n" + tbook + "\n"
    for r in range(2 * n):
        for j in range(n):
            for l in range(n):
                i = (r * n + j) * n + l
                probes["TorsD2_%d_%d_%d" % (r, j, l)] = (
                    "One boundary entry: the landed d2kModel (%d, %d, %d) against the memo." % (r, j, l),
                    base + emb_data + memo(only=("d2", i)),
                    "ptD2Ok 2 lg00Emb gW gCfg lg00Pi tBook tMemo %d %d %d = true" % (r, j, l))
    for a in range(2 * n):
        for b in range(2 * n):
            i = a * 2 * n + b
            probes["TorsA_%d_%d" % (a, b)] = (
                "One boundary entry: the landed DX_H ∘ K entry (%d, %d) at degree 0 against the memo." % (a, b),
                base + tms_defs + memo(only=("ax", i)),
                "ptAOk 2 gW gCfg lg00Pi tBook tMemo lg00TMs %d %d = true" % (a, b))
    for a in range(2 * n):
        probes["TorsD1_%d" % a] = (
            "One boundary entry: the landed DH ∘ K entry %d at degree 0 against the memo." % a,
            base + tms_defs + memo(only=("d1", a)),
            "ptD1Ok 2 gW gCfg lg00Pi tBook tMemo lg00TMs %d = true" % a)
    mut = ([(k, v + 1 if t == 0 else v) for t, (k, v) in enumerate(ax[2][0])], ax[2][1], ax[2][2])
    probes["TorsAMut_0_2"] = (
        "Negative control (data): the entry A(0, 2) against a memo whose first mantissa is off by one.",
        base + tms_defs + edef("tax_mut", mut) + memo(only=("ax", 2), sub={"tax_2": "tax_mut"}),
        "ptAOk 2 gW gCfg lg00Pi tBook tMemo lg00TMs 0 2 = false")
    os.makedirs(OUT, exist_ok=True)
    for name, (doc, body, stmt) in probes.items():
        words, lines, cur = doc.split(), [], ""
        for wd in words:
            if cur and len(cur) + 1 + len(wd) > 98:
                lines.append(cur)
                cur = wd
            else:
                cur = (cur + " " + wd) if cur else wd
        lines.append(cur)
        txt = head % (name, "\n".join(lines), name) + body
        txt += "\nset_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n" \
               "  decide +kernel\n\nend KAM.CertificateSharp.Packed.TGate.%s\n" % (stmt, name)
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write(txt)


if __name__ == "__main__":
    main()
