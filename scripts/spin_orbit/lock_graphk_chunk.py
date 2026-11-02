#!/usr/bin/env python3
"""LOCK-DATA, SOS option (a): the graph checks Pass.GraphL / Pass.GraphH by key-range chunks (untrusted tooling; the
kernel checks everything).

    lock_graphk_chunk.py GDIR SEGPROD ROOT [L|H ...]

One kernel run over the ~26k-term models of a keyed graph check needs 7-10 GB (tp12-tp14, probe). Here every list
computation of the check is split into pieces of at most ~1800 terms, each one kernel run against a literal from the
mirror (packed square from the memo; Lean's two-pointer merge; CertFixed rounding), and the pieces are assembled by
the lock-owned lemmas of GraphChunk.lean / GraphChunkFixed.lean:

  T  the square's terms, the memo literal chunks lockM201xT{RR,II,RI,IR}.cK (900 terms)
  gg = ⟨0, ⟨T⟩, ggR⟩                      (truncation keeps all; error radius 0: error-free)
  G  = ⟨0, ⟨S⟩, GR⟩                       (scalar route: rowItems s T per chunk -> S pieces, error weights VG)
  A1 = f' + f'*                            (one literal, 3.8k terms)
  M2 = merge(A1, S): the run lemma (RR run), threshold pieces merge(A_j, R_j) = M_j, the other runs copied
  M3 = the constant term merged at the [0, 0] threshold piece
  H  = ⟨0, ⟨M3⟩, …⟩; weightedNormUp by piece weights VN; the check decided on the scalars.

SEGPROD: the Seg/Prod directory (M2016.lean, M2017.lean). ROOT: output root; the modules are written under
ROOT/KAM/SpinOrbit/Data/LockN65/GraphK (GraphK/A{P,R,} and Out{L,H} are lock_graphk_lit.py's).
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import lock_cseg  # noqa: E402,F401  (sets CE.TY = LockBackend, compact term lists)
import csplit_emit as CE     # noqa: E402
import lock_seg as LSG       # noqa: E402
import lock_zadv as LZ       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_check as C       # noqa: E402
import sofx_packed as SP     # noqa: E402

NS = "KAM.SpinOrbit.Data.LockN65"
P_ = NS + ".GraphK."
TPD = 900                    # terms per memo literal chunk (lock_cseg.TERMS_PER_DEF)
W_, CFG = "cert.graph.base.weight", "cert.graph.base.cfgLow"
CUT = CFG + ".cutoff"
TOERR = "(fun (t : CertKey × CC LockBackend) => (t.1, t.2, (ofInt 0 : LockBackend)))"
STRIP = "(fun (t : ErrTerm LockBackend) => (t.1, t.2.1))"
WT = "(fun (t : ErrTerm LockBackend) => weightTermUp %s t.1 t.2.2)" % W_
WN = "(fun (t : CertKey × CC LockBackend) => upMul t.2.normUp (ofRatUp (%s.w ^ (t.1.map Int.natAbs).sum)))" % W_
KEEP = "(fun (t : ErrTerm LockBackend) => truncKeep %s t)" % CUT


class GTree(CE.Tree):
    def mod(self, rel):
        return P_ + rel.replace("/", ".")

    def save(self):
        base = os.path.join(self.root, "KAM", "SpinOrbit", "Data", "LockN65", "GraphK")
        for rel, text in self.files.items():
            path = os.path.join(base, rel + ".lean")
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, "w").write(text)
        open(os.path.join(base, "chunk_heavy_modules.txt"), "w").write("\n".join(self.heavy) + "\n")


def key_lit(k):
    return "[%s]" % ", ".join(str(int(x)) for x in k)


def scal(v):
    return "(⟨%d⟩ : LockBackend)" % int(v)


def vals_def(name, vals):
    """`def name : List LockBackend` as `(zdecs […]).map CertFixed.mk` (compact)."""
    vals = [int(v) for v in vals]
    if not vals:
        return ["def %s : List LockBackend := []" % name, ""]
    assert LZ.decode_check(vals) == vals
    out = ["def %s : List LockBackend := (zdecs [" % name]
    cs = LZ.chunks(vals)
    for i, (n, b) in enumerate(cs):
        out.append("  (%d, 0x%x)" % (n, int.from_bytes(b, "little")) + ("," if i + 1 < len(cs) else "]).map"))
    out.append("  fun z => (⟨z⟩ : LockBackend)")
    return out + [""]


def terms_def(name, terms):
    lines, expr = CE.terms_defs(name, [((int(k[0]), int(k[1])), (int(c[0]), int(c[1]))) for k, c in terms],
                                named=True)
    return lines


def mval(x):
    """a backend value's mantissa"""
    return x if isinstance(x, int) else int(getattr(x, "m", x))


def flat_expr(names):
    return "List.flatten [%s]" % ", ".join(names)


def all_split(names, pred, facts):
    """`((List.flatten names).all pred) = true` from per-name facts"""
    return ("by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.all_append, %s, Bool.and_true,"
            " Bool.true_and]" % ", ".join(facts))


def main(gdir, segprod, root, sides=("L", "H")):
    c, _ = LSG.lock_cert(gdir)
    B, W, gr = c.B, c.weight, c.graph
    cut = c.cfgLow.cutoff
    g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
    sk = pickle.load(open(os.path.join(gdir, "graphk.pkl"), "rb"))
    book = {tuple(k): a for k, a in g["books"]["cfgLow"]}
    T = GTree(root, "LockN65")
    base = [NS + ".Cert", NS + ".ZRows", NS + ".RealLowerKSq", NS + ".FallbackMul", NS + ".SegSupport",
            NS + ".GraphChunkFixed", NS + ".SegGraph"]
    fa = C.soGraphActionModel(B, c)
    cfgs = {"L": ("pLo", fa, gr["pLo0"], gr["pLo"], gr["sosLo"], (7, 1), "2016", "cert.graph.sosLo", "lockGKA",
                  "cert.graph.pLo₀", "cert.graph.pLo"),
            "H": ("pHi", M.negM(B, fa), -gr["pHi0"], -gr["pHi"], gr["sosHi"], (7, 2), "2017", "cert.graph.sosHi",
                  "lockGKA.negM", "(-cert.graph.pHi₀)", "(-cert.graph.pHi)")}
    for x in sides:
        side, f, m0, m, sos, key, mk, gname, fl, m0s, ms = cfgs[x]
        Pn, pt = "lockGK%s" % x, "lock_gk%s" % x
        memo = [mm for mm in sk["memos"] if tuple(mm["fullKey"]) == key][0]
        out_terms, R = list(memo["out"][0]), memo["out"][1]
        adv = book[key]
        sizes = [len(SP.targetTerms(po)) for po in adv[2:]]
        assert sum(sizes) == len(out_terms), (sizes, len(out_terms))
        # the memo literal chunks (names and terms), in the Lean order rr, ii, ri, ir
        chunks, i0 = [], 0
        for p, n in zip(("RR", "II", "RI", "IR"), sizes):
            for kk, a in enumerate(range(0, n, TPD)):
                chunks.append(("lockM%sT%s.c%d" % (mk, p, kk), out_terms[i0 + a:i0 + min(a + TPD, n)], p))
            i0 += n
        assert sum(len(ch[1]) for ch in chunks) == len(out_terms)
        gp = [((int(k[0]), int(k[1])), (int(v[0]), int(v[1]))) for k, v in sos]
        Cm = C.ofConst(B, C.keyLen(gp), B.ofInt(-2), B.ofInt(0))
        s = Cm.poly[0]
        # gg
        items = M.toErrTerms(B, out_terms)
        assert all(M.truncKeep(cut, t) for t in items)
        zero = B.ofInt(0)
        X0 = B.upAdd(B.upAdd(M.crossUp(B, zero, zero), M.crossUp(B, zero, zero)), B.upMul(zero, zero))
        ggR = B.upAdd(B.upAdd(R, M.errRadius(B, W, items)), X0)
        gg = M.Model(0, [(t[0], t[1]) for t in items], ggR)
        # G
        rows = [M.rowItems(B, s, ch[1]) for ch in chunks]
        Gitems = [t for r in rows for t in r]
        assert all(M.truncKeep(cut, t) for t in Gitems)
        EG = M.errRadius(B, W, Gitems)
        GR = B.upAdd(B.upAdd(zero, EG), B.upAdd(B.upAdd(M.crossUp(B, M.supNormUp(B, W, gg.poly), Cm.rad),
                                                        M.crossUp(B, M.supNormUp(B, W, Cm.poly), gg.rad)),
                                                 B.upMul(gg.rad, Cm.rad)))
        Gm = M.Model(0, [(t[0], t[1]) for t in Gitems], GR)
        cfg2 = c.cfgLow.withExtra(key, ("direct",))
        Gref = M.model_mul(B, W, cfg2, key, gg, Cm)
        assert Gref.poly == Gm.poly and B.beq(Gref.rad, Gm.rad), "G mirror mismatch"
        # A1, A2, H
        star = M.Model(f.deg, C.conjSorted(B, f.poly), f.rad)
        A1 = M.model_add(B, W, f, star)
        A2 = M.model_add(B, W, A1, Gm)
        c0 = B.ofRatUp(-2 * F(m0))
        Km = C.ofConst(B, 2, c0, B.upAdd(c0, B.neg(B.ofRatDown(-2 * F(m0)))))
        assert C.keyLen(f.poly) == 2
        H = M.model_add(B, W, A2, Km)
        sb = M.supBound(B, W, H)
        rhs = B.ofRatDown(2 * (F(m0) - F(m)))
        assert B.ble(sb, rhs), (side, "the mirror check fails")
        # pieces: the RR run, its chunks split at the [0, 0] threshold
        Sch = [[(t[0], t[1]) for t in r] for r in rows]
        nrr = sum(1 for ch in chunks if ch[2] == "RR")
        run1 = [t for q in range(nrr) for t in Sch[q]]
        assert all(run1[i][0] < run1[i + 1][0] for i in range(len(run1) - 1)), "RR run not ascending"
        A1k = [t[0] for t in A1.poly]
        assert all(A1k[i] < A1k[i + 1] for i in range(len(A1k) - 1)), "A1 not ascending"
        z = run1[-1]
        assert all(k < z[0] for k in A1k), ("A1 key not below the run's last key", max(A1k), z[0])
        k0 = (0, 0)
        Rp, splitq = [], None       # run1 pieces: (S chunk index, lo, hi)
        for q in range(nrr):
            ks = [t[0] for t in Sch[q]]
            if ks[0] < k0 <= ks[-1] and ks[0] != k0:
                cutp = next(i for i, kk in enumerate(ks) if kk >= k0)
                Rp += [(q, 0, cutp), (q, cutp, len(ks))]
                splitq = q
            else:
                Rp.append((q, 0, len(ks)))
        Rl = [Sch[q][a:b] for q, a, b in Rp]
        ts = [r[0][0] for r in Rl[1:]]
        assert k0 in ts or Rl[0][0][0] >= k0, "no [0, 0] threshold"
        jstar = ts.index(k0) + 1 if k0 in ts else 0
        bounds = [None] + ts + [None]
        Al = [[t for t in A1.poly if (bounds[j] is None or t[0] >= bounds[j]) and
               (bounds[j + 1] is None or t[0] < bounds[j + 1])] for j in range(len(Rl))]
        assert sum(map(len, Al)) == len(A1.poly)
        Ml = [[(t[0], t[1]) for t in M.mergeErrTerms(B, M.toErrTerms(B, a), M.toErrTerms(B, r))] for a, r in zip(Al, Rl)]
        rest = [t for q in range(nrr, len(Sch)) for t in Sch[q]]
        M2 = M.mergeErrTerms(B, M.toErrTerms(B, A1.poly), M.toErrTerms(B, Gm.poly))
        assert [(t[0], t[1]) for t in M2] == [t for mm in Ml for t in mm] + rest, "M2 pieces mismatch"
        assert all(mval(t[2]) == 0 for t in M2), "M2 not error-free"
        assert all(t[0] < k0 for j in range(jstar) for t in Ml[j]) and Ml[jstar][0][0] >= k0
        KM = [(t[0], t[1]) for t in M.mergeErrTerms(B, M.toErrTerms(B, Ml[jstar][:1]), M.toErrTerms(B, Km.poly))]
        Hpieces = Ml[:jstar] + [KM, Ml[jstar][1:]] + Ml[jstar + 1:] + [Sch[q] for q in range(nrr, len(Sch))]
        assert [t for pc in Hpieces for t in pc] == H.poly, "H pieces mismatch"
        wn = lambda t: B.upMul(C.normUpC(B, t[1]) if hasattr(C, "normUpC") else M.A.normUp(B, t[1]),  # noqa: E731
                               W.powUp(B, M.keyDeg(t[0])))
        VN = [[wn(t) for t in pc] for pc in Hpieces]
        global VGv
        VGv = [[M.weightTermUp(B, W, t[0], t[2]) for t in r] for r in rows]
        Nsum = B.ofInt(0)
        for v in [v for pc in VN for v in pc]:
            Nsum = B.upAdd(Nsum, v)
        assert B.beq(Nsum, M.weightedNormUp(B, W, H.poly)), "VN sum mismatch"
        print(side, "chunks %d (RR %d), run pieces %d, j* %d, A1 %d, H %d terms; margin %.6e" % (
            len(chunks), nrr, len(Rl), jstar, len(A1.poly), len(H.poly),
            float(C.val(B, rhs) - C.val(B, sb))), flush=True)
        emit_side(T, base, x, side, mk, gname, fl, m0s, ms, key, Pn, pt, chunks, rows, Sch, Rp, splitq, Rl, Al, Ml,
                  ts, jstar, KM, nrr, ggR, GR, A1, Km, H, VN, Nsum, z, B)
    T.save()
    print("graphk chunk", len(T.files), "modules", sum(len(t.encode()) for t in T.files.values()), "bytes",
          len(T.heavy), "heavy", flush=True)


def nest(xs):
    """`a ++ (b ++ (c ++ …))` (the simp normal form of a flattened list)"""
    if len(xs) == 1:
        return xs[0]
    return "%s ++ (%s)" % (xs[0], nest(xs[1:]))


def emit_side(T, base, x, side, mk, gname, fl, m0s, ms, key, Pn, pt, chunks, rows, Sch, Rp, splitq, Rl, Al, Ml, ts,
              jstar, KM, nrr, ggR, GR, A1, Km, H, VN, Nsum, z, B):
    wrap = CE.wrap
    pre = ["open SoGraph", ""]
    keyl = "[%d, %d]" % key
    CFGP = "{ %s with advice := %s.advice ++ [(%s, ProductAdvice.direct)] }" % (CFG, CFG, keyl)
    nT = len(chunks)
    Tn = [ch[0] for ch in chunks]
    # S pieces (the split chunk in two)
    Sp = []                       # (name, terms, chunk q)
    for q in range(nT):
        if q == splitq:
            a = next(b for (qq, aa, b) in Rp if qq == q and aa == 0)
            Sp += [("%sS%da" % (Pn, q), Sch[q][:a], q), ("%sS%db" % (Pn, q), Sch[q][a:], q)]
        else:
            Sp.append(("%sS%d" % (Pn, q), Sch[q], q))
    run_names = [n for n, _, q in Sp if q < nrr]
    rest_names = [n for n, _, q in Sp if q >= nrr]
    assert len(run_names) == len(Rl)
    An = ["%sAp%d" % (Pn, j) for j in range(len(Al))]
    Mn = ["%sM%d" % (Pn, j) for j in range(len(Ml))]
    Hn = Mn[:jstar] + ["%sKM" % Pn, "(%s.drop 1)" % Mn[jstar]] + Mn[jstar + 1:] + rest_names
    VNn = ["%sVN%d" % (Pn, u) for u in range(len(Hn))]
    # ---- data
    items = []
    for n, ts_, _ in Sp:
        items.append((n, terms_def(n, ts_)))
    for n, a in zip(An, Al):
        items.append((n, terms_def(n, a)))
    for n, mm in zip(Mn, Ml):
        items.append((n, terms_def(n, mm)))
    items.append(("%sKM" % Pn, terms_def("%sKM" % Pn, KM)))
    for i in range(nT):
        items.append(("%sVG%d" % (Pn, i), vals_def("%sVG%d" % (Pn, i), [mval(v) for v in VGv[i]])))
    for n, v in zip(VNn, VN):
        items.append((n, vals_def(n, [mval(w) for w in v])))
    sc = ["def %sggR : LockBackend := %s" % (Pn, scal(mval(ggR))), "", "def %sGR : LockBackend := %s" % (Pn, scal(mval(GR))), "",
          "def %ss : CertKey × CC LockBackend := (List.replicate 2 0, ⟨ofInt (-2), ofInt 0⟩)" % Pn, ""]
    sc += wrap(("def %sT : List (CertKey × CC LockBackend) := %s" % (Pn, flat_expr(Tn))).split(" "), "") + [""]
    sc += wrap(("def %sS : List (CertKey × CC LockBackend) := %s" % (Pn, flat_expr([n for n, _, _ in Sp]))).split(" "), "") + [""]
    sc += wrap(("def %sA1 : CertModel LockBackend := ⟨%d, ⟨%s⟩, %s⟩" % (Pn, A1.deg, flat_expr(An), scal(mval(A1.rad)))).split(" "), "") + [""]
    items.append(("%sdefs" % Pn, sc))
    dmods = T.data("Lit%s" % x, "Graph check (%s, chunked): literals" % side,
                   "Mirror literals of the chunked keyed graph check (lock_graphk_chunk.py).", items,
                   [NS + ".Cert", NS + ".ZRows", P_ + "Out%s" % x])
    D = dmods[-1]
    imps = base + [D, P_ + "Out%s" % x]
    # ---- per memo chunk: keep checks, S pieces, G error weights, H weights of the other runs
    fmods = []
    for i, nm in enumerate(Tn):
        srhs = " ++ ".join(n for n, _, q in Sp if q == i)
        if " ++ " in srhs:
            srhs = "(%s)" % srhs
        body = pre + ["theorem %sF%dk :" % (pt, i)] + wrap(("((%s.map %s).all %s) = true := by" % (nm, TOERR, KEEP)).split(" "), "    ") + ["  decide +kernel", ""]
        body += ["theorem %sF%dg :" % (pt, i)] + wrap(("((rowItems %ss %s).all %s) = true := by" % (Pn, nm, KEEP)).split(" "), "    ") + ["  decide +kernel", ""]
        body += ["theorem %sF%ds :" % (pt, i)] + wrap(("(rowItems %ss %s).map %s = %s :=" % (Pn, nm, STRIP, srhs)).split(" "), "    ") + ["  eq_of_termsBeq (by decide +kernel)", ""]
        body += ["theorem %sF%dv :" % (pt, i)] + wrap(("(rowItems %ss %s).map %s = %sVG%d := by" % (Pn, nm, WT, Pn, i)).split(" "), "    ") + ["  decide +kernel"]
        fmods.append(T.write("%sF%d" % (x, i), imps, "Graph check (%s): memo chunk %d" % (side, i),
                             "Keep checks, the scaled chunk and its error weights (one kernel run each).", body))
    nmods = []
    for u, n in enumerate(Hn):
        if n in rest_names:
            body = pre + ["theorem %sN%d :" % (pt, u)] + wrap(("%s.map %s = %s := by" % (n, WN, VNn[u])).split(" "), "    ") + ["  decide +kernel"]
            nmods.append(T.write("%sN%d" % (x, u), imps, "Graph check (%s): norm weights of piece %d" % (side, u),
                                 "One kernel run.", body))
    # ---- gg
    tk = ", ".join("%sF%dk" % (pt, i) for i in range(nT))
    body = pre + ["theorem %sO : %sOut.1 = %sT.map %s := by" % (pt, Pn, Pn, TOERR)]
    body += wrap(("show List.map %s (lockM%sTRR ++ lockM%sTII ++ lockM%sTRI ++ lockM%sTIR) = _" % (TOERR, mk, mk, mk, mk)).split(" "), "  ")
    body += wrap(("simp only [%sT, lockM%sTRR, lockM%sTII, lockM%sTRI, lockM%sTIR, List.flatten_cons, List.flatten_nil,"
                  " List.append_nil, List.append_assoc]" % (Pn, mk, mk, mk, mk)).split(" "), "  ") + [""]
    body += ["theorem %sTk : ((%sT.map %s).all %s) = true := by" % (pt, Pn, TOERR, KEEP)]
    body += wrap(("simp only [%sT, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.all_append,"
                  " %s, Bool.and_true, Bool.true_and]" % (Pn, tk)).split(" "), "  ") + [""]
    body += ["theorem %sGG :" % pt] + wrap(("sqModelOf %s %s %s %s %sOut = ⟨0, ⟨%sT⟩, %sggR⟩ := by" % (W_, CFG, keyl, gname, Pn, Pn, Pn)).split(" "), "    ")
    body += ["  apply certModel_eq_of_parts", "  · rfl", "  · show (truncPoly %s %sOut.1).terms = %sT" % (CUT, Pn, Pn),
             "    rw [%sO, truncPoly_of_all _ _ %sTk]" % (pt, pt),
             "    simp only [List.map_map, Function.comp_def, Prod.mk.eta, List.map_id']"]
    rshow = ("show upAdd (upAdd %sOut.2 (errRadius %s (%sOut.1.map (truncErr %s)))) (upAdd (upAdd (crossUp"
             " (CertPoly.supNormUp %s %s) (ofInt 0)) (crossUp (CertPoly.supNormUp %s %s.conjSorted) (ofInt 0)))"
             " (upMul (ofInt 0) (ofInt 0))) = %sggR" % (Pn, W_, Pn, CUT, W_, gname, W_, gname, Pn))
    rl = wrap(rshow.split(" "), "      ")
    body += ["  · " + rl[0].lstrip()] + rl[1:]
    body += wrap(("rw [%sO, map_truncErr_of_all _ _ %sTk, errRadius_eq_zero _ (%sT.map %s) (toErrTerms_errFree ⟨%sT⟩)]"
                  % (pt, pt, Pn, TOERR, Pn)).split(" "), "    ")
    body += ["    decide +kernel"]
    ggm = T.write("%sGG" % x, imps + fmods, "Graph check (%s): the square's model" % side,
                  "From the memo literal chunks; error-free (radius 0 by lemma).", body)
    # ---- G
    gk = ", ".join("%sF%dg" % (pt, i) for i in range(nT))
    gs = ", ".join("%sF%ds" % (pt, i) for i in range(nT))
    fv = "".join("(.cons %sF%dv " % (pt, i) for i in range(nT)) + ".nil" + ")" * nT
    rif = "List.flatten [%s]" % ", ".join("rowItems %ss %s" % (Pn, n) for n in Tn)
    body = pre + ["theorem %sC :" % pt] + wrap(("(CertModel.ofConst %s.keyLen (ofInt (-2)) (ofInt 0) : CertModel LockBackend) = ⟨0, ⟨[%ss]⟩, ofInt 0⟩ := by" % (gname, Pn)).split(" "), "    ")
    body += ["  rw [show %s.keyLen = 2 by decide +kernel]" % gname, "  rfl", ""]
    body += ["theorem %sPP :" % pt] + wrap(("CertModel.polyProduct %s %s %s (⟨%sT⟩ : CertPoly LockBackend) ⟨[%ss]⟩ = some (rowItems %ss %sT, ofInt 0) := by" % (W_, CFGP, keyl, Pn, Pn, Pn, Pn)).split(" "), "    ")
    body += ["  have h1 : (⟨%sT⟩ : CertPoly LockBackend).isConst = false := by decide +kernel" % Pn,
             "  have h2 : (⟨[%ss]⟩ : CertPoly LockBackend).isConst = true := by decide +kernel" % Pn]
    body += wrap("simp only [CertModel.polyProduct, h1, h2, Bool.false_eq_true, ↓reduceIte, directItems, List.map_cons, List.map_nil, mergeRowsTree]".split(" "), "  ") + [""]
    body += ["theorem %sGk : ((rowItems %ss %sT).all %s) = true := by" % (pt, Pn, Pn, KEEP)]
    body += wrap(("simp only [%sT, List.flatten_cons, List.flatten_nil, List.append_nil, rowItems_append, List.all_append, %s, Bool.and_true, Bool.true_and]" % (Pn, gk)).split(" "), "  ") + [""]
    body += ["theorem %sGv :" % pt] + wrap(("errRadius %s (rowItems %ss %sT) = (pairRounds 64 (List.flatten [%s])).foldr upAdd (ofInt 0) := by" % (W_, Pn, Pn, ", ".join("%sVG%d" % (Pn, i) for i in range(nT)))).split(" "), "    ")
    body += wrap(("rw [show rowItems %ss %sT = %s by simp only [%sT, List.flatten_cons, List.flatten_nil, List.append_nil, rowItems_append]]" % (Pn, Pn, rif, Pn)).split(" "), "  ")
    body += wrap(("exact sumUp_flatten_of_maps _ _ _ %s" % fv).split(" "), "  ") + [""]
    body += ["theorem %sGpoly : (truncPoly %s (rowItems %ss %sT)).terms = %sS := by" % (pt, CUT, Pn, Pn, Pn),
             "  rw [truncPoly_of_all _ _ %sGk]" % pt,
             "  show List.map %s (rowItems %ss %sT) = %sS" % (STRIP, Pn, Pn, Pn)]
    body += wrap(("simp only [%sT, %sS, List.flatten_cons, List.flatten_nil, List.append_nil, rowItems_append, List.map_append, %s, List.append_assoc]" % (Pn, Pn, gs)).split(" "), "  ") + [""]
    gshow = ("upAdd (upAdd (ofInt 0) (errRadius %s ((rowItems %ss %sT).map (truncErr %s)))) (upAdd (upAdd (crossUp"
             " (CertPoly.supNormUp %s ⟨%sT⟩) (ofInt 0)) (crossUp (CertPoly.supNormUp %s ⟨[%ss]⟩) %sggR)) (upMul %sggR"
             " (ofInt 0))) = %sGR := by" % (W_, Pn, Pn, CUT, W_, Pn, W_, Pn, Pn, Pn, Pn))
    body += ["theorem %sGrad :" % pt] + wrap(gshow.split(" "), "    ")
    body += ["  rw [map_truncErr_of_all _ _ %sGk, %sGv]" % (pt, pt), "  decide +kernel", ""]
    body += ["theorem %sG :" % pt] + wrap(("CertModel.mul %s %s %s ⟨0, ⟨%sT⟩, %sggR⟩ (CertModel.ofConst %s.keyLen (ofInt (-2)) (ofInt 0)) = ⟨0, ⟨%sS⟩, %sGR⟩ := by" % (W_, CFGP, keyl, Pn, Pn, gname, Pn, Pn)).split(" "), "    ")
    body += wrap(("rw [%sC, mul_eq_of_polyProduct_cseg _ _ _ (⟨0, ⟨%sT⟩, %sggR⟩ : CertModel LockBackend) ⟨0, ⟨[%ss]⟩, ofInt 0⟩ %sPP]" % (pt, Pn, Pn, Pn, pt)).split(" "), "  ")
    body += ["  exact certModel_eq_of_parts rfl %sGpoly %sGrad" % (pt, pt)]
    gm = T.write("%sG" % x, imps + fmods + [ggm], "Graph check (%s): the scaled square" % side,
                 "The scalar route of the product, by memo chunks.", body)
    # ---- A1
    body = pre + ["theorem %sA1P :" % pt] + wrap(("(CertModel.add %s %s %s.starModel).poly.terms = %sA1.poly.terms :=" % (W_, fl, fl, Pn)).split(" "), "    ") + ["  eq_of_termsBeq (by decide +kernel)"]
    a1p = T.write("%sA1P" % x, imps + [P_ + "A"], "Graph check (%s): f + f*, terms" % side, "One kernel run.", body, heavy=True)
    body = pre + ["theorem %sA1 : CertModel.add %s %s %s.starModel = %sA1 :=" % (pt, W_, fl, fl, Pn),
                  "  certModel_eq_of_parts rfl %sA1P (by" % pt]
    al = wrap(("show upAdd (upAdd %s.rad %s.starModel.rad) (errRadius %s (mergeErrTerms %s.poly.toErrTerms"
               " %s.starModel.poly.toErrTerms)) = %sA1.rad" % (fl, fl, W_, fl, fl, Pn)).split(" "), "      ")
    body += ["    " + al[0].lstrip()] + al[1:]
    body += ["    rw [errRadius_eq_zero _ _ (mergeErrTerms_errFree _ _ (toErrTerms_errFree _) (toErrTerms_errFree _))]",
             "    decide +kernel)"]
    a1 = T.write("%sA1" % x, [a1p], "Graph check (%s): f + f*" % side, "Error radius 0 by lemma.", body)
    # ---- merge pieces
    AE = ["(%s.map %s)" % (n, TOERR) for n in An]
    RE = ["(%s.map %s)" % (n, TOERR) for n in run_names]
    mmods = []
    zk = key_lit(z[0])
    for j in range(len(Ml)):
        body = pre + ["theorem %sM%d :" % (pt, j)] + wrap(("mergeErrTerms %s %s = %s.map %s :=" % (AE[j], RE[j], Mn[j], TOERR)).split(" "), "    ") + ["  eq_of_errTermsBeqCseg (by decide +kernel)", ""]
        if j < len(Ml) - 1:
            body += ["theorem %sM%dlt :" % (pt, j)] + wrap(("((%s ++ %s).all fun a => keyCmp a.1 %s == .lt) = true := by" % (AE[j], RE[j], key_lit(ts[j]))).split(" "), "    ") + ["  decide +kernel", ""]
        for i in range(j):
            for nmx, L in (("gA", AE[j]), ("gR", RE[j])):
                body += ["theorem %sM%d%s%d :" % (pt, j, nmx, i)] + wrap(("(%s.all fun b => keyCmp b.1 %s != .lt) = true := by" % (L, key_lit(ts[i]))).split(" "), "    ") + ["  decide +kernel", ""]
        body += ["theorem %sM%dz :" % (pt, j)] + wrap(("(%s.all fun a => keyCmp a.1 %s == .lt) = true := by" % (AE[j], zk)).split(" "), "    ") + ["  decide +kernel", ""]
        if j < jstar:
            body += ["theorem %sM%dk :" % (pt, j)] + wrap(("((%s.map %s).all fun a => keyCmp a.1 (List.replicate 2 0) == .lt) = true := by" % (Mn[j], TOERR)).split(" "), "    ") + ["  decide +kernel", ""]
        u = Hn.index(Mn[j]) if Mn[j] in Hn else Hn.index("(%s.drop 1)" % Mn[j])
        body += ["theorem %sN%d :" % (pt, u)] + wrap(("%s.map %s = %s := by" % (Hn[u], WN, VNn[u])).split(" "), "    ") + ["  decide +kernel"]
        mmods.append(T.write("%sM%d" % (x, j), imps, "Graph check (%s): merge piece %d" % (side, j),
                             "The merge of a key range, its threshold checks and norm weights (one kernel run each).", body))
    # the run's last term; the K piece
    zlit = "((%s, ⟨⟨%d⟩, ⟨%d⟩⟩, ofInt 0) : ErrTerm LockBackend)" % (zk, int(z[1][0]), int(z[1][1]))
    run_flat = "List.flatten [%s]" % ", ".join(RE)
    run_flat_t = run_flat
    body = pre + ["theorem %sZ :" % pt] + wrap(("((%s).getLast?.map Prod.fst) = some %s := by" % (run_flat_t, zk)).split(" "), "    ") + ["  decide +kernel"]
    zm = T.write("%sZ" % x, imps, "Graph check (%s): the RR run's last term" % side, "One kernel run.", body, heavy=True)
    c0 = "ofRatUp (-2 * %s)" % m0s
    klit = "((List.replicate 2 0, ⟨%s, ofInt 0⟩, ofInt 0) : ErrTerm LockBackend)" % c0
    uk = Hn.index("%sKM" % Pn)
    body = pre + ["theorem %sKM :" % pt] + wrap(("mergeErrTerms ((%s.map %s).take 1) [%s] = %sKM.map %s :=" % (Mn[jstar], TOERR, klit, Pn, TOERR)).split(" "), "    ") + ["  eq_of_errTermsBeqCseg (by decide +kernel)", ""]
    body += ["theorem %sN%d :" % (pt, uk)] + wrap(("%sKM.map %s = %s := by" % (Pn, WN, VNn[uk])).split(" "), "    ") + ["  decide +kernel"]
    km = T.write("%sKM" % x, imps, "Graph check (%s): the constant term" % side, "One kernel run each.", body)
    # ---- M2 assembly
    m = len(Ml)
    allS = run_names + rest_names
    restE = ["(%s.map %s)" % (n, TOERR) for n in rest_names]
    body = pre + ["theorem %sMg2 :" % pt]
    body += wrap(("mergeErrTerms %sA1.poly.toErrTerms (CertPoly.toErrTerms ⟨%sS⟩) = (List.flatten [%s]).map %s := by" % (Pn, Pn, ", ".join(Mn + rest_names), TOERR)).split(" "), "    ")
    body += wrap(("show mergeErrTerms (List.map %s (%s)) (List.map %s (%s)) = _" % (TOERR, flat_expr(An), TOERR, flat_expr([n for n, _, _ in Sp]))).split(" "), "  ")
    body += wrap(("rw [show List.map %s (%s) = %s ++ (%s) by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]]" % (TOERR, flat_expr([n for n, _, _ in Sp]), run_flat, nest(restE))).split(" "), "  ")
    zfacts = ", ".join("%sM%dz" % (pt, j) for j in range(m))
    body += wrap(("rw [mergeErrTerms_append_runK _ _ _ %s %sZ (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.all_append, %s, Bool.and_true, Bool.true_and])]" % (zk, pt, zfacts)).split(" "), "  ")
    body += wrap(("rw [show List.map %s (%s) = %s by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append]]" % (TOERR, flat_expr(An), nest(AE))).split(" "), "  ")
    body += wrap(("rw [show %s = %s by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]]" % (run_flat, nest(RE))).split(" "), "  ")
    for j in range(m - 1):
        ys = []
        for k in range(j + 1, m):
            ys += ["%sM%dgA%d" % (pt, k, j), "%sM%dgR%d" % (pt, k, j)]
        hy = "(by simp only [List.all_append, %s, Bool.and_true, Bool.true_and])" % ", ".join(ys)
        body += wrap(("rw [mergeErrTerms_append_sep %s (%s) %s (%s) (keySep_of_threshold _ _ %s %sM%dlt %s)]"
                      % (AE[j], nest(AE[j + 1:]), RE[j], nest(RE[j + 1:]), key_lit(ts[j]), pt, j, hy)).split(" "), "  ")
    body += wrap(("rw [%s]" % ", ".join("%sM%d" % (pt, j) for j in range(m))).split(" "), "  ")
    body += wrap("simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]".split(" "), "  ")
    m2 = T.write("%sMg2" % x, imps + mmods + [zm], "Graph check (%s): f + f* + G, merged" % side,
                 "The run lemma and the key-range separation (GraphChunk.lean).", body)
    # ---- M3 and the norm
    Q = Mn + rest_names
    pre_k = "(List.flatten [%s]).map %s" % (", ".join(Mn[:jstar]), TOERR) if jstar else "([] : List (ErrTerm LockBackend))"
    after = Mn[jstar + 1:] + rest_names
    body = pre + ["theorem %sMg3 :" % pt]
    body += wrap(("mergeErrTerms ((List.flatten [%s]).map %s) (CertPoly.toErrTerms ⟨[(List.replicate 2 0, ⟨%s, ofInt 0⟩)]⟩) = (List.flatten [%s]).map %s := by" % (", ".join(Q), TOERR, c0, ", ".join(Hn), TOERR)).split(" "), "    ")
    body += wrap(("show mergeErrTerms _ [%s] = _" % klit).split(" "), "  ")
    body += wrap(("rw [show (List.flatten [%s]).map %s = %s ++ ((%s.map %s) ++ (List.flatten [%s]).map %s) by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]]" % (", ".join(Q), TOERR, pre_k, Mn[jstar], TOERR, ", ".join(after), TOERR)).split(" "), "  ")
    if jstar:
        kf = ", ".join("%sM%dk" % (pt, j) for j in range(jstar))
        body += wrap(("rw [mergeErrTerms_single_lt' _ _ _ (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.all_append, %s, Bool.and_true, Bool.true_and])]" % kf).split(" "), "  ")
    body += ["  rw [mergeErrTerms_single_head _ _ (by decide +kernel) (by decide +kernel)]"]
    body += wrap(("rw [List.take_append_of_le_length (by decide +kernel), List.drop_append_of_le_length (by decide +kernel), %sKM, ← List.map_drop]" % pt).split(" "), "  ")
    body += wrap("simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]".split(" "), "  ")
    m3 = T.write("%sMg3" % x, imps + mmods + [km], "Graph check (%s): the constant merged" % side,
                 "At the [0, 0] threshold piece (GraphChunk.lean).", body)
    nfacts = "".join("(.cons %sN%d " % (pt, u) for u in range(len(Hn))) + ".nil" + ")" * len(Hn)
    body = pre + ["theorem %sNorm :" % pt]
    body += wrap(("CertPoly.weightedNormUp %s ⟨List.flatten [%s]⟩ = (pairRounds 64 (List.flatten [%s])).foldr upAdd (ofInt 0) :=" % (W_, ", ".join(Hn), ", ".join(VNn))).split(" "), "    ")
    body += wrap(("sumUp_flatten_of_maps _ _ _ %s" % nfacts).split(" "), "  ")
    nm_ = T.write("%sNorm" % x, imps + mmods + [km] + nmods, "Graph check (%s): the weighted norm" % side,
                  "From the pieces' weights.", body)
    # ---- the check
    gmod = "⟨0, ⟨%sS⟩, %sGR⟩" % (Pn, Pn)
    rr = "upAdd (%s) (neg (ofRatDown (-2 * %s)))" % (c0, m0s)
    body = pre + ["theorem %sHc :" % pt]
    body += wrap(("(decide (%s.deg = 0) && ble ((realLowerModelKParts %s %s %s %s %s).supBound %s) (ofRatDown (2 * (%s - %s)))) = true := by" % (fl, W_, fl, gname, m0s, gmod, W_, m0s, ms)).split(" "), "    ")
    body += ["  have e1 :"] + wrap(("realLowerModelKParts %s %s %s %s %s = CertModel.add %s (CertModel.add %s %sA1 %s) ⟨0, ⟨[(List.replicate 2 0, ⟨%s, ofInt 0⟩)]⟩, %s⟩ := by" % (W_, fl, gname, m0s, gmod, W_, W_, Pn, gmod, c0, rr)).split(" "), "      ")
    body += ["    rw [← %sA1]" % pt, "    simp only [realLowerModelKParts]"]
    body += wrap(("rw [show (if %s.poly.terms.isEmpty then %s.keyLen else %s.poly.keyLen) = 2 by decide +kernel]" % (fl, gname, fl)).split(" "), "    ")
    body += ["    rfl", "  rw [e1]", "  simp only [CertModel.supBound, CertModel.add]",
             "  rw [errRadius_eq_zero _ _ (mergeErrTerms_errFree _ _ (toErrTerms_errFree _) (toErrTerms_errFree _))]",
             "  rw [errRadius_eq_zero _ _ (mergeErrTerms_errFree _ _ (toErrTerms_errFree _) (toErrTerms_errFree _))]",
             "  rw [%sMg2, toErrTerms_itemsPoly_map, %sMg3, itemsPoly_map_toErr, %sNorm]" % (pt, pt, pt),
             "  decide +kernel"]
    hm = T.write("%sHc" % x, imps + [gm, a1, m2, m3, nm_], "Graph check (%s): the bound" % side,
                 "The chunked model's supBound, decided on scalars.", body)
    print(x, "modules: F %d, N %d, M %d; assembly %s" % (len(fmods), len(nmods), len(mmods), hm), flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], tuple(sys.argv[4:]) or ("L", "H"))
