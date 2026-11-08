#!/usr/bin/env python3
"""LOCK-DATA: the lock's graph check (SOS sides pLo, pHi) by row chunks (untrusted tooling; the kernel checks
everything). `csplit_graph.py` (SO-DATA3) adapted to the N = 65 lock.

    python3 -B lock_graph.py GENDIR OUTROOT

The SOS witness g has 3825 terms in data chunks of 32 rows (`sosLo0.cK`, K < 120). One `directItems` of g g*
(14.6 M term pairs) exceeds the 10 GB lane, so (`KAM/SpinOrbit/Data/LockN65/SegGraph.lean`):

  GraphLoGroups           groups of 8 data chunks (256 = 2^8 rows each) and `sosLoPoly.terms = flatten groups`
  Graph{S}Lit{k}[P{j}]    the chunk results L_k = 8 merge levels of group k (mirror; split into <= 1400-line parts)
  Graph{S}C{k}            `levelNCseg 8 (group k rows) = [L_k]`                                         heavy
  Graph{L,H}              `checkRealLowerBound … = true` from the memoized square (mergeRowsTree 56 [L_k])

Chunk size 256 keeps the literals at ~119k error terms per side (32-row chunks: 896k; mirror census).
Everything is written under OUTROOT/KAM/SpinOrbit/Data/LockN65/Pass/; the Lit parts are data.
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
os.environ.setdefault("OMP_NUM_THREADS", "1")
import sofx_model as M   # noqa: E402
import sofx_check as C   # noqa: E402
import sofx_arith as A   # noqa: E402
import sofx_lean as SL   # noqa: E402
import csplit_emit as E  # noqa: E402

P = 112
DATA_ROWS = 32           # rows per data chunk `sosLo0.cK`
LEVELS = int(os.environ.get("LOCK_GRAPH_LEVELS", "7"))   # merge levels per chunk theorem (2^7 = 128 rows; 256 OOM at 10G)
GROUP = 2 ** LEVELS // DATA_ROWS
TERMS_PER_DEF = 32
MAXLINES = 1400
NS = "KAM.SpinOrbit.Data.LockN65"
TY = "LockBackend"


def tac(text):
    """a wrapped tactic line: first line at column 2, continuations at column 4"""
    ls = E.wrap(text.strip().split(" "), "    ")
    ls[0] = "  " + ls[0].lstrip()
    return ls


def level(B, rows):
    return [M.mergeErrTerms(B, rows[i], rows[i + 1]) if i + 1 < len(rows) else rows[i] for i in range(0, len(rows), 2)]


def tree(B, rows, fuel):
    for _ in range(fuel):
        if len(rows) <= 1:
            break
        rows = level(B, rows)
    return rows[0] if rows else []


def et(t):
    (k0, k1), (re, im), e = t
    return "etF %d %s %s %s %s %s" % (P, SL.num(k0), SL.num(k1), SL.num(re), SL.num(im), SL.num(e))


def lit_files(name, terms):
    """[(part_rel_suffix, lines)] for the data parts, and the lines of the joining module"""
    defs = []
    for i in range(0, max(len(terms), 1), TERMS_PER_DEF):
        ch = terms[i:i + TERMS_PER_DEF]
        k = i // TERMS_PER_DEF
        ls = ["def %s.c%d : List (ErrTerm %s) := [" % (name, k, TY)]
        ls += ["  " + et(t) + ("," if j + 1 < len(ch) else "]") for j, t in enumerate(ch)]
        if not ch:
            ls[-1] += "]"
        defs.append(("%s.c%d" % (name, k), ls + [""]))
    parts, cur, n = [], [], 0
    for nm, ls in defs:
        if cur and n + len(ls) > MAXLINES:
            parts.append(cur)
            cur, n = [], 0
        cur.append((nm, ls))
        n += len(ls)
    if cur:
        parts.append(cur)
    names = [nm for nm, _ in defs]
    join = E.wrap(["def %s : List (ErrTerm %s) := List.flatten [" % (name, TY)] + [x + "," for x in names[:-1]] +
                  [names[-1] + "]"], "")
    return [[l for _, ls in p for l in ls] for p in parts], join


def main(gdir, outroot):
    B = A.FixedB(P)
    gr = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))["graph"]
    pdir = os.path.join(outroot, "KAM", "SpinOrbit", "Data", "LockN65", "Pass")
    os.makedirs(pdir, exist_ok=True)
    base = [NS + ".Cert", NS + ".Witness", NS + ".SegGraph", "KAM.SpinOrbit.LunarAssemblyV2"]
    opens = ["open SoGraph", "open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit "
             "CertArith"]
    files = {}
    for S, key, data, fexpr, m0, m, thm in (
            ("Lo", "sosLo", "sosLo0", "(soGraphActionModel cert.graph)", "cert.graph.pLo₀", "cert.graph.pLo", "L"),
            ("Hi", "sosHi", "sosHi0", "(soGraphActionModel cert.graph).negM", "(-cert.graph.pHi₀)",
             "(-cert.graph.pHi)", "H")):
        g = [((int(k[0]), int(k[1])), (int(c[0]), int(c[1]))) for k, c in gr[key]]
        nd = (len(g) + DATA_ROWS - 1) // DATA_ROWS
        conj = C.conjSorted(B, g)
        groups = [list(range(i, min(i + GROUP, nd))) for i in range(0, nd, GROUP)]
        Ls = []
        for grp in groups:
            rows = [M.rowItems(B, s, conj) for s in g[grp[0] * DATA_ROWS:(grp[-1] + 1) * DATA_ROWS]]
            for _ in range(LEVELS):
                rows = level(B, rows)
            assert len(rows) == 1, len(rows)
            Ls.append(rows[0])
        whole = M.directItems(B, g, conj)
        assert tree(B, list(Ls), 64 - LEVELS) == whole, "chunked tree differs from the mirror's directItems"
        print(S, "groups", len(groups), "literal terms", sum(map(len, Ls)), "square terms", len(whole), flush=True)
        # groups and the regrouping
        gnm = ["lock%sG%d" % (key.capitalize(), k) for k in range(len(groups))]
        body = []
        for k, grp in enumerate(groups):
            body += ["/-- Rows %d to %d of `%s` (data chunks %d to %d). -/" % (
                grp[0] * DATA_ROWS, min((grp[-1] + 1) * DATA_ROWS, len(g)) - 1, data, grp[0], grp[-1])]
            body += E.wrap(["def %s : List (CertKey × CC %s) := List.flatten [" % (gnm[k], TY)] +
                           ["%s.c%d," % (data, c) for c in grp[:-1]] + ["%s.c%d]" % (data, grp[-1])], "") + [""]
        nested = "[" + ", ".join("[" + ", ".join("%s.c%d" % (data, c) for c in grp) + "]" for grp in groups) + "]"
        body += ["/-- The witness in groups of %d rows. -/" % (2 ** LEVELS),
                 "theorem lock_%sGroups :" % key] + E.wrap(
            ("%sPoly.terms = List.flatten [%s] :=" % (key, ", ".join(gnm))).split(" "), "    ")
        body += tac("(flatten_groups_cseg %s).symm" % nested)
        files["Graph%sGroups" % S] = (base, "SOS side %s: row groups" % S,
                                     "Groups of eight data chunks and the regrouped witness.", body)
        # literals
        for k, L in enumerate(Ls):
            nm = "lockG%sL%d" % (S, k)
            parts, join = lit_files(nm, L)
            pmods = []
            for j, pl in enumerate(parts):
                rel = "Graph%sLit%dP%d" % (S, k, j)
                files[rel] = (base, "SOS side %s: chunk result %d, part %d" % (S, k, j),
                              "Literal error terms of the chunk result `L_%d` of `g g*` (data)." % k, pl)
                pmods.append("%s.Pass.%s" % (NS, rel))
            files["Graph%sLit%d" % (S, k)] = (base + pmods, "SOS side %s: chunk result %d" % (S, k),
                                             "The chunk result `L_%d` of `g g*` (data)." % k, join)
        # chunk theorems
        conjT = "%sPoly.conjSorted.terms" % key
        for k in range(len(groups)):
            st = "levelNCseg %d (%s.map fun s => rowItems s %s) = [lockG%sL%d] :=" % (LEVELS, gnm[k], conjT, S, k)
            files["Graph%sC%d" % (S, k)] = (
                base + ["%s.Pass.Graph%sLit%d" % (NS, S, k), "%s.Pass.Graph%sGroups" % (NS, S)],
                "SOS side %s: chunk %d" % (S, k), "%d merge levels of one %d-row group (one kernel run)." % (
                    LEVELS, 2 ** LEVELS),
                ["theorem lock_g%sc%d :" % (S, k)] + E.wrap(st.split(" "), "    ") +
                ["  eq_singleton_of_beq_cseg (by decide +kernel)"])
        n = len(groups)
        Lz = "[" + ", ".join("lockG%sL%d" % (S, k) for k in range(n)) + "]"
        gl = "[" + ", ".join(gnm) + "]"
        cfg7 = "{ base.cfgLow with advice := base.cfgLow.advice ++ [([7], ProductAdvice.direct)] }"
        body = ["theorem lock_g%sDirect :" % S] + E.wrap(
            ("directItems %sPoly.terms %s = mergeRowsTree %d %s := by" % (key, conjT, 64 - LEVELS, Lz)).split(" "),
            "    ")
        body += ["  unfold directItems"]
        body += tac("rw [show (64 : ℕ) = %d + %d from rfl, mergeRowsTree_add_cseg, lock_%sGroups,"
                    " levelNCseg_flatten %d _ %s (by decide +kernel)]" % (64 - LEVELS, LEVELS, key, LEVELS, gl))
        body += ["  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]"]
        body += tac("rw [" + ", ".join("lock_g%sc%d" % (S, k) for k in range(n)) + "]")
        body += ["  rfl", "",
                 "theorem lock_g%sSq :" % S]
        body += E.wrap(("CertModel.polyProduct base.weight %s [7] %sPoly %sPoly.conjSorted = some (mergeRowsTree"
                        " %d %s, ofInt 0) := by" % (cfg7, key, key, 64 - LEVELS, Lz)).split(" "), "    ")
        body += ["  unfold CertModel.polyProduct",
                 "  rw [if_neg (by decide +kernel), if_neg (by decide +kernel),",
                 "    adviceLookup_append_cseg _ _ _ (by decide +kernel), lock_g%sDirect]" % S, "",
                 "theorem lock_graph%s :" % thm,
                 "    checkRealLowerBound cert.graph.base.weight cert.graph.base.cfgLow",
                 "      %s" % fexpr,
                 "      %s %s cert.graph.%s = true := by" % (m0, m, key),
                 "  unfold checkRealLowerBound"]
        body += tac("rw [realLowerModel_eq_of_sq_cseg cert.graph.base.weight cert.graph.base.cfgLow %s %s"
                    " cert.graph.%s (mul_eq_of_polyProduct_cseg base.weight %s [7] _ _ lock_g%sSq)]"
                    % (fexpr, m0, key, cfg7, S))
        body += ["  decide +kernel"]
        files["Graph%s" % thm] = (base + ["%s.Pass.Graph%sC%d" % (NS, S, k) for k in range(n)] +
                                  ["%s.Pass.Graph%sGroups" % (NS, S)],
                                  "graph %s SOS by row chunks" % ("lower" if S == "Lo" else "upper"),
                                  "The SOS side from its %d chunk theorems (`SegGraph`)." % n, body)
    for rel, (imps, title, doc, body) in files.items():
        text = E.HEADER.format(imports="\n".join("public import " + i for i in sorted(set(imps))),
                               title="The N = 65 lock: %s" % title, doc=doc, ns=NS,
                               body="\n".join(opens + [""] + E.autowrap(body)).rstrip())
        text = text.replace("Generated by `scripts/spin_orbit/csplit_emit.py`", "Generated by "
                            "`scripts/spin_orbit/lock_graph.py`")
        for i, l in enumerate(text.splitlines()):
            assert len(l) <= 100, (rel, i, l)
        assert text.count("\n") <= 1500, (rel, text.count("\n"))
        open(os.path.join(pdir, rel + ".lean"), "w").write(text)
    print("lock graph", len(files), "modules", sum(len(f[3]) for f in files.values()), "lines")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
