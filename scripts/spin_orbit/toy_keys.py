#!/usr/bin/env python3
"""SO-PYALIGN key-coverage test: the advice keys the Lean checker LOOKS UP, predicted from the emitted data.

Untrusted tooling.  An independent, support-only transcription of the Lean lookup order (it shares no code with
toy_model.py / toy_check.py).  Whether `CertModel.polyProduct` consults the advice book depends only on the KEY
SETS of its factors (`CertPoly.isConst`: every key all zero, the empty polynomial included), and the key set of
every model the checker builds is determined structurally: no Lean operation of the direct route drops a term
because of its coefficient value (zero coefficients are kept), only by key (`derivItem`: k_j = 0;
`deriv2Item`: k_j k_l = 0; `truncKeep`: |k|₁ > cutoff).  So propagating key sets through the checker
reproduces its lookups exactly (assuming every witness check passes, as for a passing certificate).

Lookup sites (Lean):
  Slp.compose (whole program, slot order)  `.mul a b` -> [0, slot] (cfg);  `.exp` witness i -> residual
      products [1, i, j] (forWitness 1 i, key [1, j]);  `.char` -> character witness c (normalized key, cache,
      -k reflection) -> [1, |expWit| + c, j];  `.inv` witness i -> [2, i] (forWitness 2 i, key [2]);
  checkInvariance, checkEnergy: compose at cfgFull; `[5, a, l]` is a scalar product (constant freqModel);
  gramCheck (cfgLow): [3, 0, a, b, r] (a <= b; the entries a > b recompute (b, a)), [3, 1, i, j, k];
  torsionModels (cfgLow): compose, [4, t, i, j, k] for t = 0..9; [4, 10, i, j, l] is scalar.

    python3 toy_keys.py JETS.json OUTDIR [toy ...]     (exit 1 on any mismatch; writes OUTDIR/key_coverage.json)
"""
import json, sys


def zeros(n):
    return (0,) * n


def pack(k, l):
    if len(k) < len(l):
        k, l = l, k
    return tuple(k[i] + (l[i] if i < len(l) else 0) for i in range(len(k)))


def gd(L, i, d=0):
    return L[i] if i < len(L) else d


def const(S):
    return all(all(z == 0 for z in k) for k in S)


class Pred:
    def __init__(self, cert, jet):
        self.c, self.jet, self.n = cert, jet, cert["n"]
        self.look = {"cfgFull": [], "cfgLow": []}
        self.cut = {"cfgFull": cert["cfgFull"]["cutoff"], "cfgLow": cert["cfgLow"]["cutoff"]}

    # ------------------------------------------------------------ key sets of data
    def real(self, P):
        if P is None:
            return set()
        half = [tuple(t[0]) for t in P["half"]]
        return {tuple(-x for x in k) for k in half} | {zeros(self.n)} | set(half)

    def poly(self, P):
        return {tuple(t[0]) for t in P}

    def ang(self, i):
        return gd(self.c["emb"]["angle"], i, None)

    def act(self, i):
        return gd(self.c["emb"]["action"], i, None)

    # ------------------------------------------------------------ products
    def mul(self, cfg, key, A, B, scalar_ok=True):
        if not (const(A) or const(B)):
            self.look[cfg].append(tuple(key))
        return {k for k in (pack(a, b) for a in A for b in B) if sum(abs(x) for x in k) <= self.cut[cfg]}

    # ------------------------------------------------------------ witnesses
    def residual(self, cfg, idx, g0, E):
        for j in range(self.n):
            dg = {k for k in g0 if gd(k, j) != 0}
            if not (const(dg) or const(E)):
                self.look[cfg].append((1, idx, j))

    def compose(self, cfg):
        n, c, wit = self.n, self.c, self.c["wit"]
        S, nExp, nInv, cache = [], 0, 0, {}
        slot = lambda i: S[i] if i < len(S) else set()
        zero_ang = lambda j: self.ang(j) is None or (not self.ang(j)["half"] and float(eval_q(self.ang(j)["zero"])) == 0)
        charkeys = [tuple(k) for k, _ in wit["charWit"]]

        def resolve(kk):
            if kk in cache:
                return cache[kk]
            if kk not in charkeys:
                return None
            ci = charkeys.index(kk)
            g0 = set()
            for j in range(n):
                if gd(kk, j) != 0:
                    g0 |= self.real(self.ang(j))
            E = self.poly(wit["charWit"][ci][1]["poly"])
            self.residual(cfg, len(wit["expWit"]) + ci, g0, E)
            cache[kk] = E
            return E

        for op in self.jet["ops"]:
            t = op[0]
            if t == "C":
                S.append({zeros(n)})
            elif t == "A":
                S.append(self.real(self.act(op[1])) if op[1] < n else set())
            elif t == "X":
                k = tuple(op[1])
                kk = tuple(0 if zero_ang(j) else gd(k, j) for j in range(n))
                E = resolve(kk)
                if E is None:
                    E = resolve(tuple(-x for x in kk))
                    assert E is not None, "no character witness for %s" % (kk,)
                    E = {tuple(-x for x in e) for e in E}
                    cache[kk] = E
                pk = tuple(gd(k, j) for j in range(n))
                S.append({pack(pk, e) for e in E})
            elif t == "+":
                S.append(slot(op[1]) | slot(op[2]))
            elif t == "*":
                S.append(self.mul(cfg, (0, len(S)), slot(op[1]), slot(op[2])))
            elif t == "E":
                E = self.poly(wit["expWit"][nExp]["poly"])
                self.residual(cfg, nExp, slot(op[1]), E)
                S.append(E)
                nExp += 1
            elif t == "I":
                Q = self.poly(wit["invWit"][nInv])
                if not (const(Q) or const(slot(op[1]))):
                    self.look[cfg].append((2, nInv))
                S.append(Q)
                nInv += 1
            else:
                raise ValueError(op)
        return slot

    # ------------------------------------------------------------ embedding matrices
    def deriv(self, P, j):
        return {k for k in P if gd(k, j) != 0}

    def dk(self, r, j):
        n = self.n
        if r < n:
            s = self.deriv(self.real(self.ang(r)), j)
            return s | {zeros(n)} if r == j else s
        return self.deriv(self.real(self.act(r - n)), j)

    def d2k(self, r, j, l):
        n = self.n
        P = self.real(self.ang(r)) if r < n else self.real(self.act(r - n))
        return {k for k in P if gd(k, j) * gd(k, l) != 0}

    def matmul(self, cfg, key, r, m, cc, X, Y):
        out = []
        for i in range(r):
            row = []
            for j in range(cc):
                s = set()
                for k in range(m):
                    s |= self.mul(cfg, tuple(key) + (i, j, k), X[i][k], Y[k][j])
                row.append(s)
            out.append(row)
        return out

    def run(self):
        n, c, jet = self.n, self.c, self.jet
        m2 = 2 * n
        # checkInvariance and checkEnergy: compose at cfgFull (twice; [5, a, l] scalar)
        self.compose("cfgFull")
        self.compose("cfgFull")
        # gramCheck at cfgLow (run by checkGram and again by checkTorsion)
        B = [[self.poly(P) for P in row] for row in c["gramInv"]]
        for _ in range(2):
            G = [[None] * n for _ in range(n)]
            for a in range(n):
                for b in range(n):
                    x, y = (a, b) if a <= b else (b, a)
                    s = set()
                    for r in range(m2):
                        s |= self.mul("cfgLow", (3, 0, x, y, r), self.dk(r, x), self.dk(r, y))
                    G[a][b] = s
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        self.mul("cfgLow", (3, 1, i, j, k), B[i][k], G[k][j])
        # torsionModels at cfgLow
        slot = self.compose("cfgLow")
        L = [[self.dk(r, j) for j in range(n)] for r in range(m2)]
        DL = [[set().union(*[self.d2k(r, j, l) for l in range(n)]) for j in range(n)] for r in range(m2)]
        T = lambda X: [list(col) for col in zip(*X)]
        om = lambda X: [X[n + i] for i in range(n)] + [X[i] for i in range(n)]
        madd = lambda X, Y: [[a | b for a, b in zip(r1, r2)] for r1, r2 in zip(X, Y)]
        N = om(self.matmul("cfgLow", (4, 0), m2, n, n, L, B))
        DG = madd(self.matmul("cfgLow", (4, 1), n, m2, n, T(DL), L), self.matmul("cfgLow", (4, 2), n, m2, n, T(L), DL))
        DGi = self.matmul("cfgLow", (4, 4), n, n, n, self.matmul("cfgLow", (4, 3), n, n, n, B, DG), B)
        DN = om(madd(self.matmul("cfgLow", (4, 5), m2, n, n, DL, B), self.matmul("cfgLow", (4, 6), m2, n, n, L, DGi)))
        d1 = [gd(jet["d1"], a) for a in range(m2)]
        d2 = [[gd(gd(jet["d2"], a, []), b) for b in range(m2)] for a in range(m2)]
        swap = lambda a: a + n if a < n else a - n
        DXH = [[slot(d2[swap(a)][b]) for b in range(m2)] for a in range(m2)]
        XN = madd(self.matmul("cfgLow", (4, 7), m2, m2, n, DXH, N), DN)
        self.matmul("cfgLow", (4, 8), n, m2, n, T(N), om(XN))
        self.matmul("cfgLow", (4, 9), 1, m2, n, [[slot(a) for a in d1]], N)
        return self.look


def eval_q(s):
    from fractions import Fraction
    return Fraction(s)


def coverage(cert, jet):
    pred = Pred(cert, jet).run()
    out, ok = {}, True
    for nm in ("cfgFull", "cfgLow"):
        emitted = [tuple(k) for k, adv in cert[nm]["advice"]]
        P, E = set(pred[nm]), set(emitted)
        r = dict(lookups=len(pred[nm]), lookedUpDistinct=len(P), emitted=len(emitted),
                 emittedDuplicates=len(emitted) - len(E), unused=sorted(map(list, E - P)),
                 missing=sorted(map(list, P - E)), allDirect=all(a == "direct" for _, a in cert[nm]["advice"]))
        r["ok"] = not r["unused"] and not r["missing"] and r["emittedDuplicates"] == 0 and r["allDirect"]
        ok = ok and r["ok"]
        out[nm] = r
    return ok, out


def main():
    jets = json.load(open(sys.argv[1]))["jets"]
    outdir = sys.argv[2]
    names = sys.argv[3:] or ["T2", "T2d", "T3", "TR"]
    res, allok = {}, True
    for name in names:
        cert = json.load(open("%s/%s.json" % (outdir, name)))["certificate"]
        ok, r = coverage(cert, jets["T2" if name == "TR" else name])
        res[name] = dict(r, ok=ok)
        allok = allok and ok
        print(name, "OK" if ok else "MISMATCH",
              {nm: (r[nm]["lookedUpDistinct"], r[nm]["emitted"], len(r[nm]["unused"]), len(r[nm]["missing"]))
               for nm in ("cfgFull", "cfgLow")}, flush=True)
    with open("%s/key_coverage.json" % outdir, "w") as fh:
        json.dump(dict(toys=res, all_ok=allok), fh, indent=1, sort_keys=True)
        fh.write("\n")
    if not allok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
