"""Independent replay of hh-cert.json with the RAW (unmerged) semantics of the Lean definitions.

usage: python3 -B -I verify.py <hh-cert.json>
Mirrors checkOscChain / oscillatorChain_physical conjunct by conjunct.  Raw term lists are kept as
multisets {(key, coeff): multiplicity}; this is exactly the Lean list semantics, since cartBracket is
linear per raw term and cartSupBound sums over raw terms.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import factorial
from collections import defaultdict
from qs import QS

N = 2
cert = json.load(open(sys.argv[1]))


def qs(d):
    return QS(F(d["a"]), F(d["b"]))


def load(pl):
    out = []
    for m in pl:
        a = (m["a"] + [0] * N)[:N]; b = (m["b"] + [0] * N)[:N]
        assert len(m["a"]) <= N and len(m["b"]) <= N, "exponent past n"   # cartFitsB
        out.append((tuple(a) + tuple(b), qs(m["c"])))
    return out


def toraw(lst):
    c = defaultdict(int)
    for k, v in lst:
        c[(k, v)] += 1
    return c


def raw_dq_dp_mul(P, Q, i):
    """cartMul (cartDq i P) (cartDp i Q) - cartMul (cartDp i P) (cartDq i Q), all raw (multisets)."""
    out = defaultdict(int)
    for (k1, v1), n1 in P.items():
        for (k2, v2), n2 in Q.items():
            if k1[i] > 0 and k2[N + i] > 0:
                k = list(k1); k[i] -= 1
                k = [x + y for x, y in zip(k, k2)]; k[N + i] -= 1
                out[(tuple(k), v1 * k1[i] * v2 * k2[N + i])] += n1 * n2
            if k1[N + i] > 0 and k2[i] > 0:
                k = list(k1); k[N + i] -= 1
                k = [x + y for x, y in zip(k, k2)]; k[i] -= 1
                out[(tuple(k), -(v1 * k1[N + i] * v2 * k2[i]))] += n1 * n2
    return out


def raw_bracket(P, Q, width=N):
    out = defaultdict(int)
    for i in range(width):
        for kv, n in raw_dq_dp_mul(P, Q, i).items():
            out[kv] += n
    return out


def raw_adpow(chi, k, P):
    for _ in range(k):
        P = raw_bracket(P, chi)
    return P


def raw_smul(c, P):
    return {(k, v * c): n for (k, v), n in P.items()}


def raw_liesum(chi, H, L):
    out = defaultdict(int)
    for j in range(L):
        for (k, v), n in raw_adpow(chi, j, H).items():
            out[(k, v * QS(F(1, factorial(j))))] += n
    return out


def normalize(raw):
    acc = {}
    for (k, v), n in raw.items():
        acc[k] = acc.get(k, QS(0)) + v * n
    return {k: v for k, v in acc.items() if not v.iszero()}


def eqcheck(raw1, raw2):
    neg = defaultdict(int)
    for kv, n in raw1.items():
        neg[kv] += n
    for (k, v), n in raw2.items():
        neg[(k, -v)] += n
    return len(normalize(neg)) == 0


def supbound(raw, rho):
    s = F(0)
    for (k, v), n in raw.items():
        s += n * v.absub() * rho ** sum(k)
    return s


def action(j):
    a = [0] * (2 * N); a[j] = 2
    b = [0] * (2 * N); b[N + j] = 2
    return {(tuple(a), QS(F(1, 2))): 1, (tuple(b), QS(F(1, 2))): 1}


def dq_raw(P, i):
    out = defaultdict(int)
    for (k, v), n in P.items():
        if k[i] > 0:
            kk = list(k); kk[i] -= 1
            out[(tuple(kk), v * k[i])] += n
    return out


def dp_raw(P, i):
    out = defaultdict(int)
    for (k, v), n in P.items():
        if k[N + i] > 0:
            kk = list(k); kk[N + i] -= 1
            out[(tuple(kk), v * k[N + i])] += n
    return out


def pow_prod_action(kq):
    """cartActSubst for one Nact monomial (coefficient excluded): prod_L (cartAction L)^{kq[L]} as raw."""
    cur = {((0,) * (2 * N), QS(1)): 1}
    for L in range(len(kq)):
        for _ in range(kq[L]):
            nxt = defaultdict(int)
            for (k1, v1), n1 in cur.items():
                for (k2, v2), n2 in action(L).items():
                    nxt[(tuple(x + y for x, y in zip(k1, k2)), v1 * v2)] += n1 * n2
            cur = nxt
    return cur


res = []


def chk(name, ok, detail=""):
    res.append((name, bool(ok), detail))
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""), flush=True)


H = toraw(load(cert["H"]))
Nact = load(cert["Nact"])
P = toraw(load(cert["P"]))
dc = F(cert["dc"]); epsb = F(cert["epsb"]); T = F(cert["T"])
a = [F(x) for x in cert["a"]]; b = [F(x) for x in cert["b"]]; eta = [F(x) for x in cert["eta"]]; r = [F(x) for x in cert["r"]]
steps = cert["steps"]
chk("cartActOnly Nact (b exponents zero)", all(sum(k[N:]) == 0 for k, _ in Nact))
chk("cartFitsB (n=2)", True)

# oscChainOKB
Q = H
bound = F(0)
tail_list = []
for idx, s in enumerate(steps):
    gen = toraw(load(s["gen"])); out = toraw(load(s["out"]))
    L = s["order"]; rho = F(s["rho"]); delta = F(s["delta"]); eps = F(s["eps"])
    chk(f"step{idx+1} 0<delta,0<=eps<=1/2,1<=order", delta > 0 and 0 <= eps <= F(1, 2) and L >= 1)
    for i in range(N):
        mq = supbound(dq_raw(gen, i), rho); mp = supbound(dp_raw(gen, i), rho)
        chk(f"step{idx+1} i={i} supBound dq/dp <= eps*delta", mq <= eps * delta and mp <= eps * delta, f"{float(mq):.3e},{float(mp):.3e} <= {float(eps*delta):.3e}")
    lie = raw_liesum(gen, Q, L)
    chk(f"step{idx+1} cartEqCheck(cartLieSum chi Q L={L}) out   [raw terms {sum(lie.values())}]", eqcheck(lie, out))
    bound += supbound(raw_adpow(gen, L, Q), rho) / factorial(L)
    Q = out
nsub = defaultdict(int)
for k, v in Nact:
    for (kk, vv), n in pow_prod_action(k[:N]).items():
        nsub[(kk, vv * v)] += n
for kv, n in P.items():
    nsub[kv] += n
chk("final cartEqCheck(Q_m, cartActSubst Nact + P)", eqcheck(Q, nsub))
# oscDomOKB
for idx in range(len(steps)):
    s = steps[idx]; ta = sum(F(t["eps"]) * F(t["delta"]) for t in steps[idx + 1:])
    rho = F(s["rho"]); delta = F(s["delta"])
    for i in range(N):
        chk(f"dom step{idx+1} i={i}", r[i] + ta + delta < rho and r[i] + dc + ta + delta / 2 < rho)
tail = sum(F(t["eps"]) * F(t["delta"]) for t in steps)
chk("0<dc, 0<epsb, 0<=T", dc > 0 and epsb > 0 and T >= 0)
for j in range(N):
    br = raw_bracket(action(j), P, width=j + 1)   # cartWidth (cartAction j) = j+1
    sb = supbound(br, r[j])
    rhs = eta[j] - 2 * r[j] * bound / dc
    chk(f"j={j} 0<=r, 2(b+epsb)<=r^2, 0<=eta", r[j] >= 0 and 2 * (b[j] + epsb) <= r[j] ** 2 and eta[j] >= 0)
    chk(f"j={j} supBound(bracket(cartAction j,P)) <= eta - 2rB/dc", sb <= rhs, f"{float(sb):.3e} <= {float(rhs):.3e}; B={float(bound):.3e}")
    chk(f"j={j} a + T eta < b", a[j] + T * eta[j] < b[j], f"{float(a[j]+T*eta[j]):.3e} < {float(b[j]):.3e}")
ph = cert["physical"]
ap = [F(x) for x in ph["a_phys"]]; sv = [F(x) for x in ph["s"]]; dv = [F(x) for x in ph["d"]]
for j in range(N):
    chk(f"phys j={j} hs0,hs1 (0<=s, 2a'<=s^2)", sv[j] >= 0 and 2 * ap[j] <= sv[j] ** 2)
    c = F(0); ok = True
    for t in steps:
        ok &= sv[j] + c + F(t["delta"]) < F(t["rho"]); c += F(t["eps"]) * F(t["delta"])
    chk(f"phys j={j} hs2 OscPhysDom", ok)
    chk(f"phys j={j} hs3 (s+tail)^2<=a", (sv[j] + tail) ** 2 <= a[j], f"{float((sv[j]+tail)**2):.4e} vs a={float(a[j]):.4e}")
    chk(f"phys j={j} hd tail(2r+tail)<=d", tail * (2 * r[j] + tail) <= dv[j], f"{float(tail*(2*r[j]+tail)):.3e} <= {float(dv[j]):.3e}")
    chk(f"phys j={j} d<=1e-10", dv[j] <= F(1, 10 ** 10))
    chk(f"phys j={j} conclusion a+eta T+d<101e-10 and 2d+eta T<=12e-10", a[j] + eta[j] * T + dv[j] < F(101, 10 ** 10) and 2 * dv[j] + eta[j] * T <= F(12, 10 ** 10))
print("SUMMARY: %d checks, %d failed: %s" % (len(res), sum(1 for x in res if not x[1]), [x[0] for x in res if not x[1]]))
