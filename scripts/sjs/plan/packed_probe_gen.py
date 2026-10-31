#!/usr/bin/env python3
"""SJS-PLAN experiment E1: a GMP-resident packed model product in the Lean kernel (measurement device, no soundness).

Writes one Lean file (no Mathlib, plain `import Init`) with `decide +kernel` theorems on pseudo-random packed models of
n digits, cell width w, payload p bits:
  t_gen    forces the two operands (baseline to subtract);
  t_mul    the signed Kronecker product |A||B| and its offset form;
  t_round  mul + per-cell round (mask, shift) + overflow check (mask compare);
  t_full   t_round + central truncation + bit-parallel |.| split + digit-sum norm (mod 2^w - 1) of one shell mask;
  t_mid    t_full + weighted norm by one middle product with a packed weight table.
Every step is O(1) big-integer operations; nothing walks the digits.  Each theorem is checked separately, so each pays its
own generator (the kernel caches do not survive a declaration).  Usage: packed_probe_gen.py OUT.lean --n N [--w W] [--p P]
  [--only t_gen,t_mul,...]
"""
import argparse, math

TEMPLATE = r"""
set_option profiler true
set_option profiler.threshold 100

namespace PK

/-- repunit: n cells of width w, value 1 in each. -/
def rep (w n : Nat) : Nat := ((1 <<< (w * n)) - 1) / ((1 <<< w) - 1)

/-- `bits` pseudo-random bits: a power of three, squared j times, truncated. -/
def rnd (e j bits : Nat) : Nat := (Nat.rec (3 ^ e) (fun _ x => x * x + 1) j : Nat) % (1 <<< bits)

def N : Nat := {n}
def W : Nat := {w}
def P : Nat := {p}
def Q : Nat := {q}

def U : Nat := rep W N
def U2 : Nat := rep W (2 * N)

/-- offset digits in [0, 2^p): random bits masked cell by cell -/
def A' : Nat := rnd {e} {j} (W * N) &&& (((1 <<< P) - 1) * U)
def B' : Nat := rnd {e2} {j} (W * N) &&& (((1 <<< P) - 1) * U)

def oA : Nat := (1 <<< (P - 1)) * U

/-- signed packed integers |A|, sign -/
def absA : Nat := if oA ≤ A' then A' - oA else oA - A'
def absB : Nat := if oA ≤ B' then B' - oA else oA - B'
def sg : Bool := (decide (oA ≤ A')) == (decide (oA ≤ B'))

def C : Nat := absA * absB
def oC : Nat := (1 <<< (W - 1)) * U2
def Coff : Nat := if sg then oC + C else oC - C

/-- clear the low Q bits of every cell, then shift: cells stay aligned -/
def RM : Nat := ((1 <<< W) - (1 <<< Q)) * U2
def D : Nat := (Coff &&& RM) >>> Q
/-- back to offset digits of P bits; a digit out of range sets a bit of HM -/
def oD : Nat := ((1 <<< (W - 1 - Q)) - (1 <<< (P - 1))) * U2
def A2 : Nat := D - oD
def HM : Nat := (((1 <<< W) - 1) - ((1 <<< P) - 1)) * U2
def okRange : Bool := (A2 &&& HM) == 0

/-- central truncation -/
def A3 : Nat := (A2 >>> (W * (N / 2))) &&& ((1 <<< (W * N)) - 1)

/-- bit-parallel abs: t = 1 in the cells with digit >= 2^(p-1) -/
def T : Nat := (A3 >>> (P - 1)) &&& U
def mp : Nat := (T <<< P) - T
def Pd : Nat := (A3 &&& mp) - ((1 <<< (P - 1)) * T)
def mn : Nat := (((1 <<< P) - 1) * U) ^^^ mp
def Nd : Nat := ((1 <<< (P - 1)) * (U ^^^ T)) - (A3 &&& mn)
def Ab : Nat := Pd + Nd
/-- shell mask: every 7th cell; digit sum by casting out 2^w - 1 -/
def SM : Nat := ((1 <<< W) - 1) * rep (7 * W) (N / 7)
def shellSum : Nat := (Ab &&& SM) % ((1 <<< W) - 1)
/-- weights: 32-bit table, reversed order irrelevant here; middle digit of one product -/
def Wt : Nat := rnd {e3} {j} (W * N) &&& (((1 <<< 32) - 1) * U)
def wnorm : Nat := ((Ab * Wt) >>> (W * (N - 1))) &&& ((1 <<< W) - 1)

end PK
"""

THMS = {
    "t_gen": "theorem t_gen : (PK.A' + PK.B') != 0 := by decide +kernel",
    "t_mul": "theorem t_mul : PK.Coff != 0 := by decide +kernel",
    "t_round": "theorem t_round : PK.okRange = true := by decide +kernel",
    "t_full": "theorem t_full : (PK.okRange && (PK.shellSum != 0)) = true := by decide +kernel",
    "t_mid": "theorem t_mid : (PK.okRange && (PK.shellSum != 0) && (PK.wnorm != 0)) = true := by decide +kernel",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--w", type=int, default=460)
    ap.add_argument("--p", type=int, default=212)
    ap.add_argument("--only", default="t_gen,t_mul,t_round,t_full,t_mid")
    a = ap.parse_args()
    bits = a.n * a.w
    # generator: 3^e has 1.585 e bits, e <= 2^24 - 1 in the kernel; square j times to reach `bits`
    j = 0
    while (2 ** 22) * 1.585 * 2 ** j < bits * 1.02:
        j += 1
    e = max(1000, int(bits * 1.02 / 2 ** j / 1.585) + 1)
    q = a.p + int(math.ceil(math.log2(a.n))) // 2 + 2        # product digits ~ sqrt(n) 2^(2p-2): keep them in p bits
    src = TEMPLATE.format(n=a.n, w=a.w, p=a.p, q=q, e=e, e2=e + 1, e3=e + 3, j=j)
    src += "\n" + "\n".join(THMS[t] for t in a.only.split(",")) + "\n"
    open(a.out, "w").write(src)
    print("bits per operand %d, e %d, j %d, q %d" % (bits, e, j, q))


if __name__ == "__main__":
    main()
