#!/usr/bin/env python3
"""SJS-PLAN experiment E2: moving a packed model into the kernel as a literal stored in an .olean (no soundness).

The Lean decimal/hex parser folds n*10+d, which is quadratic in the digits.  A ledger literal must arrive another way:
a file of raw little-endian bytes is read at elaboration time, joined by a balanced shift tree, and added as a definition
whose body is one Nat literal.  This writes Producer.lean (reads FILE, declares `PKL.a : Nat := <lit>`) and Consumer.lean
(imports it, runs one kernel product on the literal).  Run with: lean -o .drafts/lit/Producer.olean ...
Usage: literal_probe_gen.py DIR --mb M
"""
import argparse, os, hashlib

PRODUCER = r"""
import Lean
open Lean Elab Command

set_option profiler true
set_option profiler.threshold 100

/-- little-endian bytes [lo, hi) to a Nat, balanced -/
partial def bytesToNat (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi - lo ≤ 8 then
    (List.range (hi - lo)).foldr (fun i acc => acc * 256 + (b.get! (lo + i)).toNat) 0
  else
    let mid := lo + (hi - lo) / 2
    bytesToNat b lo mid + (bytesToNat b mid hi <<< (8 * (mid - lo)))

run_cmd do
  let b ← IO.FS.readBinFile "{path}"
  let t0 ← IO.monoMsNow
  let n := bytesToNat b 0 b.size
  let t1 ← IO.monoMsNow
  logInfo m!"bytes {{b.size}}, join {{t1 - t0}} ms, log2 {{n.log2}}"
  let decl := Declaration.defnDecl {{
    name := `PKL.a, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit n,
    hints := .abbrev, safety := .safe }}
  liftCoreM (addDecl decl)
  let t2 ← IO.monoMsNow
  logInfo m!"addDecl {{t2 - t1}} ms"
"""

CONSUMER = r"""
import Producer

set_option profiler true
set_option profiler.threshold 100

theorem t_lit : (PKL.a &&& 1) ≤ 1 := by decide +kernel
theorem t_mul : ((PKL.a * PKL.a) >>> 8) != 0 := by decide +kernel
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--mb", type=float, required=True)
    a = ap.parse_args()
    os.makedirs(a.dir, exist_ok=True)
    n = int(a.mb * 1e6)
    p = os.path.join(a.dir, "data.bin")
    with open(p, "wb") as f:
        seed = b"sjs-plan"
        written = 0
        while written < n:
            h = hashlib.shake_256(seed + written.to_bytes(8, "little")).digest(1 << 20)
            f.write(h[:min(1 << 20, n - written)])
            written += 1 << 20
    open(os.path.join(a.dir, "Producer.lean"), "w").write(PRODUCER.format(path=p))
    open(os.path.join(a.dir, "Consumer.lean"), "w").write(CONSUMER)


if __name__ == "__main__":
    main()
