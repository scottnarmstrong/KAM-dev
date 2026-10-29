# SO-ABK prover handoff (branch inp-soabk, ba485492; track SO package run by the main orchestrator)


**Files:** new `KAM/Certificate/Arith/Fixed.lean` (~210 lines). Nothing else touched (KAM.lean is
generated; lint reports "KAM.lean is out of date": the orchestrator regenerates it).

**Approach:** `structure CertFixed (P) where m : ℤ`, `val a = m / 2^P`. `ulpDen P = ((2^P : ℕ) : ℤ)`
(Nat.pow literal, kernel-accelerated). `add`/`neg`/`upAdd`/`ofInt` exact (`addErr = 0`);
`mul = ⌊a.m*b.m / 2^P⌋` (`Int.ediv`), `mulErr = ⟨1⟩` (one ulp); `upMul` and `ofRatUp` use
`cdiv x d = -((-x)/d)` (ceiling), `ofRatDown` floors; `abs` via `Int.natAbs`; comparisons are
`decide` on `Int`. No wf recursion, no lists. Helpers `CertFixed.{ulpDen, cdiv, fdiv_bounds,
cdiv_bounds, val_def}`; the instance is `noncomputable` (the `val` field lands in `ℝ`) which does not
affect kernel evaluation. Names are `instCertArithFixed`/`instLawfulCertArithFixed` as in SOSignatures.

**Checks:**
- `inp_lake_build.sh KAM.Certificate.Arith.Fixed`: "Build completed successfully", no warnings in Fixed.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only
  note "KAM.lean is out of date" (generated; not edited by me).
- No `maxHeartbeats`, `native_decide`, `EuclideanSpace`, axiom, sorry; lines ≤ 100.
- `decide +kernel` examples (all pass): P=64 true/false controls for ble/blt/beq/upAdd/upMul;
  P=448: `mul` rounding sandwich (true and false control), `certCExpSmall` (true), and
  `checkPiEnclosure` with Machin (50,15) (true; false control with rad = 0).

**Kernel timings** (profiler, threshold 100ms): the whole file's examples type-check in ~0.65 s
total; the two slowest examples took 404 ms and 239 ms (the P=448 π-enclosure pair); all others
< 100 ms. Whole-file build 4.9 s incl. proofs.

**`#print axioms`:** `instCertArithFixed`, `instLawfulCertArithFixed`: propext, Classical.choice,
Quot.sound.

**Uncertainties / errata / deviations:** none. `upAdd` is exact (≥ the sum trivially). `ofRatUp`
is the tight ceiling; `ofInt z` is exact `z·2^P`.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean section A 'Backends' (CertFixed P, instCertArithFixed, instLawfulCertArithFixed). Production backend chosen after the replay gate (SO-REPLAY recommendation: fixed point with a global scale 2^P). Check EVERY LawfulCertArith law (KAM/Certificate/Arith/Interface.lean) is proved for the actual operations, in particular the directed-rounding laws (ofRatUp >= q, ofRatDown <= q, upMul >= the exact product, mulErr bounds the floor error of mul for ALL signs, including negative operands where Int.ediv rounds toward minus infinity), and that the decide +kernel examples reduce in the kernel with false controls.

AUDIT FOCUS: the signed declarations match the draft signatures verbatim; every law is proved soundly with no added premise; the slice is complete. Audit ONLY KAM/Certificate/Arith/Fixed.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
