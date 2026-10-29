# SO-RFREQ prover handoff (branch inp-sorfreq, eab2bb8b; track SO package run by the main orchestrator)


**Files:** new `KAM/SpinOrbit/RotFreq.lean` (~85 lines). Nothing else touched.

**Declarations (all in `KAM.SpinOrbit`, signed types verbatim):** `lunarRotFreq`, `lunarRotFreqMinus_eq`,
`lunarRotFreqPlus_eq`, `isDiophantine_smul`, `lunarRotFreqMinus_isDiophantine`,
`lunarRotFreqPlus_isDiophantine`. Private helpers: `algFreq_two'`, `lunarRotFreq_eq_smul`.

**Approach:** `_eq`: rewrite `algFreq` on a 2-vector, `lunarNu±_eq`, `fin_cases`, `ring`.
`isDiophantine_smul`: pull `t` out of the sum, `abs_mul`, scale the hypothesis.
Diophantine: `lunarRotFreq ν κ = κ • ![ν-1, 1]`, SO-ROTDIO's `lunarNu±_rot_isDiophantine`, smul, `ring`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-sorfreq KAM.SpinOrbit.RotFreq`: "Build completed successfully (2199 jobs)", no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK, short-name check OK.
  It reports only "KAM.lean is out of date" (expected: generated root, not edited by me).
- `main_shortname_check.py`: no reused public short name.
- `#print axioms` of all five theorems: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties:** none. `KAM.Iso.Linear.isDiophantine_smul` (different statement, `1 ≤ s`) shares the short name but
the check passes; the signed name was kept. **Errata/deviations:** none.

CONTEXT: owner ruling O5 (/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md): the lunar client in rotated angles, frequency (nu -+ - 1, 1). Design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md Revision 5 (its round-5 audit is running), row SO-RFREQ; signatures /root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean, the SpinOrbit/RotFreq part. Stacked on inp-sorotdio (SO-ROTDIO, passed: the rotated Diophantine theorems). Check that the exact rotated frequencies are EXACTLY (lunarNu{Minus,Plus} - 1, 1) as landed (KAM/Certificate/QuadraticDiophantine.lean), that the rational boxes provably enclose them, and that the Diophantine facts used are the SO-ROTDIO theorems.

AUDIT FOCUS: signed declarations match verbatim; soundness with no added premise; the slice complete. Audit ONLY KAM/SpinOrbit/RotFreq.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.

## Round 2 (orchestrator naming repair, commit 3ddbaff8)

Audit 1: proofs and types PASS; FAIL only because the SIGNED name isDiophantine_smul reuses the short name of
KAM/Iso/Linear/Tools.lean:38. The orchestrator renamed it to soIsDiophantine_smul (statement unchanged; the design's
Revision 6 renames it in SOSignaturesLunar.lean). Rebuilt through the compile gate: success.
ROUND 2 FOCUS: naming closed; statement unchanged apart from the name. Verdict.
