# SO-GRAPHR prover handoff (branch inp-sographr, c2bcc8ef; track SO package run by the main orchestrator)


**Files:** new `KAM/SpinOrbit/Graph/Rot.lean` (224 lines). No other file touched (KAM.lean is stale; the
orchestrator regenerates it).

**Declarations (names and types verbatim from SOSignaturesLunar.lean §I.5):**
- `KAM.SpinOrbit.SoGraph.torus_of_rot` (shear to the generic `SoGraph.Torus`).
- `KAM.SpinOrbit.soBarrier_of_exact_rotTorus` (rotated exact torus ⇒ `Nonempty (SoBarrier lo hi)`).
- Helper (not in signatures): `KAM.SpinOrbit.isDiophantine_smul_scale`: `IsDiophantine γ τ ω → 0<s →
  IsDiophantine (s*γ) τ (s•ω)`.

**Approach:** `invarianceError_const_mul` turns the `c·H'` invariance into `H'` at `(c⁻¹ sinf) ωstar`;
`clock_frequency` (with `soRotHamExpr_clock`) gives `(c⁻¹ sinf) ωstar₁ = 1` and `Q₁ = θ₁ + c₀`;
`hamiltonianVectorFieldℂ_soRotHC` + `hamiltonianVectorFieldℂ_soHC` give the real flow
`Q₀' = P₀ - 1`, `P₀' = -∂_q V(Q₀+Q₁, Q₁)` at `(ν-1, 1)`; `torus_of_rot` then `soBarrier_of_torus`
(same packaging as `soBarrier_of_exact_torus`).

**Deviation (signature-compatible):** the brief note says `isDiophantine_smul` moves the Diophantine
condition; that lemma needs `s ≥ 1`, but here `s = c⁻¹` (c = 7/4 gives s < 1). I used the new
`isDiophantine_smul_scale` (γ becomes `c⁻¹γ`, still positive). The signed statement is unchanged.

**Checks:**
- `inp_lake_build.sh … KAM.SpinOrbit.Graph.Rot`: Build completed successfully (3209 jobs), no warnings in Rot.lean.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only note:
  "KAM.lean is out of date" (generated, not edited by me).
- `main_shortname_check.py … KAM.SpinOrbit.Graph.Rot`: OK.
- 0 lines over 100 columns; no maxHeartbeats, no sorry/axiom/native_decide.
- `#print axioms soBarrier_of_exact_rotTorus` and `torus_of_rot`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata:** none. No signed statement was false.

CONTEXT: owner ruling O5 (/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md): the lunar client in rotated angles. Design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md Revision 6, row SO-GRAPHR; signatures /root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean, the SpinOrbit/Graph/Rot part. Stacked on inp-sorot (SO-ROT, landed). Check: the wrapper uses SO-GRAPHM's landed generic core (SoGraph.Torus, soBarrier_of_torus) with the rotated frequency, and SO-ROT's map back to (q, p, phi) so that the result is an invariant barrier of the ORIGINAL lunar flow in the exact sense of SO-CONF's SoBarrier (KAM/SpinOrbit/Barrier.lean); the exact-torus hypotheses are exactly what the isoenergetic theorem plus the clock lemma deliver in the rotated frame; no conclusion-shaped premise.

AUDIT FOCUS: signed declarations match verbatim; soundness with no added premise; the slice complete. Audit ONLY KAM/SpinOrbit/Graph/Rot.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
