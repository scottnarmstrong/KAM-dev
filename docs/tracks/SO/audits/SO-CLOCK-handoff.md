# SO-CLOCK prover handoff (branch inp-soclock, 0ba16e09; off inp; track SO package run by the main orchestrator)


## Files (branch inp-soclock)
- `KAM/Certificate/PhaseBasis.lean` (new, ~35 lines): `KAM.Certificate.phaseBasis` verbatim from
  SOSignatures §D, plus helper `phaseBasis_inr : phaseBasis (.inr j) = (0, Pi.single j 1)`.
- `KAM/Certificate/Clock.lean` (new, 204 lines): `KAM.Certificate.clock_frequency`, signed type verbatim.

## Approach
- `s∞ω*_j = 1`: w(θ) = K∞,j(θ) − θ_j is holomorphic and 1-periodic on the strip (from
  `IsPrimaryOnStrip`); the j-th angle invariance equation plus `hH1` gives D_ω K∞,j = 1 with
  ω = s∞ω*, so D_ω w = 1 − ω_j; its torus average is 0 (`torusAverage_complex_direction_eq_zero`).
- Constancy: `torusCoeff_fderiv` gives 2πi(k·ω)·ŵ_k = coeff of D_ω w = 0; `IsDiophantine` with γ>0
  gives k·ω ≠ 0 for k ≠ 0, so ŵ_k = 0 for k ≠ 0; `eq_zero_of_torusCoeff_eq_zero` applied to
  w − avg w gives w constant on reals; `IsRealOnReals` at 0 gives the real constant c = z.1 j.
- No extra hypotheses; `hH1` is used only through `D` containing the range of K∞ on the strip.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-soclock KAM.Certificate.Clock` -> `Build completed successfully
  (3163 jobs)`; PhaseBasis built likewise. No warnings in the files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
  message is `KAM.lean is out of date; run scripts/gen_root_imports.py` (generated file, not edited
  by me; orchestrator to regenerate for the two new modules).
- `#print axioms KAM.Certificate.clock_frequency` -> [propext, Classical.choice, Quot.sound]
  (same for `phaseBasis_inr`).
- Lines ≤ 100 columns, no maxHeartbeats, no sorry/native_decide, no EuclideanSpace.

## Uncertainties / coordination
- `phaseBasis` is not yet in KAM (SO-EXPR will define it per design §D). I put the verbatim def in the
  tiny module `KAM/Certificate/PhaseBasis.lean` so Clock needs no Expr dependency. **SO-EXPR must
  `public import KAM.Certificate.PhaseBasis` and delete its own `phaseBasis` def** (otherwise a
  duplicate-declaration clash on merge). Same definition, same namespace `KAM.Certificate`.
- Design signal: none (no heartbeat issues). No suspected errata; no deviations from the signature.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md). The signatures are the DRAFT design signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean (Revision 1; Revision 2 is in progress for unrelated findings: frequency interface, arithmetic laws, torsion, division; it does not change §D phaseBasis or §H clock_frequency unless it says so).

AUDIT FOCUS: (1) phaseBasis and clock_frequency match the draft signatures (§D, §H) VERBATIM; (2) the proof of proposal §7.1 (/root/code/KAM/docs/explorations/lunar-spin-orbit-certificate-proposal.md): from IsPrimaryOnStrip, the invariance equation and the Diophantine condition, the output frequency scalar is forced (s_inf omega_star_j = 1 for the clock coordinate) and the clock correction w is constant and real; check the averaging step on the complex strip, the Fourier-coefficient step, and that no premise is conclusion-shaped; (3) is the statement strong enough for its consumer (the lunar barrier: physical frequency exactly (nu, 1) and a constant phase shift)? Audit KAM/Certificate/Clock.lean and KAM/Certificate/PhaseBasis.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
