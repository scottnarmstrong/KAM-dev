# SO-NORM prover handoff (branch inp-sonorm, 1c254591; track SO package run by the main orchestrator)


## Files
New: `KAM/Certificate/NormBridge.lean` (257 lines, module). No other file touched.
`KAM.lean` is not regenerated (rule 10): `lint_sources.sh` reports "KAM.lean is out of date; run
scripts/gen_root_imports.py" — orchestrator to regenerate.

## Signed declarations (all in `KAM.Certificate`, types verbatim from SOSignatures §E)
`norm_fderiv_le_sum_partials`, `norm_iteratedFDeriv_two_le_sum_partials`,
`hamiltonianVectorFieldℂ_sumVec`, `norm_fderiv_hamiltonianVectorFieldℂ_le` (hn : 1 ≤ n),
`norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (hn : 1 ≤ n). No signed statement was false;
`n` is a section `variable {n : ℕ}` (same binder order/implicitness as signed).

## Approach
* Phase-basis expansion `sum_sumVec_smul_phaseBasis`; `norm_clm_le_sum_phaseBasis` (any normed
  codomain) gives thm 1; `norm_cmm_two_le_sum_phaseBasis` (curryLeft twice) gives thm 2.
* `X_H` coordinates: `sumVec (X_H z) a = hamSign a * fderiv H z (phaseBasis a.swap)`.
* `DX_H`: `sumVec (D X_H w v) a = hamSign a * D²H w v e_{swap a}` (chain rule through `sumVecIso`),
  symmetry of `D²H` (`ContDiffAt.isSymmSndFDerivAt`), expansion of `v` in the phase basis.
* `D²X_H`: `‖D²(sumVecIso ∘ X_H)‖ = ‖D²X_H‖`; coordinatewise via `iteratedFDeriv_comp_left`
  with `proj a`, then with `apply e ∘ fderiv H`; gives `hamSign a * D³H[m0,m1,e]`. Third-derivative
  symmetry is not in Mathlib: proved the rotation `D³H[u,v,e] = D³H[e,u,v]` from two swaps
  (`iteratedFDeriv_three_swap_last` via symmetry of `D²H` at nearby points,
  `iteratedFDeriv_three_swap_first` via symmetry of `D²(fderiv H)`), then bounded the bilinear
  form `fderiv (iteratedFDeriv 2 H) z e` by thm-2 style expansion.
Public helper names (all unique in KAM): `sum_sumVec_smul_phaseBasis`, `norm_sumVec_apply_le`,
`norm_clm_le_sum_phaseBasis`, `norm_cmm_two_le_sum_phaseBasis`, `phaseBasis_inl`, `hamSign`,
`norm_hamSign`, `sumVec_hamiltonianVectorFieldℂ_swap`, `hamiltonianVectorFieldℂ_eq_symm`,
`sumVec_fderiv_hamiltonianVectorFieldℂ`, `iteratedFDeriv_three_apply`,
`iteratedFDeriv_three_swap_first/_last`, `iteratedFDeriv_three_rotate` (grep: no other use of any).

## Checks
* `inp_lake_build.sh /root/code/KAM-inp-sonorm KAM.Certificate.NormBridge`: Build completed
  successfully, no warnings.
* `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only
  the "KAM.lean out of date" notice (generated file, not mine to edit). No lines > 100.
* No sorry/axiom/maxHeartbeats/native_decide/EuclideanSpace in the file.
* `#print axioms` of all five main results: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
None; no defects found in sources. Imports `Mathlib.Analysis.Calculus.FDeriv.Symmetric` and
`ContDiff.Comp` directly (plus PhaseBasis and the frozen HamiltonianVectorFieldC def).

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4, passed its design audit); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section E, including the Revision 3 F8 hypotheses (1 <= n). These bridges turn the checker's row-sum bounds of partial derivatives into the operator norms that IG1Body (KAM/Iso/Apost) consumes: check the norms are EXACTLY the ones IG1Body uses (same norm on C^n x C^n, same carriers), so that the black box's soundness composes.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/NormBridge.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
