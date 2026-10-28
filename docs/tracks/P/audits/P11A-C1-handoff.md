# P11A-C1 prover handoff (branch inp-p11ac1, 1517825; contains inp-p11ac0 (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Planetary/MaximalStep/FourierCutoffTail.lean` (~260 lines): `p11C_ge_one` (stepP:p11a:fc-const), `p11_tail_le`
  (fc-count, fc-poly, fc-assemble): `∑_{|k|₁>T} e^{-2πd|k|₁} ≤ p11Error n T d`.
- `KAM/Planetary/MaximalStep/FourierCutoffCoeff.lean` (~125 lines): `p11ParamEquiv`, `coeff_joint_differentiableOn`
  (joint holomorphy of û_k(η,b) on `polyNbhd {0} s ×ˢ B`, via `holomorphic_parametric_integral`).
- `KAM/Planetary/MaximalStep/FourierCutoff.lean` (~250 lines): `fourier_cutoff` (bpP:p11a:fourier-cutoff), statement
  copied verbatim from `P11ASignatures.lean` L229; helpers are private (`cf`, `p11Cut_eq_sum`, `slice_facts`, `cutoff_tail`).
No file under KAM/Frozen, manifest, KAM.lean, README touched. Imports: no provider, no frozen theorem anchor.

## Approach
Decay of coefficients by `KAM.decay_boundary_radius`, representation by `KAM.eq_fourierSumVec_torusCoeffW`
(fc-decay); character bound `norm_character_le` on the strip (fc-tail); lattice count through
`KAM.Measure.card_l1Sphere_le` (from `lattice_count`) grouped by shells, `KAM.Fourier.exp_sums` (a) for j^{N-1}e^{-πjd},
geometric tail. `p11Cut` is rewritten as a finite sum over `modeCutoff n ⌈T⌉₊` (admissibility, periodicity,
entireness in θ); realness via `torusCoeff_conjugateSymmetric` and `conj_character_real`, reindexing k ↦ -k.

## Checks
- `inp_lake_build.sh .. KAM.Planetary.MaximalStep.FourierCutoff` : Build completed successfully (only unused-variable
  lint for the signature's `hs`, and `if_pos`/`if_neg` deprecation warnings in FourierCutoffTail).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only message is
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, not edited by instruction; new modules need it).
- `#print axioms KAM.Planetary.fourier_cutoff` / `p11_tail_le` / `coeff_joint_differentiableOn`:
  [propext, Classical.choice, Quot.sound].

## Notes
- Signature has no defect found; `hs : 0 < s` is unused (kept verbatim). `p11C` n=2 case uses e<2.7182818286, π<3.15.
- No heartbeat problems; no overrides used. Suspected errata: none. Deviations: none (extra helper modules Tail/Coeff
  added beside the one in the module table).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C1 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (decay_boundary_radius, vector Fourier reconstruction, lattice_count); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY MaximalStep/FourierCutoff*.lean (compare with branch inp-p11ac0).
