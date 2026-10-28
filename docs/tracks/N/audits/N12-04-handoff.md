# N12-04 prover handoff (branch inp-n1204, 66d3e86; contains inp-n1201 (N12-01, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Coefficients.lean` (~335 lines). Branch inp-n1204, committed. No other file touched
(KAM.lean not regenerated: lint reports "KAM.lean is out of date" solely because of this new module; orchestrator to run
scripts/gen_root_imports.py).

**Nodes:** `avgCoeff`, `avgBeta`, `avgQ` (bpN:p12:s-data#data) and `coef` (co-a..co-d, incl. polynomial-weight summability), all
copied verbatim from N12Signatures.lean, no signature change, no extra hypothesis.

**Approach:** inClass via `dom_eq` (`Dom n (ι''B) s s = complexDomain` by `actionNbhd_eq_polyNbhd`) + periodicity from `hf`.
(a) `coeff_differentiableOn`. (b) `KAM.decay_boundary_radius` at width s, A=1 gives e^{-2π s|k|} ≤ β_k.
(c) `coefficients_deriv` identifies fderiv in I with coeff of `dI j f`; Cauchy (`norm_fderiv_le_of_closedBall`, radius s/2) bounds
`dI j f` by 2/s on strip s/2; `decay_boundary_radius` at ρ=s/2 gives (2/s)β_k exactly.
(d) `hasSum_slice` (eq_fourierSumVec_torusCoeffW + summableWeighted_torusCoeffW + summable_character_smul) at real angles, ρ=s/2.
(e) same for `dtheta j f` (coefficient = 2πi k_j f̂_k via `coefficients_deriv`), negated; real partial of Re(f∘ι) equals the complex
derivative (`real_partial`: Im(f∘ι)≡0 on open Wdom). (f) (1+m)³ ≤ 6/c³ e^{c(1+m)} with c=πs/2, comparison with
`hasSum_exp_neg_modeSize`.

**Checks:**
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-n1204 KAM.Nekhoroshev.Averaging.Coefficients` → "Build completed successfully (3179 jobs)", no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only note: KAM.lean out of date (generated; not edited).
- `#print axioms KAM.Nekhoroshev.coef` → [propext, Classical.choice, Quot.sound].
- No sorry/maxHeartbeats; no provider/DRAFT_SORRY imports (imports: Averaging.Field, Weighted.Coefficients).

**Uncertainties / errata / deviations:** none. No statement was false or under-hypothesised. No heartbeat design signals.
Note: β_k = e^{-π s|k|} is weaker than the true decay e^{-2π s|k|} used in (b); fine as stated.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-04 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements/definitions = design signatures (avgCoeff, avgBeta, avgQ, coef, polynomial-weight summability), faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the Coefficients module (compare with branch inp-n1201).
