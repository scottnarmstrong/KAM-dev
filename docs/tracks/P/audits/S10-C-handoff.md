# S10-C prover handoff (branch inp-s10c, 45970cd; contains inp-s10j and inp-s10z (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Nondegeneracy/FiniteType.lean` (~445 lines). No other file touched; KAM.lean not edited
(lint reports it out of date: the orchestrator regenerates it). Imports: DiagonalTensor, AnalyticZeros only (no provider,
no frozen theorem).

**Declarations (signatures verbatim; only whitespace re-wrapping of the long `hCont` binder line in `finite_type`):**
`betaFamily`, `sphere`, `squaredForm`, `betaMu`, `index_def`, `finite_type`, `index_amount`, `cp09_lemma1`,
`cp09_unsquared`, `cp09_product` (all in `KAM.Planetary.Nondegeneracy`).

**Approach.**
- `scalarJet` is `jetOp ∘ iteratedFDeriv` with `jetOp` 1-Lipschitz in the operator norm, so jets and `jetMax`
  (recursion `jetMax (μ+1) = max (jetMax μ) (scalarJet (μ+1))`) are continuous on any set where `hCont` holds; `jetMax` is monotone in μ.
- `finite_type`: pointwise step (all diagonal jets zero => power series zero via `HasFPowerSeriesOnBall.factorial_smul`,
  so f vanishes near the point, hence on B by the identity theorem; polarization not needed), finite subcover of `C0 ×ˢ K` by the relatively
  open sets {jetMax ν > 0}, monotonicity gives one μ, the infimum is attained (`betaFamily_attained`).
- `index_amount`: pure order theory (`Nat.find_spec`, `Nat.find_min'`, monotone infimum); its compactness/continuity
  hypotheses are carried but unused (as in the signature).
- CP09 corollaries: one lemma `expansion` (g c y = ∑ₖ pₖ(c) hₖ(y), pₖ continuous, hₖ analytic on B => analytic in y and
  jointly continuous iterated derivatives), applied with index `Fin m × Fin m` (squared), `Fin m` (unsquared),
  `∀ l, Fin (dims l)` (product). Product nonvanishing uses `generic` of S10-Z for a common non-zero point.

**Checks.** `inp_lake_build.sh /root/code/KAM-inp-s10c KAM.Planetary.Nondegeneracy.FiniteType` (also DiagonalTensor, AnalyticZeros):
"Build completed successfully", no warnings in FiniteType. `sh scripts/lint_sources.sh`: only "KAM.lean is out of date";
check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. No sorry/axiom/maxHeartbeats; all lines <=100.

**`#print axioms`** (run in file, then removed): `finite_type`, `index_amount`, `cp09_lemma1`, `cp09_unsquared`,
`cp09_product` each depend only on [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations / design signals:** none. `finite_type` and `index_amount` do not use `hB`
(openness) resp. `hC hK hCont`; they are silenced with `have _ := ...`. Design says `f_pol` feeds this package;
it was not needed (the power-series route avoids polarization). No heartbeat problems.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-C and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (sphere, squaredForm, betaFamily, betaMu, index_def, finite_type, index_amount, cp09_lemma1, cp09_unsquared, cp09_product); definitions faithful on their whole carrier (index_def: infimum attained where the design requires); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY Nondegeneracy/FiniteType*.lean (compare with branch inp-s10j).
