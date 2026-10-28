# P23-20 prover handoff (branch inp-p2320, 1dbc4052; contains inp-p2318 (audited, PASS round 2) and P23-19; offloaded package run by the main orchestrator)


## Files (new; all < 250 lines)
ToriSetup (ToriLimit, StageSteps, iterative_all, tori_limit_of_iterative), ToriEstimates
(StripLimit.fderiv_tendsto, tori_complex_ext, tori_estimates_of_limit), ToriLagr
(tori_lagr_of_limit), ToriInvLimit (curve_limit_field), ToriInvField (hvf_continuousOn),
ToriInvStage (freq_lip, fderiv_f_le, field_err), ToriInvConj (conj_field, psiR_fderiv_bound),
ToriInvariance (stage_bound, stage_err_le, eHat_tendsto, tori_invariance_of_limit),
Tori (facade, inventory, tori_of_iterative). No signed declaration; no existing file edited.

## Approach
Private conditional interfaces (N2). Hypotheses are only proved outputs of `iterative`
(ActionSteps, PsiSteps, StageSteps; `iterative_all` destructures `iterative` once) and of the
P23-17/18 helpers (`ToriLimit`, discharged by `tori_limit_of_iterative`), on the same witnesses
(Ds,hs,fs,Ψ,Φ,is) and one (i, Φinf). `tori_of_iterative` is the joint applicability check.
Inventory: estimates→tori_estimates_of_limit; lagr→tori_lagr_of_limit; invariance→tori_invariance_of_limit.
- estimates: KC reassembled from the coordinatewise StripLimits; angle bound 3Ês/4π, block bounds
  20(M̄₁/M̄+M̂/M)Êρ̂, 20(M̄₂/M̄+1)Êρ̂, location in realTube D (32Êρ̂) (22<32 via 3/2+20).
- lagr: Cauchy on polydisc s̄/4π gives ‖D u‖ ≤ 3Ês/s̄ ≤ 3Ê/4 ≤ (3/4)nÊ; injectivity; analyticity
  (real_restriction); Lagrangian by limit of the finite-stage Lagrangian tori using first-derivative convergence.
- invariance: γ_j' − X_H(γ_j)=Dψ_j((ω,0)−X_{H_j}); ‖Dψ_j‖ ≤ 1+κ₁κ₂ uniform (from proved Lipschitz 768nÊ);
  ‖(ω,0)−X_{H_j}‖ ≤ C·Ê_j (frequency MVT using proved ω_j(ǐ_j I₀)=ω and tail 20ρ̂_jÊ_j; Cauchy ‖Df_j‖ ≤ E_j/δ_j;
  merges the three source error terms: ∂_I f and ∂_θ f bounded together by the operator norm). Limit via
  `curve_limit_field`: compact thickening of the limit curve, uniform continuity of X_H there (the "common inner
  domain for close pairs"; no global uniform continuity, no B₀ second-derivative bound needed).

## Checks
Gate build `KAM.Planetary.TwoScale.Tori` succeeds, no sorry. #print axioms of tori_estimates_of_limit,
tori_lagr_of_limit, tori_invariance_of_limit, tori_of_iterative: propext, Classical.choice, Quot.sound.
lint_sources.sh: only "KAM.lean is out of date" (generated; not edited, per rule 10); no long lines.

## Uncertainties / deviations / errata
- `lagr` statement is private (no signature): includes analyticity, ‖D u‖ ≤ (3/4)nÊ (proved stronger 3Ê/4),
  injectivity of Dφ, Lagrangian = symplecticForm (Dφ u)(Dφ v)=0 — matches IsLatticeTorus clauses L1,L4,L5 content.
- `invariance` is stated exactly as IsLatticeTorus clause L6 with w = realFreq h I₀, G = Hr of two_scale_kam.
- Not covered here (P23-22 must supply): IsLatticeTorus clauses L2 periodicity (T.phi_per gives it),
  L3 injectivity mod lattice, DifferentiableAt Hr at K θ, and `∀ θ, K θ ∈ O` for O = univ ×ˢ realTube D r
  (estimates gives location).
- Errata: p3b invariance Step (3) bounds ‖DX_H‖ ≤ B₀ globally; not needed with the compactness argument.
  No source defect found. 3 error terms of P3b L137–141 are merged as noted (no change of statement).
- No design/heartbeat signals; no set_option used. Name `eHat_pos` etc. reused from existing code.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md row P23-20 (line 284) and its proof plan; P23 design audits; DESIGN note N2 on private conditional interfaces): (1) P23-20 has NO signed declaration: it supplies the local estimates, lagr and invariance of the two-scale tori with the same witnesses and a uniform field error, for P23-22 to assemble two_scale_kam / IsLatticeTorus. Check that every hypothesis of tori_estimates_of_limit, tori_lagr_of_limit, tori_invariance_of_limit and tori_of_iterative is a PROVED output of iterative (P23-18/19) or a source premise of two_scale_kam, never a hard proof step smuggled in; (2) the handoff lists what P23-22 must still supply (IsLatticeTorus L2 periodicity, L3 injectivity mod lattice, DifferentiableAt Hr at K theta, K theta in O): confirm each is genuinely cheap/available downstream and not a hidden hard obligation that P23-20 was assigned; (3) invariance is stated as IsLatticeTorus clause L6 with w = realFreq h I0 and G = Hr: check exactness; (4) mathematical soundness of the compactness argument replacing the blueprint's global bound (handoff errata note), and the merged error terms of P3b L137-141; (5) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM, e.g. eHat_pos reuse claim; no root shadow). Audit ONLY the KAM/Planetary/TwoScale/Tori*.lean files.
