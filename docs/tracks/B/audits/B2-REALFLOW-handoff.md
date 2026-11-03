# Handoff B2-REALFLOW

## Files (all new, under KAM/EffectiveStability/)
- RealFlow/Basic.lean (180 lines), RealFlow/Symplectic.lean (119), RealFlow/Lie.lean (128), RealFlow.lean facade (18).
  Below the 150–600 target: the proofs were short; nothing was padded.
- Imports: KAM.Canonical.{FlowInverse,Setting,Symplectic,Lie}, KAM.Frozen.Defs.SymplecticForm. No Nekhoroshev import.

## Declarations (namespace KAM.EffectiveStability; common vars n, W, Ω, φ, ε; hreal := ∀ x, ι x ∈ Ω → (φ (ι x)).im = 0)
- `reMap Ψ x` (local copy of Nekhoroshev's `reMap`, same body); `realInclusion₂_reMap`; `reMap_hasFDerivAt` (copy/adaptation of the private lemma, hypotheses: DifferentiableAt at ι x, real near x); `contDiffOn_reMap`.
- `realFlow φ Ω t := reMap (flow (hamiltonianVectorFieldℂ φ) Ω t)`; `realInterior W Ω c := {x | ι x ∈ gaugeInterior W Ω c}`; `isOpen_realInterior (hΩ) c`; `realInterior_mono`.
- `field_real` (item 1, field maps real points of Ω to real points, via `hamiltonianVectorField_eq_of_real`).
- `realInclusion₂_realFlow (hΩ hφ h hreal) (hx : x ∈ realInterior W Ω (1/2)) (ht : t ∈ Icc (-1) 1) : ι (realFlow φ Ω t x) = flow (X_ℂ φ) Ω t (ι x)` (item 1).
- `contDiffOn_realFlow (h : SmallField ..) (ht) : ContDiffOn ℝ ∞ (realFlow φ Ω t) (realInterior W Ω (1/2))` (item 2). Needs only `h` (not hφ/hreal): reMap of a holomorphic map is smooth regardless of reality.
- `realFlow_hasFDerivAt` (derivative bridge ι (L u) = fderiv ℂ (flow t) (ι x) (ι u)).
- `realFlow_symplectic (hφ h hreal) (ht) (hx) (u v) : KAM.symplecticForm (fderiv ℝ (realFlow φ Ω t) x u) (fderiv ℝ (realFlow φ Ω t) x v) = KAM.symplecticForm u v` (item 3, B1's hΨsymp shape).
- `realFlow_mem_realInterior (hx : x ∈ realInterior W Ω 1) (ht : t = 1 ∨ t = -1) : realFlow φ Ω t x ∈ realInterior W Ω (1/2)`; `realFlow_neg_realFlow_one`, `realFlow_one_realFlow_neg` (item 4).
- `realFlow_zero`; `norm_realFlow_sub_le : ‖W (ι (realFlow φ Ω t x) - ι x)‖ ≤ |t| * ε` (item 5, from flow_a).
- `realObs_realFlow` (item 6; for any g : (g (ι (realFlow t x))).re = (g (flow t (ι x))).re); `contDiffOn_realObs (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ (fun x => (g (ι x)).re) {x | ι x ∈ U}`. Reality of g is not needed for either.
- `real_taylor_lie_bound` (item 7): |(u (flow 1 (ι x))).re - ∑ j<N, (j!)⁻¹ * (adPow φ j u (ι x)).re| ≤ B / N!, premises of taylor_lie at z = ι x plus hB on Icc 0 1; no reality of u or adPow needed.
- `smoke_zero_generator n` (item 8): φ = 0, Ω = univ, W = refl, ε = 0: SmallField, differentiability, reality hold and realFlow φ univ t x = x on realInterior.

## Approach
Direct reuse: flow_e for reality (field reality from hamiltonianVectorField_eq_of_real with H = Re φ∘ι), flow_b for complex differentiability, `KAM.contDiffOn_infty_of_differentiableOn` + restrict_scalars + ι/Re CLMs for smoothness, `symplectic` for form invariance transported through the derivative bridge, flow_c for inverses.

## Signature notes / deviations (read these)
- Smoothness is stated at order `∞` (smooth), NOT `⊤`: in current Mathlib `⊤ : WithTop ℕ∞` is `ω` (analytic). B1 consumers use `ContDiffOn ℝ 2`, which follows by `of_le`. Analytic (ω) was not proved.
- `realInclusion₂_realFlow` etc. take `hΩ : IsOpen Ω` explicitly in a few theorems although `h.isOpen` gives it (redundant but harmless); symplectic/contDiff versions use `h.isOpen` internally.
- `reMap` is re-defined locally (namespace KAM.EffectiveStability) instead of importing the heavy Nekhoroshev Setting; it is definitionally the same as the root-namespace one. `symplFormC_realInclusion₂` was re-proved inline (simp).
- `real_taylor_lie_bound` states `htraj` for `ι x` as in taylor_lie (flow in Ω₁ for t ∈ Icc (-1) 1).

## Checks
- `b_build.sh` builds, in order: RealFlow.Basic, RealFlow.Symplectic, RealFlow.Lie, RealFlow: all "Build completed successfully", no warnings shown from my files.
- `sh scripts/lint_sources.sh`: 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms` of every main lemma (realInclusion₂_realFlow, contDiffOn_realFlow, realFlow_symplectic, realFlow_neg_realFlow_one, realFlow_one_realFlow_neg, realFlow_mem_realInterior, norm_realFlow_sub_le, contDiffOn_realObs, realObs_realFlow, real_taylor_lie_bound, smoke_zero_generator): only propext, Classical.choice, Quot.sound. (scratch file .drafts/axioms_scratch.lean, untracked)

## Design signals / errata
None. No heartbeat issues; no file near 1500 lines. No source defects found.

## Post-handoff changes (kam-b1)
`field_real` renamed `hamiltonianVectorFieldℂ_real` (short-name clash with KAM/Planetary/MaximalStep/AffineFlow.lean);
three lines wrapped to ≤ 100 columns. Rebuilt.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope extended by root-b8, OD-B7). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B2-REALFLOW.md and brief-B1-common.md; design: program-b-plan §3.2
(/root/code/KAM/docs/explorations/program-b-plan.md lines 341-420); owner defaults OD-B8..B10 in
docs/tracks/B/OWNER-DECISIONS.md. Consumer: B1's oscillator_confinement / torus_confinement premises hΨ (C²),
hΨsymp, hΨinv (KAM/EffectiveStability/Oscillator.lean). Check: (1) each theorem true as stated, with exactly the
premises it needs, no conclusion-shaped hypothesis (never assume the flow is real, smooth, symplectic or invertible);
(2) the real/complex bridge (reMap derivative, realInclusion₂ of fderiv) and the real symplectic form identity;
(3) the copied private helpers are faithful and the local `reMap` does not clash/duplicate badly; (4) that the
outputs have the exact shapes B1 consumes (ContDiffOn ℝ ∞ ⇒ ContDiffOn ℝ 2; hΨsymp form; inverse on
realInterior W Ω 1); (5) real_taylor_lie_bound faithful to taylor_lie; (6) hygiene (AGENTS rules 3, 4, 7, line
length ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
