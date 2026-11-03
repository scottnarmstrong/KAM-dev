# Handoff B5-NF (branch inp-b5nf)

## Files (all new, each < 150 lines; no frozen/manifest/root/lakefile edits)
- `KAM/EffectiveStability/TorusNormalForm/Taylor.lean` — sharp 2nd-order Taylor bound along a segment
- `.../TorusNormalForm/Basic.lean` — `torusNFGraph`, `TorusNFTorus`, `torusNFRem`, `torusNFLin`, item 1
- `.../TorusNormalForm/Remainder.lean` — item 2
- `.../TorusNormalForm/Drift.lean` — item 3
- `KAM/EffectiveStability/TorusNormalForm.lean` — item 4 (`torusNormalForm_confinement`) + facade docstring
- `KAM/EffectiveStability/TorusNormalFormSmoke.lean` — item 5

## Key signatures
```
structure TorusNFTorus (u v) (hR) (E0 : ℝ) (ω' : Fin n → ℝ) : Prop where
  hRdiff : ∀ φ, DifferentiableAt ℝ hR (torusNFGraph u v φ)
  invariance : ∀ φ, fderiv ℝ (torusNFGraph u v) φ ω' = hamiltonianVectorField hR (torusNFGraph u v φ)
  energy : ∀ φ, hR (torusNFGraph u v φ) = E0          -- torusNFGraph u v φ = (torusChartX u φ, v φ)
def torusNFRem hR u v E0 ω' w := hR (torusChartMap u v w) - (E0 + ∑ j, ω' j * w.2 j)

theorem torusNF_dG_J (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω') (φ J) :
  fderiv ℝ (hR ∘ torusChartMap u v) (φ, 0) (0, J) = ∑ j, ω' j * J j            -- item 1
theorem torusNF_G_zero ht φ : (hR ∘ torusChartMap u v) (φ, 0) = E0                -- item 1
theorem torusNFRem_zero / torusNFRem_dJ / torusNFRem_dphi / torusNFRem_d2           -- item 2
  (R (φ,0)=0; DR(φ,0)(0,J)=0; DR(φ,0)(e,0)=0; D²R(φ,0)(e,0)(0,J)=0)  [last three need hG, hc]
theorem torusNFRem_shift h (hper : ∀ k w, w ∈ cyl c → hR (Ψ w + angleShift k) = hR (Ψ w)) k (hw : w ∈ cyl c) :
  torusNFRem … (w + angleShift k) = torusNFRem … w
theorem torusNF_drift (h) (ht) (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j)
  {C₃} (hD3 : ∀ y ∈ cyl c, ∀ a b d, |fderiv ℝ (fderiv ℝ (fderiv ℝ (hR ∘ torusChartMap u v))) y a b d| ≤ C₃*‖a‖*‖b‖*‖d‖)
  {b} (hbc : ∀ j, b j < c j) {w} (hw : w ∈ cylClosed b) (i) :
  |fderiv ℝ (torusNFRem hR u v E0 ω') w (Pi.single i 1, 0)| ≤ C₃ * ‖w.2‖ ^ 2 / 2
theorem torusNormalForm_confinement  -- full statement in TorusNormalForm.lean; conclusion = torus_confinement's
  with H := hR, Ψ := torusChartMap u v, Ψinv := torusChartInvMap u v
```
**Constant proved: exactly `C₃/2 · ‖J‖²`, ‖J‖ = max_j |J j|; no n-dependent factor** (all norms are sup norms, `‖(e_i,0)‖ = 1`).
Corollary margin: `η j ≥ C₃ B²/2` where `B ≥ b j` (premise `hηB`, plus `0 ≤ C₃`, `0 ≤ B`).

## Approach
Item 1: `DΨ(φ,0)(0,J) = (0, Dx⁻ᵀ J)` from B5-CHART's `torusChartMap_fderiv_fst/snd`; invariance's first component
gives `∂_p hR(Kφ) = Dx ω'`; then `(Dx⁻ᵀ J)·(Dx ω') = ω'·J` via `torusChartJacT_invT_mulVec`. Item 2: `G(·,0)≡E0`
gives `D_φ G=0`; `D_φ D_J G` from symmetry of the 2nd derivative (`isSymmSndFDerivAt`, needs `G ∈ C³`) and
`D_J G(φ,0)` constant in φ; transfer to `R` since `fderiv R = fderiv G − torusNFLin` on the open cylinder.
Item 3: along `t ↦ (φ, tJ)`, `g(t)=D_φi G` has `g(0)=0, g'(0)=0, |g''|≤C₃‖J‖²`; two applications of a 1-D
comparison lemma (`abs_le_of_abs_deriv_le_nfT`) give the sharp `1/2` (`fderiv_taylor_bound_nfT`, generic in the normed space).

## Checks (all run in /root/code/KAM-inp-b5nf)
- `b_build.sh` of Taylor, Basic, Remainder, Drift, TorusNormalForm, TorusNormalFormSmoke: all "Build completed successfully", no warnings.
- `sh scripts/lint_sources.sh`: `OK`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK` (25 tests OK).
- Line length script: `[]`. `main_shortname_check.py` (all 6 modules): `short-name check OK`, rc 0.
- `#print axioms` of `torusNormalForm_confinement`, `torusNF_drift`, `torusNF_dG_J`, `torusNFRem_d2`, `torusNFRem_shift`,
  `fderiv_taylor_bound_nfT`, `torusNF_smoke_confinement`: all `[propext, Classical.choice, Quot.sound]`.
- Smoke (`TorusNormalFormSmoke`): u=v=0, `hR = E0 + ω'·J` (`torusNFLinearHam`): `torusNF_smoke_torus`, `torusNF_smoke_rem` (R = 0),
  `torusNF_smoke_confinement` (applies the corollary with C₃=0, η=0).

## Deviations / design signals (no signature requested by the brief was false)
1. **`G = hR ∘ Ψ ∈ C³` is an explicit premise (`hG`)**, not derived: B5-CHART gives `Ψ ∈ C²` only
   (`torusChartMap_contDiff` is `ContDiff ℝ 2`; `u ∈ C³`, `v ∈ C²`). B5-ROUTE must supply it (e.g. via
   analyticity of the certificate torus + hR analytic, or by strengthening `v` to C³ and the chart to C³ upstream).
2. The third-derivative bound `hD3` is stated in evaluated trilinear form `|D³G y a b d| ≤ C₃‖a‖‖b‖‖d‖`
   rather than `‖D³G y‖ ≤ C₃`, because `Norm (E →L E →L E →L ℝ)` fails to synthesize for general `E` (instance depth);
   it is equivalent to the operator-norm bound. B5-ROUTE discharges it on `cyl (b+ε)`.
3. Periodicity premise is `hR (Ψ w + angleShift k) = hR (Ψ w)` for `w ∈ cyl (b+ε)` (only along the chart image).
4. `TorusNFTorus.invariance` is stated for `torusNFGraph u v φ = (torusChartX u φ, v φ)`; route must bridge from
   `realRestriction K` (`torusChartX (torusRealU K) φ = torusRealX K φ`, since `x = φ + (x−φ)`).
5. Positivity `0 < b j` is derived inside the corollary from the margin and `hw₀` (so no extra premise).
No heartbeat/line-cap issues; no errata found in B5-CHART or B5-LAG (nothing in their statements was changed or found defective).

## AUDIT FOCUS (kam-b1)
Track B, program B5 (overnight D71; nothing frozen; OD-B14; design docs/tracks/B/B5-DESIGN.md item 3). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B5-NF.md and brief-B1-common.md; plan §3.4 ("An invariant exact torus gives
H∘Ψ_K = E + ω·J + O(J²). Derive this from DK·ω = X_H∘K, rather than add it as a hypothesis"),
/root/code/KAM/docs/explorations/program-b-plan.md lines 426-457. Built on audited B5-CHART and B5-LAG (batch 14 in landing).
Scope: prover commit 71a046f4a and merges. Check: (1) E0 + ω'·J is DERIVED from the invariance and energy identities
(TorusNFTorus holds only those source identities, never the normal-form conclusion); (2) the second-order vanishing of R
at J = 0 and the sharp Taylor drift bound C₃‖J‖²/2 (sup norms); (3) the explicit premises hG (C³ of hR∘Ψ) and hD3
(evaluated trilinear third-derivative bound) are quantitative source premises, not conclusion-shaped, and are clearly
reported as obligations for B5-ROUTE; (4) torusNormalForm_confinement's conclusion is exactly torus_confinement's; periodicity
premise only along the chart image is sufficient; (5) smoke test; (6) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names,
axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
