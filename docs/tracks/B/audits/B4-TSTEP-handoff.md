# Handoff B4-TSTEP (branch inp-b4tstep)

## Files (all new, under KAM/EffectiveStability/)
- TorusStep/Remainder.lean (167 lines), TorusStep/Drift.lean (130), TorusStep.lean (139), TorusStep/Smoke.lean (58).

## Main theorem (`TorusStep.lean`), signature
```
theorem torusStep_confinement {H χ Nact P : FTPoly}
  (hH : FTFits n H) (hχ : FTFits n χ) (hP : FTFits n P) (hA : ftActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
  (hid : ftEqCheck (ftLieSum χ H L) (ftAdd Nact P) = true)
  {σ ρ σ' ρ' δc ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ') (hδc : 0 < δc) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/2)
  {πub lam : ℚ} (hπ : Real.pi ≤ πub) (hx : 2*πub*σ < 1) (hlam : 1/(1 - 2*πub*σ) ≤ lam)
  (ρl : List ℚ) (hρl : ∀ i : Fin n, (ρl.getD i 0 : ℝ) = ρ)
  (hJ : ∀ i : Fin n, (ftSupBound (ftDJ i χ) πub lam ρl : ℝ) ≤ ε*σ')
  (hφ : ∀ i : Fin n, (ftSupBound (ftDφ i χ) πub lam ρl : ℝ) ≤ ε*ρ')
  (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
  (bl : List ℚ) (hbl : ∀ i, (bl.getD i 0 : ℝ) = b i) (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
  (hσσ' : σ' < σ) (hdom1 : ∀ i, b i + εb + ρ' ≤ ρ) (hσc : δc + σ'/2 < σ)
  (hr3 : ∀ i, r i + δc + ρ'/2 < ρ) (hη : ∀ j, 0 ≤ η j)
  (hdrift : ∀ j, (ftAngleDriftBound P j πub bl : ℝ) + (ftSupBound (ftAdPow χ L H) πub lam ρl : ℝ)/(L! * δc) ≤ η j)
  (hmargin : ∀ j, a j + T*η j < b j) (w₀) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
  ∃ T₁, T < T₁ ∧ ∃ z, z 0 = torusChart χ σ ρ w₀ ∧ ... (exactly torus_confinement's conclusion, V = univ,
  H := ftEvalR H, Ψ := torusChart χ σ ρ, Ψinv := torusChartInv χ σ ρ)
```
`torusChart/torusChartInv` = `realFlow (ftEvalC χ) (cstripOpen σ ρ) (±1)`. Other lemmas: `strip_le_log_lam`,
`smallField_of_ftBounds`, `torusRem`, `differentiableOn_torusRem`, `norm_torusRem_le`, `torusRem_realInclusion₂`,
`ftActOnly`, `ftEvalR_actOnly`, `torusRemainder_eq`, `torusDrift_le`, smoke `torusStepSmoke_zeroDrift` (H=J₀²/2).

## Approach
Mirror of B2-STEP: instantiate `torus_confinement` with N J = ftEvalR Nact (0,J), R w = ftEvalR H (Ψ w) − N w.2.
hRper via `comp_realFlow_angleShift` + `ftEvalR_add_period`; hΨsymp/hΨinv via realFlow_symplectic /
realFlow_neg_realFlow_one on `cyl_subset_realInterior_cstrip`; hRη: R = ftEvalR P + Re(Rem∘ι) locally
(exact identity + actions-only), polynomial part by `abs_fderiv_ftEvalR_le`, Cauchy part by
`abs_fderiv_realPart_fst_le` with M = B/L! (no 2r_j factor).

## Deviations from brief (all weakening/clarifying, none strengthen premises)
- Added list `bl` (hbl) for the polynomial drift term `ftAngleDriftBound P j πub bl` (action radii b); the Cauchy discs use r (b ≤ r).
- `0 ≤ x` of the strip check is not a premise (derived from σ' < σ, σ' > 0, π ≤ πub). Nact needs no FTFits.
- `hdom2` (b i + ρ' < ρ) derived from hdom1 and εb > 0.

## Checks
- `b_build.sh` of TorusStep.Remainder, .Drift, TorusStep, .Smoke: all succeed, no warnings from my files.
- `sh scripts/lint_sources.sh`: OK (25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- line-length script: `[]`. main_shortname_check on all 4 modules: "short-name check OK", rc=0.
- `#print axioms` of torusStep_confinement, torusStepSmoke_zeroDrift, torusDrift_le, norm_torusRem_le,
  smallField_of_ftBounds, strip_le_log_lam: [propext, Classical.choice, Quot.sound].

## Design signals / errata / uncertainties
None. No heartbeat issues; no defect found in B4-FT or B4-TDOM (FT strip hypothesis |Im φ| ≤ log lam/(2π) used as-is).
Note: `hx`, `hlam` are real-number inequalities (σ real); for rational σ they are decidable ℚ checks.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11, OD-B12). The torus analogue of the landed, audited B2-STEP
(oscillatorStep_confinement): plan §3.1 checker soundness for ONE Fourier–Taylor generator, ending in B1-T
torus_confinement (KAM/EffectiveStability/Torus.lean). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B4-TSTEP.md and
brief-B1-common.md. Dependencies audited: B4-FT, B4-TDOM (batch 10), B2-REALFLOW, B2-CAUCHY, B1. Scope: prover commit
d65c286bb (TorusStep{,/Remainder,/Drift,/Smoke}.lean) and merges. Check: (1) every premise of torusStep_confinement is
finite data, an exact Bool check (ftEqCheck, ftActOnly), typing (FTFits) or an explicit real/rational inequality — none
mentions the flow, remainder, chart or confinement; (2) conclusion = torus_confinement's for V = univ, H = ftEvalR H,
Ψ = torusChart, Ψinv = torusChartInv; (3) the strip-width check hx/hlam really gives |Im φ| ≤ log lam/(2π) on the
domain used (strip_le_log_lam); (4) hRper: R angle-periodic from H periodic + Ψ lattice-equivariant + N angle-free
(actions-only Nact); (5) TRACE hRη: exact identity ⇒ R = P + Re Rem∘ι near real points; poly part by
ftAngleDriftBound with action radii b; Cauchy part B/(L! δc) with discs in the half interior; (6) the listed
deviations only weaken premises; (7) smoke test; (8) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms.
Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
