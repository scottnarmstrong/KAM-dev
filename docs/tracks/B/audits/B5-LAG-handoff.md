# Handoff B5-LAG (branch inp-b5lag)

## Files (all new, `KAM/EffectiveStability/`, each < 200 lines)
- `TorusLagrangian.lean` (item 1, general)
- `TorusRealSlice.lean` (items 2, 3, general)
- `TorusProjection.lean` (item 4, general)
- `TorusLagrangianCert.lean` (CertifiedTorus corollaries; imports `KAM.Application.Certified`, a core module)

## Approach
Item 1 is the DIRECT route, no `geometry_sep`: `fi_dLagrange` with E = 0 gives `∂_ω Ω_K = 0`; `periodic_lagrangeMat` and
`Exactness.avg_lagrangeMat` give periodicity and zero average; `CohData.apriori` (`cohData_crude`) with bound H = 0 gives
`Ω_K = 0` on `T_{r-min(δ,1)} ⊇ T_{r-δ}`. Standing data (`Apost.Standing`) is built from `G1Hyps` + `IsDiophantine γ τ ω*`
(`g1Hyps_standing`; scaling by `s ≥ 1` via `Iso.Linear.isDiophantine_smul`, γ unchanged). `CertifiedTorus` itself does NOT
carry the Diophantine hypothesis or the bounds on H: the corollaries need `G1Hyps c ω*` and
`IsDiophantine c.params.γ c.params.tau ω*` (the same premises as `checkTorusCertificate_sound`). The general lemma needs
only `Standing`, K holomorphic+primary on `T_r`, `K(T_r) ⊆ 𝔅`, E = 0.
Real slice via `KAM.realRestriction`. Frequency identity via `hamiltonianVectorField_eq_of_real`. Projection: vector Cauchy
estimate on the strip (via `Cauchy.norm_fderiv_le_of_closedDisc`) + triangle inequality.
I used `CertifiedTorusAt` (landed in `KAM/Application/Certified.lean`) as the named-witness form of `CertifiedTorus`, and
`KAM.Application.realHam h = Re h ∘ ι₂` as the real Hamiltonian `hR`.

## Final signatures (namespace KAM.EffectiveStability; `x = torusRealX K`, `v = torusRealV K`, `u = torusRealU K`)
General:
```
theorem fderiv_lagrangeMat_omega_eq_zero (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError h K ω θ = 0) :
    ∀ θ ∈ complexStrip n r, fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) = 0
theorem lagrangeMat_eq_zero_of_exact (hS : Standing ...) (hr : 0 < r) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError h K ω θ = 0) (hδ : 0 < δ) (hδr : δ < r) :
    ∀ θ ∈ complexStrip n (r - δ), lagrangeMat K θ = 0
def torusRealX/torusRealV/torusRealU (K) (φ : Fin n → ℝ) : Fin n → ℝ   -- (realRestriction K φ).1 / .2 / x φ - φ
theorem torusRealX_add_int / torusRealU_add_int / torusRealV_add_int (hρ : 0 < ρ) (hKp : IsPrimaryOnStrip K ρ)
    (hreal : IsRealOnReals K) (φ) (k : Fin n → ℤ) :
    torusRealX K (φ + fun i => (k i : ℝ)) = torusRealX K φ + fun i => (k i : ℝ)   -- U, V: = value at φ
theorem torusRealX_contDiff / torusRealV_contDiff / torusRealU_contDiff (hρ : 0 < ρ)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) : ContDiff ℝ (⊤ : ℕ∞) (torusRealX K)   -- ⊤ : ℕ∞ is ∞ (smooth); also analytic
theorem fderiv_torusRealX_incl / fderiv_torusRealV_incl ... :
    realInclusion n (fderiv ℝ (torusRealX K) φ e) = (fderiv ℂ K (realInclusion n φ) (realInclusion n e)).1   -- .2 for V
theorem torusReal_lagrangian (hρ) (hK) (hreal) {φ} (hΩ : lagrangeMat K (realInclusion n φ) = 0) (i j : Fin n) :
    ∑ l, (fderiv ℝ (torusRealX K) φ (Pi.single i 1)) l * (fderiv ℝ (torusRealV K) φ (Pi.single j 1)) l =
      ∑ l, (fderiv ℝ (torusRealX K) φ (Pi.single j 1)) l * (fderiv ℝ (torusRealV K) φ (Pi.single i 1)) l
theorem torusReal_frequency (hρ) (hK) (hreal) (hD : IsOpen D) (hh : DifferentiableOn ℂ h D)
    (hhreal : ∀ y, realInclusion₂ n y ∈ D → (h (realInclusion₂ n y)).im = 0) (hKD : ∀ θ ∈ complexStrip n ρ, K θ ∈ D)
    {ω'} (hinv : ∀ θ ∈ complexStrip n ρ, invarianceError h K ω' θ = 0) (φ) :
    fderiv ℝ (realRestriction K) φ ω' = hamiltonianVectorField (Application.realHam h) (realRestriction K φ)
theorem torusReal_energy (hreal) {E} (φ) (hE : h (K (realInclusion n φ)) = (E : ℂ)) :
    Application.realHam h (realRestriction K φ) = E
theorem norm_fderiv_real_le_of_strip_bound {F : (Fin n → ℂ) → (Fin n → ℂ)} {d} (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (complexStrip n ρ)) (hδ : 0 < δ) (hδρ : δ < ρ) (hd : ∀ θ ∈ complexStrip n ρ, ‖F θ‖ ≤ d) (x) :
    ‖fderiv ℂ F (realInclusion n x)‖ ≤ d / δ
theorem torusRealU_fderiv_le (hρ) (hK) (hKc : DifferentiableOn ℂ Kc (complexStrip n ρ)) (hreal : IsRealOnReals K)
    (hδ : 0 < δ) (hδρ : δ < ρ) {κc disp} (hκ : ∀ φ, ‖fderiv ℂ (fun θ => (Kc θ).1 - θ) (realInclusion n φ)‖ ≤ κc)
    (hdisp : ∀ θ ∈ complexStrip n ρ, ‖K θ - Kc θ‖ ≤ disp) (φ) : ‖fderiv ℝ (torusRealU K) φ‖ ≤ κc + disp / δ
```
Certificate (`hG : G1Hyps c ωstar`, `hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar`,
`hT : CertifiedTorusAt c ωstar Kinf sinf`, `0 < δ < ρ∞`):
```
theorem g1Hyps_standing (hG) (hdio) {s} (hs : 1 ≤ s) : Apost.Standing n τ M σK σB σT c.D c.H (s • ωstar) γ
theorem certifiedTorusAt_lagrangian ... : ∀ θ ∈ complexStrip n (ρ∞ - δ), lagrangeMat Kinf θ = 0
theorem certifiedTorusAt_realLagrangian ... (φ) (i j) : <torusReal_lagrangian form for torusRealX Kinf, torusRealV Kinf>
theorem certifiedTorusAt_frequency (hG) (hT) (φ) : fderiv ℝ (realRestriction Kinf) φ (sinf • ωstar) =
    hamiltonianVectorField (realHam c.H) (realRestriction Kinf φ)          -- no hdio, no δ
theorem certifiedTorusAt_energy (hG) (hT) (φ) : realHam c.H (realRestriction Kinf φ) = (c.params.E0 : ℝ)
theorem certifiedTorusAt_projection (hG) (hT) (hδ) (hδρ) (hκ : ∀ φ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) (realInclusion n φ)‖ ≤ κc) (φ) :
    ‖fderiv ℝ (torusRealU Kinf) φ‖ ≤ κc + (c.params.disp : ℝ) / δ
```
Periodicity/smoothness of the slice for the certificate: apply the general lemmas with `hρ := hG.hρinf`, `hT.2.2.1` (holo),
`hT.2.2.2.1` (primary), `hT.2.2.2.2.1` (real). `ω' = sinf • ωstar` is Diophantine with the same γ since sinf > 1
(`Iso.Linear.isDiophantine_smul`; also `CertifiedTorusAt.isDiophantine` gives (sinf·γ, τ)).

## Signature deviations
None of substance. Item 4 hypothesis `‖D(Kc^θ - id)‖ ≤ κc` is required only at real points (weaker than the strip form requested),
and takes `0 < δ < ρ` (strict, so the closed Cauchy discs sit inside the open strip). The `ContDiff` order is `(⊤ : ℕ∞)`,
i.e. `∞`; `ContDiff ℝ 3` follows by `.of_le`. Item 1's loss: any `0 < δ < r` (internally min(δ,1)).

## Checks
- `b_build.sh` of TorusLagrangian, TorusRealSlice, TorusProjection, TorusLagrangianCert: all `Build completed successfully`;
  no warnings from my files (warnings printed are pre-existing ones in KAM/Certificate/*, KAM/Strip/*).
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, 25 tests OK, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- Line length script: `[]`. Short-name check: `short-name check OK (no reused public short name)`, rc=0.
- Files 81/184/154/123 lines.
- `#print axioms` of every main lemma (14 listed incl. all `certifiedTorusAt_*`): `[propext, Classical.choice, Quot.sound]`.

## Design signals / uncertainties / errata
- No heartbeat or memory issues; every file elaborates in ~2 s.
- Standing data: `CertifiedTorus` alone does not suffice for item 1 (needs Diophantine ω* and the H bounds); both come from the
  existing soundness premises (`G1Hyps`, `hdio`), as in `checkTorusCertificate_sound`. No new conclusion-shaped premise.
- Files import `KAM.Application.Certified` / `KAM.Application.RealTorus` (core library modules, `KAM.Root.Application`).
- Errata: none found.

## AUDIT FOCUS (kam-b1)
Track B, program B5 (overnight D71; nothing frozen; root-b8 scope; OD-B13..B15; design docs/tracks/B/B5-DESIGN.md). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B5-LAG.md and brief-B1-common.md; plan §3.4 (/root/code/KAM/docs/explorations/
program-b-plan.md lines 426-457: "The Lagrangian property is essential"; derive, never assume). Scope: prover commit f942b9273
(four modules) and merges. Check: (1) the Lagrangian theorem lagrangeMat_eq_zero_of_exact is DERIVED from exact invariance
(E = 0), periodicity/zero average and the cohomological uniqueness (CohData) — its premises are source premises
(Standing, holomorphy, primary, image in 𝔅, E = 0), none Lagrangian-shaped; (2) the certificate corollaries use only
CertifiedTorusAt plus the soundness premises G1Hyps and IsDiophantine (as checkTorusCertificate_sound), and the
Diophantine scaling for s∞ ≥ 1 is correct; (3) the real slice (x, v, u periodicity, smoothness) and the real Lagrangian
condition in B5-CHART's exact form (Dxᵀ Dv symmetric); (4) the frequency identity's sign/convention vs
KAM.hamiltonianVectorField and invarianceError; energy; (5) the projection bound (Cauchy on strips) with strict 0 < δ < ρ;
(6) imports of KAM.Application.* are core (KAM/Root/Application.lean), not opt-in applications; (7) hygiene (AGENTS rules 3,
4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
