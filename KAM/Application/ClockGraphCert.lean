/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.ClockGraph
public import KAM.Application.GraphCert
public import KAM.Certificate.Clock

/-!
# The clock-triangular graph adapter (certificate level)

From a certified torus (`CertifiedTorusAt`, any certifier) to the clock-triangular graph property
of its real restriction `k = Re ∘ K∞ ∘ ι` (`IsClockAngleGraph`, `ClockGraph.lean`):

* **clocks**: if `∂_{I_l} H ≡ a > 0` on the certified domain `D` (the clock slope, `a = 1` for a
  plain clock, `a = κ` for a time-scaled one), the clock lemma `clock_frequency`, applied to
  `a⁻¹ H` at the frequency `a⁻¹ s∞ ω*` (`invarianceError_ofReal_mul`), gives
  `s∞ ω*_l = a` and `A_l(θ) = θ_l + c_l` on the reals (`CertifiedTorusAt.clock`); it needs the
  Diophantine property of `ω*`, an input of every certifier's soundness theorem;
* **free diagonal**: if the certificate's embedding satisfies `∂_i K_{θ,i} ≥ m` at real points
  (`ClockMono c i m`, checkable: `ClockGraphCheck.lean`), Cauchy on `T_{ρ∞}`
  (`norm_fderiv_sub_le_of_real`) moves it to `K∞` with loss `disp/ρ∞`
  (`CertifiedTorusAt.le_fderiv_torusAngle`).

`CertifiedTorusAt.isClockAngleGraph`, `CertifiedTorus.exists_clockGraph`: with every `l ≠ i` a
clock and the strict margin `disp < m ρ∞`, the real torus is an analytic graph over the angles,
clock-triangular with diagonal bound `m - disp/ρ∞ > 0`. No bound on the off-diagonal entries
`∂_l U_i` is needed (in contrast with `AngleNearId`, which bounds whole rows of `DU`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate

variable {n : ℕ}

/-- Time scaling: `invarianceError (r H) K ω = r · invarianceError H K (r⁻¹ ω)` (`r ≠ 0`; both
sides use `fderiv`, so no differentiability premise is needed). -/
theorem invarianceError_ofReal_mul {r : ℝ} (hr : r ≠ 0) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    invarianceError (fun z => (r : ℂ) * H z) K ω θ =
      (r : ℂ) • invarianceError H K (r⁻¹ • ω) θ := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  have hf : ∀ x, fderiv ℂ (fun z => (r : ℂ) * H z) x = (r : ℂ) • fderiv ℂ H x := fun x => by
    have : Invertible (r : ℂ) := invertibleOfNonzero hr'
    exact fderiv_const_smul_of_invertible (𝕜 := ℂ) (f := H) (x := x) (r : ℂ)
  have hω : (fun i => (((r⁻¹ • ω) i : ℝ) : ℂ)) = (r : ℂ)⁻¹ • fun i => (ω i : ℂ) := by
    funext i; simp
  unfold invarianceError hamiltonianVectorFieldℂ
  simp only [hf, hω, map_smul, smul_apply, smul_inv_smul₀ hr', smul_sub, Prod.smul_mk]
  refine Prod.ext ?_ ?_ <;> ext i <;> simp

variable {α : Type} [CertArith α]

/-- **The free diagonal condition on the certificate's embedding** `K` (checkable,
`ClockGraphCheck.lean`): `Re ∂_i K_{θ,i}(ι x) ≥ m` at every real `x`. -/
def ClockMono (c : TorusCertificate n α) (i : Fin n) (m : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, m ≤ ((fderiv ℂ c.K (realInclusion n x) (Pi.single i 1)).1 i).re

variable [LawfulCertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

/-- **The clock lemma for a certified torus.** If `∂_{I_l} H ≡ a > 0` on the certified domain and
`ω*` is Diophantine, then `s∞ ω*_l = a` and the `l`-th angle of the real torus is exact:
`A_l(θ) = θ_l + c_l`. -/
theorem CertifiedTorusAt.clock (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) {l : Fin n} {a : ℝ} (ha : 0 < a)
    (hH : ∀ z ∈ c.D, fderiv ℂ c.H z (phaseBasis (.inr l)) = a) {γ τ : ℝ} (hγ : 0 < γ)
    (hdio : IsDiophantine γ τ ωstar) :
    sinf * ωstar l = a ∧ ∃ cl : ℝ, ∀ x, torusAngle (realRestriction Kinf) x l = x l + cl := by
  have S := checkStatic_sound hs
  obtain ⟨hs1, -, hd, hp, hr, hinv, -, hball, -, -, -⟩ := hT
  have hsinf : 0 < sinf := by linarith
  have ha' : a⁻¹ ≠ 0 := inv_ne_zero ha.ne'
  set b : ℝ := a⁻¹ * sinf with hb
  have hb0 : 0 < b := mul_pos (inv_pos.2 ha) hsinf
  have hKD : ∀ θ ∈ complexStrip n c.params.rhoInf, Kinf θ ∈ c.D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self (half_pos S.hμ))
  have hinv' : ∀ θ ∈ complexStrip n c.params.rhoInf,
      invarianceError (fun z => ((a⁻¹ : ℝ) : ℂ) * c.H z) Kinf (b • ωstar) θ = 0 := by
    intro θ hθ
    have e : (a⁻¹)⁻¹ • b • ωstar = sinf • ωstar := by
      rw [inv_inv, smul_smul, hb, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [invarianceError_ofReal_mul ha', e, hinv θ hθ, smul_zero]
  have hH1 : ∀ z ∈ c.D,
      fderiv ℂ (fun z => ((a⁻¹ : ℝ) : ℂ) * c.H z) z (phaseBasis (.inr l)) = 1 := by
    intro z hz
    have : Invertible ((a⁻¹ : ℝ) : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.2 ha')
    rw [show (fun z => ((a⁻¹ : ℝ) : ℂ) * c.H z) = ((a⁻¹ : ℝ) : ℂ) • c.H from rfl,
      fderiv_const_smul_of_invertible, smul_apply, hH z hz, smul_eq_mul,
      ← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one]
  obtain ⟨h1, cl, hcl⟩ := clock_frequency l S.hρinf hH1 hKD hd hp hr hinv'
    (mul_pos hb0 hγ) (isDiophantine_mul_smul hb0 hdio)
  refine ⟨?_, cl, fun x => ?_⟩
  · rw [hb, mul_assoc] at h1
    have := congrArg (fun t => a * t) h1
    simp only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_one] at this
    exact this
  · have hx := hcl x
    simp only [torusAngle, realRestriction, realPartCLM₂_apply, realPartCLM_apply]
    rw [show realInclusion n x = fun i => (x i : ℂ) from rfl, hx, Complex.ofReal_re]

/-- **Cauchy transfer of the free diagonal**: `ClockMono c i m` for the certificate's `K` gives
`∂_i A_i ≥ m - disp/ρ∞` for the angle map `A` of the exact real torus. -/
theorem CertifiedTorusAt.le_fderiv_torusAngle (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) {i : Fin n} {m : ℝ} (hm : ClockMono c i m) (x : Fin n → ℝ) :
    m - (c.params.disp : ℝ) / c.params.rhoInf ≤
      fderiv ℝ (torusAngle (realRestriction Kinf)) x (Pi.single i 1) i := by
  have S := checkStatic_sound hs
  obtain ⟨-, -, hd, -, hr, -, -, -, -, hdisp, -⟩ := hT
  have hR := realRestriction_fderiv S.hρinf hd hr x
  have hC := norm_fderiv_sub_le_of_real S.hρinf hd
    (CertEmbedding.differentiable_eval n c.emb).differentiableOn hdisp x
  set ι := realInclusion n
  set DKi := fderiv ℂ Kinf (ι x)
  set DK := fderiv ℂ c.K (ι x)
  have h1 : (((fderiv ℝ (realRestriction Kinf) x (Pi.single i 1)).1 i : ℝ) : ℂ) =
      (DKi (Pi.single i 1)).1 i := by
    have := congrArg (fun z => z.1 i) (hR.2 (Pi.single i 1))
    simpa [ι, DKi, realInclusion_single] using this
  rw [fderiv_torusAngle hR.1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
  have h2 : (fderiv ℝ (realRestriction Kinf) x (Pi.single i 1)).1 i =
      ((DKi (Pi.single i 1)).1 i).re := by
    rw [← h1, Complex.ofReal_re]
  rw [h2]
  have h3 : |((DKi (Pi.single i 1)).1 i).re - ((DK (Pi.single i 1)).1 i).re| ≤
      (c.params.disp : ℝ) / c.params.rhoInf := by
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    have e : (DKi (Pi.single i 1)).1 i - (DK (Pi.single i 1)).1 i =
        ((DKi - DK) (Pi.single i 1)).1 i := by simp
    rw [e]
    refine (norm_le_pi_norm _ i).trans ((norm_fst_le _).trans
      (((DKi - DK).le_opNorm _).trans ?_))
    rw [Pi.norm_single, norm_one, mul_one]
    exact hC
  have := hm x
  linarith [(abs_le.1 h3).1]

/-- **The certified real torus is a clock-triangular graph over the angles** (named witnesses).
Every angle `l ≠ i` is a clock of slope `a > 0` (`∂_{I_l} H ≡ a` on `D`), `ω*` is Diophantine,
the certificate's `K` satisfies `ClockMono c i m`, and `disp < m ρ∞`. Then `s∞ ω*_l = a` for
`l ≠ i`, and `k = Re ∘ K∞ ∘ ι` is an analytic graph over the angles whose angle map has the clock
components `θ_l + c_l` and free diagonal `∂_i A_i ≥ m - disp/ρ∞ > 0`. -/
theorem CertifiedTorusAt.isClockAngleGraph (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) {i : Fin n} {a : ℝ} (ha : 0 < a)
    (hclock : ∀ l, l ≠ i → ∀ z ∈ c.D, fderiv ℂ c.H z (phaseBasis (.inr l)) = a) {γ τ : ℝ}
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ ωstar) {m : ℝ} (hm : ClockMono c i m)
    (hmargin : (c.params.disp : ℝ) < m * c.params.rhoInf) :
    (∀ l, l ≠ i → sinf * ωstar l = a) ∧ ∃ cc : Fin n → ℝ,
      IsClockAngleGraph (realRestriction Kinf) i cc (m - (c.params.disp : ℝ) / c.params.rhoInf) := by
  have S := checkStatic_sound hs
  have hc2 : ∀ l, l ≠ i → ∃ cl : ℝ, ∀ x, torusAngle (realRestriction Kinf) x l = x l + cl :=
    fun l hl => (hT.clock hs ha (hclock l hl) hγ hdio).2
  choose cc hcc using hc2
  refine ⟨fun l hl => (hT.clock hs ha (hclock l hl) hγ hdio).1,
    fun l => if hl : l = i then 0 else cc l hl, ?_⟩
  have hmono := hT.le_fderiv_torusAngle hs hm
  obtain ⟨-, -, hd, hp, hr, -⟩ := hT
  obtain ⟨han, -, -, hper⟩ := real_restriction S.hρinf hd hr
  refine isClockAngleGraph_of_clock han (hper hp) ?_ (fun θ l hl => ?_) hmono
  · rw [sub_pos, div_lt_iff₀ S.hρinf]; exact hmargin
  · rw [hcc l hl θ]
    simp [hl]

/-- **The clock-triangular graph adapter.** A certified torus (from any certifier), the static
check, the certified Hamiltonian facts (`IsRealHolo c.D c.H`), clocks `∂_{I_l} H ≡ a > 0` for every
`l ≠ i`, a Diophantine `ω*`, the free diagonal condition `ClockMono c i m` and the margin
`disp < m ρ∞` give an exact torus `K∞` at `s∞` (all clauses of `CertifiedTorus`) with
`s∞ ω*_l = a` (`l ≠ i`) whose real restriction `k = Re ∘ K∞ ∘ ι` is a real model torus of
`realHam c.H` at `s∞ ω*` on the level `E₀` and a clock-triangular analytic graph over the angles
(`IsClockAngleGraph k i c' (m - disp/ρ∞)`). -/
theorem _root_.KAM.Certificate.CertifiedTorus.exists_clockGraph (hT : CertifiedTorus c ωstar)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H) {i : Fin n} {a : ℝ} (ha : 0 < a)
    (hclock : ∀ l, l ≠ i → ∀ z ∈ c.D, fderiv ℂ c.H z (phaseBasis (.inr l)) = a) {γ τ : ℝ}
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ ωstar) {m : ℝ} (hm : ClockMono c i m)
    (hmargin : (c.params.disp : ℝ) < m * c.params.rhoInf) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      (∀ l, l ≠ i → sinf * ωstar l = a) ∧ ∃ cc : Fin n → ℝ,
      IsClockAngleGraph (realRestriction Kinf) i cc (m - (c.params.disp : ℝ) / c.params.rhoInf) := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff c ωstar).1 hT
  exact ⟨Kinf, sinf, hT, hT.isRealModelTorus hs hH,
    hT.isClockAngleGraph hs ha hclock hγ hdio hm hmargin⟩

end KAM.Application
