/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Planetary.TwoScale.Tori
public import KAM.Planetary.TwoScale.StepFreq
public import KAM.Planetary.TwoScale.MeasureJoint
public import KAM.Planetary.TwoScale.LimitMapScale

/-!
# Two-scale KAM: the lattice tori (`bpP:p3:two-scale-kam`, clauses `IsLatticeTorus`)

Assembly of `IsLatticeTorus angleShift Hr (univ ×ˢ realTube D r) ω (K ω)` from the local
estimates, `lagr` and `invariance` of P23-20 (`Tori`) and the periodicity and injectivity of the
limit map `Φinf`: injectivity of `Φinf` and of `i` on the base follows from the proved defect
Lipschitz bounds (`768 n Ê < 1` resp. `2560 n Ê < 1`). Design package P23-22.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

theorem rhoHat_le_rho (p : ScaleData) : rhoHat p ≤ p.ρ := by
  unfold rhoHat constants; exact min_le_right _ _

/-- The limit map is injective on `ℝⁿ × D_*`: the defect Lipschitz constant is `< 1`. -/
theorem KamHyp.phi_injOn (H : KamHyp D sbar p h f) {S : Set (Fin (a + b) → ℝ)}
    {Φinf : Phase (a + b) → Phase (a + b)}
    (hlip : ∀ x ∈ (univ ×ˢ S : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ S : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
        768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) :
    InjOn Φinf (univ ×ˢ S : Set (Phase (a + b))) := by
  intro x hx y hy hxy
  have hR := H.R_pos
  have hs := H.positive.2.1
  have hk := H.kam_small_n
  have he := H.eHat_nonneg
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := hlip x hx y hy
  have e : (Φinf x - x) - (Φinf y - y) = -(x - y) := by rw [hxy]; abel
  have hneg : limitmap_data (rhoHat p) p.s (-(x - y)) = limitmap_data (rhoHat p) p.s (x - y) := by
    simp only [limitmap_data, Prod.fst_neg, Prod.snd_neg, norm_neg]
  rw [e, hneg] at h1
  have hd := limitmap_data_nonneg hR hs (x - y)
  have hc : 768 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by nlinarith
  have : limitmap_data (rhoHat p) p.s (x - y) ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (limitmap_data_eq_zero hR hs (le_antisymm this hd))

/-- The limit action map is injective on `D₀`: the defect Lipschitz constant is `< 1`. -/
theorem KamHyp.i_injOn (H : KamHyp D sbar p h f) {S : Set (Fin (a + b) → ℝ)}
    {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)}
    (hlip : ∀ I ∈ S, ∀ J ∈ S, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) :
    InjOn i S := by
  intro I hI J hJ hIJ
  have hk := H.kam_small_n
  have he := H.eHat_nonneg
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := hlip I hI J hJ
  have e : (i I - I) - (i J - J) = -(I - J) := by rw [hIJ]; abel
  rw [e, norm_neg] at h1
  rw [Nat.cast_add] at hk hn
  have : ‖I - J‖ ≤ 0 := by nlinarith [norm_nonneg (I - J)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- The real part of the Hamiltonian is differentiable at every point of the torus region. -/
theorem KamHyp.Hr_differentiableAt (H : KamHyp D sbar p h f) {z : Phase (a + b)}
    (hz : z.2 ∈ realTube D (32 * eHat p * rhoHat p)) :
    DifferentiableAt ℝ (fun z : Phase (a + b) =>
      (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re) z := by
  have hk := H.kam_small_n
  have he := H.eHat_nonneg
  have hR := H.R_pos
  have ha : (1 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by have := H.a_pos; omega)
  have hle : 32 * eHat p * rhoHat p ≤ p.ρ := by
    have h1 : 32 * eHat p ≤ 1 := by nlinarith
    calc 32 * eHat p * rhoHat p ≤ 1 * rhoHat p := by gcongr
      _ ≤ p.ρ := by rw [one_mul]; exact rhoHat_le_rho p
  have hmem : KAM.realInclusion₂ (a + b) z ∈ coefficientDom D p.ρ (sbar + p.s) := by
    rw [(conv_data D p.ρ (sbar + p.s)).2]
    refine ⟨fun i => ?_, actionNbhd_mono hle hz⟩
    have : 0 < (sbar + p.s) / (2 * π) := by
      have h1 := H.positive.2.1; have h2 := H.widths.1
      exact div_pos (by linarith) (by positivity)
    simpa [KAM.realInclusion_apply] using this
  have hG := (kam_G_diff H).differentiableAt ((isOpen_coefficientDom D p.ρ (sbar + p.s)).mem_nhds hmem)
  exact (Complex.reCLM.differentiableAt.comp z
    ((hG.restrictScalars ℝ).comp z (KAM.realInclusion₂ (a + b)).differentiableAt))

variable {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}

/-- `IsLatticeTorus` for `θ ↦ Φinf (θ, ǐ I₀)`, `I₀ ∈ D₀`, with `w = realFreq h I₀`: clauses L1-L6
from `tori_estimates_of_limit`, `tori_lagr_of_limit`, `tori_invariance_of_limit`, `phi_per` and the
injectivity of `Φinf`. -/
theorem lattice_torus_of_limit (H : KamHyp D sbar p h f)
    (P : PsiSteps sbar p Ds hs fs Ψ Φ) (Q : StageSteps D sbar p h f Ds hs fs Φ)
    (hD0 : Ds 0 ⊆ D) (T : ToriLimit sbar p h Ds hs Φ is i Φinf)
    {I₀ : Fin (a + b) → ℝ} (hI₀ : I₀ ∈ Ds 0) :
    IsLatticeTorus KAM.ODE.angleShift
      (fun z : Phase (a + b) => (h (KAM.realInclusion (a + b) z.2) +
        f (KAM.realInclusion₂ (a + b) z)).re)
      (univ ×ˢ realTube D (32 * eHat p * rhoHat p)) (realFreq h I₀)
      (fun θ => Φinf (θ, i I₀)) := by
  obtain ⟨-, -, e3⟩ := tori_estimates_of_limit H hD0 T hI₀
  obtain ⟨an, -, inj, lag⟩ := tori_lagr_of_limit H T hI₀
  have hmem : ∀ θ : Fin (a + b) → ℝ, (θ, i I₀) ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))) :=
    fun θ => ⟨trivial, I₀, hI₀, rfl⟩
  refine ⟨⟨an, fun θ => ⟨⟨trivial, e3 θ⟩, H.Hr_differentiableAt (e3 θ)⟩⟩, fun θ k => ?_,
    fun θ θ' hθ => ⟨0, ?_⟩, inj, lag, tori_invariance_of_limit H P Q hD0 T hI₀⟩
  · have := T.phi_per (θ, i I₀) (hmem θ) k
    simpa [KAM.ODE.angleShift] using this
  · have := H.phi_injOn T.phi_lip (hmem θ) (hmem θ') hθ
    have h1 : θ = θ' := congrArg Prod.fst this
    subst h1
    ext j; simp

end KAM.Planetary

end
