/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.RealHam
public import KAM.Strip.RealRestriction

/-!
# Part 5: the tori are graphs over all angles

Blueprint `bpI:p5:graph`. For one
torus `K` with the output (T1)-(T4) of `bpI:p3:tori` (`TorusOutput`), the real restriction
`k = Re ∘ K ∘ ι` (`KAM.realRestriction`) parametrises the real torus `𝒯 = k(ℝ²)`.

* (a) `torus_phase_sub_lipschitz`, `torus_phase_bijective`, `torus_phase_inv`: the phase map
  `Ψ θ = (k θ).1` is `θ` plus a `½`-Lipschitz map (the derivative bound on `T_{ρ∞/2}` restricted
  to the real points), hence a bi-Lipschitz bijection of `ℝ²` with a `2`-Lipschitz inverse.
* (b), (c, energy) `torus_graph`: `𝒯` is the graph of the continuous map `Y = (k ∘ Ψ⁻¹).2` with
  `‖Y - I‖ ≤ C_K ε`, on which `H_ℝ` equals `E`.
* (c, position) `torus_graph_mem`, `torus_graph_energy_close`: the graph lies in `𝒩 ⊆ W ⊆ B`
  when the base point is in `𝒦`, and `|h(Y φ) - E| ≤ ε`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace KAM.Iso.Confinement

open KAM

section Graph

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε C_K E : ℝ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
  {I ωt : Fin 2 → ℝ}

/-- `ρ∞ = min {s₀, 1} / 8` is positive for `s₀ > 0`. -/
private theorem rhoInf_pos (hs : 0 < s₀) : 0 < rhoInf s₀ :=
  div_pos (lt_min hs one_pos) (by norm_num)

/-- The real derivative of `θ ↦ (k θ).1 - θ` is the restriction of the complex derivative of
`θ ↦ (K θ).1 - θ` to the real points. -/
private theorem phase_fderiv (hρ : 0 < rhoInf s₀)
    (hK : DifferentiableOn ℂ K (complexStrip 2 (rhoInf s₀)))
    (hreal : IsRealOnReals K) (x : Fin 2 → ℝ) :
    DifferentiableAt ℝ (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ) x ∧
      ∀ v : Fin 2 → ℝ, realInclusion 2
          (fderiv ℝ (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ) x v) =
        fderiv ℂ (fun θ : Fin 2 → ℂ => (K θ).1 - θ) (realInclusion 2 x) (realInclusion 2 v) := by
  obtain ⟨hdk, hk⟩ := realRestriction_fderiv hρ hK hreal x
  have hKd : DifferentiableAt ℂ K (realInclusion 2 x) :=
    hK.differentiableAt
      ((isOpen_complexStrip 2 _).mem_nhds (realInclusion_mem_complexStrip hρ x))
  have h1 : HasFDerivAt (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ)
      ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).comp (fderiv ℝ (realRestriction K) x) -
        ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) x :=
    hdk.hasFDerivAt.fst.sub (hasFDerivAt_id x)
  have h2 : HasFDerivAt (fun θ : Fin 2 → ℂ => (K θ).1 - θ)
      ((ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).comp (fderiv ℂ K (realInclusion 2 x)) -
        ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) (realInclusion 2 x) :=
    hKd.hasFDerivAt.fst.sub (hasFDerivAt_id (realInclusion 2 x))
  refine ⟨h1.differentiableAt, fun v => ?_⟩
  rw [h1.fderiv, h2.fderiv]
  simp only [sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.id_apply, map_sub]
  exact congrArg (fun w => w - realInclusion 2 v) (congrArg Prod.fst (hk v))

/-- The operator norm of the real derivative of `θ ↦ (k θ).1 - θ` is at most `½`. -/
private theorem phase_fderiv_norm_le (hs : 0 < s₀)
    (hsm : 8 * C_K * ε < rhoInf s₀) (T : TorusOutput h f ε C_K s₀ E K I ωt)
    (x : Fin 2 → ℝ) :
    ‖fderiv ℝ (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ) x‖ ≤ 1 / 2 := by
  have hρ := rhoInf_pos hs
  obtain ⟨-, hv⟩ := phase_fderiv hρ T.holo T.real x
  have hx : realInclusion 2 x ∈ complexStrip 2 (rhoInf s₀ / 2) :=
    realInclusion_mem_complexStrip (half_pos hρ) x
  have h1 := T.du (realInclusion 2 x) hx
  have h2 : 4 * C_K * ε / rhoInf s₀ ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  exact (norm_le_of_isometric_restriction (norm_realInclusion) (norm_realInclusion)
    (fderiv ℂ (fun θ : Fin 2 → ℂ => (K θ).1 - θ) (realInclusion 2 x))
    (fderiv ℝ (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ) x)
    fun v => (hv v).symm).trans (h1.trans h2)

/-- (a), contraction: `θ ↦ (k θ).1 - θ` is `½`-Lipschitz on `ℝ²` (`8 C_K ε < ρ∞`), `k = Re K ι`. -/
theorem torus_phase_sub_lipschitz (hs : 0 < s₀) (hε : 0 ≤ ε) (hsm : 8 * C_K * ε < rhoInf s₀)
    (hC : 0 < C_K) (T : TorusOutput h f ε C_K s₀ E K I ωt) :
    LipschitzWith (1 / 2 : ℝ≥0) (fun θ : Fin 2 → ℝ => (realRestriction K θ).1 - θ) := by
  have hρ := rhoInf_pos hs
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun x => (phase_fderiv hρ T.holo T.real x).1) fun x => ?_
  have _hCε : 0 ≤ C_K * ε := mul_nonneg hC.le hε
  have := phase_fderiv_norm_le hs hsm T x
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- (a) `Ψ = θ ↦ θ + u(θ)` is a bijection of `ℝ²` with `‖Ψθ - Ψθ'‖ ≥ ½‖θ - θ'‖`. -/
theorem torus_phase_bijective (hs : 0 < s₀) (hε : 0 ≤ ε) (hsm : 8 * C_K * ε < rhoInf s₀)
    (hC : 0 < C_K) (T : TorusOutput h f ε C_K s₀ E K I ωt) :
    Function.Bijective (fun θ : Fin 2 → ℝ => (realRestriction K θ).1) ∧
      ∀ θ θ' : Fin 2 → ℝ, ‖θ - θ'‖ / 2 ≤
        ‖(realRestriction K θ).1 - (realRestriction K θ').1‖ := by
  have hL := torus_phase_sub_lipschitz hs hε hsm hC T
  have hdist : ∀ θ θ' : Fin 2 → ℝ,
      ‖((realRestriction K θ).1 - θ) - ((realRestriction K θ').1 - θ')‖ ≤ ‖θ - θ'‖ / 2 := by
    intro θ θ'
    have := hL.dist_le_mul θ θ'
    simpa [dist_eq_norm, div_eq_inv_mul] using this
  have hlow : ∀ θ θ' : Fin 2 → ℝ, ‖θ - θ'‖ / 2 ≤
      ‖(realRestriction K θ).1 - (realRestriction K θ').1‖ := by
    intro θ θ'
    have h1 := hdist θ θ'
    have h3 : ‖θ - θ'‖ ≤ ‖(realRestriction K θ).1 - (realRestriction K θ').1‖ +
        ‖((realRestriction K θ).1 - θ) - ((realRestriction K θ').1 - θ')‖ :=
      calc ‖θ - θ'‖ = ‖((realRestriction K θ).1 - (realRestriction K θ').1) -
            (((realRestriction K θ).1 - θ) - ((realRestriction K θ').1 - θ'))‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  refine ⟨⟨fun a b hab => ?_, fun φ => ?_⟩, hlow⟩
  · have h1 := hlow a b
    have h2 : (realRestriction K a).1 = (realRestriction K b).1 := hab
    rw [h2, sub_self, norm_zero] at h1
    have : ‖a - b‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · have hc : ContractingWith (1 / 2 : ℝ≥0)
        (fun θ : Fin 2 → ℝ => φ - ((realRestriction K θ).1 - θ)) := by
      refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h1 := hL.dist_le_mul a b
      have h2 : dist (φ - ((realRestriction K a).1 - a)) (φ - ((realRestriction K b).1 - b)) =
          dist ((realRestriction K a).1 - a) ((realRestriction K b).1 - b) := by
        rw [dist_sub_left]
      rw [h2]
      exact h1
    refine ⟨ContractingWith.fixedPoint _ hc, ?_⟩
    have hfix := ContractingWith.fixedPoint_isFixedPt (f := fun θ : Fin 2 → ℝ =>
      φ - ((realRestriction K θ).1 - θ)) hc
    have hfix' : φ - ((realRestriction K (ContractingWith.fixedPoint _ hc)).1 -
        ContractingWith.fixedPoint _ hc) = ContractingWith.fixedPoint _ hc := hfix
    show (realRestriction K (ContractingWith.fixedPoint _ hc)).1 = φ
    linear_combination -hfix'

/-- (a) `Ψ⁻¹` exists and is `2`-Lipschitz (in particular continuous). -/
theorem torus_phase_inv (hs : 0 < s₀) (hε : 0 ≤ ε) (hsm : 8 * C_K * ε < rhoInf s₀)
    (hC : 0 < C_K) (T : TorusOutput h f ε C_K s₀ E K I ωt) :
    ∃ Ψinv : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      Function.LeftInverse Ψinv (fun θ => (realRestriction K θ).1) ∧
      Function.RightInverse Ψinv (fun θ => (realRestriction K θ).1) ∧ LipschitzWith 2 Ψinv := by
  obtain ⟨⟨hinj, hsurj⟩, hlow⟩ := torus_phase_bijective hs hε hsm hC T
  refine ⟨Function.invFun (fun θ : Fin 2 → ℝ => (realRestriction K θ).1),
    Function.leftInverse_invFun hinj, Function.rightInverse_invFun hsurj, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have ha := Function.rightInverse_invFun hsurj a
  have hb := Function.rightInverse_invFun hsurj b
  have h1 := hlow (Function.invFun (fun θ : Fin 2 → ℝ => (realRestriction K θ).1) a)
    (Function.invFun (fun θ : Fin 2 → ℝ => (realRestriction K θ).1) b)
  rw [ha, hb] at h1
  rw [dist_eq_norm, dist_eq_norm]
  simp only [NNReal.coe_ofNat]
  linarith

/-- (b), (c, energy): `𝒯 = k(ℝ²)` is the graph of a continuous `Y` with `‖Y - I‖ ≤ C_K ε`, and
`H_ℝ(φ, Y φ) = E`. -/
theorem torus_graph (hs : 0 < s₀) (hε : 0 ≤ ε) (hsm : 8 * C_K * ε < rhoInf s₀) (hC : 0 < C_K)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) :
    ∃ Y : (Fin 2 → ℝ) → (Fin 2 → ℝ), Continuous Y ∧ (∀ φ, ‖Y φ - I‖ ≤ C_K * ε) ∧
      range (realRestriction K) = {z : P2 | z.2 = Y z.1} ∧
      ∀ φ, realHamiltonian h f (φ, Y φ) = E := by
  have hρ := rhoInf_pos hs
  obtain ⟨Ψinv, hleft, hright, hlip⟩ := torus_phase_inv hs hε hsm hC T
  have hkc : Continuous (realRestriction K) :=
    continuousOn_univ.mp (analyticOnNhd_realRestriction hρ T.holo).continuousOn
  -- the point `(φ, Y φ)` of the graph is `k (Ψinv φ)`
  have hpt : ∀ φ : Fin 2 → ℝ, (φ, (realRestriction K (Ψinv φ)).2) = realRestriction K (Ψinv φ) :=
    fun φ => Prod.ext (hright φ).symm rfl
  refine ⟨fun φ => (realRestriction K (Ψinv φ)).2, ?_, ?_, ?_, ?_⟩
  · exact continuous_snd.comp (hkc.comp hlip.continuous)
  · intro φ
    have hmem : realInclusion 2 (Ψinv φ) ∈ complexStrip 2 (rhoInf s₀) :=
      realInclusion_mem_complexStrip hρ _
    have h1 := T.close _ hmem
    rw [isRealOnReals_iff.mp T.real (Ψinv φ)] at h1
    have h2 : realInclusion₂ 2 (realRestriction K (Ψinv φ)) -
        (realInclusion 2 (Ψinv φ), toC I) =
        realInclusion₂ 2 (realRestriction K (Ψinv φ) - (Ψinv φ, I)) := by
      rw [map_sub]
      rfl
    rw [h2, norm_realInclusion₂] at h1
    exact (norm_snd_le (realRestriction K (Ψinv φ) - (Ψinv φ, I))).trans h1
  · ext z
    constructor
    · rintro ⟨θ, rfl⟩
      show (realRestriction K θ).2 = (realRestriction K (Ψinv (realRestriction K θ).1)).2
      rw [hleft θ]
    · intro hz
      refine ⟨Ψinv z.1, ?_⟩
      have hz' : z.2 = (realRestriction K (Ψinv z.1)).2 := hz
      refine Prod.ext (hright z.1) hz'.symm
  · intro φ
    have hmem : realInclusion 2 (Ψinv φ) ∈ complexStrip 2 (rhoInf s₀) :=
      realInclusion_mem_complexStrip hρ _
    show realHamiltonian h f (φ, (realRestriction K (Ψinv φ)).2) = E
    rw [hpt φ]
    have h1 : realHamiltonian h f (realRestriction K (Ψinv φ)) =
        (totalH h f (realInclusion₂ 2 (realRestriction K (Ψinv φ)))).re := rfl
    rw [h1, ← isRealOnReals_iff.mp T.real (Ψinv φ), T.energy _ hmem, Complex.ofReal_re]

/-- (c, position): if the base point is in `𝒦` and `C_K ε ≤ r` then `Y φ ∈ 𝒩 = cthickening r 𝒦
⊆ W ⊆ B`. -/
theorem torus_graph_mem {η₁ : ℝ} (p : EnergyPatch (realPart h) B η₁) {r Lm LΦ κ : ℝ}
    (pc : PatchConst p r Lm LΦ κ) {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hY : ∀ φ, ‖Y φ - I‖ ≤ C_K * ε) (hI : I ∈ p.K) (hCr : C_K * ε ≤ r) (φ : Fin 2 → ℝ) :
    Y φ ∈ cthickening r p.K ∧ Y φ ∈ p.W ∧ Y φ ∈ B := by
  have h1 : Y φ ∈ cthickening r p.K :=
    mem_cthickening_of_dist_le (Y φ) I r p.K hI
      (by rw [dist_eq_norm]; exact (hY φ).trans hCr)
  have h2 : Y φ ∈ p.W := pc.thick_subset h1
  exact ⟨h1, h2, p.W_subset_B h2⟩

/-- (c, energy window): `|h(Y φ) - E| ≤ ε` (needs `Y φ ∈ ℝ² ∩ B_{r₀}`). -/
theorem torus_graph_energy_close (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hE : ∀ φ, realHamiltonian h f (φ, Y φ) = E)
    {φ : Fin 2 → ℝ} (hY : Y φ ∈ realAct B r₀) : |realPart h (Y φ) - E| ≤ ε := by
  have h1 := realHam_sub_le hb hf (z := (φ, Y φ)) hY
  rw [hE φ, abs_sub_comm] at h1
  exact h1

end Graph

end KAM.Iso.Confinement
