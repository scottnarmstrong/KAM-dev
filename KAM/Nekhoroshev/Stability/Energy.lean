/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import KAM.Nekhoroshev.Stability.Setting
public import KAM.ODE.Hamiltonian

/-!
# The energy argument (`bpN:p7:resonance-data`, `bpN:p7:energy-core`)

Orthogonal projections of `(ℝⁿ, ⬝ᵥ)` without `EuclideanSpace` (`IsOrthProj`, `exists_orthProj`),
the resonance data `resSpace`, `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound`, and the
reusable energy estimate `energy_core`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Stability

variable {n : ℕ}

/-- An orthogonal projection of `(ℝⁿ, ⟨·,·⟩)` (`dotProduct`), as a linear map. -/
structure IsOrthProj (P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Prop where
  idem : ∀ v, P (P v) = P v
  symm : ∀ u v, P u ⬝ᵥ v = u ⬝ᵥ P v

/-- The orthogonal projection onto any subspace exists (no `EuclideanSpace`: via the dot-product
bilinear form). -/
theorem exists_orthProj (V : Submodule ℝ (Fin n → ℝ)) :
    ∃ P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), IsOrthProj P ∧ (∀ v, P v ∈ V) ∧ ∀ v ∈ V, P v = v := by
  let B : LinearMap.BilinForm ℝ (Fin n → ℝ) := Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) ℝ)
  have hB : ∀ u v, B u v = u ⬝ᵥ v := fun u v => by
    simp [B, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := fun u v h => by
    rw [hB] at h ⊢
    rwa [dotProduct_comm]
  have hself : ∀ x : V, B (x : Fin n → ℝ) x = 0 → x = 0 := fun x h => by
    rw [hB] at h
    exact Subtype.ext (by simpa using h)
  have hnd : (B.restrict V).Nondegenerate :=
    ⟨fun x hx => hself x (by simpa using hx x), fun x hx => hself x (by simpa using hx x)⟩
  have hcompl := B.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  have hmem : ∀ v, V.projection _ hcompl v ∈ V := fun v => Submodule.projection_apply_mem hcompl v
  have hperp : ∀ u v, u ∈ V → v - V.projection _ hcompl v ∈ B.orthogonal V →
      u ⬝ᵥ (v - V.projection _ hcompl v) = 0 :=
    fun u v hu hw => by
      have := (LinearMap.BilinForm.mem_orthogonal_iff).1 hw u hu
      rwa [hB] at this
  have hid : ∀ v ∈ V, V.projection _ hcompl v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hcompl hv
  refine ⟨V.projection _ hcompl, ⟨fun v => hid _ (hmem v), fun u v => ?_⟩, hmem, hid⟩
  have h1 := hperp _ v (hmem u) (Submodule.sub_projection_mem hcompl v)
  have h2 := hperp _ u (hmem v) (Submodule.sub_projection_mem hcompl u)
  rw [dotProduct_sub] at h1 h2
  rw [dotProduct_comm (V.projection _ hcompl v) u] at h2
  rw [dotProduct_comm (V.projection _ hcompl v) (V.projection _ hcompl u)] at h2
  linarith

/-- Linear functionals on `ℝⁿ` are the dot product with their values on the basis. -/
theorem clm_eq_dot (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = (fun i => L (Pi.single i 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [dotProduct, smul_eq_mul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

private theorem taylor_segment {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    (hhR : ContDiffOn ℝ 2 hR U) {x Δ : Fin n → ℝ} (hseg : ∀ a ∈ Icc (0 : ℝ) 1, x + a • Δ ∈ U) :
    ∃ a ∈ Ioo (0 : ℝ) 1, hR (x + Δ) - hR x - fderiv ℝ hR x Δ =
      1 / 2 * hessR hR (x + a • Δ) Δ Δ := by
  set φ : ℝ → ℝ := fun a => hR (x + a • Δ) with hφ
  have hp : ∀ a : ℝ, HasDerivAt (fun a : ℝ => x + a • Δ) Δ a := fun a => by
    simpa using ((hasDerivAt_id a).smul_const Δ).const_add x
  have hat : ∀ a : ℝ, x + a • Δ ∈ U → ContDiffAt ℝ 2 hR (x + a • Δ) := fun a ha =>
    hhR.contDiffAt (hU.mem_nhds ha)
  have hd1 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt φ (fderiv ℝ hR (x + a • Δ) Δ) a := fun a ha =>
    ((hat a ha).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a (hp a)
  have hd2 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (hessR hR (x + a • Δ) Δ Δ) a := fun a ha => by
    have h1 : DifferentiableAt ℝ (fderiv ℝ hR) (x + a • Δ) :=
      ((hat a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h2 := h1.hasFDerivAt.comp_hasDerivAt a (hp a)
    exact (ContinuousLinearMap.apply ℝ ℝ Δ).hasFDerivAt.comp_hasDerivAt a h2
  have hS : IsOpen {a : ℝ | x + a • Δ ∈ U} :=
    hU.preimage (by fun_prop)
  have hderiv : ∀ a ∈ {a : ℝ | x + a • Δ ∈ U}, deriv φ a = fderiv ℝ hR (x + a • Δ) Δ :=
    fun a ha => (hd1 a ha).deriv
  have hcd : ∀ a ∈ uIcc (0 : ℝ) 1, ContDiffAt ℝ 2 φ a := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    exact (hat a (hseg a ha')).comp a (by fun_prop : ContDiffAt ℝ 2 (fun a : ℝ => x + a • Δ) a)
  have hcdOn : ContDiffOn ℝ 2 φ (uIcc 0 1) := fun a ha => (hcd a ha).contDiffWithinAt
  have hud : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact uniqueDiffOn_Icc zero_lt_one
  have hit1 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 1 φ (uIcc 0 1) a = deriv φ a :=
      fun a ha => by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud ((hcd a ha).of_le (by norm_num)) ha,
      iteratedDeriv_one]
  have hit2 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 2 φ (uIcc 0 1) a =
      hessR hR (x + a • Δ) Δ Δ := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hcd a ha) ha, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hev : deriv φ =ᶠ[nhds a] fun a => fderiv ℝ hR (x + a • Δ) Δ :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds (hseg a ha')) hderiv
    rw [hev.deriv_eq]
    exact (hd2 a (hseg a ha')).deriv
  have hIoo : ∀ a ∈ uIoo (0 : ℝ) 1, a ∈ uIcc (0 : ℝ) 1 := fun a ha => by
    rw [uIoo_of_le zero_le_one] at ha
    rw [uIcc_of_le zero_le_one]
    exact Ioo_subset_Icc_self ha
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 1 φ (uIcc 0 1)) (uIoo 0 1) := by
    have h0 : ∀ a ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ) a :=
      fun a ha => (hd2 a (hseg a (by simpa [uIcc_of_le zero_le_one] using ha))).differentiableAt
    refine DifferentiableOn.congr (f := fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (fun a ha => (h0 a (hIoo a ha)).differentiableWithinAt) fun a ha => ?_
    rw [hit1 a (hIoo a ha)]
    exact hderiv a (hseg a (by simpa [uIcc_of_le zero_le_one] using hIoo a ha))
  obtain ⟨a, ha, h⟩ := taylor_mean_remainder_lagrange (n := 1) (x₀ := 0) (x := 1) zero_ne_one
    (hcdOn.of_le (by norm_num)) hdiff
  have ha' : a ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_le zero_le_one] using ha
  refine ⟨a, ha', ?_⟩
  rw [hit2 a (hIoo a ha), taylorWithinEval_succ, taylor_within_zero_eval,
    hit1 0 (by simp), hderiv 0 (by simpa using hseg 0 (by simp))] at h
  simp only [hφ, zero_smul, add_zero, one_smul] at h
  simp at h
  linarith

/-- `R_Λ = {ω : k·ω = 0 ∀ k ∈ Λ}`. -/
def resSpace (Λ : Set (Fin n → ℤ)) : Set (Fin n → ℝ) := {w | ∀ k ∈ Λ, ∑ i, (k i : ℝ) * w i = 0}

/-- `D` is `δ`-close to exact `Λ`-resonances: `dist₂(ω(I), R_Λ) ≤ δ` on `D` (`= ‖Π_Λ ω(I)‖₂`). -/
def IsCloseToRes (D : Set (Fin n → ℝ)) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (δ : ℝ) : Prop :=
  ∀ I ∈ D, ∃ w ∈ resSpace Λ, KAM.Nekhoroshev.euclid (KAM.frequencyMap h I - w) ≤ δ

/-- `m`-convex on `U`. -/
def IsMConvex (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (m : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ, m * KAM.Nekhoroshev.euclid ξ ^ 2 ≤ hessR (KAM.Nekhoroshev.realPart h) I ξ ξ

/-- `ℓ,m`-quasi-convex on `U` (never full positive definiteness). -/
def IsQuasiConvex (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (ℓ m : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ, ℓ * KAM.Nekhoroshev.euclid ξ < |KAM.frequencyMap h I ⬝ᵥ ξ| ∨
    m * KAM.Nekhoroshev.euclid ξ ^ 2 ≤ hessR (KAM.Nekhoroshev.realPart h) I ξ ξ

/-- `‖Q(I)‖_{2→2} ≤ M` on `U`. -/
def HessBound (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (M : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ η, |hessR (KAM.Nekhoroshev.realPart h) I ξ η| ≤
    M * KAM.Nekhoroshev.euclid ξ * KAM.Nekhoroshev.euclid η

theorem euclid_sq_eq_dot (x : Fin n → ℝ) : KAM.Nekhoroshev.euclid x ^ 2 = x ⬝ᵥ x := by
  unfold KAM.Nekhoroshev.euclid
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [dotProduct, sq]

/-- Cauchy–Schwarz for `dotProduct` in the Euclidean size. -/
theorem abs_dot_le_euclid (u v : Fin n → ℝ) :
    |u ⬝ᵥ v| ≤ KAM.Nekhoroshev.euclid u * KAM.Nekhoroshev.euclid v := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h2 : (u ⬝ᵥ v) ^ 2 ≤ (KAM.Nekhoroshev.euclid u * KAM.Nekhoroshev.euclid v) ^ 2 := by
    rw [mul_pow, euclid_sq_eq_dot, euclid_sq_eq_dot]
    simpa [dotProduct, sq] using h
  exact abs_le_of_sq_le_sq h2 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

section Core

variable {U : Set (Fin n → ℝ)} {hR : (Fin n → ℝ) → ℝ} {g f HR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

private theorem HR_diffAt (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g (univ ×ˢ U))
    (hf : ContDiffOn ℝ 1 f (univ ×ˢ U)) (hhR : ContDiffOn ℝ 2 hR U)
    (hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, HR x = hR x.2 + g x + f x)
    {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ (univ : Set (Fin n → ℝ)) ×ˢ U) :
    DifferentiableAt ℝ HR w ∧ fderiv ℝ HR w = fderiv ℝ (fun x => hR x.2) w +
      fderiv ℝ g w + fderiv ℝ f w := by
  have hW : (univ : Set (Fin n → ℝ)) ×ˢ U ∈ nhds w := (isOpen_univ.prod hU).mem_nhds hw
  have h1 : DifferentiableAt ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) => hR x.2) w :=
    ((hhR.contDiffAt (hU.mem_nhds hw.2)).differentiableAt (by norm_num)).comp w
      differentiableAt_snd
  have h2 : DifferentiableAt ℝ g w := (hg.contDiffAt hW).differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ f w := (hf.contDiffAt hW).differentiableAt (by norm_num)
  have hev : HR =ᶠ[nhds w] fun x => hR x.2 + g x + f x :=
    Filter.eventuallyEq_of_mem hW hHR
  exact ⟨(h1.add h2 |>.add h3).congr_of_eventuallyEq hev, by
    rw [hev.fderiv_eq]
    change fderiv ℝ ((fun x => hR x.2) + g + f) w = _
    rw [fderiv_add (h1.add h2) h3, fderiv_add h1 h2]⟩

private theorem theta_split (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g (univ ×ˢ U))
    (hf : ContDiffOn ℝ 1 f (univ ×ˢ U)) (hhR : ContDiffOn ℝ 2 hR U)
    (hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, HR x = hR x.2 + g x + f x)
    {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ (univ : Set (Fin n → ℝ)) ×ˢ U) (i : Fin n) :
    fderiv ℝ HR w (Pi.single i 1, 0) = thetaGradR g w i + thetaGradR f w i := by
  have h1 : DifferentiableAt ℝ hR w.2 :=
    (hhR.contDiffAt (hU.mem_nhds hw.2)).differentiableAt (by norm_num)
  have h2 := (h1.hasFDerivAt.comp w hasFDerivAt_snd).fderiv
  rw [(HR_diffAt hU hg hf hhR hHR hw).2]
  simp [thetaGradR, show (fun x : (Fin n → ℝ) × (Fin n → ℝ) => hR x.2) = hR ∘ Prod.snd from rfl,
    h2]

/-- Derivative of `τ ↦ c ⬝ᵥ (z τ).2` along a solution: `-(c ⬝ θ-gradient)`. -/
private theorem hasDerivAt_dot_snd (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g (univ ×ˢ U))
    (hf : ContDiffOn ℝ 1 f (univ ×ˢ U)) (hhR : ContDiffOn ℝ 2 hR U)
    (hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, HR x = hR x.2 + g x + f x)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {t : ℝ} {c : Fin n → ℝ}
    (hz : z t ∈ (univ : Set (Fin n → ℝ)) ×ˢ U)
    (hd : HasDerivAt z (KAM.hamiltonianVectorField HR (z t)) t) :
    HasDerivAt (fun τ => c ⬝ᵥ (z τ).2) (-(c ⬝ᵥ (thetaGradR g (z t) + thetaGradR f (z t)))) t := by
  have h2 : HasDerivAt (fun τ => (z τ).2) (KAM.hamiltonianVectorField HR (z t)).2 t := hd.snd
  have h3 : ∀ i, HasDerivAt (fun τ => (z τ).2 i) ((KAM.hamiltonianVectorField HR (z t)).2 i) t :=
    fun i => (hasDerivAt_pi.1 h2) i
  have h4 : HasDerivAt (fun τ => ∑ i, c i * (z τ).2 i)
      (∑ i, c i * (KAM.hamiltonianVectorField HR (z t)).2 i) t :=
    HasDerivAt.fun_sum fun i _ => (h3 i).const_mul (c i)
  convert h4 using 1
  · rfl
  show -(∑ i, c i * (thetaGradR g (z t) + thetaGradR f (z t)) i) = _
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ = c i * -fderiv ℝ HR (z t) (Pi.single i 1, 0)
  rw [theta_split hU hg hf hhR hHR hz i]
  simp only [Pi.add_apply]
  ring

end Core

/-- `bpN:p7:energy-core` (reusable core; track I, Part 11). -/
theorem energy_core {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    {g f HR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hhR : ContDiffOn ℝ 2 hR U)
    (hg : ContDiffOn ℝ 1 g (univ ×ˢ U)) (hf : ContDiffOn ℝ 1 f (univ ×ˢ U))
    (hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, HR x = hR x.2 + g x + f x)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (hgP : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, P (thetaGradR g x) = thetaGradR g x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField HR) (univ ×ˢ U) J z) {t₁ : ℝ}
    (ht₁ : t₁ ∈ J) (hseg : ∀ a ∈ Icc (0 : ℝ) 1, (z 0).2 + a • ((z t₁).2 - (z 0).2) ∈ U) :
    -- (a)
    hR (z t₁).2 - hR (z 0).2 = -((g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0))) ∧
    -- (b)
    (∀ B, (∀ τ ∈ uIcc 0 t₁, KAM.Nekhoroshev.euclid (thetaGradR f (z τ)) ≤ B) →
      KAM.Nekhoroshev.euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2)) ≤ |t₁| * B) ∧
    -- (c)
    (∃ a ∈ Ioo (0 : ℝ) 1, hR (z t₁).2 - hR (z 0).2 -
        (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1)) ⬝ᵥ ((z t₁).2 - (z 0).2) =
      1 / 2 * hessR hR ((z 0).2 + a • ((z t₁).2 - (z 0).2)) ((z t₁).2 - (z 0).2)
        ((z t₁).2 - (z 0).2)) ∧
    -- (d)
    (∀ m, (∀ a ∈ Icc (0 : ℝ) 1, m * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
        hessR hR ((z 0).2 + a • ((z t₁).2 - (z 0).2)) ((z t₁).2 - (z 0).2) ((z t₁).2 - (z 0).2)) →
      m / 2 * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
        |(g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0))| +
        KAM.Nekhoroshev.euclid (P (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1))) *
          KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) +
        KAM.Nekhoroshev.euclid (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1)) *
          KAM.Nekhoroshev.euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2))) := by
  have hmem : ∀ t ∈ J, z t ∈ (univ : Set (Fin n → ℝ)) ×ˢ U := fun t ht => (hz t ht).1
  have h0' := hmem 0 h0
  have h1' := hmem t₁ ht₁
  set Δ : Fin n → ℝ := (z t₁).2 - (z 0).2 with hΔ
  clear_value Δ
  have ha : hR (z t₁).2 - hR (z 0).2 = -((g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0))) := by
    have := KAM.ODE.ham_energy hJ (fun t ht => ⟨(HR_diffAt hU hg hf hhR hHR (hmem t ht)).1,
      (hz t ht).2⟩) 0 h0 t₁ ht₁
    rw [hHR _ h0', hHR _ h1'] at this
    linarith
  have hPc : P (Δ - P Δ) = 0 := by rw [map_sub, hP.idem, sub_self]
  have hcΔ : (Δ - P Δ) ⬝ᵥ Δ = (Δ - P Δ) ⬝ᵥ (Δ - P Δ) := by
    have : (Δ - P Δ) ⬝ᵥ P Δ = 0 := by
      rw [← hP.symm, hPc, zero_dotProduct]
    rw [dotProduct_sub (Δ - P Δ) Δ (P Δ), this, sub_zero]
  have hb : ∀ B, (∀ τ ∈ uIcc 0 t₁, KAM.Nekhoroshev.euclid (thetaGradR f (z τ)) ≤ B) →
      KAM.Nekhoroshev.euclid (Δ - P Δ) ≤ |t₁| * B := by
    intro B hB
    set c : Fin n → ℝ := Δ - P Δ with hc
    have hsub : uIcc 0 t₁ ⊆ J := hJ.uIcc_subset h0 ht₁
    have hder : ∀ τ ∈ uIcc 0 t₁, HasDerivWithinAt (fun τ => c ⬝ᵥ (z τ).2)
        (-(c ⬝ᵥ thetaGradR f (z τ))) (uIcc 0 t₁) τ := fun τ hτ => by
      have := hasDerivAt_dot_snd hU hg hf hhR hHR (c := c) (hmem τ (hsub hτ)) (hz τ (hsub hτ)).2
      have hg0 : c ⬝ᵥ thetaGradR g (z τ) = 0 := by
        rw [← hgP _ (hmem τ (hsub hτ)), ← hP.symm, hPc, zero_dotProduct]
      rw [dotProduct_add, hg0, zero_add] at this
      exact this.hasDerivWithinAt
    have hbd : ∀ τ ∈ uIcc 0 t₁, ‖-(c ⬝ᵥ thetaGradR f (z τ))‖ ≤ KAM.Nekhoroshev.euclid c * B :=
      fun τ hτ => by
        rw [norm_neg, Real.norm_eq_abs]
        exact (abs_dot_le_euclid _ _).trans
          (mul_le_mul_of_nonneg_left (hB τ hτ) (Real.sqrt_nonneg _))
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
      (convex_uIcc 0 t₁) left_mem_uIcc right_mem_uIcc
    have hval : c ⬝ᵥ (z t₁).2 - c ⬝ᵥ (z 0).2 = KAM.Nekhoroshev.euclid c ^ 2 := by
      rw [← dotProduct_sub, euclid_sq_eq_dot, ← hΔ]
      exact hcΔ
    rw [hval, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hmv
    have hE : 0 ≤ KAM.Nekhoroshev.euclid c := Real.sqrt_nonneg _
    have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans (hB 0 left_mem_uIcc)
    rcases hE.eq_or_lt with h | h
    · rw [← h]; exact mul_nonneg (abs_nonneg _) hB0
    · nlinarith [mul_pos h h]
  have hc : ∃ a ∈ Ioo (0 : ℝ) 1, hR (z t₁).2 - hR (z 0).2 -
        (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1)) ⬝ᵥ Δ =
      1 / 2 * hessR hR ((z 0).2 + a • Δ) Δ Δ := by
    obtain ⟨a, ha, h⟩ := taylor_segment hU hhR hseg
    refine ⟨a, ha, ?_⟩
    rw [← clm_eq_dot (fderiv ℝ hR (z 0).2) Δ, ← h, hΔ, add_sub_cancel]
  refine ⟨ha, hb, hc, fun m hm => ?_⟩
  obtain ⟨a, ha', h⟩ := hc
  have hm' := hm a (Ioo_subset_Icc_self ha')
  set G : Fin n → ℝ := fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1) with hG
  clear_value G
  have hsplit : G ⬝ᵥ Δ = P G ⬝ᵥ Δ + G ⬝ᵥ (Δ - P Δ) := by
    rw [hP.symm G Δ, ← dotProduct_add]
    congr 1
    abel
  have h1 := abs_dot_le_euclid (P G) Δ
  have h2 := abs_dot_le_euclid G (Δ - P Δ)
  have h3 := neg_le_abs (P G ⬝ᵥ Δ)
  have h4 := neg_le_abs (G ⬝ᵥ (Δ - P Δ))
  have h5 := neg_le_abs ((g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0)))
  linarith

end KAM.Stability

end
