/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Planetary.Preparation.PreparedCauchy
public import KAM.Planetary.Preparation.SlowSmall

/-!
# Jet inputs of the prepared frequency (P11A-P8b, `stepP:p11:pr-in`)

Helper lemmas, parametric in the slow datum `A` with `P11SlowSpecOf C Fast nu eps c A` (so they
apply to `p11SlowData D nu eps` through `P11SlowSpec`).  They are exported helpers, not the signed
`prepared` / `amount` (which are assembled in P8e).

* `p11_prin_g2_jet`, `p11_prin_g2_jet_log`: step pr-in (iii), the mixed Cauchy estimate for `g₂`
  with radii `s₂/4` in `J` and `ε/4` in `ρ̃`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section PrIn

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

private theorem p11Box_isOpen_aux {a b : ℕ} (c : P11CVec (a+b)) (r1 r2 : ℝ) :
    IsOpen (p11Box c r1 r2) := by
  rw [p11Box_eq]
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

private theorem prin_prod_append (α γ : Fin n → ℕ) (f : ℕ → ℝ) :
    ∏ j : Fin (n+n), f (Fin.append α γ j) = (∏ i, f (α i)) * ∏ i, f (γ i) := by
  rw [Fin.prod_univ_add]; simp [Fin.append_left]

private theorem prin_poly_prod (α γ : Fin n → ℕ) (r1 r2 : ℝ) :
    ∏ j : Fin (n+n), p11BoxRad n n r1 r2 j ^ (Fin.append α γ j) =
      r1 ^ (∑ i, α i) * r2 ^ (∑ i, γ i) := by
  rw [Fin.prod_univ_add]
  simp [p11BoxRad, Fin.append_left, Finset.prod_pow_eq_pow_sum]

/-- Step pr-in (iii), sharp form: the mixed Cauchy estimate for `g₂` on the polydisc of radii
`s₂/4` (in `J`) and `ε/4` (in `ρ̃`). -/
theorem p11_prin_g2_jet {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hs2 : 0 < p11s2 C nu eps) (heps : 0 < eps) (hc : P11SlowSpecOf C Fast nu eps c A)
    (α γ : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2*Real.pi*eps : ℂ))‖ < 5*eps/4) :
    ‖p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n+n)) (_ : Fin 1) => A.g2 I)
        (Fin.append J ρ)‖ ≤
      (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
        (c*eps^3*Real.log (1/eps)^(5*C.tau+2)) /
        ((p11s2 C nu eps/4) ^ (∑ i, α i) * (eps/4) ^ (∑ i, γ i)) := by
  obtain ⟨-, -, -, -, -, -, -, hdg, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbg, -, -⟩ := hc
  have hπ := Real.pi_gt_three
  have hUo := p11Box_isOpen_aux (Fin.append (KAM.realInclusion n C.J0)
    (fun _ : Fin n => (2*Real.pi*eps : ℂ))) (p11s2 C nu eps/2) (Real.pi*eps/2)
  have hR : ∀ j, 0 < p11BoxRad n n (p11s2 C nu eps/4) (eps/4) j := fun j => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11BoxRad] <;> positivity
  have hcl : {y : P11CVec (n+n) | ∀ j, ‖y j - Fin.append J ρ j‖ ≤
      p11BoxRad n n (p11s2 C nu eps/4) (eps/4) j} ⊆
      p11Box (Fin.append (KAM.realInclusion n C.J0) (fun _ : Fin n => (2*Real.pi*eps : ℂ)))
        (p11s2 C nu eps/2) (Real.pi*eps/2) := by
    intro y hy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := hy (Fin.castAdd n i)
      simp only [p11BoxRad, Fin.append_left] at h1 ⊢
      have h2 : ‖J i - KAM.realInclusion n C.J0 i‖ < p11s2 C nu eps/4 :=
        lt_of_le_of_lt (by simpa using norm_le_pi_norm (J - KAM.realInclusion n C.J0) i) hJ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.castAdd n i)) (J i)
        (KAM.realInclusion n C.J0 i)
      linarith
    · have h1 := hy (Fin.natAdd n i)
      simp only [p11BoxRad, Fin.append_right] at h1 ⊢
      have h2 : ‖ρ i - (2*Real.pi*eps : ℂ)‖ < 5*eps/4 :=
        lt_of_le_of_lt (norm_le_pi_norm (ρ - fun _ : Fin n => (2*Real.pi*eps : ℂ)) i) hρ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.natAdd n i)) (ρ i) (2*Real.pi*eps : ℂ)
      nlinarith
  have hg : DifferentiableOn ℂ (fun (I : P11CVec (n+n)) (_ : Fin 1) => A.g2 I)
      (p11Box (Fin.append (KAM.realInclusion n C.J0) (fun _ : Fin n => (2*Real.pi*eps : ℂ)))
        (p11s2 C nu eps/2) (Real.pi*eps/2)) :=
    differentiableOn_pi.2 fun _ => hdg
  have hM : ∀ w ∈ p11Box (Fin.append (KAM.realInclusion n C.J0)
      (fun _ : Fin n => (2*Real.pi*eps : ℂ))) (p11s2 C nu eps/2) (Real.pi*eps/2),
      ‖(fun _ : Fin 1 => A.g2 w)‖ ≤ c*eps^3*Real.log (1/eps)^(5*C.tau+2) := fun w hw => by
    rw [pi_norm_const]; exact hbg w hw
  have h := p11PartialVec_norm_le_poly hUo hg hR hcl hM (Fin.append α γ)
  rw [prin_prod_append α γ (fun k => (k.factorial : ℝ)), prin_poly_prod] at h
  refine h.trans (le_of_eq ?_)
  ring

end PrIn

end KAM.Planetary

end
