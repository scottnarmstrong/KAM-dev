/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffCalculus

/-!
# Second- and third-order rules for directional derivatives

The second-order rules (sums, products, `exp`, the inverse) and their third-order analogues, on
top of the first-order rules of `KAM.Certificate.Expr.DiffCalculus`. Each is an equality on an open
set `S` of the iterated directional derivative `jetDeriv u (jetDeriv v (jetDeriv w f))`. The module
also identifies the third iterated derivative with an iterated directional derivative (the
counterpart of `iteratedFDeriv_two_eq_jetDeriv`).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

theorem JetSmoothOn.jetNeg {S : Set Ph} {f : Ph → ℂ} (hf : JetSmoothOn S f) :
    JetSmoothOn S (fun z => -f z) := ContDiffOn.neg hf

theorem jetDeriv_neg {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (fun z => -f z)) (fun z => -jetDeriv u f z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  have e : fderiv ℂ (fun z => -f z) z = -fderiv ℂ f z := h1.hasFDerivAt.neg.fderiv
  simp only [jetDeriv]
  rw [e]
  rfl

theorem jetDeriv2_mul {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => f z * g z)))
      (fun z => (jetDeriv u (jetDeriv v f) z * g z + jetDeriv v f z * jetDeriv u g z) +
        (jetDeriv u f z * jetDeriv v g z + f z * jetDeriv u (jetDeriv v g) z)) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_mul hS v hf hg) hz,
    jetDeriv_add hS u ((hf.jetDeriv hS v).mul hg) (hf.mul (hg.jetDeriv hS v)) hz]
  beta_reduce
  rw [jetDeriv_mul hS u (hf.jetDeriv hS v) hg hz, jetDeriv_mul hS u hf (hg.jetDeriv hS v) hz]

theorem jetDeriv2_add {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => f z + g z)))
      (fun z => jetDeriv u (jetDeriv v f) z + jetDeriv u (jetDeriv v g) z) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_add hS v hf hg) hz]
  beta_reduce
  rw [jetDeriv_add hS u (hf.jetDeriv hS v) (hg.jetDeriv hS v) hz]

theorem jetDeriv2_cexp {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => Complex.exp (f z))))
      (fun z => Complex.exp (f z) * (jetDeriv u f z * jetDeriv v f z) +
        Complex.exp (f z) * jetDeriv u (jetDeriv v f) z) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_cexp hS v hf) hz,
    jetDeriv_mul hS u hf.cexp (hf.jetDeriv hS v) hz]
  beta_reduce
  rw [jetDeriv_cexp hS u hf hz]
  ring

theorem jetDeriv2_inv {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => (f z)⁻¹)))
      (fun z => 2 * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) * (jetDeriv u f z * jetDeriv v f z) +
        (-1) * ((f z)⁻¹ * (f z)⁻¹) * jetDeriv u (jetDeriv v f) z) S := by
  intro z hz
  have hw := hf.inv h0
  have hww := hw.mul hw
  have hnww := hww.neg
  rw [jetDeriv_congr hS u (jetDeriv_inv hS v hf h0) hz]
  have hm : JetSmoothOn S (fun z => -((f z)⁻¹ * (f z)⁻¹)) := hnww
  rw [jetDeriv_mul hS u hm (hf.jetDeriv hS v) hz]
  beta_reduce
  rw [jetDeriv_neg hS u hww hz]
  beta_reduce
  rw [jetDeriv_mul hS u hw hw hz]
  beta_reduce
  rw [jetDeriv_inv hS u hf h0 hz]
  ring

/-! ### Third-order rules -/

theorem jetDeriv_congr2 {S : Set Ph} (hS : IsOpen S) (u v : Ph) {F G : Ph → ℂ}
    (h : Set.EqOn F G S) :
    Set.EqOn (jetDeriv u (jetDeriv v F)) (jetDeriv u (jetDeriv v G)) S :=
  jetDeriv_congr hS u (jetDeriv_congr hS v h)

theorem jetDeriv_cmul {S : Set Ph} (hS : IsOpen S) (u : Ph) (c : ℂ) {g : Ph → ℂ}
    (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (fun z => c * g z)) (fun z => c * jetDeriv u g z) S := by
  intro z hz
  have := jetDeriv_mul hS u (JetSmoothOn.const S c) hg hz
  rw [jetDeriv_const] at this
  simpa using this

theorem jetDeriv3_add {S : Set Ph} (hS : IsOpen S) (u v w : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (jetDeriv w (fun z => f z + g z))))
      (fun z => jetDeriv u (jetDeriv v (jetDeriv w f)) z +
        jetDeriv u (jetDeriv v (jetDeriv w g)) z) S := by
  intro z hz
  rw [jetDeriv_congr2 hS u v (jetDeriv_add hS w hf hg) hz]
  beta_reduce
  exact jetDeriv2_add hS u v (hf.jetDeriv hS w) (hg.jetDeriv hS w) hz

theorem jetDeriv3_mul {S : Set Ph} (hS : IsOpen S) (u v w : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (jetDeriv w (fun z => f z * g z))))
      (fun z => ((jetDeriv u (jetDeriv v (jetDeriv w f)) z * g z +
          jetDeriv v (jetDeriv w f) z * jetDeriv u g z) +
        (jetDeriv u (jetDeriv w f) z * jetDeriv v g z +
          jetDeriv w f z * jetDeriv u (jetDeriv v g) z)) +
        ((jetDeriv u (jetDeriv v f) z * jetDeriv w g z +
          jetDeriv v f z * jetDeriv u (jetDeriv w g) z) +
        (jetDeriv u f z * jetDeriv v (jetDeriv w g) z +
          f z * jetDeriv u (jetDeriv v (jetDeriv w g)) z))) S := by
  intro z hz
  have hfw := hf.jetDeriv hS w
  have hgw := hg.jetDeriv hS w
  rw [jetDeriv_congr2 hS u v (jetDeriv_mul hS w hf hg) hz]
  beta_reduce
  rw [jetDeriv2_add hS u v (hfw.mul hg) (hf.mul hgw) hz]
  beta_reduce
  rw [jetDeriv2_mul hS u v hfw hg hz, jetDeriv2_mul hS u v hf hgw hz]

theorem jetDeriv3_cexp {S : Set Ph} (hS : IsOpen S) (u v w : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (jetDeriv v (jetDeriv w (fun z => Complex.exp (f z)))))
      (fun z => Complex.exp (f z) * (jetDeriv u f z * (jetDeriv v f z * jetDeriv w f z) +
        (jetDeriv u (jetDeriv v f) z * jetDeriv w f z +
          jetDeriv v f z * jetDeriv u (jetDeriv w f) z +
          jetDeriv u f z * jetDeriv v (jetDeriv w f) z +
          jetDeriv u (jetDeriv v (jetDeriv w f)) z))) S := by
  intro z hz
  rw [jetDeriv_congr2 hS u v (jetDeriv_cexp hS w hf) hz]
  beta_reduce
  rw [jetDeriv2_mul hS u v hf.cexp (hf.jetDeriv hS w) hz]
  beta_reduce
  rw [jetDeriv2_cexp hS u v hf hz, jetDeriv_cexp hS u hf hz, jetDeriv_cexp hS v hf hz]
  ring

theorem jetDeriv_inv_sq {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (fun z => (f z)⁻¹ * (f z)⁻¹))
      (fun z => -2 * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) * jetDeriv u f z) S := by
  intro z hz
  have hw := hf.inv h0
  rw [jetDeriv_mul hS u hw hw hz]
  beta_reduce
  rw [jetDeriv_inv hS u hf h0 hz]
  ring

theorem jetDeriv_inv_cube {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (fun z => (f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)))
      (fun z => -3 * ((f z)⁻¹ * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹))) * jetDeriv u f z) S := by
  intro z hz
  have hw := hf.inv h0
  rw [jetDeriv_mul hS u hw (hw.mul hw) hz]
  beta_reduce
  rw [jetDeriv_inv hS u hf h0 hz, jetDeriv_inv_sq hS u hf h0 hz]
  ring

theorem jetDeriv3_inv {S : Set Ph} (hS : IsOpen S) (u v w : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (jetDeriv v (jetDeriv w (fun z => (f z)⁻¹))))
      (fun z => -6 * ((f z)⁻¹ * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹))) *
          (jetDeriv u f z * (jetDeriv v f z * jetDeriv w f z)) +
        (2 * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) *
          ((jetDeriv u (jetDeriv v f) z * jetDeriv w f z +
            jetDeriv v f z * jetDeriv u (jetDeriv w f) z) +
            jetDeriv u f z * jetDeriv v (jetDeriv w f) z) +
        (-1) * ((f z)⁻¹ * (f z)⁻¹) * jetDeriv u (jetDeriv v (jetDeriv w f)) z)) S := by
  intro z hz
  have hw := hf.inv h0
  have hw2 := hw.mul hw
  have hw3 := hw.mul hw2
  have hfv := hf.jetDeriv hS v
  have hfw := hf.jetDeriv hS w
  have hfvw := hfv.jetDeriv hS w
  have hA : JetSmoothOn S (fun z => 2 * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) *
      (jetDeriv v f z * jetDeriv w f z)) :=
    ((JetSmoothOn.const S 2).mul hw3).mul (hfv.mul hfw)
  have hB : JetSmoothOn S (fun z => (-1) * ((f z)⁻¹ * (f z)⁻¹) * jetDeriv v (jetDeriv w f) z) :=
    ((JetSmoothOn.const S (-1)).mul hw2).mul (hf.jetDeriv hS w |>.jetDeriv hS v)
  rw [jetDeriv_congr hS u (jetDeriv2_inv hS v w hf h0) hz]
  rw [jetDeriv_add hS u hA hB hz]
  beta_reduce
  rw [jetDeriv_mul hS u ((JetSmoothOn.const S 2).mul hw3) (hfv.mul hfw) hz,
    jetDeriv_mul hS u ((JetSmoothOn.const S (-1)).mul hw2) (hf.jetDeriv hS w |>.jetDeriv hS v) hz]
  beta_reduce
  rw [jetDeriv_cmul hS u 2 hw3 hz, jetDeriv_cmul hS u (-1) hw2 hz,
    jetDeriv_mul hS u hfv hfw hz]
  beta_reduce
  rw [jetDeriv_inv_sq hS u hf h0 hz, jetDeriv_inv_cube hS u hf h0 hz]
  ring

/-- The third iterated derivative is an iterated directional derivative. -/
theorem iteratedFDeriv_three_eq_jetDeriv {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) {z : Ph} (hz : z ∈ S) (u v w : Ph) :
    iteratedFDeriv ℂ 3 f z ![u, v, w] = jetDeriv u (jetDeriv v (jetDeriv w f)) z := by
  have hc : ∀ y ∈ S, ContDiffAt ℂ 3 f y := fun y hy =>
    (hf.contDiffAt (hS.mem_nhds hy)).of_le (by simp)
  rw [iteratedFDeriv_succ_apply_left]
  have h2 : DifferentiableAt ℂ (iteratedFDeriv ℂ 2 f) z :=
    ((hc z hz).differentiableAt_iteratedFDeriv (m := 2) (by norm_num))
  let E : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => Ph) ℂ →L[ℂ] ℂ :=
    ContinuousMultilinearMap.apply ℂ (fun _ : Fin 2 => Ph) ℂ ![v, w]
  have e1 : fderiv ℂ (fun y => E (iteratedFDeriv ℂ 2 f y)) z =
      E.comp (fderiv ℂ (iteratedFDeriv ℂ 2 f) z) := by
    exact (E.hasFDerivAt.comp z h2.hasFDerivAt).fderiv
  have e2 : (fun y => E (iteratedFDeriv ℂ 2 f y)) =ᶠ[nhds z] jetDeriv v (jetDeriv w f) := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact iteratedFDeriv_two_eq_jetDeriv ((hc y hy).of_le (by norm_num)) v w
  have e3 := congrArg (fun L => L u) (e1.symm.trans (e2.fderiv_eq))
  simp only [ContinuousLinearMap.comp_apply] at e3
  have ht : (Fin.tail ![u, v, w] : Fin 2 → Ph) = ![v, w] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact e3

end KAM.Certificate

end
