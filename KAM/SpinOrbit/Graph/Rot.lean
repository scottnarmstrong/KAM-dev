/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Inverse
public import KAM.SpinOrbit.Rotated

/-!
# Graph inversion in the rotated frame (track SO, package SO-GRAPHR; owner ruling O5)

Unfrozen helper code. The exact torus of the time-scaled rotated client `c · H'` is turned into an
invariant barrier of the original lunar flow.

* `SoGraph.torus_of_rot`: the shear `(x, y) ↦ (x - y, y)` takes the rotated real data
  (`Q₀`, `P₀`, clock `y + c₀`, frequency `(ν - 1, 1)`) to the generic core's `SoGraph.Torus`.
* `soBarrier_of_exact_rotTorus`: the rotated-frame exact torus is an `SoBarrier`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

namespace SoGraph

/-- **Shear** `(x, y) ↦ (x - y, y)`: rotated real data (`Q₁` the angle `Q₀`, `Pp` the momentum
`P₀ = p`, clock `φ = y + c`, flow at `(ν - 1, 1)`) give the generic core's data at `(ν, 1)`:
`q = Q₀ + Q₁`, i.e. `Q x y = Q₁ (x - y) y + y + c`, `Pp x y = Pp (x - y) y`. -/
theorem torus_of_rot {Q₁ Pp dQ : ℝ → ℝ → ℝ} {ν c m : ℝ} (hm : 0 < m)
    (hQc : Continuous fun z : ℝ × ℝ => Q₁ z.1 z.2) (hPc : Continuous fun z : ℝ × ℝ => Pp z.1 z.2)
    (hQ₀ : ∀ x y, Q₁ (x + 1) y = Q₁ x y + 1) (hQ₁ : ∀ x y, Q₁ x (y + 1) = Q₁ x y)
    (hP₀ : ∀ x y, Pp (x + 1) y = Pp x y) (hP₁ : ∀ x y, Pp x (y + 1) = Pp x y)
    (hdQ : ∀ x y, HasDerivAt (fun s => Q₁ s y) (dQ x y) x) (hmono : ∀ x y, m ≤ dQ x y)
    (hflowQ : ∀ x y, HasDerivAt (fun t => Q₁ (x + t * (ν - 1)) (y + t)) (Pp x y - 1) 0)
    (hflowP : ∀ x y, HasDerivAt (fun t => Pp (x + t * (ν - 1)) (y + t))
      (-soVq (Q₁ x y + y + c) (y + c)) 0) :
    Torus (fun x y => Q₁ (x - y) y + y + c) (fun x y => Pp (x - y) y)
      (fun x y => dQ (x - y) y) ν c m := by
  have hsh : Continuous fun z : ℝ × ℝ => (z.1 - z.2, z.2) :=
    (continuous_fst.sub continuous_snd).prodMk continuous_snd
  refine ⟨hm, ?_, hPc.comp hsh, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_,
    fun x y => ?_, fun x y => hmono _ _, fun x y => ?_, fun x y => ?_⟩
  · have := hQc.comp hsh
    fun_prop
  · have := hQ₀ (x - y) y
    rw [show x + 1 - y = x - y + 1 by ring, this]; ring
  · have h1 := hQ₀ (x - y - 1) (y + 1)
    rw [sub_add_cancel, hQ₁] at h1
    show Q₁ (x - (y + 1)) (y + 1) + (y + 1) + c = Q₁ (x - y) y + y + c
    rw [show x - (y + 1) = x - y - 1 by ring]
    linarith
  · show Pp (x + 1 - y) y = Pp (x - y) y
    rw [show x + 1 - y = x - y + 1 by ring, hP₀]
  · show Pp (x - (y + 1)) (y + 1) = Pp (x - y) y
    have h1 := hP₀ (x - y - 1) (y + 1)
    rw [sub_add_cancel, hP₁] at h1
    rw [show x - (y + 1) = x - y - 1 by ring, ← h1]
  · exact ((hdQ (x - y) y).comp_sub_const x y).add_const _ |>.add_const _
  · have h := (hflowQ (x - y) y).add (((hasDerivAt_id (0 : ℝ)).const_add y).add_const c)
    have e : (fun t : ℝ => Q₁ (x + t * ν - (y + t)) (y + t) + (y + t) + c) =
        fun t => Q₁ (x - y + t * (ν - 1)) (y + t) + (y + id t) + c := by
      funext t; rw [show x + t * ν - (y + t) = x - y + t * (ν - 1) by ring]; rfl
    show HasDerivAt (fun t : ℝ => Q₁ (x + t * ν - (y + t)) (y + t) + (y + t) + c) _ 0
    rw [e]
    convert h using 1
    · funext t; simp [add_assoc]
    · ring
  · have h := hflowP (x - y) y
    have e : (fun t : ℝ => Pp (x + t * ν - (y + t)) (y + t)) =
        fun t => Pp (x - y + t * (ν - 1)) (y + t) := by
      funext t; rw [show x + t * ν - (y + t) = x - y + t * (ν - 1) by ring]
    show HasDerivAt (fun t : ℝ => Pp (x + t * ν - (y + t)) (y + t)) _ 0
    rw [e]
    exact h

end SoGraph

/-- The scaled Diophantine inequality: `s • ω` is `(s γ, τ)`-Diophantine for `s > 0`. -/
theorem isDiophantine_smul_scale {n : ℕ} {γ τ s : ℝ} {ω : Fin n → ℝ} (hs : 0 < s)
    (hdio : IsDiophantine γ τ ω) : IsDiophantine (s * γ) τ (s • ω) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (s • ω) i = s * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_pos hs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hdio k hk) hs.le

open SoGraph in
/-- **Rotated-frame exact torus ⇒ barrier** (SO-GRAPHR). `K∞` is the black box's exact torus for
the scaled client `c · H'`, invariant at `s∞ ω*` with `s∞ ω*` Diophantine. With
`∂_{θ₀} Q₀ ≥ m > 0` and `P₀ ∈ [lo, hi]` on the real torus: `invarianceError_const_mul` and
`isDiophantine_smul_scale` move to `H'` at `(s∞/c) ω*`; the landed `clock_frequency` (with
`soRotHamExpr_clock`) gives `Q₁ = θ₁ + c₀` and `(s∞/c) ω*₁ = 1`; `hamiltonianVectorFieldℂ_soRotHC`
gives the real flow `d/dt Q₀ = P₀ - 1`, `d/dt P₀ = -∂_q V(Q₀ + Q₁, Q₁)` at `(ν - 1, 1)`,
`ν = (s∞/c) ω*₀ + 1`; `torus_of_rot` and `soBarrier_of_torus` give the barrier in
`(q, p, φ) = (Q₀ + Q₁, P₀, Q₁)`. -/
theorem soBarrier_of_exact_rotTorus {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ρ sinf γ τ m lo hi : ℝ} {c : ℚ} (hc : 0 < c) {ωstar : Fin 2 → ℝ} (hρ : 0 < ρ)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip 2 ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip 2 ρ,
      invarianceError (soRotHamExprScaled c).eval Kinf (sinf • ωstar) θ = 0)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) (hm : 0 < m)
    (hmono : ∀ x y : ℝ, m ≤ ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re)
    (hlo : ∀ x y : ℝ, lo ≤ ((Kinf (realPt x y)).2 0).re)
    (hhi : ∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ hi) :
    Nonempty (SoBarrier lo hi) := by
  have hcr : 0 < (c : ℝ) := by exact_mod_cast hc
  have hsm : (c : ℝ)⁻¹ • (sinf • ωstar) = ((c : ℝ)⁻¹ * sinf) • ωstar := smul_smul _ _ _
  have heval : (soRotHamExprScaled c).eval = fun z => ((c : ℝ) : ℂ) * soRotHC z := by
    funext z
    rw [soRotHamExprScaled_eval, Complex.ofReal_ratCast]
  have hinv' : ∀ θ ∈ complexStrip 2 ρ,
      invarianceError soRotHamExpr.eval Kinf (((c : ℝ)⁻¹ * sinf) • ωstar) θ = 0 := by
    intro θ hθ
    have h := hinv θ hθ
    have h2 : soRotHamExpr.eval = soRotHC := funext soRotHamExpr_eval
    rw [heval, invarianceError_const_mul hcr.ne', hsm] at h
    rw [h2]
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hcr.ne')
  have hdio' : IsDiophantine ((c : ℝ)⁻¹ * γ) τ (((c : ℝ)⁻¹ * sinf) • ωstar) := by
    rw [← hsm]
    exact isDiophantine_smul_scale (inv_pos.2 hcr) hdio
  obtain ⟨hone, c₀, hc₀⟩ := clock_frequency (D := Set.univ) (H := soRotHamExpr.eval) (j := 1)
    hρ (fun z _ => soRotHamExpr_clock z) (fun _ _ => Set.mem_univ _) hholo hprim hreal hinv'
    (mul_pos (inv_pos.2 hcr) hγ) hdio'
  set ν : ℝ := ((c : ℝ)⁻¹ * sinf) * ωstar 0 with hν
  have hω : ((c : ℝ)⁻¹ * sinf) • ωstar = ![ν, 1] := by
    funext i; fin_cases i <;> simp [hν, hone]
  have hcl : ∀ x y : ℝ, (Kinf (realPt x y)).1 1 = ((y + c₀ : ℝ) : ℂ) := fun x y => by
    have h : (Kinf (realPt x y)).1 1 = ((![x, y] 1 + c₀ : ℝ) : ℂ) := hc₀ ![x, y]
    simpa using h
  have hflow : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => Kinf (realPt (x + s * ν) (y + s)))
      (soRotMapInv (soExtFieldC (soRotMap (Kinf (realPt x y))))) 0 := by
    intro x y
    have h := graphHasDerivAt_lineK hholo hρ ![x, y] ![ν, 1] 0
    have e := hinv' (realPt x y) (realPt_mem hρ x y)
    rw [invarianceError, hω, show soRotHamExpr.eval = soRotHC from funext soRotHamExpr_eval,
      hamiltonianVectorFieldℂ_soRotHC, hamiltonianVectorFieldℂ_soHC, sub_eq_zero] at e
    have e2 : (fun i => ((![x, y] i + (0 : ℝ) * ![ν, 1] i : ℝ) : ℂ)) = realPt x y := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e2, ← e] at h
    simpa only [realPt_line] using h
  have hper : ∀ (x y : ℝ) (k : Fin 2 → ℤ),
      Kinf (realPt x y + fun i => ((k i : ℤ) : ℂ)) =
        Kinf (realPt x y) + (fun i => ((k i : ℤ) : ℂ), 0) :=
    fun x y k => hprim _ (realPt_mem hρ x y) k
  have hPeq : ∀ x y, (Kinf (realPt x y)).2 0 = ((realP Kinf x y : ℝ) : ℂ) := realP_eq hreal
  have hcp : Continuous fun z : ℝ × ℝ => realPt z.1 z.2 :=
    continuous_pi fun i => by fin_cases i <;> simp [realPt] <;> fun_prop
  have hcK : Continuous fun z : ℝ × ℝ => Kinf (realPt z.1 z.2) :=
    hholo.continuousOn.comp_continuous hcp fun z => realPt_mem hρ _ _
  have T := torus_of_rot (Q₁ := realQ Kinf) (Pp := realP Kinf)
    (dQ := fun x y => ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re) (ν := ν + 1) (c := c₀)
    (m := m) hm
    (Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_fst.comp hcK)))
    (Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_snd.comp hcK)))
    (fun x y => by
      have h := hper x y ![1, 0]
      have e : realPt x y + (fun i => ((![1, 0] i : ℤ) : ℂ)) = realPt (x + 1) y := by
        funext i; fin_cases i <;> simp [realPt]
      rw [e] at h
      simpa [realQ] using congrArg (fun u => (u.1 0).re) h)
    (fun x y => by
      have h := hper x y ![0, 1]
      have e : realPt x y + (fun i => ((![0, 1] i : ℤ) : ℂ)) = realPt x (y + 1) := by
        funext i; fin_cases i <;> simp [realPt]
      rw [e] at h
      simpa [realQ] using congrArg (fun u => (u.1 0).re) h)
    (fun x y => by
      have h := hper x y ![1, 0]
      have e : realPt x y + (fun i => ((![1, 0] i : ℤ) : ℂ)) = realPt (x + 1) y := by
        funext i; fin_cases i <;> simp [realPt]
      rw [e] at h
      simpa [realP] using congrArg (fun u => (u.2 0).re) h)
    (fun x y => by
      have h := hper x y ![0, 1]
      have e : realPt x y + (fun i => ((![0, 1] i : ℤ) : ℂ)) = realPt x (y + 1) := by
        funext i; fin_cases i <;> simp [realPt]
      rw [e] at h
      simpa [realP] using congrArg (fun u => (u.2 0).re) h)
    (fun x y => by
      have h := graphHasDerivAt_lineK hholo hρ ![0, y] ![1, 0] x
      simp only [realPt_zero_line] at h
      exact hasDerivAt_re_comp h)
    hmono
    (fun x y => by
      rw [add_sub_cancel_right]
      have h := hasDerivAt_re_comp (hflow x y)
      have hv : ((soRotMapInv (soExtFieldC (soRotMap (Kinf (realPt x y))))).1 0).re =
          realP Kinf x y - 1 := by
        simp [soRotMapInv, soExtFieldC, soRotMap, hPeq]
      rw [hv] at h
      exact h)
    (fun x y => by
      rw [add_sub_cancel_right]
      have h := hasDerivAt_re_comp₂ (hflow x y)
      have hv : ((soRotMapInv (soExtFieldC (soRotMap (Kinf (realPt x y))))).2 0).re =
          -soVq (realQ Kinf x y + y + c₀) (y + c₀) := by
        have h1 : ((realQ Kinf x y : ℝ) : ℂ) + ((y + c₀ : ℝ) : ℂ) =
            ((realQ Kinf x y + y + c₀ : ℝ) : ℂ) := by push_cast; ring
        simp only [soRotMapInv, soExtFieldC, soRotMap, Matrix.cons_val_zero, Matrix.cons_val_one,
          realQ_eq hreal, hcl, h1, soVqC_ofReal]
        simp
      rw [hv] at h
      exact h)
  refine ⟨⟨T.soGraphFun, T.continuous_soGraphFun, fun q φ => ?_, fun q φ => ?_,
    T.soGraph_invariant, fun q φ => hlo _ _, fun q φ => hhi _ _⟩⟩
  · unfold SoGraph.Torus.soGraphFun
    rw [T.soGraphInv_add_one]
    exact T.perP₀ _ _
  · unfold SoGraph.Torus.soGraphFun
    rw [T.soGraphInv_periodic_φ, show φ + 1 - c₀ = (φ - c₀) + 1 by ring]
    exact T.perP₁ _ _

end KAM.SpinOrbit

end
