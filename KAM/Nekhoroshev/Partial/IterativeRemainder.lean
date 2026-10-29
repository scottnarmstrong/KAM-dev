/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.IterativeMap
public import KAM.Nekhoroshev.Partial.Transform
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Iterative Lemma on the extended phase space: the remainder (`bpN:p11:iterative`)

Part 11, package N11-H, second module: clauses (c), (d), (e) of the source.

* `nitF` is `f₊ = H ∘ Φ - h - g₊` (`g₊ = g + ξ`, `ξ = P_Λ T_K f`), so the identity
  `H ∘ Φ = h + g₊ + f₊` is `nitF_identity`.
* Step `it-taylor`: on `𝒟_{R-2ρ,s-2σ}`, `ext_taylor_second` along the trajectories of
  `ExtCompose.traj_solution` (data `(R-ρ, s-σ; R, s)`, admissible by `2ρ < R`, `2σ < s`) gives
  `f₊ = 𝓡 + (f - T_K f) ∘ Φ` with `𝓡 = ∫₀¹ v_t ∘ X^t dt`, `v_t = nitW … t`
  (`{(1-t){h,φ}_c + g + T_K f, φ}_c`), using `{h,φ}_c = ξ - T_K f` (`NitHyp.nit_bracket_eq`).
* Step `it-est`: on `𝒟_{R-ρ,s-σ}`, `v_t = {g,φ}_c + (1-t){ξ,φ}_c + t{T_K f,φ}_c`, so the family
  is jointly continuous with its derivative; `bracket_g` with the extra decomposition term
  `f_t = (1-t)ξ + t T_K f` (weight `1`, norm `≤ δ`) bounds it (`nit_integrand_bound`);
  `transform_integral` bounds `𝓡`, `truncation_tail` and `composition` bound
  `(f - T_K f) ∘ Φ` (`nit_remainder_core`, `NitHyp.nit_remainder`).
* Clause (e): `NitHyp.nit_real` (reality of `φ`, `g₊`, `f₊`; the reality of `Φ` is the last
  clause of `canonical_map`).

Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-- The integrand `v_t = {(1-t){h, φ}_c + g + T, φ}_c` of the Lie remainder. -/
def nitW (c : ℝ) (h : (Fin n → ℂ) → ℂ) (φ g T : EC n k → ℂ) (t : ℝ) : EC n k → ℂ :=
  extBracket c (fun x => ((1 - t : ℝ) : ℂ) * extBracket c (liftFast h) φ x + (g x + T x)) φ

/-- `f₊ = H ∘ Φ - h - g₊` with `H = h + g + f`, `Φ = X¹_φ`, `g₊ = g + ξ`. -/
def nitF (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ) (h : (Fin n → ℂ) → ℂ)
    (g f ξ : EC n k → ℂ) : EC n k → ℂ :=
  fun z => liftFast h (extFlow b R s ρ σ φ 1 z) + g (extFlow b R s ρ σ φ 1 z) +
    f (extFlow b R s ρ σ φ 1 z) - liftFast h z - (g z + ξ z)

/-- Clause (c) of the source: `H ∘ Φ = h + g₊ + f₊` (definitional for `nitF`). -/
theorem nitF_identity (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ)
    (h : (Fin n → ℂ) → ℂ) (g f ξ : EC n k → ℂ) (z : EC n k) :
    liftFast h (extFlow b R s ρ σ φ 1 z) + g (extFlow b R s ρ σ φ 1 z) +
        f (extFlow b R s ρ σ φ 1 z) =
      liftFast h z + (g + ξ) z + nitF b R s ρ σ φ h g f ξ z := by
  simp only [nitF, Pi.add_apply]
  ring

/-! ### Step `it-est`: the integrand -/

/-- `bracket_g` with the decomposition `gⱼ` and the extra term `f_t = (1-t)ξ + tT`
(radius `R`, width `s`, bound `δ`): `|v_t|_{R-ρ,s-σ} ≤ (|g|_* + δ) V/(ρσ)`. -/
theorem nit_integrand_bound (b : PartialBlock n k) {N : ℕ} (gj : Fin N → EC n k → ℂ)
    (Rj sj Uj : Fin N → ℝ) {R s ρ σ V δ t : ℝ} {h : (Fin n → ℂ) → ℂ} {φ g ξ T : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s) (hSL : slowLoss b.c ρ σ k)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j))
    (hδ : 0 ≤ δ) (hV : 0 ≤ V) (hφc : InClass b.base R s φ) (hφb : WBound b.base R s φ V)
    (hξc : InClass b.base R s ξ) (hξb : WBound b.base R s ξ δ)
    (hTc : InClass b.base R s T) (hTb : WBound b.base R s T δ)
    (hg : ∀ z, g z = ∑ j, gj j z)
    (hw : ∀ z ∈ Dom n b.base R s, extBracket b.c (liftFast h) φ z = ξ z - T z)
    (ht : t ∈ Icc (0:ℝ) 1) :
    WBound b.base (R-ρ) (s-σ) (nitW b.c h φ g T t)
      (((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)*V/(ρ*σ)) := by
  have hs : 0 < s := by linarith
  have e1 : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have e2 : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hc1 : InClass b.base R s (fun x => ((1 - t : ℝ) : ℂ) * ξ x) :=
    inClass_const_mul_ext _ hξc
  have hc2 : InClass b.base R s (fun x => (t : ℂ) * T x) := inClass_const_mul_ext _ hTc
  have hftc : InClass b.base R s (fun x => ((1 - t : ℝ) : ℂ) * ξ x + (t : ℂ) * T x) :=
    nit_inClass_add hc1 hc2
  have hftb : WBound b.base R s (fun x => ((1 - t : ℝ) : ℂ) * ξ x + (t : ℂ) * T x) δ := by
    refine (wbound_add_ext hs hc1 hc2 (wbound_const_mul_ext _ hξb)
      (wbound_const_mul_ext _ hTb)).mono le_rfl le_rfl ?_
    rw [e1, e2]
    linarith
  have hbg := KAM.Nekhoroshev.bracket_g b
    (Fin.cons (fun x => ((1 - t : ℝ) : ℂ) * ξ x + (t : ℂ) * T x) gj :
      Fin (N+1) → EC n k → ℂ)
    (Fin.cons R Rj : Fin (N+1) → ℝ) (Fin.cons s sj : Fin (N+1) → ℝ)
    (Fin.cons δ Uj : Fin (N+1) → ℝ) φ hρ hρR hσ hσs hSL
    (fun j => Fin.cases (by simp) (fun j => by simpa using hRj j) j)
    (fun j => Fin.cases (by simp) (fun j => by simpa using hsj j) j)
    (fun j => Fin.cases (by simpa using hδ) (fun j => by simpa using hUj j) j)
    hV
    (fun j => Fin.cases (by simpa using hftc) (fun j => by simpa using hgj j) j)
    (fun j => Fin.cases (by simpa using hftb) (fun j => by simpa using hgjb j) j)
    hφc hφb
  refine wbound_congr_ext (by linarith : (0:ℝ) < s - σ) (fun z hz => ?_)
    (hbg.mono le_rfl le_rfl (le_of_eq ?_))
  · show extBracket b.c _ φ z = extBracket b.c _ φ z
    refine nit_bracket_congr (isOpen_Dom (n := n) b.base R s) (fun x hx => ?_)
      (Dom_mono (by linarith) (by linarith) hz)
    rw [Fin.sum_univ_succ, hw x hx, hg x]
    simp only [Fin.cons_zero, Fin.cons_succ]
    push_cast
    ring
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sub_self, zero_add]
    rw [div_self hρ.ne', div_self hσ.ne']
    ring

/-! ### Steps `it-taylor` and `it-est`: the remainder -/

/-- `f₊ = 𝓡 + (f - T_K f) ∘ Φ` on `𝒟_{R-2ρ,s-2σ}`, its class, and
`|f₊| ≤ (1-η)⁻¹ W + (1-η)⁻¹ e^{-2πKσ} δ` for any bound `W` of the integrand. -/
theorem nit_remainder_core (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V δ K Ug Wt : ℝ}
    {h : (Fin n → ℂ) → ℂ} {φ g f ξ : EC n k → ℂ}
    (hc : ExtCompose b R s (R-ρ) (s-σ) ρ σ V φ)
    (hlh : DifferentiableOn ℂ (liftFast h) (Dom n b.base R s))
    (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hξc : InClass b.base R s ξ) (hξb : WBound b.base R s ξ δ)
    (hTc : InClass b.base R s (truncate K f)) (hTb : WBound b.base R s (truncate K f) δ)
    (hgc : InClass b.base R s g) (hgb : WBound b.base R s g Ug) (hUg : 0 ≤ Ug)
    (hw : ∀ z ∈ Dom n b.base R s, extBracket b.c (liftFast h) φ z = ξ z - truncate K f z)
    (hWt : 0 ≤ Wt)
    (hvb : ∀ t ∈ Icc (0:ℝ) 1,
      WBound b.base (R-ρ) (s-σ) (nitW b.c h φ g (truncate K f) t) Wt) :
    InClass b.base (R-ρ-ρ) (s-σ-σ) (nitF b R s ρ σ φ h g f ξ) ∧
    WBound b.base (R-ρ-ρ) (s-σ-σ) (nitF b R s ρ σ φ h g f ξ)
      ((1-2*V/(ρ*σ))⁻¹*Wt + (1-2*V/(ρ*σ))⁻¹*(Real.exp (-(2*Real.pi*K*σ))*δ)) := by
  have hρ : 0 < ρ := hc.rho_pos
  have hσ : 0 < σ := hc.sig_pos
  have hρR : ρ < R - ρ := hc.rho_lt
  have hσs : σ < s - σ := hc.sig_lt
  have hΩ : IsOpen (Dom n b.base (R-ρ) (s-σ)) := isOpen_Dom _ _ _
  have hsub : Dom n b.base (R-ρ) (s-σ) ⊆ Dom n b.base R s :=
    Dom_mono (by linarith) (by linarith)
  have hs2 : 0 < s - σ - σ := by linarith
  have hat : ∀ {u : EC n k → ℂ}, DifferentiableOn ℂ u (Dom n b.base R s) →
      ∀ z ∈ Dom n b.base R s, DifferentiableAt ℂ u z := fun hu z hz =>
    hu.differentiableAt ((isOpen_Dom _ _ _).mem_nhds hz)
  -- the three brackets with `φ`
  have hAc : InClass b.base (R-ρ) (s-σ) (extBracket b.c g φ) :=
    (bracket b hρ (by linarith) hσ (by linarith) (by linarith) (by linarith) hgc hc.hol hUg
      hc.bound_nonneg hgb hc.bound).1
  have hBc : InClass b.base (R-ρ) (s-σ) (extBracket b.c ξ φ) :=
    (bracket b hρ (by linarith) hσ (by linarith) (by linarith) (by linarith) hξc hc.hol hδ
      hc.bound_nonneg hξb hc.bound).1
  have hCc : InClass b.base (R-ρ) (s-σ) (extBracket b.c (truncate K f) φ) :=
    (bracket b hρ (by linarith) hσ (by linarith) (by linarith) (by linarith) hTc hc.hol hδ
      hc.bound_nonneg hTb hc.bound).1
  have hAd := hAc.differentiableOn
  have hBd := hBc.differentiableOn
  have hCd := hCc.differentiableOn
  -- the integrand on `𝒟_{R-ρ,s-σ}` is affine in `t`
  have eq1 : ∀ t : ℝ, ∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      nitW b.c h φ g (truncate K f) t z = extBracket b.c g φ z +
        ((1 - t : ℝ) : ℂ) * extBracket b.c ξ φ z +
        (t : ℂ) * extBracket b.c (truncate K f) φ z := fun t z hz => by
    have hz' := hsub hz
    have hG : EqOn (fun x => ((1 - t : ℝ) : ℂ) * extBracket b.c (liftFast h) φ x +
        (g x + truncate K f x))
        (fun x => g x + ((1 - t : ℝ) : ℂ) * ξ x + (t : ℂ) * truncate K f x)
        (Dom n b.base R s) := fun x hx => by
      beta_reduce
      rw [hw x hx]
      push_cast
      ring
    have h1 := nit_bracket_congr (c := b.c) (φ := φ) (isOpen_Dom _ _ _) hG hz'
    have h2 := nit_bracket_lin b.c (φ := φ) ((1 - t : ℝ) : ℂ) (t : ℂ)
      (hat hgc.differentiableOn z hz') (hat hξc.differentiableOn z hz')
      (hat hTc.differentiableOn z hz')
    exact h1.trans h2
  have eq2 : ∀ t : ℝ, ∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      fderiv ℂ (nitW b.c h φ g (truncate K f) t) z =
        fderiv ℂ (extBracket b.c g φ) z +
          ((1 - t : ℝ) : ℂ) • fderiv ℂ (extBracket b.c ξ φ) z +
          (t : ℂ) • fderiv ℂ (extBracket b.c (truncate K f) φ) z := fun t z hz => by
    have hA := hAd.differentiableAt (hΩ.mem_nhds hz)
    have hB := hBd.differentiableAt (hΩ.mem_nhds hz)
    have hC := hCd.differentiableAt (hΩ.mem_nhds hz)
    have h1 : HasFDerivAt (fun x => extBracket b.c g φ x +
        ((1 - t : ℝ) : ℂ) * extBracket b.c ξ φ x +
        (t : ℂ) * extBracket b.c (truncate K f) φ x) _ z :=
      (hA.hasFDerivAt.add (hB.hasFDerivAt.const_mul _)).add (hC.hasFDerivAt.const_mul _)
    rw [← h1.fderiv]
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hz) fun w hw' => eq1 t w hw')
  -- class of the integrand
  have hvc : ∀ t : ℝ, InClass b.base (R-ρ) (s-σ) (nitW b.c h φ g (truncate K f) t) := by
    intro t
    have hEqv : EqOn (fun z => extBracket b.c g φ z + ((1 - t : ℝ) : ℂ) * extBracket b.c ξ φ z +
        (t : ℂ) * extBracket b.c (truncate K f) φ z) (nitW b.c h φ g (truncate K f) t)
        (Dom n b.base (R-ρ) (s-σ)) := fun z hz => (eq1 t z hz).symm
    exact inClass_congr_ext hEqv (nit_inClass_add (nit_inClass_add hAc
      (inClass_const_mul_ext _ hBc)) (inClass_const_mul_ext _ hCc))
  -- joint continuity of the integrand and of its derivative
  have hcontD : ∀ {u : EC n k → ℂ}, DifferentiableOn ℂ u (Dom n b.base (R-ρ) (s-σ)) →
      ContinuousOn (fun z => fderiv ℂ u z) (Dom n b.base (R-ρ) (s-σ)) := fun hu =>
    (KAM.holomorphic_regularity_of_finiteDimensional hΩ hu).1.continuousOn
  have hsnd : ∀ {E : Type} [TopologicalSpace E] {u : EC n k → E},
      ContinuousOn u (Dom n b.base (R-ρ) (s-σ)) →
      ContinuousOn (fun x : ℝ × EC n k => u x.2) (Icc 0 1 ×ˢ Dom n b.base (R-ρ) (s-σ)) :=
    fun hu => hu.comp continuousOn_snd fun x hx => hx.2
  have hc1 : Continuous fun x : ℝ × EC n k => ((1 - x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)
  have hc2 : Continuous fun x : ℝ × EC n k => (x.1 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  have hcont : ContinuousOn (fun x : ℝ × EC n k => nitW b.c h φ g (truncate K f) x.1 x.2)
      (Icc 0 1 ×ˢ Dom n b.base (R-ρ) (s-σ)) := by
    refine ContinuousOn.congr (f := fun x : ℝ × EC n k => extBracket b.c g φ x.2 +
      ((1 - x.1 : ℝ) : ℂ) * extBracket b.c ξ φ x.2 +
      (x.1 : ℂ) * extBracket b.c (truncate K f) φ x.2) ?_ fun x hx => eq1 x.1 x.2 hx.2
    exact ((hsnd hAd.continuousOn).add (hc1.continuousOn.mul (hsnd hBd.continuousOn))).add
      (hc2.continuousOn.mul (hsnd hCd.continuousOn))
  have hdcont : ContinuousOn
      (fun x : ℝ × EC n k => fderiv ℂ (nitW b.c h φ g (truncate K f) x.1) x.2)
      (Icc 0 1 ×ˢ Dom n b.base (R-ρ) (s-σ)) := by
    refine ContinuousOn.congr (f := fun x : ℝ × EC n k => fderiv ℂ (extBracket b.c g φ) x.2 +
      ((1 - x.1 : ℝ) : ℂ) • fderiv ℂ (extBracket b.c ξ φ) x.2 +
      (x.1 : ℂ) • fderiv ℂ (extBracket b.c (truncate K f) φ) x.2) ?_
      fun x hx => eq2 x.1 x.2 hx.2
    exact ((hsnd (hcontD hAd)).add (hc1.continuousOn.smul (hsnd (hcontD hBd)))).add
      (hc2.continuousOn.smul (hsnd (hcontD hCd)))
  -- the integral remainder (`transform_integral`)
  obtain ⟨I1, I2⟩ := transform_integral b hk hc (nitW b.c h φ g (truncate K f)) hWt
    (fun t _ => hvc t) hvb hcont hdcont
  -- the truncation tail composed with `Φ` (`truncation_tail`, `composition`)
  obtain ⟨-, htail⟩ := truncation_tail hf hfb hσ (by linarith) hK
  have htc : InClass b.base (R-ρ) (s-σ) (fun z => f z - truncate K f z) :=
    nit_inClass_mono (nit_inClass_sub hf hTc) (by linarith) (by linarith)
  obtain ⟨-, hcomp, -, -⟩ := composition b hk hc
    (by positivity : 0 ≤ Real.exp (-(2*Real.pi*K*σ))*δ) htc
    (htail.mono (by linarith) le_rfl le_rfl)
  obtain ⟨t5, t6⟩ := hcomp 1 abs_one.le
  rw [abs_one, one_mul] at t6
  -- step `it-taylor`: `f₊ = 𝓡 + (f - T_K f) ∘ Φ`
  have hEq : EqOn (fun z => (∫ t in (0:ℝ)..1,
        nitW b.c h φ g (truncate K f) t (extFlow b R s ρ σ φ t z)) +
      ((fun z => f z - truncate K f z) ∘ extFlow b R s ρ σ φ 1) z)
      (nitF b R s ρ σ φ h g f ξ) (Dom n b.base (R-ρ-ρ) (s-σ-σ)) := by
    intro z hz
    obtain ⟨hγ, h0⟩ := hc.traj_solution hk hz
    have T1 := ext_taylor_second hΩ (hc.hol.differentiableOn.mono hsub)
      (hlh.mono hsub) ((hgc.differentiableOn.add hTc.differentiableOn).mono hsub) hγ h0
    have T2 : liftFast h (extFlow b R s ρ σ φ 1 z) +
        (g (extFlow b R s ρ σ φ 1 z) + truncate K f (extFlow b R s ρ σ φ 1 z)) =
        liftFast h z + extBracket b.c (liftFast h) φ z + (g z + truncate K f z) +
          ∫ t in (0:ℝ)..1, nitW b.c h φ g (truncate K f) t (extFlow b R s ρ σ φ t z) := T1
    have hwz := hw z (Dom_mono (by linarith) (by linarith) hz)
    simp only [nitF, Function.comp_apply]
    linear_combination (-1 : ℂ) * T2 + (-1 : ℂ) * hwz
  exact ⟨inClass_congr_ext hEq (nit_inClass_add I1 t5),
    wbound_congr_ext hs2 hEq (wbound_add_ext hs2 I1 t5 I2 t6)⟩

namespace NitHyp

variable {b : PartialBlock n k} {R s ρ σ K α p δ : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : EC n k → ℂ} {Λ : Set (Fin n → ℤ)}

/-- Clauses (c), (d) of the source (steps `it-taylor`, `it-est`): `f₊ ∈ 𝒪_{R-2ρ,s-2σ}` and
`|f₊| ≤ (1 - 2qδ/(ᾱρσ))⁻¹ (q/(ᾱρσ) (|g|_* + δ) + e^{-2πKσ}) δ`. -/
theorem nit_remainder (H : NitHyp b R s ρ σ K α p δ h f Λ) {N : ℕ} (gj : Fin N → EC n k → ℂ)
    (Rj sj Uj : Fin N → ℝ) (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j)
    (hUj : ∀ j, 0 ≤ Uj j) (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    InClass b.base (R-2*ρ) (s-2*σ)
      (nitF b R s ρ σ (homGenerator K Λ h f) h (fun z => ∑ j, gj j z) f
        (projMode Λ (truncate K f))) ∧
    WBound b.base (R-2*ρ) (s-2*σ)
      (nitF b R s ρ σ (homGenerator K Λ h f) h (fun z => ∑ j, gj j z) f
        (projMode Λ (truncate K f)))
      ((1-2*conjExp p*δ/(2*Real.pi*α*ρ*σ))⁻¹*
        (conjExp p/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
          Real.exp (-2*Real.pi*K*σ))*δ) := by
  obtain ⟨hξc, hφc, hξb, hTb, hφb, -, -⟩ := H.nit_hom
  have hρ := H.nit_rho
  have hσ := H.nit_sig
  have hTc : InClass b.base R s (truncate K f) :=
    (projections H.nit_s_pos H.nit_fc H.nit_fb {l | KAM.Fourier.modeSize l ≤ K}).1
  obtain ⟨hgc, hgb⟩ := nit_sum_class b gj Rj sj Uj H.nit_s_pos hRj hsj hgj hgjb
  have hUg : 0 ≤ ∑ j, Uj j := Finset.sum_nonneg fun j _ => hUj j
  have hS : 0 ≤ ∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j := by
    refine Finset.sum_nonneg fun j _ => ?_
    have h1 : 0 < Rj j - R + ρ := by linarith [hRj j]
    have h2 : 0 < sj j - s + σ := by linarith [hsj j]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hρ.le h1.le) (div_nonneg hσ.le h2.le))) (hUj j)
  have hWt : 0 ≤ ((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)*
      (conjExp p*δ/(2*Real.pi*α))/(ρ*σ) :=
    div_nonneg (mul_nonneg (add_nonneg hS H.nit_delta) H.nit_V_nonneg) (mul_pos hρ hσ).le
  have hvb : ∀ t ∈ Icc (0:ℝ) 1, WBound b.base (R-ρ) (s-σ)
      (nitW b.c h (homGenerator K Λ h f) (fun z => ∑ j, gj j z) (truncate K f) t)
      (((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)*
        (conjExp p*δ/(2*Real.pi*α))/(ρ*σ)) := fun t ht =>
    nit_integrand_bound b gj Rj sj Uj hρ (by linarith [H.nit_rho2]) hσ
      (by linarith [H.nit_sig2]) H.nit_slow hRj hsj hUj hgj hgjb H.nit_delta H.nit_V_nonneg
      hφc hφb hξc hξb hTc hTb (fun _ => rfl) H.nit_bracket_eq ht
  obtain ⟨c1, c2⟩ := nit_remainder_core b H.nit_k H.nit_compose
    (nit_liftFast_class b H.nit_hol le_rfl).differentiableOn H.nit_fc H.nit_fb H.nit_delta
    H.nit_K hξc hξb hTc hTb hgc hgb hUg H.nit_bracket_eq hWt hvb
  have e1 : R - 2*ρ = R-ρ-ρ := by ring
  have e2 : s - 2*σ = s-σ-σ := by ring
  rw [e1, e2]
  refine ⟨c1, c2.mono le_rfl le_rfl (le_of_eq ?_)⟩
  have hη : 2*(conjExp p*δ/(2*Real.pi*α))/(ρ*σ) = 2*conjExp p*δ/(2*Real.pi*α*ρ*σ) := by
    ring
  have hE : -(2*Real.pi*K*σ) = -2*Real.pi*K*σ := by ring
  rw [hη, hE]
  ring

/-- Clause (e) of the source: for `Λ = -Λ` and `h`, `g`, `f` real on real points, `φ`, `g₊`,
`f₊` are real on real points. -/
theorem nit_real (H : NitHyp b R s ρ σ K α p δ h f Λ) {g : EC n k → ℂ}
    (hΛ : ∀ j, j ∈ Λ ↔ -j ∈ Λ)
    (hhr : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
      (h (KAM.realInclusion n I)).im = 0)
    (hgr : extReal (Dom n b.base R s) g) (hfr : extReal (Dom n b.base R s) f) :
    extReal (Dom n b.base R s) (homGenerator K Λ h f) ∧
    extReal (Dom n b.base (R-2*ρ) (s-2*σ)) (g + projMode Λ (truncate K f)) ∧
    extReal (Dom n b.base (R-2*ρ) (s-2*σ))
      (nitF b R s ρ σ (homGenerator K Λ h f) h g f (projMode Λ (truncate K f))) := by
  obtain ⟨-, -, -, -, -, -, hr⟩ := H.nit_hom
  obtain ⟨hξr, hφr⟩ := hr hΛ hfr fun I hI i => nit_freq_im H.nit_hol hhr hI i
  have hρ := H.nit_rho
  have hσ := H.nit_sig
  have hsub : Dom n b.base (R-2*ρ) (s-2*σ) ⊆ Dom n b.base R s :=
    Dom_mono (by linarith) (by linarith)
  have hsub1 : Dom n b.base (R-ρ) (s-σ) ⊆ Dom n b.base R s :=
    Dom_mono (by linarith) (by linarith)
  have hgp : extReal (Dom n b.base R s) (g + projMode Λ (truncate K f)) := fun x hx => by
    show (g _ + projMode Λ (truncate K f) _).im = 0
    rw [Complex.add_im, hgr x hx, hξr x hx, add_zero]
  refine ⟨hφr, fun x hx => hgp x (hsub hx), ?_⟩
  have hlr : extReal (Dom n b.base R s) (liftFast (k := k) h) :=
    nit_liftFast_real (b := b) (le_refl R) hhr
  have hur : extReal (Dom n b.base (R-ρ) (s-σ)) (fun z => liftFast h z + g z + f z) :=
    fun x hx => by
      have hx' := hsub1 hx
      show (liftFast h _ + g _ + f _).im = 0
      rw [Complex.add_im, Complex.add_im, hlr x hx', hgr x hx', hfr x hx', add_zero, add_zero]
  have hcr := composition_real b H.nit_k H.nit_compose hφr hur
  intro x hx
  have e1 : R - 2*ρ = R-ρ-ρ := by ring
  have e2 : s - 2*σ = s-σ-σ := by ring
  have hx2 : (KAM.realInclusion n x.1, KAM.realInclusion (n + (k + k)) x.2) ∈
      Dom n b.base (R-ρ-ρ) (s-σ-σ) := by
    rw [← e1, ← e2]
    exact hx
  have h1 := hcr x hx2
  have h2 := hlr x (hsub hx)
  have h3 := hgr x (hsub hx)
  have h4 := hξr x (hsub hx)
  simp only [Function.comp_apply, Complex.add_im] at h1
  simp only [nitF, Complex.sub_im, Complex.add_im]
  linarith

end NitHyp

end KAM.Nekhoroshev

end
