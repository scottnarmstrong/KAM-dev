/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Iterative
public import KAM.Nekhoroshev.Partial.CompositionCoeff
public import KAM.Nekhoroshev.NormalForm.Arith
public import KAM.Weighted.Projections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normal Form Lemma with slow parameters: the induction (Part 11, package N11-K1)

Blueprint node `bpN:p11:nf` (`blueprint-N/parts/p11b-partial-nf.tex`), steps `nf-sl`,
`nf-first`, `nf-case`, `nf-N`, `nf-induct`, `nf-real`; data `bpN:p11:s-nf#data`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md` (package N11-K1). The joint theorem `nf` and the
displacement are in `KAM.Nekhoroshev.Partial.NormalForm` (N11-K2).

* Numerics of the bound of the signed `iterative` (coefficient `q/(ᾱρσ)`, no `2/e` factor):
  `nnfBound`, Case A (6.1) `nnfBound_caseA`, Case B `nnfBound_caseB`, the induction constant
  `nnf_induct_step`. The step schedule, `ε₁` and the carried bounds are the Part 6 ones
  (`nfRho`, `nfSig`, `nfR`, `nfS`, `nfEps1`, `nfB` of `KAM.Nekhoroshev.NormalForm.Arith`).
* One step: `nnfMap` (the time-one map), `nnfGp` (`g₊ = g + P_Λ T_K f`), `nnfFp`
  (`f₊ = (h+g+f) ∘ Φ - h - g₊`, so the identity is exact everywhere, `nnfFp_identity`), and
  `nnf_iter`: the signed `iterative` gives `NnfStep` (map, displacement, reality, class and bound
  of `f₊`) on `𝒟_{R-2ρ,s-2σ}`. The slow-loss condition `(SL)_{ρ,σ}` follows from `b.SL s` when
  `σ R ≤ 2 s ρ` (`nnf_slowLoss`, step `nf-sl`).
* The step sequence `nnfState` (λ and c fixed by the block: only `R`, `s` change), the invariant
  `NnfInv` and the induction `nnf_inv_all` in Case A (`nf-first`, `nf-case`, `nf-N`, `nf-induct`,
  `nf-real`); the per-step facts `nnf_step_props`; Case B `nnf_caseB_step`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-! ### Numerics of the signed `iterative` bound -/

section NnfArith

/-- The bound of the signed `iterative` for `f₊`: loss pair `(ρ, σ)`, `|f| ≤ δ`, decomposition
norm `S` (the coefficient is `q/(ᾱρσ)`, as in the source). -/
def nnfBound (α p K ρ σ δ S : ℝ) : ℝ :=
  (1-2*conjExp p*δ/(2*Real.pi*α*ρ*σ))⁻¹*
    (conjExp p/(2*Real.pi*α*ρ*σ)*(S+δ)+Real.exp (-2*Real.pi*K*σ))*δ

theorem nnfBound_eq (α p K ρ σ δ S : ℝ) :
    nnfBound α p K ρ σ δ S = (1 - 2 * iterU α p δ ρ σ)⁻¹ *
      (iterU α p S ρ σ + iterU α p δ ρ σ + Real.exp (-(2 * Real.pi * K * σ))) * δ := by
  have e1 : 2*conjExp p*δ/(2*Real.pi*α*ρ*σ) = 2 * iterU α p δ ρ σ := by
    unfold iterU
    ring
  have e2 : conjExp p/(2*Real.pi*α*ρ*σ)*(S+δ) = iterU α p S ρ σ + iterU α p δ ρ σ := by
    unfold iterU
    ring
  have e3 : -2*Real.pi*K*σ = -(2 * Real.pi * K * σ) := by ring
  unfold nnfBound
  rw [e1, e2, e3]

theorem nnf_iterU_zero (α p ρ σ : ℝ) : iterU α p 0 ρ σ = 0 := by
  unfold iterU
  simp

private theorem nnf_iterU_first_mul {α p r s ε : ℝ} (hα : 0 < α) (hr : 0 < r) (hs : 0 < s) :
    iterU α p ε (r / 8) (s / 6) * ε = 48 * (conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s)) := by
  have := Real.pi_pos
  unfold iterU
  field_simp
  ring

private theorem nnf_nfEps1_eq {α p r s ε : ℝ} :
    nfEps1 α p r s ε = 2 ^ 7 * (conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s)) := by
  unfold nfEps1
  ring

/-- `nf-case`, Case A (6.1): `|f₁| ≤ (8/7)(u + e^{-κ/6}) ε ≤ (16/7) u ε ≤ ε₁` when
`e^{-κ/6} ≤ u`, `u = q ε/(ᾱ (R/8)(s/6))`. -/
theorem nnfBound_caseA {α p K r s ε : ℝ} (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r)
    (hs : 0 < s) (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)) :
    nnfBound α p K (r / 8) (s / 6) ε 0 ≤ nfEps1 α p r s ε := by
  have hu := iterU_first hp hα hK hr hs hε0 hi hii
  have hu0 := iterU_nonneg hp hα (by positivity : 0 < r / 8) (by positivity : 0 < s / 6) hε0
  have hX : 0 ≤ conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s) := by
    have := KAM.NormalForm.conjExp_pos' hp
    have := Real.pi_pos
    positivity
  have hexp : Real.exp (-(2 * Real.pi * K * (s / 6))) =
      Real.exp (-(2 * Real.pi * K * s) / 6) := by
    congr 1
    ring
  rw [nnfBound_eq, nnf_iterU_zero, zero_add, hexp]
  have h1 : (1 - 2 * iterU α p ε (r / 8) (s / 6))⁻¹ ≤ 8 / 7 := by
    have := KAM.NormalForm.inv_one_sub_le (t := 2 * iterU α p ε (r / 8) (s / 6)) (c := 1 / 8)
      (by linarith) (by norm_num)
    norm_num at this
    exact this
  have h3 : (1 - 2 * iterU α p ε (r / 8) (s / 6))⁻¹ *
      (iterU α p ε (r / 8) (s / 6) + Real.exp (-(2 * Real.pi * K * s) / 6)) ≤
        8 / 7 * (2 * iterU α p ε (r / 8) (s / 6)) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hε0
  have h5 := nnf_iterU_first_mul (p := p) (ε := ε) hα hr hs
  rw [nnf_nfEps1_eq]
  linarith [h4, h5, hX]

/-- `nf-case`, Case B: the doubled losses `(R/4, s/3)` give `|f₁| ≤ e^{-κ/6} ε` when
`u < e^{-κ/6}`. -/
theorem nnfBound_caseB {α p K r s ε : ℝ} (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r)
    (hs : 0 < s) (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s)
    (hB : iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) :
    nnfBound α p K (r / 4) (s / 3) ε 0 ≤ Real.exp (-(2 * Real.pi * K * s) / 6) * ε := by
  have hu := iterU_first hp hα hK hr hs hε0 hi hii
  have hu0 := iterU_nonneg hp hα (by positivity : 0 < r / 8) (by positivity : 0 < s / 6) hε0
  set E := Real.exp (-(2 * Real.pi * K * s) / 6) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 / 2 := by
    have h1 : E ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg] at h1
    have : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      norm_num
      exact KAM.NormalForm.exp_one_gt.le
    linarith
  have hexp : Real.exp (-(2 * Real.pi * K * (s / 3))) = E * E := by
    rw [hE, ← Real.exp_add]
    congr 1
    ring
  have hd := iterU_double (p := p) (ε := ε) hα hr hs
  have hu'0 := iterU_nonneg hp hα (by positivity : 0 < r / 4) (by positivity : 0 < s / 3) hε0
  rw [nnfBound_eq, nnf_iterU_zero, zero_add, hexp]
  have h1 : (1 - 2 * iterU α p ε (r / 4) (s / 3))⁻¹ ≤ 32 / 31 := by
    have := KAM.NormalForm.inv_one_sub_le (t := 2 * iterU α p ε (r / 4) (s / 3)) (c := 1 / 32)
      (by linarith) (by norm_num)
    norm_num at this
    exact this
  have hEE : E * E ≤ E / 2 := by
    have := mul_le_mul_of_nonneg_left hE1 hE0.le
    linarith
  have h3 : (1 - 2 * iterU α p ε (r / 4) (s / 3))⁻¹ * (iterU α p ε (r / 4) (s / 3) + E * E) ≤
      32 / 31 * (3 / 4 * E) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hε0
  have h5 := mul_nonneg hE0.le hε0
  linarith [h4, h5]

/-- `nf-induct`: `u_δ ≤ 2⁻⁸`, `u_S ≤ 2⁻⁴`, `e^{-2πKσ} ≤ 1/8` give
`|f₊| ≤ (128/127)(1/16 + 1/256 + 1/8) δ < δ/4`. -/
theorem nnf_induct_step {α p : ℝ} (hp : 1 < p) (hα : 0 < α) {ρ σ δ S K : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hδ0 : 0 ≤ δ) (hS0 : 0 ≤ S) (hδ : iterU α p δ ρ σ ≤ 1 / 2 ^ 8)
    (hS : iterU α p S ρ σ ≤ 1 / 2 ^ 4) (hexp : Real.exp (-(2 * Real.pi * K * σ)) ≤ 1 / 8) :
    nnfBound α p K ρ σ δ S ≤ δ / 4 := by
  have ha0 := iterU_nonneg hp hα hρ hσ hδ0
  have hb0 := iterU_nonneg hp hα hρ hσ hS0
  rw [nnfBound_eq]
  have h1 : (1 - 2 * iterU α p δ ρ σ)⁻¹ ≤ 128 / 127 := by
    have := KAM.NormalForm.inv_one_sub_le (t := 2 * iterU α p δ ρ σ) (c := 1 / 2 ^ 7)
      (by linarith) (by norm_num)
    norm_num at this
    exact this
  have h3 : (1 - 2 * iterU α p δ ρ σ)⁻¹ *
      (iterU α p S ρ σ + iterU α p δ ρ σ + Real.exp (-(2 * Real.pi * K * σ))) ≤
        128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hδ0
  have h5 : 128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) * δ ≤ δ / 4 := by
    have : (128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) : ℝ) ≤ 1 / 4 := by norm_num
    have := mul_le_mul_of_nonneg_right this hδ0
    linarith
  linarith

theorem nnf_B_nonneg {ε₁ ε : ℝ} (hε₁ : 0 ≤ ε₁) (hε : 0 ≤ ε) (i : ℕ) : 0 ≤ nfB ε₁ ε i := by
  cases i with
  | zero => exact hε
  | succ i => exact div_nonneg hε₁ (by positivity)

theorem nnf_B_le_eps1 {ε₁ ε : ℝ} (hε₁ : 0 ≤ ε₁) {i : ℕ} (hi : 1 ≤ i) : nfB ε₁ ε i ≤ ε₁ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact div_le_self hε₁ (one_le_pow₀ (by norm_num))

end NnfArith

/-! ### One step of the iteration -/

section NnfStepGeneric

/-- The time-one map `Φ = X¹_φ` of the generating function `φ = homGenerator K Λ h f`
(flow domain `𝒟_{R-ρ,s-σ}`), exactly the `Φ` of the signed `iterative`. -/
def nnfMap (b : PartialBlock n k) (R s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) : EC n k → EC n k :=
  extFlow b R s ρ σ (homGenerator K Λ h f) 1

/-- `g₊ = g + P_Λ T_K f`. -/
def nnfGp (K : ℝ) (Λ : Set (Fin n → ℤ)) (g f : EC n k → ℂ) (z : EC n k) : ℂ :=
  g z + projMode Λ (truncate K f) z

/-- `f₊ = (h + g + f) ∘ Φ - h - g₊`. The identity `(h+g+f) ∘ Φ = h + g₊ + f₊` then holds
everywhere; the content of `iterative` is the class, the bound and the reality of `f₊`. -/
def nnfFp (b : PartialBlock n k) (R s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (g f : EC n k → ℂ) (z : EC n k) : ℂ :=
  liftFast h (nnfMap b R s ρ σ K Λ h f z) + g (nnfMap b R s ρ σ K Λ h f z) +
    f (nnfMap b R s ρ σ K Λ h f z) - liftFast h z - nnfGp K Λ g f z

/-- `H ∘ Φ = h + g₊ + f₊` (Theorem `bpN:p11:iterative` (c)), exact at every point. -/
theorem nnfFp_identity (b : PartialBlock n k) (R s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (g f : EC n k → ℂ) (z : EC n k) :
    liftFast h (nnfMap b R s ρ σ K Λ h f z) + g (nnfMap b R s ρ σ K Λ h f z) +
        f (nnfMap b R s ρ σ K Λ h f z) =
      liftFast h z + nnfGp K Λ g f z + nnfFp b R s ρ σ K Λ h g f z := by
  simp only [nnfFp]
  ring

theorem nnf_extReal_congr {U : Set (EC n k)} {u v : EC n k → ℂ} (h : EqOn u v U)
    (hu : extReal U u) : extReal U v := fun x hx => by
  rw [← h hx]
  exact hu x hx

/-- The class shrinks with the domain. -/
theorem nnf_inClass_mono {D : Set (Fin (n + (k + k)) → ℂ)} {r₀ s₀ r s' : ℝ}
    {u : EC n k → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s' ≤ s₀) :
    InClass D r s' u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

/-- `P_Λ T_K u` is in the class with the bound of `u`, and its coefficients vanish off
`Λ ∩ Z_K`. -/
theorem nnf_proj {D : Set (Fin (n + (k + k)) → ℂ)} {r s' M K : ℝ} {Λ : Set (Fin n → ℤ)}
    {u : EC n k → ℂ} (hs : 0 < s') (hu : InClass D r s' u) (hb : WBound D r s' u M) :
    InClass D r s' (projMode Λ (truncate K u)) ∧ WBound D r s' (projMode Λ (truncate K u)) M ∧
      ∀ I ∈ polyNbhd D r, ∀ j : Fin n → ℤ, j ∉ Λ ∩ zBall n K →
        coeff (projMode Λ (truncate K u)) I j = 0 := by
  obtain ⟨t1, t2, t3, -⟩ := projections hs hu hb {j : Fin n → ℤ | KAM.Fourier.modeSize j ≤ K}
  obtain ⟨p1, p2, p3, -⟩ := projections hs t1 t3 Λ
  refine ⟨p1, p3, fun I hI j hj => ?_⟩
  have e1 : coeff (projMode Λ (truncate K u)) I j = Λ.indicator (coeff (truncate K u) I) j :=
    p2 I hI j
  have e2 : coeff (truncate K u) I j =
      {j : Fin n → ℤ | KAM.Fourier.modeSize j ≤ K}.indicator (coeff u I) j := t2 I hI j
  rw [e1]
  by_cases hΛ : j ∈ Λ
  · rw [Set.indicator_of_mem hΛ, e2]
    exact Set.indicator_of_notMem (fun hZ => hj ⟨hΛ, hZ⟩) _
  · exact Set.indicator_of_notMem hΛ _

/-- `nf-sl`: the fixed-block condition `(SL)` gives `(SL)_{ρ,σ}` whenever `σ R ≤ 2 s ρ`. -/
theorem nnf_slowLoss (b : PartialBlock n k) {s ρ σ : ℝ} (hR : 0 < b.rB) (hw : 0 < b.w)
    (hSL : b.SL s) (hρ : 0 ≤ ρ) (hσρ : σ * b.rB ≤ 2 * s * ρ) : slowLoss b.c ρ σ k := by
  have hc : b.c = 2 * Real.pi * b.rB ^ 2 / b.w ^ 2 := by
    show 2 * Real.pi / (b.w / b.rB) ^ 2 = 2 * Real.pi * b.rB ^ 2 / b.w ^ 2
    rw [div_pow, div_div_eq_mul_div]
  have hw2 : 0 < b.w ^ 2 := by positivity
  have hSL' : 64 * Real.pi * k * s * b.rB ≤ b.w ^ 2 := hSL
  show 16 * k * b.c * σ ≤ ρ
  rw [hc]
  have e : 16 * (k : ℝ) * (2 * Real.pi * b.rB ^ 2 / b.w ^ 2) * σ =
      32 * Real.pi * k * b.rB * (σ * b.rB) / b.w ^ 2 := by ring
  rw [e, div_le_iff₀ hw2]
  have h1 : 32 * Real.pi * k * b.rB * (σ * b.rB) ≤ 32 * Real.pi * k * b.rB * (2 * s * ρ) :=
    mul_le_mul_of_nonneg_left hσρ (by positivity)
  have h2 : 64 * Real.pi * k * s * b.rB * ρ ≤ b.w ^ 2 * ρ := mul_le_mul_of_nonneg_right hSL' hρ
  calc 32 * Real.pi * k * b.rB * (σ * b.rB) ≤ 32 * Real.pi * k * b.rB * (2 * s * ρ) := h1
    _ = 64 * Real.pi * k * s * b.rB * ρ := by ring
    _ ≤ b.w ^ 2 * ρ := h2
    _ = ρ * b.w ^ 2 := by ring

/-- What one step provides on `U₂ = 𝒟_{R-2ρ,s-2σ}`: Theorem `bpN:p11:iterative` (a), (b), (d),
(e) for `Φ = nnfMap …`, `g₊ = nnfGp …`, `f₊ = nnfFp …` (`S` is the decomposition norm of `g`). -/
structure NnfStep (b : PartialBlock n k) (R s ρ σ K α p δ : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (g f : EC n k → ℂ) (S : ℝ) : Prop where
  nnf_diff : DifferentiableOn ℂ (nnfMap b R s ρ σ K Λ h f) (Dom n b.base (R-2*ρ) (s-2*σ))
  nnf_maps : MapsTo (nnfMap b R s ρ σ K Λ h f) (Dom n b.base (R-2*ρ) (s-2*σ)) (Dom n b.base R s)
  nnf_transl : ∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ ℓ : Fin n → ℤ,
    nnfMap b R s ρ σ K Λ h f (z.1+(fun i => (ℓ i:ℂ)),z.2) =
      nnfMap b R s ρ σ K Λ h f z+((fun i => (ℓ i:ℂ)),0)
  nnf_canon : ExtCanonical b.c (Dom n b.base (R-2*ρ) (s-2*σ)) (nnfMap b R s ρ σ K Λ h f)
  nnf_inj : Set.InjOn (nnfMap b R s ρ σ K Λ h f) (Dom n b.base (R-2*ρ) (s-2*σ))
  nnf_disp : ∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ),
    ‖(nnfMap b R s ρ σ K Λ h f z).1-z.1‖ ≤ conjExp p*δ/(2*Real.pi*α*ρ) ∧
    ‖fastAction (nnfMap b R s ρ σ K Λ h f z)-fastAction z‖ ≤
      conjExp p*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
    ‖slowPair (nnfMap b R s ρ σ K Λ h f z)-slowPair z‖ ≤ conjExp p*δ/(16*k*2*Real.pi*α*σ)
  nnf_real : ∀ z : ER n k, extCx z ∈ Dom n b.base (R-2*ρ) (s-2*σ) →
    extCx (extRe (nnfMap b R s ρ σ K Λ h f (extCx z))) = nnfMap b R s ρ σ K Λ h f (extCx z)
  nnf_fp_class : InClass b.base (R-2*ρ) (s-2*σ) (nnfFp b R s ρ σ K Λ h g f)
  nnf_fp_bound : WBound b.base (R-2*ρ) (s-2*σ) (nnfFp b R s ρ σ K Λ h g f) (nnfBound α p K ρ σ δ S)
  nnf_fp_real : extReal (Dom n b.base (R-2*ρ) (s-2*σ)) (nnfFp b R s ρ σ K Λ h g f)
  nnf_gp_real : extReal (Dom n b.base (R-2*ρ) (s-2*σ)) (nnfGp K Λ g f)

/-- One step of the iteration from the signed `iterative`: its `fp` agrees with `nnfFp` on
`𝒟_{R-2ρ,s-2σ}` (by its identity), whence the class, bound and reality of `nnfFp`. -/
theorem nnf_iter (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f g : EC n k → ℂ} {Λ : Set (Fin n → ℤ)}
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hc : 0 < b.c) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {M : ℕ} (gj : Fin M → EC n k → ℂ) (Rj sj Uj : Fin M → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j))
    (hg : g = fun z => ∑ j, gj j z) (hΛ : ∀ j, j ∈ Λ ↔ -j ∈ Λ)
    (hhr : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
      (h (KAM.realInclusion n I)).im = 0)
    (hgr : extReal (Dom n b.base R s) g) (hfr : extReal (Dom n b.base R s) f) :
    NnfStep b R s ρ σ K α p δ Λ h g f (starNorm R s ρ σ Rj sj Uj) := by
  subst hg
  obtain ⟨a1, a2, a3, -, fp, b1, b2, b3, b4, b5, -, b7, b8⟩ :=
    iterative b hk h f Λ hR hR' hs hs' hSL hc hα hp hK hh hdiv hδ hf hfb hsmall gj Rj sj Uj
      hRj hsj hUj hgj hgjb
  obtain ⟨-, r2, r3, r4⟩ := b8 hΛ hhr hgr hfr
  have hsub : Dom n b.base (R-2*ρ) (s-2*σ) ⊆ Dom n b.base (R-3*ρ/2) (s-3*σ/2) :=
    Dom_mono (by linarith) (by linarith)
  have hsub' : Dom n b.base (R-ρ) (s-σ) ⊆ Dom n b.base R s :=
    Dom_mono (by linarith) (by linarith)
  have hs2 : 0 < s - 2*σ := by linarith
  have heq : EqOn fp (nnfFp b R s ρ σ K Λ h (fun z => ∑ j, gj j z) f)
      (Dom n b.base (R-2*ρ) (s-2*σ)) := by
    intro z hz
    have e : liftFast h (nnfMap b R s ρ σ K Λ h f z) + (∑ j, gj j (nnfMap b R s ρ σ K Λ h f z)) +
        f (nnfMap b R s ρ σ K Λ h f z) =
        liftFast h z + ((∑ j, gj j z) + projMode Λ (truncate K f) z) + fp z := b2 z hz
    have e' : nnfFp b R s ρ σ K Λ h (fun z => ∑ j, gj j z) f z =
        liftFast h (nnfMap b R s ρ σ K Λ h f z) + (∑ j, gj j (nnfMap b R s ρ σ K Λ h f z)) +
          f (nnfMap b R s ρ σ K Λ h f z) - liftFast h z -
          ((∑ j, gj j z) + projMode Λ (truncate K f) z) := rfl
    rw [e', e]
    ring
  have b3' : WBound b.base (R-2*ρ) (s-2*σ) fp (nnfBound α p K ρ σ δ (starNorm R s ρ σ Rj sj Uj)) :=
    b3
  refine ⟨a1.mono hsub, fun z hz => hsub' (a2 (hsub hz)), fun z hz ℓ => a3 z (hsub hz) ℓ,
    fun z hz => b4 z (hsub hz), b5, fun z hz => b7 z (hsub hz), fun z hz => r4 z (hsub hz),
    inClass_congr_ext heq b1, wbound_congr_ext hs2 heq b3', nnf_extReal_congr heq r3,
    fun x hx => r2 x hx⟩

end NnfStepGeneric

/-! ### The step sequence -/

section NnfSchedule

/-- `nnfState i = (g_{i-1}, f_i)` (`bpN:p11:nf`, indexing of Theorem `bpN:p6:normal-form`):
`g_{-1} = 0`, `f_0 = f`; step `i` uses the losses `(ρᵢ, σᵢ)` and radii `(Rᵢ, sᵢ)` of the Part 6
schedule with `R = b.rB`. The block constants `λ`, `c` never change. -/
def nnfState (b : PartialBlock n k) (s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (N : ℕ) : ℕ → (EC n k → ℂ) × (EC n k → ℂ)
  | 0 => (fun _ => 0, f)
  | i + 1 =>
    (nnfGp K Λ (nnfState b s K Λ h f N i).1 (nnfState b s K Λ h f N i).2,
      nnfFp b (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i) K Λ h
        (nnfState b s K Λ h f N i).1 (nnfState b s K Λ h f N i).2)

/-- `g_{i-1}`. -/
def nnfG (b : PartialBlock n k) (s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (N i : ℕ) : EC n k → ℂ :=
  (nnfState b s K Λ h f N i).1

/-- `f_i`. -/
def nnfF (b : PartialBlock n k) (s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (N i : ℕ) : EC n k → ℂ :=
  (nnfState b s K Λ h f N i).2

/-- The `i`-th map `Φᵢ : Uᵢ₊₁ → Uᵢ`. -/
def nnfPhi (b : PartialBlock n k) (s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (N i : ℕ) : EC n k → EC n k :=
  nnfMap b (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i) K Λ h
    (nnfF b s K Λ h f N i)

/-- The parts `P_Λ T_K f_j` of the decomposition of `g_{i-1}`. -/
def nnfPart (b : PartialBlock n k) (s K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (N j : ℕ) : EC n k → ℂ :=
  projMode Λ (truncate K (nnfF b s K Λ h f N j))

/-- `Uᵢ = 𝒟_{Rᵢ,sᵢ}`. -/
def nnfU (b : PartialBlock n k) (s : ℝ) (N i : ℕ) : Set (EC n k) :=
  Dom n b.base (nfR b.rB N i) (nfS s N i)

variable {b : PartialBlock n k} {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} {N : ℕ}

theorem nnfG_zero : nnfG b s K Λ h f N 0 = fun _ => 0 := rfl

theorem nnfF_zero : nnfF b s K Λ h f N 0 = f := rfl

theorem nnfG_succ (i : ℕ) :
    nnfG b s K Λ h f N (i + 1) = nnfGp K Λ (nnfG b s K Λ h f N i) (nnfF b s K Λ h f N i) :=
  rfl

theorem nnfF_succ (i : ℕ) :
    nnfF b s K Λ h f N (i + 1) =
      nnfFp b (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i) K Λ h
        (nnfG b s K Λ h f N i) (nnfF b s K Λ h f N i) :=
  rfl

/-- `g_{i-1} = ∑_{j<i} P_Λ T_K f_j`. -/
theorem nnfG_eq_sum (i : ℕ) :
    nnfG b s K Λ h f N i = fun z => ∑ j ∈ Finset.range i, nnfPart b s K Λ h f N j z := by
  induction i with
  | zero => funext z; simp [nnfG_zero]
  | succ i ih =>
    funext z
    rw [nnfG_succ, Finset.sum_range_succ, ← congrFun ih z]
    rfl

/-- The same sum indexed by `Fin i`, the form of the decomposition consumed by `iterative`. -/
theorem nnfG_eq_fin (i : ℕ) :
    nnfG b s K Λ h f N i = fun z => ∑ j : Fin i, nnfPart b s K Λ h f N j z := by
  rw [nnfG_eq_sum]
  funext z
  exact (Fin.sum_univ_eq_sum_range (fun j => nnfPart b s K Λ h f N j z) i).symm

/-- Every step identity `(h + g_{i-1} + f_i) ∘ Φᵢ = h + g_i + f_{i+1}` (exact everywhere). -/
theorem nnf_step_identity (i : ℕ) (z : EC n k) :
    liftFast h (nnfPhi b s K Λ h f N i z) + nnfG b s K Λ h f N i (nnfPhi b s K Λ h f N i z) +
        nnfF b s K Λ h f N i (nnfPhi b s K Λ h f N i z) =
      liftFast h z + nnfG b s K Λ h f N (i + 1) z + nnfF b s K Λ h f N (i + 1) z :=
  nnfFp_identity b (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i) K Λ h
    (nnfG b s K Λ h f N i) (nnfF b s K Λ h f N i) z

/-! #### Source data -/

/-- Hypothesis (i) of `bpN:p11:nf` in the form of the Part 6 numerics. -/
theorem nnf_hi (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * b.rB / K) := by
  have e : 1 / (2 ^ 7 * conjExp p) * (α * b.rB / K) = α*b.rB/(2^7*conjExp p*K) := by ring
  rw [e]
  exact hsm

/-- `c = 2π/λ² > 0` for the block (premise `hc` of the signed `iterative`, ruling F2-C1). -/
theorem nnf_c_pos (ha : ExtNFHyp b s K α L p ε Λ h f) : 0 < b.c := by
  have h1 := ha.radius_pos
  have h2 := ha.slow_width_pos
  show 0 < 2*Real.pi/(b.w/b.rB)^2
  positivity

/-- `nf-N`: `N = ⌊κ/(12 ln 2)⌋`, `κ = 2πK s`. -/
theorem nnf_floor (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) :
    (N : ℝ) * (12 * Real.log 2) ≤ 2 * Real.pi * K * s ∧
      2 * Real.pi * K * s < ((N : ℝ) + 1) * (12 * Real.log 2) ∧
      8 * (N : ℝ) ≤ 2 * Real.pi * K * s :=
  KAM.NormalForm.floor_facts (by linarith [ha.cutoff]) hN

/-- `nf-sl`: `(SL)_{ρᵢ,σᵢ}` for every loss pair of the schedule (`σ/ρ ≤ 2s/R`). -/
theorem nnf_slow_at (ha : ExtNFHyp b s K α L p ε Λ h f) (N i : ℕ) :
    slowLoss b.c (nfRho b.rB N i) (nfSig s N i) k := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  refine nnf_slowLoss b hr ha.slow_width_pos ha.slow (nfRho_nonneg hr.le N i) ?_
  have hsr : 0 ≤ s * b.rB := by positivity
  unfold nfRho nfSig
  split_ifs
  · linarith
  · exact le_of_eq (by ring)

/-- (6.2): `ε ≤ ᾱ R s/(2¹⁰ q N)` and `u(ε₁) ≤ 2⁻⁸` for `N ≥ 1`. -/
theorem nnf_sixtwo (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) (hN1 : 1 ≤ N) :
    ε ≤ 2 * Real.pi * α * b.rB * s / (2 ^ 10 * conjExp p * N) ∧
      iterU α p (nfEps1 α p b.rB s ε) (b.rB / (8 * N)) (s / (4 * N)) ≤ 1 / 2 ^ 8 := by
  have h6 := eps_le_sixtwo ha.p_gt ha.alpha_pos ha.K_pos ha.radius_pos ha.s_pos ha.eps_pos.le
    (nnf_hi hsm) hN1 (nnf_floor ha hN).2.2
  exact ⟨h6, eps1_sixtwo ha.p_gt ha.alpha_pos ha.radius_pos ha.s_pos ha.eps_pos.le hN1 h6⟩

/-- `nf-first` (`i = 0`, `u ≤ 1/16`) and (6.2) (`i ≥ 1`): step `i ≤ N` is small. -/
theorem nnf_small_at (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N) :
    iterU α p (nfB (nfEps1 α p b.rB s ε) ε i) (nfRho b.rB N i) (nfSig s N i) ≤ 1 / 4 := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hε0 := ha.eps_pos.le
  have hε₁0 := nfEps1_nonneg ha.p_gt ha.alpha_pos hr hs (ε := ε)
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    have e1 : nfRho b.rB N 0 = b.rB / 8 := by simp [nfRho]
    have e2 : nfSig s N 0 = s / 6 := by simp [nfSig]
    rw [e1, e2]
    exact (iterU_first ha.p_gt ha.alpha_pos ha.K_pos hr hs hε0 (nnf_hi hsm) ha.cutoff).trans
      (by norm_num)
  · have hN1 : 1 ≤ N := h1.trans_le hi
    have hρ := nfRho_pos hr hi
    have hσ := nfSig_pos hs hi
    have hρ' : 0 < b.rB / (8 * (N : ℝ)) := by rw [← nfRho_ne_zero h1.ne']; exact hρ
    have hσ' : 0 < s / (4 * (N : ℝ)) := by rw [← nfSig_ne_zero h1.ne']; exact hσ
    rw [nfRho_ne_zero h1.ne', nfSig_ne_zero h1.ne']
    have hm := iterU_mono ha.p_gt ha.alpha_pos hρ' hσ' (nnf_B_le_eps1 hε₁0 h1 (ε := ε))
    have := (nnf_sixtwo ha hsm hN hN1).2
    have h8 : (1 : ℝ) / 2 ^ 8 ≤ 1 / 4 := by norm_num
    linarith

/-- `nf-induct`, size of `|g_{i-1}|_*`: weights `≤ 5/(8N)` for `g₀`, `≤ 1` (in fact `≤ 1/2`)
afterwards, so `u(|g_{i-1}|_*) ≤ 2⁻⁴`. -/
theorem nnf_star_at (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N) (hi1 : 1 ≤ i) :
    0 ≤ starNorm (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i)
        (fun j : Fin i => nfR b.rB N j) (fun j : Fin i => nfS s N j)
        (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j) ∧
      iterU α p (starNorm (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i)
        (fun j : Fin i => nfR b.rB N j) (fun j : Fin i => nfS s N j)
        (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j)) (nfRho b.rB N i) (nfSig s N i) ≤
        1 / 2 ^ 4 := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hε0 := ha.eps_pos.le
  have hN1 : 1 ≤ N := hi1.trans hi
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hε6, hε1⟩ := nnf_sixtwo ha hsm hN hN1
  have hε₁0 := nfEps1_nonneg ha.p_gt ha.alpha_pos hr hs (ε := ε)
  have hρ : 0 < b.rB / (8 * (N : ℝ)) := by positivity
  have hσ : 0 < s / (4 * (N : ℝ)) := by positivity
  rw [nfRho_ne_zero (by omega : i ≠ 0), nfSig_ne_zero (by omega : i ≠ 0)]
  set w : ℕ → ℝ := fun j => 1 / 2 * ((b.rB / (8 * N)) /
    (nfR b.rB N j - nfR b.rB N i + b.rB / (8 * N)) +
      (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N))) with hw
  have hsum : starNorm (nfR b.rB N i) (nfS s N i) (b.rB / (8 * N)) (s / (4 * N))
      (fun j : Fin i => nfR b.rB N j) (fun j : Fin i => nfS s N j)
      (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j) =
      ∑ j ∈ Finset.range i, w j * nfB (nfEps1 α p b.rB s ε) ε j := by
    unfold starNorm
    exact Fin.sum_univ_eq_sum_range (fun j => w j * nfB (nfEps1 α p b.rB s ε) ε j) i
  rw [hsum]
  have hwpos : ∀ j ∈ Finset.range i, 0 ≤ w j := by
    intro j hj
    have hji : j ≤ i := (Finset.mem_range.mp hj).le
    have h1 : nfR b.rB N i ≤ nfR b.rB N j := nfR_anti hr.le N hji
    have h2 : nfS s N i ≤ nfS s N j := nfS_anti hs.le N hji
    simp only [hw]
    have a1 : 0 ≤ (b.rB / (8 * N)) / (nfR b.rB N j - nfR b.rB N i + b.rB / (8 * N)) :=
      div_nonneg hρ.le (by linarith)
    have a2 : 0 ≤ (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N)) :=
      div_nonneg hσ.le (by linarith)
    linarith
  refine ⟨Finset.sum_nonneg fun j hj => mul_nonneg (hwpos j hj) (nnf_B_nonneg hε₁0 hε0 j), ?_⟩
  refine star_small ha.p_gt ha.alpha_pos hr hs hε0 hN1 hε6 hε1 ?_
  refine star_sum_le hε0 hε₁0 (by positivity) i w ?_ ?_
  · intro _
    exact w0_le hN1 hr hs (nfR_le_three hr.le hi1) (nfS_le_two hs.le hi1)
  · intro j _ hji
    have h1 : nfR b.rB N i ≤ nfR b.rB N j := nfR_anti hr.le N hji.le
    have h2 : nfS s N i ≤ nfS s N j := nfS_anti hs.le N hji.le
    simp only [hw]
    have a1 : (b.rB / (8 * N)) / (nfR b.rB N j - nfR b.rB N i + b.rB / (8 * N)) ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by linarith)
    have a2 : (s / (4 * N)) / (nfS s N j - nfS s N i + s / (4 * N)) ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by linarith)
    linarith

/-! #### The invariant and the induction -/

/-- The invariant at step `i`: `f_j ∈ O(Rⱼ, sⱼ)` with `|f_j| ≤ Bⱼ` for `j ≤ i` (`B₀ = ε`,
`Bⱼ = 4^{1-j} ε₁`), and `f_i`, `g_{i-1}` real on the real points of `Uᵢ`. -/
def NnfInv (b : PartialBlock n k) (s K α p ε : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (N i : ℕ) : Prop :=
  (∀ j ≤ i, InClass b.base (nfR b.rB N j) (nfS s N j) (nnfF b s K Λ h f N j) ∧
    WBound b.base (nfR b.rB N j) (nfS s N j) (nnfF b s K Λ h f N j)
      (nfB (nfEps1 α p b.rB s ε) ε j)) ∧
  extReal (Dom n b.base (nfR b.rB N i) (nfS s N i)) (nnfF b s K Λ h f N i) ∧
  extReal (Dom n b.base (nfR b.rB N i) (nfS s N i)) (nnfG b s K Λ h f N i)

theorem nnf_inv_zero (ha : ExtNFHyp b s K α L p ε Λ h f) : NnfInv b s K α p ε Λ h f N 0 := by
  refine ⟨fun j hj => ?_, ha.pert.2, fun _ _ => Complex.zero_im⟩
  obtain rfl : j = 0 := by omega
  exact ⟨ha.pert.1, ha.bound⟩

/-- Step `i ≤ N` of the schedule is an application of `iterative` (`nf-first`, admissibility
of `nf-induct`, `nf-sl`, `nf-real`): the decomposition of `g_{i-1}` has the parts
`P_Λ T_K f_j` on `(Rⱼ, sⱼ)` with bounds `Bⱼ`. -/
theorem nnf_step_at (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N)
    (hinv : NnfInv b s K α p ε Λ h f N i) :
    NnfStep b (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i) K α p
      (nfB (nfEps1 α p b.rB s ε) ε i) Λ h (nnfG b s K Λ h f N i) (nnfF b s K Λ h f N i)
      (starNorm (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i)
        (fun j : Fin i => nfR b.rB N j) (fun j : Fin i => nfS s N j)
        (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j)) := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hρ := nfRho_pos hr hi
  have hσ := nfSig_pos hs hi
  have hRle : nfR b.rB N i ≤ b.rB := nfR_anti hr.le N (Nat.zero_le i)
  have hε₁0 := nfEps1_nonneg ha.p_gt ha.alpha_pos hr hs (ε := ε)
  have hdiv := (KAM.NormalForm.divisor ha.p_gt ha.alpha_pos ha.K_pos.le ha.L_nonneg ha.nr ha.lip
    ha.divisor_size).2
  have hjS : ∀ j : Fin i, 0 < nfS s N j := fun j => by
    have h1 := nfSig_pos hs (j.2.le.trans hi)
    have h2 := nfS_gt_two_sig hs (j.2.le.trans hi)
    linarith
  have hP : ∀ j : Fin i,
      InClass b.base (nfR b.rB N j) (nfS s N j) (nnfPart b s K Λ h f N j) ∧
      WBound b.base (nfR b.rB N j) (nfS s N j) (nnfPart b s K Λ h f N j)
        (nfB (nfEps1 α p b.rB s ε) ε j) := fun j => by
    obtain ⟨c1, c2⟩ := hinv.1 j j.2.le
    obtain ⟨p1, p2, -⟩ := nnf_proj (Λ := Λ) (K := K) (hjS j) c1 c2
    exact ⟨p1, p2⟩
  exact nnf_iter b ha.k_pos hρ (nfR_gt_two_rho hr hi) hσ (nfS_gt_two_sig hs hi)
    (nnf_slow_at ha N i) (nnf_c_pos ha) ha.alpha_pos ha.p_gt ha.K_pos.le
    (ha.hol.mono (polyNbhd_mono hRle)) (fun I hI => hdiv I (polyNbhd_mono hRle hI))
    (nnf_B_nonneg hε₁0 ha.eps_pos.le i) (hinv.1 i le_rfl).1 (hinv.1 i le_rfl).2
    ((small_iff_iterU ha.p_gt ha.alpha_pos hρ hσ).2 (nnf_small_at ha hsm hN hi))
    (fun j : Fin i => nnfPart b s K Λ h f N j) (fun j : Fin i => nfR b.rB N j)
    (fun j : Fin i => nfS s N j) (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j)
    (fun j => nfR_anti hr.le N j.2.le) (fun j => nfS_anti hs.le N j.2.le)
    (fun j => nnf_B_nonneg hε₁0 ha.eps_pos.le j) (fun j => (hP j).1) (fun j => (hP j).2)
    (nnfG_eq_fin i) ha.symmetric (fun I hI => ha.real I (polyNbhd_mono hRle hI))
    hinv.2.2 hinv.2.1

/-- The bound of step `i ≤ N` in Case A: `B₁ = ε₁` for `i = 0` ((6.1)), `B_{i+1} = Bᵢ/4`
afterwards (`nf-induct`). -/
theorem nnf_bound_at (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (b.rB / 8) (s / 6))
    {i : ℕ} (hi : i ≤ N) :
    nnfBound α p K (nfRho b.rB N i) (nfSig s N i) (nfB (nfEps1 α p b.rB s ε) ε i)
      (starNorm (nfR b.rB N i) (nfS s N i) (nfRho b.rB N i) (nfSig s N i)
        (fun j : Fin i => nfR b.rB N j) (fun j : Fin i => nfS s N j)
        (fun j : Fin i => nfB (nfEps1 α p b.rB s ε) ε j)) ≤
      nfB (nfEps1 α p b.rB s ε) ε (i + 1) := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    have e1 : nfRho b.rB N 0 = b.rB / 8 := by simp [nfRho]
    have e2 : nfSig s N 0 = s / 6 := by simp [nfSig]
    have e3 : starNorm (nfR b.rB N 0) (nfS s N 0) (nfRho b.rB N 0) (nfSig s N 0)
        (fun j : Fin 0 => nfR b.rB N j) (fun j : Fin 0 => nfS s N j)
        (fun j : Fin 0 => nfB (nfEps1 α p b.rB s ε) ε j) = 0 := by
      simp [starNorm]
    have e4 : nfB (nfEps1 α p b.rB s ε) ε (0 + 1) = nfEps1 α p b.rB s ε := by simp [nfB]
    rw [e3, e1, e2, e4]
    exact nnfBound_caseA ha.p_gt ha.alpha_pos ha.K_pos hr hs ha.eps_pos.le (nnf_hi hsm)
      ha.cutoff hA
  · have hN1 : 1 ≤ N := h1.trans_le hi
    have hε₁0 := nfEps1_nonneg ha.p_gt ha.alpha_pos hr hs (ε := ε)
    have hρ := nfRho_pos hr hi
    have hσ := nfSig_pos hs hi
    obtain ⟨hS0, hS⟩ := nnf_star_at ha hsm hN hi h1
    have hρ' : 0 < b.rB / (8 * (N : ℝ)) := by rw [← nfRho_ne_zero h1.ne']; exact hρ
    have hσ' : 0 < s / (4 * (N : ℝ)) := by rw [← nfSig_ne_zero h1.ne']; exact hσ
    have hδ : iterU α p (nfB (nfEps1 α p b.rB s ε) ε i) (nfRho b.rB N i) (nfSig s N i) ≤
        1 / 2 ^ 8 := by
      rw [nfRho_ne_zero h1.ne', nfSig_ne_zero h1.ne']
      exact (iterU_mono ha.p_gt ha.alpha_pos hρ' hσ' (nnf_B_le_eps1 hε₁0 h1 (ε := ε))).trans
        (nnf_sixtwo ha hsm hN hN1).2
    have hex : Real.exp (-(2 * Real.pi * K * nfSig s N i)) ≤ 1 / 8 := by
      rw [nfSig_ne_zero h1.ne']
      exact exp_sigma_le hN1 (nnf_floor ha hN).1
    have := nnf_induct_step ha.p_gt ha.alpha_pos hρ hσ (nnf_B_nonneg hε₁0 ha.eps_pos.le i) hS0
      hδ hS hex
    refine this.trans_eq ?_
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [nfB]
    rw [pow_succ, div_div]

/-- The induction step in Case A: `NnfInv i → NnfInv (i+1)` for `i ≤ N`. -/
theorem nnf_inv_succ (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (b.rB / 8) (s / 6))
    {i : ℕ} (hi : i ≤ N) (hinv : NnfInv b s K α p ε Λ h f N i) :
    NnfInv b s K α p ε Λ h f N (i + 1) := by
  have st := nnf_step_at ha hsm hN hi hinv
  have hB := nnf_bound_at ha hsm hN hA hi
  refine ⟨fun j hj => ?_, st.nnf_fp_real, st.nnf_gp_real⟩
  by_cases hji : j ≤ i
  · exact hinv.1 j hji
  · obtain rfl : j = i + 1 := by omega
    exact ⟨st.nnf_fp_class, st.nnf_fp_bound.mono le_rfl le_rfl hB⟩

/-- `nf-induct`: all invariants up to step `N + 1` in Case A. -/
theorem nnf_inv_all (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (b.rB / 8) (s / 6)) :
    ∀ i ≤ N + 1, NnfInv b s K α p ε Λ h f N i := by
  intro i
  induction i with
  | zero => exact fun _ => nnf_inv_zero ha
  | succ i ih => exact fun hi => nnf_inv_succ ha hsm hN hA (by omega) (ih (by omega))

/-- The properties of the `i`-th map on `Uᵢ₊₁` (Theorem `bpN:p11:iterative` (a), (b), (e)
transported to the schedule), as consumed by the telescope of `NormalForm`. -/
theorem nnf_step_props (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K)) (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    {i : ℕ} (hi : i ≤ N) (hinv : NnfInv b s K α p ε Λ h f N i) :
    DifferentiableOn ℂ (nnfPhi b s K Λ h f N i) (nnfU b s N (i + 1)) ∧
    MapsTo (nnfPhi b s K Λ h f N i) (nnfU b s N (i + 1)) (nnfU b s N i) ∧
    (∀ z ∈ nnfU b s N (i + 1), ∀ ℓ : Fin n → ℤ,
      nnfPhi b s K Λ h f N i (z.1 + (fun j => (ℓ j : ℂ)), z.2) =
        nnfPhi b s K Λ h f N i z + ((fun j => (ℓ j : ℂ)), 0)) ∧
    ExtCanonical b.c (nnfU b s N (i + 1)) (nnfPhi b s K Λ h f N i) ∧
    Set.InjOn (nnfPhi b s K Λ h f N i) (nnfU b s N (i + 1)) ∧
    (∀ z ∈ nnfU b s N (i + 1),
      ‖(nnfPhi b s K Λ h f N i z).1 - z.1‖ ≤
        conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (2*Real.pi*α*nfRho b.rB N i) ∧
      ‖fastAction (nnfPhi b s K Λ h f N i z) - fastAction z‖ ≤
        conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (Real.exp 1*2*Real.pi*α*nfSig s N i) ∧
      ‖slowPair (nnfPhi b s K Λ h f N i z) - slowPair z‖ ≤
        conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (16*k*2*Real.pi*α*nfSig s N i)) ∧
    (∀ z : ER n k, extCx z ∈ nnfU b s N (i + 1) →
      extCx (extRe (nnfPhi b s K Λ h f N i (extCx z))) = nnfPhi b s K Λ h f N i (extCx z)) := by
  have st := nnf_step_at ha hsm hN hi hinv
  exact ⟨st.nnf_diff, st.nnf_maps, st.nnf_transl, st.nnf_canon, st.nnf_inj, st.nnf_disp,
    st.nnf_real⟩

/-! #### Case B -/

/-- `nf-case`, Case B: the single step with the doubled losses `(R/4, s/3)`, `g = 0`, `δ = ε`
(`(SL)_{R/4,s/3}`, `u' = u/4 ≤ 1/64`). -/
theorem nnf_caseB_step (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    NnfStep b b.rB s (b.rB / 4) (s / 3) K α p ε Λ h (fun _ => 0) f
      (starNorm b.rB s (b.rB / 4) (s / 3) (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0)) := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hu := iterU_first ha.p_gt ha.alpha_pos ha.K_pos hr hs ha.eps_pos.le (nnf_hi hsm) ha.cutoff
  have hd := iterU_double (p := p) (ε := ε) ha.alpha_pos hr hs
  have hdiv := (KAM.NormalForm.divisor ha.p_gt ha.alpha_pos ha.K_pos.le ha.L_nonneg ha.nr ha.lip
    ha.divisor_size).2
  have hρ : 0 < b.rB / 4 := by positivity
  have hσ : 0 < s / 3 := by positivity
  have hsr : 0 ≤ s * b.rB := by positivity
  have hSL : slowLoss b.c (b.rB / 4) (s / 3) k :=
    nnf_slowLoss b hr ha.slow_width_pos ha.slow hρ.le (by linarith)
  exact nnf_iter b ha.k_pos hρ (by linarith) hσ (by linarith) hSL (nnf_c_pos ha) ha.alpha_pos
    ha.p_gt ha.K_pos.le ha.hol hdiv ha.eps_pos.le ha.pert.1 ha.bound
    ((small_iff_iterU ha.p_gt ha.alpha_pos hρ hσ).2 (by linarith))
    (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
    (fun j : Fin 0 => j.elim0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (fun j => j.elim0) (by funext z; simp) ha.symmetric ha.real
    (fun _ _ => Complex.zero_im) ha.pert.2

end NnfSchedule

end KAM.Nekhoroshev

end
