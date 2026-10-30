/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean.Balanced
public import KAM.CertificateSharp.Freq.QuadraticLunar
public import KAM.CertificateSharp.V2.RouteAQ
public import KAM.CertificateSharp.V2.ClassicalQ

/-!
# Certified small-divisor constants on the ray

For a clock frequency `ω* = κ (ω', 1)`, `n = 2`, `τ = 1`, `biteOk` checks a rational bound of the
whole sum `S(ω*, b)` with the balanced fibered checker of `KAM.Sharp2.Examples`, and the constant it
gives. `sdConst_ray_of_biteOk` is its soundness: `SDConst` on the whole ray `{s ω* : s ≥ 1}`, which
the isoenergetic scheme needs, through `S(s ω*, b) ≤ S(ω*, b)` (`sdSum_ray_le`) and
`S(κ ω, b) = κ⁻² S(ω, b)` (`smallDivisorSum_smul`). The box of `ω'` is `fiberBox`.

`siteOk` chooses, per site of the schedule, the certified constant (`some`) or the classical one
(`none`, for every `n` and `τ`). `NumQ.cert_ray` assembles the certificates of a run.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.Sharp2.Examples KAM.Sharp2.RouteA KAM.CertificateSharp

/-- The witness of one bite: the short rational `E₁ ≥ e^{-4πb}`, the cut-off `2^l`, the degree `J` of
the exponential polynomial, and the claimed bound of `S((ω', 1), b)`. -/
structure BiteWit where
  E1 : ℚ
  l : ℕ
  J : ℕ
  B : ℚ

/-- The box of `ω'`, for `ω = κ (ω', 1)`. -/
def fiberBox (box : FreqBox) (κ : ℚ) : FreqBox :=
  [((box.getD 0 (0, 0)).1 / κ, (box.getD 0 (0, 0)).2 / κ)]

/-- The checker's data at the bite `b`: `S(ω, b) = smallDivisorSum ω (2b)`. -/
def biteData (box : FreqBox) (κ γ b : ℚ) (w : BiteWit) : SdsData :=
  { box := fiberBox box κ, γ := γ / κ, δ := 2 * b, N := 2 ^ w.l, J := w.J, E1 := w.E1 }

/-- The last coordinate of the box is exactly `κ > 0`. -/
def clockOk (box : FreqBox) (κ : ℚ) : Bool :=
  decide (0 < κ) && decide (box.getD 1 (0, 0) = (κ, 0))

/-- The test at one bite. -/
def biteOk (box : FreqBox) (κ γ b c : ℚ) (w : BiteWit) : Bool :=
  decide (0 < c) && decide (0 < b) && balCheck (biteData box κ γ b w) w.l &&
    decide (balBound (biteData box κ γ b w) w.l ≤ w.B) &&
    decide (w.B * (κ ^ 2)⁻¹ * (γ * b) ^ 2 ≤ (31415 / 10000 * c) ^ 2)

/-- The test at a site: certified or classical. -/
def siteOk (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) : Option BiteWit → Bool
  | none => classicalOk n τ J b c
  | some w => decide (n = 2) && decide (τ = 1) && clockOk box κ && biteOk box κ γ b c w

theorem sdSum_clock_le {box : FreqBox} {κ γ b : ℚ} {w : BiteWit} (hκ : clockOk box κ = true)
    (hγ : 0 < γ) (hchk : balCheck (biteData box κ γ b w) w.l = true)
    (hB : balBound (biteData box κ γ b w) w.l ≤ w.B) {ωstar : Fin 2 → ℝ}
    (hω : FreqEncloses 2 box ωstar) (hdio : IsDiophantine (γ : ℝ) 1 ωstar) :
    sdSum ωstar b ≤ ((w.B * (κ ^ 2)⁻¹ : ℚ) : ℝ) := by
  simp only [clockOk, Bool.and_eq_true, decide_eq_true_eq] at hκ
  obtain ⟨hκ0, hbx⟩ := hκ
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ0
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have h1 : ωstar 1 = κ := by
    have := hω 1
    simp only [Fin.val_one, hbx] at this
    push_cast at this
    have h0 : |ωstar 1 - κ| = 0 := le_antisymm this (abs_nonneg _)
    exact sub_eq_zero.1 (abs_eq_zero.1 h0)
  set ω' : Fin 1 → ℝ := ![ωstar 0 / κ] with hω'
  have hsn : (Fin.snoc ω' 1 : Fin 2 → ℝ) = (κ : ℝ)⁻¹ • ωstar := by
    funext i
    fin_cases i
    · simp [hω', Fin.snoc, div_eq_inv_mul]
    · have : (κ : ℝ)⁻¹ * ωstar 1 = 1 := by rw [h1]; exact inv_mul_cancel₀ hκ'.ne'
      simpa [Fin.snoc] using this.symm
  have hsn' : ωstar = (κ : ℝ) • (Fin.snoc ω' 1 : Fin 2 → ℝ) := by
    rw [hsn, smul_smul, mul_inv_cancel₀ hκ'.ne', one_smul]
  have hbox : FreqEncloses 1 (fiberBox box κ) ω' := by
    intro i
    have h0 := hω 0
    have e : ((box.getD 0 (0, 0)).2 : ℝ) / κ = |ωstar 0 - (box.getD 0 (0, 0)).1| / κ -
        (|ωstar 0 - (box.getD 0 (0, 0)).1| - (box.getD 0 (0, 0)).2) / κ := by ring
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [fiberBox, hω', Fin.val_zero, List.getD_cons_zero, Matrix.cons_val_fin_one]
    push_cast
    rw [← sub_div, abs_div, abs_of_pos hκ']
    exact div_le_div_of_nonneg_right h0 hκ'.le
  have hdio' : IsDiophantine (((γ / κ : ℚ)) : ℝ) 1 (Fin.snoc ω' 1 : Fin 2 → ℝ) := by
    have h2 := isDiophantine_smul hdio ((κ : ℝ)⁻¹)
    have e1 : (γ : ℝ) * |(κ : ℝ)⁻¹| = ((γ / κ : ℚ) : ℝ) := by
      rw [abs_of_pos (inv_pos.2 hκ')]; push_cast; rw [div_eq_mul_inv]
    have e2 : (fun i => (κ : ℝ)⁻¹ * ωstar i) = (Fin.snoc ω' 1 : Fin 2 → ℝ) := by
      rw [hsn]; rfl
    rwa [e1, e2] at h2
  have hS := smallDivisorSum_le_bal (biteData box κ γ b w) rfl hchk hB hbox hdio'
  have e3 : (((biteData box κ γ b w).δ : ℚ) : ℝ) = 2 * (b : ℝ) := by simp [biteData]
  rw [e3] at hS
  rw [sdSum_eq_smallDivisorSum, hsn', smallDivisorSum_smul]
  push_cast
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hS (by positivity)

/-- **Soundness of the test at one bite.** -/
theorem sdConst_ray_of_biteOk {box : FreqBox} {κ γ b c : ℚ} {w : BiteWit}
    (hκ : clockOk box κ = true) (hγ : 0 < γ) (h : biteOk box κ γ b c w = true)
    {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 box ωstar) (hdio : IsDiophantine (γ : ℝ) 1 ωstar) :
    SDConst 2 1 (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  simp only [biteOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hb⟩, hchk⟩, hB⟩, hnum⟩ := h
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hS := sdSum_clock_le hκ hγ hchk hB hω hdio
  have hnum' : ((w.B * (κ ^ 2)⁻¹ : ℚ) : ℝ) * ((γ : ℝ) * b) ^ 2 ≤ (31415 / 10000 * (c : ℝ)) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hnum
    push_cast at this ⊢
    exact this
  have key : ∀ ω ∈ ray ωstar, SDConst 2 1 (γ : ℝ) (b : ℝ) (c : ℝ) {ω} := by
    rintro ω ⟨t, ht, rfl⟩
    exact sdConst_two_of_sdSum hγ' hb' hc' (isDiophantine_ray hdio ht)
      ((sdSum_ray_le hdio hγ' zero_le_one ht hb').trans hS) hnum'
  exact ⟨hc', hb', fun ω hω' => (key ω hω').sol ω rfl, fun ω hω' => (key ω hω').apriori ω rfl,
    fun ω hω' => (key ω hω').real ω rfl⟩

/-- **Soundness of the test at a site**, for a bite `b ≤ 1`. -/
theorem sdConst_of_siteOk {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {o : Option BiteWit}
    (hn : 1 ≤ n) (hτ : 1 ≤ τ) (hγ : 0 < γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (h : siteOk n τ J box κ γ b c o = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  cases o with
  | none =>
    refine sdConst_subset (sdConst_mono hγ' (sdConst_classical hn hτ' hγ' hb'
      (by exact_mod_cast hb1)) (cohConstC_le_of_ok hb.le h)) ?_
    rintro ω ⟨t, ht, rfl⟩
    exact isDiophantine_ray hdio ht
  | some w =>
    simp only [siteOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hκ⟩, hbite⟩ := h
    have e : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
    rw [e] at hdio ⊢
    exact sdConst_ray_of_biteOk hκ hγ hbite hω hdio

variable {Q : NumQ}

/-- The certificates of a run on the ray: certified or classical at each site of the prefix, the
classical constant in the tail. -/
theorem NumQ.cert_ray (hN : Q.toNum.Wf) {γ : ℝ} (hγ : 0 < γ) {ωstar : Fin Q.n → ℝ}
    (hdio : IsDiophantine γ Q.τ ωstar)
    (hc : ∀ s < Q.kp, SDConst Q.n Q.τ γ (Q.δ s) (Q.c.getD s 0) (ray ωstar))
    (hb : ∀ s < Q.kp, SDConst Q.n Q.τ γ (Q.b s) (Q.cbar.getD s 0) (ray ωstar))
    (ht : cohConstC Q.n Q.τ (Q.δ Q.kp) ≤ Q.ctail) :
    Q.toNum.Cert γ (ray ωstar) where
  stage := fun s hs => by rw [NumQ.cast_δ]; exact hc s hs
  bar := fun s hs => by rw [NumQ.cast_b]; exact hb s hs
  tail := fun δ hδ hle => by
    have h1 := sdConst_classical (n := Q.toNum.n) (by have := hN.two_le; omega) hN.τ_ge hγ hδ
      (hle.trans (hN.δ_le _))
    have h2 : cohConstC Q.toNum.n Q.toNum.τ δ ≤ Q.toNum.ctail := by
      refine (cohConstC_mono hN.τ_ge hδ.le hle).trans ?_
      rw [NumQ.cast_δ]
      exact ht
    refine sdConst_subset (sdConst_mono hγ h1 h2) ?_
    rintro ω ⟨t, ht', rfl⟩
    exact isDiophantine_ray hdio ht'

end KAM.CertificateSharp.V2

end
