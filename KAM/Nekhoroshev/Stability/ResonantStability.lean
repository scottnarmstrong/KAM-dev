/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.ResonantStabilityCore
public import KAM.Nekhoroshev.Stability.Preimage
public import KAM.Nekhoroshev.NormalForm.NormalForm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Resonant Stability Lemma (`bpN:p7:resonant-prop2`)

Proposition 2: the reduction `δ' = mr/8`, `L = √n M` (`stepN:p7:p2-red`), the three cases
(`stepN:p7:p2-cases`: A `Λ ≠ ℤⁿ`, `κ ≥ 6` via `normal_form`; B `Λ ≠ ℤⁿ`, `κ < 6` with `Ψ = id`;
C `Λ = ℤⁿ`), (T1)/(T2) (`stepN:p7:p2-t12`) and the conclusion from `prop2_core`
(`stepN:p7:p2-t3`, `stepN:p7:p2-concl`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical KAM.NormalForm
open KAM.Nekhoroshev (euclid)

variable {n : ℕ}

theorem reMap_id (x : (Fin n → ℝ) × (Fin n → ℝ)) : reMap id x = x := by
  ext i <;> simp [reMap]

theorem reMap_eq_of {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {x y : (Fin n → ℝ) × (Fin n → ℝ)} (h : Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y) :
    reMap Ψ x = y := by
  unfold reMap
  rw [h]
  ext i <;> simp

theorem euclid_re_le (v : Fin n → ℂ) : euclid (fun i => (v i).re) ≤ euclid v := by
  unfold euclid
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

/-- Real points of `ℝⁿ × D` lie in `W_ϱ` (`ϱ > 0`). -/
theorem mem_realStrip_of_mem {D : Set (Fin n → ℝ)} {ϱ : ℝ} (hϱ : 0 < ϱ)
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y.2 ∈ D) : y ∈ realStrip D ϱ :=
  ⟨mem_univ _, y.2, hy, by simpa using hϱ⟩

variable {D : Set (Fin n → ℝ)} {r s K α p m M ℓ δ ε : ℝ} {Λ : AddSubgroup (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The hypotheses of `resonant_prop2` (bundled for the case lemmas). -/
structure Prop2Hyp (D : Set (Fin n → ℝ)) (r s K α p m M ℓ δ ε : ℝ) (Λ : AddSubgroup (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hn : 1 ≤ n
  hp : 1 < p
  hp32 : p ≤ 3 / 2
  hr : 0 < r
  hs : 0 < s
  hK : 0 < K
  hα : 0 < α
  hm : 0 < m
  hmM : m ≤ M
  hℓ : 0 < ℓ
  hδ : 0 < δ
  hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)
  hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2)
  hHess : ∀ I ∈ polyNbhd (cpx D) r, ∀ v : Fin n → ℂ,
    euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v
  hqc : IsQuasiConvex (realNbhd D r) h ℓ m
  hf : InClass (cpx D) r s f
  hfr : RealOn (Dom n (cpx D) r s) f
  hfb : WBound (cpx D) r s f ε
  hε0 : 0 ≤ ε
  hnr : IsNonresonant (cpx D) K α (Λ : Set (Fin n → ℤ)) h
  hclose : IsCloseToRes D (Λ : Set (Fin n → ℤ)) h δ
  hεb : ε ≤ p / conjExp p * (m * r ^ 2 / 2 ^ 7)
  hδb : δ ≤ m * r / 8
  hc1 : r ≤ α / (p * Real.sqrt n * M * K)
  hc2 : r ≤ 4 * ℓ / m
  hc3 : M * r ≤ ℓ / 2

/-- The confinement statement of `resonant_prop2` in the Euclidean norm. -/
def Prop2Concl (D : Set (Fin n → ℝ)) (r s K m ε : ℝ) (Λ : AddSubgroup (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ Ω : ℝ, (∀ I, euclid (I - I₀) ≤ r / 2 → euclid (KAM.frequencyMap h I) ≤ Ω) →
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
      (z 0).2 = I₀ → ∀ t ∈ J, ((Λ : Set (Fin n → ℤ)) = univ ∨
          |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
        euclid ((z t).2 - I₀) ≤ r / 2

/-- Numerical consequences of the hypotheses (`stepN:p7:p2-red`). -/
structure Prop2Nums (D : Set (Fin n → ℝ)) (r K α p m M ε : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  hMpos : 0 < M
  hqpos : 0 < conjExp p
  hsn0 : 0 < Real.sqrt n
  hsn : 1 ≤ Real.sqrt n
  hε1 : ε ≤ m * r ^ 2 / 2 ^ 8
  hqε : conjExp p * ε ≤ p * (m * r ^ 2 / 2 ^ 7)
  hc1' : p * Real.sqrt n * M * K * r ≤ α
  hrad : K * (Real.sqrt n * M) * r ≤ α / p
  hε2 : ε * (2 ^ 7 * conjExp p * K) ≤ α * r
  hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)
  hess : HessBound (realNbhd D (r / 2)) h M
  hlip : FreqLipschitz (cpx D) r (Real.sqrt n * M) h

theorem Prop2Hyp.nums (H : Prop2Hyp D r s K α p m M ℓ δ ε Λ h f) :
    Prop2Nums D r K α p m M ε h := by
  obtain ⟨hn, hp, hp32, hr, hs, hK, hα, hm, hmM, hℓ, hδ, hh, hhr, hHess, hqc, hf, hfr, hfb,
    hε0, hnr, hclose, hεb, hδb,
    hc1, hc2, hc3⟩ := H
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  have hp0 : 0 < p := by linarith
  have hqpos : 0 < conjExp p := div_pos hp0 (by linarith)
  have hpq : p / conjExp p = p - 1 := by unfold conjExp; field_simp
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsn : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hmr2 : 0 ≤ m * r ^ 2 := by positivity
  have hε1 : ε ≤ m * r ^ 2 / 2 ^ 8 := by
    calc ε ≤ p / conjExp p * (m * r ^ 2 / 2 ^ 7) := hεb
      _ ≤ 1 / 2 * (m * r ^ 2 / 2 ^ 7) := by
        rw [hpq]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = m * r ^ 2 / 2 ^ 8 := by ring
  have hqε : conjExp p * ε ≤ p * (m * r ^ 2 / 2 ^ 7) := by
    have := mul_le_mul_of_nonneg_left hεb hqpos.le
    calc conjExp p * ε ≤ conjExp p * (p / conjExp p * (m * r ^ 2 / 2 ^ 7)) := this
      _ = p * (m * r ^ 2 / 2 ^ 7) := by field_simp
  have hc1' : p * Real.sqrt n * M * K * r ≤ α := by
    have := (le_div_iff₀ (by positivity : 0 < p * Real.sqrt n * M * K)).1 hc1
    linarith
  have hrad : K * (Real.sqrt n * M) * r ≤ α / p := by
    rw [le_div_iff₀ hp0]; linarith
  have hε2 : ε * (2 ^ 7 * conjExp p * K) ≤ α * r := by
    have h1 : p * M * K * r ≤ α := by
      have : p * M * K * r ≤ p * Real.sqrt n * M * K * r := by
        have : 0 ≤ p * M * K * r := by positivity
        nlinarith
      linarith
    have h2 : conjExp p * ε * K * 2 ^ 7 ≤ p * m * r ^ 2 * K := by
      have := mul_le_mul_of_nonneg_right hqε (by positivity : 0 ≤ K * 2 ^ 7)
      nlinarith
    have h3 : p * m * r ^ 2 * K ≤ p * M * r ^ 2 * K := by gcongr
    have h4 : p * M * r ^ 2 * K ≤ α * r := by nlinarith
    nlinarith
  have hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K) := by
    have e : 1 / (2 ^ 7 * conjExp p) * (α * r / K) = α * r / (2 ^ 7 * conjExp p * K) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    exact hε2
  exact ⟨hMpos, hqpos, hsn0, hsn, hε1, hqε, hc1', hrad, hε2, hi,
    fun I hI => hessBound_of_complex hh hHess I (realNbhd_mono D (by linarith) hI),
    freqLipschitz_of_complex hMpos.le hh hHess⟩

theorem Prop2Concl.wrap (hc : Prop2Concl D r s K m ε Λ h f) (hr : 0 < r) :
    ∀ I₀ ∈ D, ∀ Ω : ℝ, (∀ I, euclid (I - I₀) ≤ r / 2 → euclid (KAM.frequencyMap h I) ≤ Ω) →
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
        (z 0).2 = I₀ → ∀ t ∈ J, ((Λ : Set (Fin n → ℤ)) = univ ∨
            |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
          euclid ((z t).2 - I₀) ≤ r / 2 ∧ ‖(z t).2 - I₀‖ ≤ r := by
  intro I₀ hI₀ Ω hΩ J hJ h0 z hz hz0 t ht htime
  have := hc I₀ hI₀ Ω hΩ J hJ h0 z hz hz0 t ht htime
  exact ⟨this, ((KAM.Nekhoroshev.norm_le_euclid _).1.trans this).trans (by linarith)⟩

/-- The trivial conjugacy `Ψ = id` (cases B and C). -/
theorem prop2_idData (hr : 0 < r) (s : ℝ) :
    DifferentiableOn ℂ (id : (Fin n → ℂ) × (Fin n → ℂ) → _) (Dom n (cpx D) (r / 2) s) ∧
    MapsTo (id : (Fin n → ℂ) × (Fin n → ℂ) → _) (Dom n (cpx D) (r / 2) s) (Dom n (cpx D) r s) ∧
    (∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) (r / 2) s →
      (id : (Fin n → ℂ) × (Fin n → ℂ) → _) (KAM.realInclusion₂ n x) ∈
        range (KAM.realInclusion₂ n)) ∧
    (∀ z ∈ Dom n (cpx D) (r / 2) s, ∀ v w,
      symplFormC (fderiv ℂ (id : (Fin n → ℂ) × (Fin n → ℂ) → _) z v)
        (fderiv ℂ (id : (Fin n → ℂ) × (Fin n → ℂ) → _) z w) = symplFormC v w) ∧
    (∀ x ∈ realStrip D (r / 2),
      euclid ((reMap (id : (Fin n → ℂ) × (Fin n → ℂ) → _) x).2 - x.2) ≤ 0) ∧
    (∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D (r / 2),
      reMap (id : (Fin n → ℂ) × (Fin n → ℂ) → _) x = y) := by
  refine ⟨differentiableOn_id, fun z hz => Dom_mono (by linarith) le_rfl hz,
    fun x _ => ⟨x, rfl⟩, ?_, fun x _ => by simp [reMap_id, euclid], fun y hy =>
    ⟨y, mem_realStrip_of_mem (by positivity) hy, reMap_id y⟩⟩
  intro z _ v w
  simp

theorem prop2_hρ0 (hM : 0 < M) (hm : 0 < m) (hr : 0 < r) : 0 ≤ resRho (m * r / 8) M / 4 := by
  unfold resRho; positivity

/-- Case C: `Λ = ℤⁿ`. -/
theorem prop2_caseC (H : Prop2Hyp D r s K α p m M ℓ δ ε Λ h f)
    (hΛ : (Λ : Set (Fin n → ℤ)) = univ) : Prop2Concl D r s K m ε Λ h f := by
  have N := H.nums
  obtain ⟨hn, hp, hp32, hr, hs, hK, hα, hm, hmM, hℓ, hδ, hh, hhr, hHess, hqc, hf, hfr, hfb,
    hε0, hnr, hclose, hεb, hδb,
    hc1, hc2, hc3⟩ := H
  obtain ⟨hMpos, hqpos, hsn0, hsn, hε1, hqε, hc1', hrad, hε2, hi, hess, hlip⟩ := N
  obtain ⟨hid, hidmap, hidreal, hidsympl, hidT1, hidT2⟩ := prop2_idData (D := D) hr s
  have hρ0 := prop2_hρ0 hMpos hm hr
  have hclassId : ∀ (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ), InClass (cpx D) r s u →
      InClass (cpx D) (r / 2) s u := fun u hu => inClass_mono_nf hu (by linarith) le_rfl
  refine (prop2_core hn (s' := s) (K := K) (Mg := ε) (η := 0) (ζ := ε) (d := 0)
    (Ψ := id) (g := f) (fs := fun _ => 0) hr hs hs le_rfl hm hmM hε0 hδ hh hhr hess hqc hf hfr
    hclose hδb hc2 hc3 (hclassId f hf) (realOn_mono' hfr (Dom_mono (by linarith) le_rfl))
    (hfb.mono (by linarith) le_rfl le_rfl) ?_
    ⟨differentiableOn_const _, fun _ _ _ => rfl⟩ (fun x _ => by simp)
    (wbound_zero_nf le_rfl) le_rfl (by linarith) (by nlinarith) hid hidmap hidreal hidsympl
    (fun z _ => by simp) hidT1 hidT2 le_rfl hρ0 ?_)
  · intro I _ k hk
    exact absurd (by rw [hΛ]; exact mem_univ k) hk
  · intro Ω _ t _
    simp only [mul_zero]
    positivity

/-- Case B: `Λ ≠ ℤⁿ`, `κ < 6`, `Ψ = id`, `g = 0`, `f_* = f`. -/
theorem prop2_caseB (H : Prop2Hyp D r s K α p m M ℓ δ ε Λ h f)
    (hΛ : (Λ : Set (Fin n → ℤ)) ≠ univ) (hκ : 2 * Real.pi * K * s < 6) :
    Prop2Concl D r s K m ε Λ h f := by
  have N := H.nums
  obtain ⟨hn, hp, hp32, hr, hs, hK, hα, hm, hmM, hℓ, hδ, hh, hhr, hHess, hqc, hf, hfr, hfb,
    hε0, hnr, hclose, hεb, hδb,
    hc1, hc2, hc3⟩ := H
  obtain ⟨hMpos, hqpos, hsn0, hsn, hε1, hqε, hc1', hrad, hε2, hi, hess, hlip⟩ := N
  obtain ⟨hid, hidmap, hidreal, hidsympl, hidT1, hidT2⟩ := prop2_idData (D := D) hr s
  have hρ0 := prop2_hρ0 hMpos hm hr
  have hclassId : ∀ (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ), InClass (cpx D) r s u →
      InClass (cpx D) (r / 2) s u := fun u hu => inClass_mono_nf hu (by linarith) le_rfl
  have hexp : Real.exp (2 * Real.pi * K * s / 6) ≤ 3 := by
    have h1 : Real.exp (2 * Real.pi * K * s / 6) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by linarith)
    have := Real.exp_one_lt_three
    linarith
  refine (prop2_core hn (s' := s) (K := K) (Mg := 0) (η := ε) (ζ := ε) (d := 0)
    (Ψ := id) (g := fun _ => 0) (fs := f) hr hs hs le_rfl hm hmM hε0 hδ hh hhr hess hqc hf hfr
    hclose hδb hc2 hc3 ⟨differentiableOn_const _, fun _ _ _ => rfl⟩ (fun x _ => by simp)
    (wbound_zero_nf le_rfl) ?_ (hclassId f hf)
    (realOn_mono' hfr (Dom_mono (by linarith) le_rfl)) (hfb.mono (by linarith) le_rfl le_rfl)
    hε0 (by linarith) (by nlinarith) hid hidmap hidreal hidsympl
    (fun z _ => by simp) hidT1 hidT2 le_rfl hρ0 ?_)
  · intro I _ k _
    simp [coeff, KAM.torusCoeffW, KAM.torusAverage]
  · intro Ω hΩ t hc
    rcases hc with hc | hc
    · exact absurd hc hΛ
    · have h1 : 0 ≤ |t| * (Ω * ε) := by positivity
      have h2 : 0 ≤ s * m * r ^ 2 := by positivity
      have h3 : s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6) ≤ s * m * r ^ 2 * 3 :=
        mul_le_mul_of_nonneg_left hexp h2
      nlinarith

/-- Case A: `Λ ≠ ℤⁿ`, `κ ≥ 6`: the normal form. -/
theorem prop2_caseA (H : Prop2Hyp D r s K α p m M ℓ δ ε Λ h f)
    (hΛ : (Λ : Set (Fin n → ℤ)) ≠ univ) (hκ : 6 ≤ 2 * Real.pi * K * s) :
    Prop2Concl D r s K m ε Λ h f := by
  have N := H.nums
  obtain ⟨hn, hp, hp32, hr, hs, hK, hα, hm, hmM, hℓ, hδ, hh, hhr, hHess, hqc, hf, hfr, hfb,
    hε0, hnr, hclose, hεb, hδb,
    hc1, hc2, hc3⟩ := H
  obtain ⟨hMpos, hqpos, hsn0, hsn, hε1, hqε, hc1', hrad, hε2, hi, hess, hlip⟩ := N
  have hρ0 := prop2_hρ0 hMpos hm hr
  have hΛ' : ∀ k ∈ (Λ : Set (Fin n → ℤ)), -k ∈ (Λ : Set (Fin n → ℤ)) := fun k hk =>
    Λ.neg_mem hk
  obtain ⟨Ψ, g, fs, hΨd, -, hΨmap, hΨsym, -, hgc, hfsc, hgco, hΨconj, hga, -, hfsb, hdisp,
    hrealD⟩ := normal_form (D := cpx D) (L := Real.sqrt n * M) (Λ := (Λ : Set (Fin n → ℤ)))
      hp hα hK (by positivity) hr hs hh hnr hlip hrad hf hfb hε0 hi hκ
  obtain ⟨hgr, hfsr, hΨreal⟩ := hrealD hΛ' hhr hfr
  have hs6 : 0 < s / 6 := by positivity
  -- the bound of `g`
  obtain ⟨t1, -, t3, -⟩ := projections hs hf hfb {k : Fin n → ℤ | KAM.Fourier.modeSize k ≤ K}
  obtain ⟨p1, -, p3, -⟩ := projections hs t1 t3 (Λ : Set (Fin n → ℤ))
  have hg0c : InClass (cpx D) (r / 2) (s / 6) (homRes K (Λ : Set (Fin n → ℤ)) f) :=
    inClass_mono_nf (p1 : InClass (cpx D) r s (homRes K (Λ : Set (Fin n → ℤ)) f))
      (by linarith) (by linarith)
  have hg0b : WBound (cpx D) (r / 2) (s / 6) (homRes K (Λ : Set (Fin n → ℤ)) f) ε :=
    (p3 : WBound (cpx D) r s (homRes K (Λ : Set (Fin n → ℤ)) f) ε).mono (by linarith)
      (by linarith) le_rfl
  have hcε : 16 * (2 * conjExp p * K / (α * r)) * ε ^ 2 ≤ ε / 4 := by
    have e : 16 * (2 * conjExp p * K / (α * r)) * ε ^ 2 =
        ε * (ε * (32 * conjExp p * K)) / (α * r) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hε2 hε0]
  have hgdc : InClass (cpx D) (r / 2) (s / 6)
      (fun z => g z - homRes K (Λ : Set (Fin n → ℤ)) f z) :=
    ⟨hgc.differentiableOn.sub hg0c.differentiableOn, fun j z hz => by
      show g (z.1 + Pi.single j 1, z.2) - homRes K (Λ : Set (Fin n → ℤ)) f
        (z.1 + Pi.single j 1, z.2) = g z - homRes K (Λ : Set (Fin n → ℤ)) f z
      rw [hgc.periodic j z hz, hg0c.periodic j z hz]⟩
  have hgb : WBound (cpx D) (r / 2) (s / 6) g (ε + ε / 4) := by
    have := wbound_add hs6 hgdc hg0c (hga.mono le_rfl le_rfl hcε) hg0b
    have e : (fun z => (g z - homRes K (Λ : Set (Fin n → ℤ)) f z) +
        homRes K (Λ : Set (Fin n → ℤ)) f z) = g := by funext z; ring
    rw [e] at this
    exact this.mono le_rfl le_rfl (by linarith)
  have hex : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ 1 / 2 := by
    have h1 : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_one_gt_two
    have h4 := Real.exp_pos (-1)
    nlinarith
  have hex0 := Real.exp_pos (-(2 * Real.pi * K * s) / 6)
  -- (T1)
  have hT1 : ∀ x ∈ realStrip D (r / 2),
      euclid ((reMap Ψ x).2 - x.2) ≤ resRho (m * r / 8) M / 4 := by
    intro x hx
    have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) (r / 2) (s / 6) :=
      (realInclusion₂_mem_Dom_iff D hs6 x).2 hx
    have hdi := (hdisp _ hxD).1
    have hfin : Real.sqrt n * K * (p * (m * r ^ 2 / 2 ^ 7)) ≤
        m * r / 8 / (4 * M) / 4 * α := by
      have e : m * r / 8 / (4 * M) / 4 * (p * Real.sqrt n * M * K * r) =
          Real.sqrt n * K * (p * (m * r ^ 2 / 2 ^ 7)) := by field_simp; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left hc1' (by positivity)
    calc euclid ((reMap Ψ x).2 - x.2)
        ≤ euclid ((Ψ (KAM.realInclusion₂ n x)).2 - (KAM.realInclusion₂ n x).2) := by
          have : ((reMap Ψ x).2 - x.2) =
              fun i => (((Ψ (KAM.realInclusion₂ n x)).2 - (KAM.realInclusion₂ n x).2) i).re := by
            ext i; simp [reMap]
          rw [this]; exact euclid_re_le _
      _ ≤ Real.sqrt n * ‖(Ψ (KAM.realInclusion₂ n x)).2 - (KAM.realInclusion₂ n x).2‖ :=
          (KAM.Nekhoroshev.norm_le_euclid _).2.1
      _ ≤ Real.sqrt n * (conjExp p * K * ε / α) := mul_le_mul_of_nonneg_left hdi hsn0.le
      _ ≤ resRho (m * r / 8) M / 4 := by
          rw [resRho, show Real.sqrt n * (conjExp p * K * ε / α) =
            Real.sqrt n * K * (conjExp p * ε) / α by ring, div_le_iff₀ hα]
          calc Real.sqrt n * K * (conjExp p * ε)
              ≤ Real.sqrt n * K * (p * (m * r ^ 2 / 2 ^ 7)) :=
                mul_le_mul_of_nonneg_left hqε (by positivity)
            _ ≤ _ := hfin
  -- (T2)
  have hT2 : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D →
      ∃ x ∈ realStrip D (r / 2), reMap Ψ x = y := by
    intro y hy
    obtain ⟨x, hx, hΨx, -⟩ := preimage_nfl hp hα hK hr hs hε0 hi hκ hΨd hΨreal hdisp y hy
    exact ⟨x, hx, reMap_eq_of hΨx⟩
  refine (prop2_core hn (s' := s / 6) (K := K) (Mg := ε + ε / 4)
    (η := Real.exp (-(2 * Real.pi * K * s) / 6) * ε) (ζ := 2 * ε)
    (d := resRho (m * r / 8) M / 4) (Ψ := Ψ) (g := g) (fs := fs) hr hs hs6 (by linarith) hm hmM
    hε0 hδ hh hhr hess hqc hf hfr hclose hδb hc2 hc3 hgc hgr hgb
    (fun I hI k hk => hgco I hI k (fun hk' => hk hk'.1)) hfsc hfsr hfsb (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_right hex hε0]) (by linarith) hΨd hΨmap hΨreal hΨsym
    (fun z hz => (hΨconj z hz).symm) hT1 hT2 hρ0 le_rfl ?_)
  intro Ω hΩ0 t hc
  rcases hc with hc | hc
  · exact absurd hc hΛ
  · have hEe : Real.exp (-(2 * Real.pi * K * s) / 6) * Real.exp (2 * Real.pi * K * s / 6) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc |t| * (12 * Ω * (Real.exp (-(2 * Real.pi * K * s) / 6) * ε))
        = Real.exp (-(2 * Real.pi * K * s) / 6) * (|t| * (288 * Ω * ε)) / 24 := by ring
      _ ≤ Real.exp (-(2 * Real.pi * K * s) / 6) *
          (s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) / 24 := by gcongr
      _ = s / 6 * m * (r / 2) ^ 2 := by
          have : Real.exp (-(2 * Real.pi * K * s) / 6) *
              (s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) = s * m * r ^ 2 := by
            rw [show Real.exp (-(2 * Real.pi * K * s) / 6) *
              (s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) =
              s * m * r ^ 2 * (Real.exp (-(2 * Real.pi * K * s) / 6) *
                Real.exp (2 * Real.pi * K * s / 6)) by ring, hEe, mul_one]
          rw [this]; ring

/-- `bpN:p7:resonant-prop2`. `Ω(I₀)` is any bound of `‖ω‖₂` on `{‖I - I₀‖₂ ≤ r/2}`; `|t| ≤ T(I₀)` is
`|t| · 288 Ω ε ≤ s m r² e^{κ/6}`. Complex Hessian bound in the Euclidean operator norm on
`V_r D`. -/
theorem resonant_prop2 (hn : 1 ≤ n) {D : Set (Fin n → ℝ)} {r s K α p m M ℓ δ ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hp : 1 < p) (hp32 : p ≤ 3 / 2) (hr : 0 < r) (hs : 0 < s) (hK : 0 < K) (hα : 0 < α)
    (hm : 0 < m) (hmM : m ≤ M) (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2))
    (hHess : ∀ I ∈ polyNbhd (cpx D) r, ∀ v : Fin n → ℂ,
      KAM.Nekhoroshev.euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤
        M * KAM.Nekhoroshev.euclid v)
    (hqc : IsQuasiConvex (realNbhd D r) h ℓ m)
    (hf : InClass (cpx D) r s f) (hfr : RealOn (Dom n (cpx D) r s) f)
    (hfb : WBound (cpx D) r s f ε) (hε0 : 0 ≤ ε)
    -- (a)
    (hnr : IsNonresonant (cpx D) K α (Λ : Set (Fin n → ℤ)) h)
    (hclose : IsCloseToRes D (Λ : Set (Fin n → ℤ)) h δ)
    -- (b)
    (hεb : ε ≤ p / conjExp p * (m * r ^ 2 / 2 ^ 7)) (hδb : δ ≤ m * r / 8)
    -- (c)
    (hc1 : r ≤ α / (p * Real.sqrt n * M * K)) (hc2 : r ≤ 4 * ℓ / m) (hc3 : M * r ≤ ℓ / 2) :
    ∀ I₀ ∈ D, ∀ Ω : ℝ, (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r / 2 →
        KAM.Nekhoroshev.euclid (KAM.frequencyMap h I) ≤ Ω) →
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
        (z 0).2 = I₀ →
        ∀ t ∈ J, ((Λ : Set (Fin n → ℤ)) = univ ∨
            |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
          KAM.Nekhoroshev.euclid ((z t).2 - I₀) ≤ r / 2 ∧ ‖(z t).2 - I₀‖ ≤ r := by
  have H : Prop2Hyp D r s K α p m M ℓ δ ε Λ h f :=
    ⟨hn, hp, hp32, hr, hs, hK, hα, hm, hmM, hℓ, hδ, hh, hhr, hHess, hqc, hf, hfr, hfb, hε0, hnr,
      hclose, hεb, hδb, hc1, hc2, hc3⟩
  refine Prop2Concl.wrap ?_ hr
  by_cases hΛ : (Λ : Set (Fin n → ℤ)) = univ
  · exact prop2_caseC H hΛ
  · by_cases hκ : 6 ≤ 2 * Real.pi * K * s
    · exact prop2_caseA H hΛ hκ
    · exact prop2_caseB H hΛ (not_le.1 hκ)

end KAM.Stability

end
