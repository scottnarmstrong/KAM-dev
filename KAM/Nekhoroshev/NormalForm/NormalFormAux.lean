/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.Steps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: auxiliary lemmas for the assembly

Integer translations and reality along `chain Φ m` (`chain_translate`, `chain_real`), and the
Fourier coefficients of `P_Λ T_K u` and of finite sums of such (`coeff_homRes`,
`coeff_sum_eq_zero`), used by `normal_form` to show `ĝ_k = 0` for `k ∉ Λ ∩ Z_K`. Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 2).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section Chain

variable {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Integer translations commute with `chain Φ m`. -/
theorem chain_translate {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (htr : ∀ i ≤ m, ∀ k : Fin n → ℤ, ∀ z ∈ U (i + 1),
      Φ i (z.1 + (fun j => (k j : ℂ)), z.2) = Φ i z + ((fun j => (k j : ℂ)), 0))
    (k : Fin n → ℤ) : ∀ z ∈ U (m + 1),
      chain Φ m (z.1 + (fun j => (k j : ℂ)), z.2) = chain Φ m z + ((fun j => (k j : ℂ)), 0) := by
  induction m with
  | zero => exact fun z hz => htr 0 le_rfl k z hz
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => htr i (hle i hi))
    have hz' := hmap (m + 1) le_rfl hz
    show chain Φ m (Φ (m + 1) (z.1 + (fun j => (k j : ℂ)), z.2)) =
      chain Φ m (Φ (m + 1) z) + _
    rw [htr (m + 1) le_rfl k z hz]
    have e : Φ (m + 1) z + ((fun j => (k j : ℂ)), 0) =
        ((Φ (m + 1) z).1 + (fun j => (k j : ℂ)), (Φ (m + 1) z).2) := by
      ext <;> simp
    rw [e]
    exact h1 (Φ (m + 1) z) hz'

/-- Real points go to real points along `chain Φ m`. -/
theorem chain_real {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hreal : ∀ i ≤ m, ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ U (i + 1) →
        Φ i (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) :
    ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ U (m + 1) →
      chain Φ m (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) := by
  induction m with
  | zero => exact fun x hx => hreal 0 le_rfl x hx
  | succ m ih =>
    intro x hx
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hreal i (hle i hi))
    obtain ⟨y, hy⟩ := hreal (m + 1) le_rfl x hx
    show chain Φ m (Φ (m + 1) (KAM.realInclusion₂ n x)) ∈ _
    rw [← hy]
    refine h1 y ?_
    rw [hy]
    exact hmap (m + 1) le_rfl hx

end Chain

section Coeff

variable {D : Set (Fin n → ℂ)} {r s : ℝ}

/-- `P_Λ T_K u` is in the class and has the coefficients `1_{Λ ∩ Z_K} û_k`. -/
theorem coeff_homRes {K M : ℝ} {Λ : Set (Fin n → ℤ)} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass D r s u) (hb : WBound D r s u M) :
    ∀ I ∈ polyNbhd D r, ∀ k,
      coeff (homRes K Λ u) I k = (Λ ∩ zBall n K).indicator (coeff u I) k := by
  intro I hI k
  obtain ⟨t1, t2, t3, -⟩ := projections hs hu hb {k | KAM.Fourier.modeSize k ≤ K}
  obtain ⟨-, p2, -⟩ := projections hs t1 t3 Λ
  show coeff (projMode Λ (projMode {k | KAM.Fourier.modeSize k ≤ K} u)) I k = _
  rw [p2 I hI k]
  have e := t2 I hI k
  by_cases hΛ : k ∈ Λ <;> by_cases hZ : k ∈ zBall n K <;>
    simp_all [Set.indicator, zBall]

private theorem coeff_zero_fn {I : Fin n → ℂ} (k : Fin n → ℤ) :
    coeff (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) I k = 0 := by
  simp [coeff, KAM.torusCoeffW, KAM.torusAverage]

/-- A finite sum of class members, each with vanishing coefficients off `S`, has the same. -/
theorem coeff_sum_eq_zero (hs : 0 < s) (S : Set (Fin n → ℤ))
    (u : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (M : ℕ → ℝ) (m : ℕ)
    (hu : ∀ j < m, InClass D r s (u j) ∧ WBound D r s (u j) (M j))
    (hz : ∀ j < m, ∀ I ∈ polyNbhd D r, ∀ k, k ∉ S → coeff (u j) I k = 0) :
    ∀ I ∈ polyNbhd D r, ∀ k, k ∉ S →
      coeff (fun z => ∑ j ∈ Finset.range m, u j z) I k = 0 := by
  induction m with
  | zero =>
    intro I _ k _
    simpa using coeff_zero_fn (I := I) k
  | succ m ih =>
    intro I hI k hk
    have ih' := ih (fun j hj => hu j (by omega)) (fun j hj => hz j (by omega)) I hI k hk
    have key := sum_inClass_wbound (D := D) (r' := r) (s' := s) hs u M m
      (fun j hj => hu j (by omega))
    have e : (fun z => ∑ j ∈ Finset.range (m + 1), u j z) =
        fun z => (∑ j ∈ Finset.range m, u j z) + u m z := by
      funext z; rw [Finset.sum_range_succ]
    rw [e, coeff_add hs key.1 (hu m (by omega)).1 hI, ih', hz m (by omega) I hI k hk, add_zero]

/-- The class shrinks with the domain. -/
theorem inClass_mono_nf {r₀ s₀ : ℝ} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u)
    (hr : r ≤ r₀) (hs : s ≤ s₀) : InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

/-- The zero function has weighted norm `≤ M` for every `M ≥ 0`. -/
theorem wbound_zero_nf {M : ℝ} (hM : 0 ≤ M) :
    WBound D r s (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) M := by
  intro I _
  have h0 : ∀ k : Fin n → ℤ, coeff (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) I k = 0 :=
    fun k => coeff_zero_fn k
  simpa [WSummable, wsum, h0] using hM

section Seq

variable {K α p ε : ℝ} {Λ : Set (Fin n → ℤ)} {L : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}

/-- `ĝ_k = 0` for `k ∉ Λ ∩ Z_K`, `g = g_N` (a sum of the parts `P_Λ T_K f_j`). -/
theorem nf_coeff_g (H : NFHyp D r s K α L p ε Λ h f)
    (hinv : ∀ i ≤ N + 1, NFInv D r s K α p ε Λ h f N i) :
    ∀ I ∈ polyNbhd D (r / 2), ∀ k, k ∉ Λ ∩ zBall n K →
      coeff (nfG D r s K Λ h f N (N + 1)) I k = 0 := by
  have hs' : 0 < s / 6 := by have := H.hs; positivity
  have hr := nfR_half_le H.hr N
  have hs6 := nfS_sixth_le H.hs N
  have hj : ∀ j < N + 1, InClass D (r / 2) (s / 6) (nfF D r s K Λ h f N j) ∧
      WBound D (r / 2) (s / 6) (nfF D r s K Λ h f N j) (nfB (nfEps1 α p r s ε) ε j) := by
    intro j hj
    have hjr : nfR r N (N + 1) ≤ nfR r N j := nfR_anti H.hr.le N (by omega)
    have hjs : nfS s N (N + 1) ≤ nfS s N j := nfS_anti H.hs.le N (by omega)
    obtain ⟨c1, c2, -⟩ := hinv j (by omega)
    exact ⟨inClass_mono_nf c1 (by linarith) (by linarith),
      c2.mono (by linarith) (by linarith) le_rfl⟩
  have key := coeff_sum_eq_zero (D := D) (r := r / 2) (s := s / 6) hs' (Λ ∩ zBall n K)
    (fun j => homRes K Λ (nfF D r s K Λ h f N j)) (fun j => nfB (nfEps1 α p r s ε) ε j) (N + 1)
    (fun j hjN => by
      have hjr : nfR r N (N + 1) ≤ nfR r N j := nfR_anti H.hr.le N (by omega)
      have hjs : nfS s N (N + 1) ≤ nfS s N j := nfS_anti H.hs.le N (by omega)
      obtain ⟨c1, c2⟩ := (hinv (N + 1) le_rfl).2.2 j hjN
      exact ⟨inClass_mono_nf c1 (by linarith) (by linarith),
        c2.mono (by linarith) (by linarith) le_rfl⟩)
    (fun j hjN I hI k hk => by
      rw [coeff_homRes hs' (hj j hjN).1 (hj j hjN).2 I hI k]
      exact Set.indicator_of_notMem hk _)
  rw [nfG_eq_sum]
  exact key

end Seq

end Coeff

end KAM.NormalForm

end
