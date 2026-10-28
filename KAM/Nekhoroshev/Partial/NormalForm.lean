/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.NormalFormInduction
public import KAM.Nekhoroshev.Partial.Symplectic
public import KAM.Nekhoroshev.NormalForm.Telescope
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normal Form Lemma with slow parameters (`bpN:p11:nf`, Part 11, package N11-K2)

The signed theorem `KAM.Nekhoroshev.nf` (blueprint `bpN:p11:nf`,
`blueprint-N/parts/p11b-partial-nf.tex`), steps `nf-concl`, `nf-disp`, `nf-real`, and the Case
A / Case B assembly of the induction of `KAM.Nekhoroshev.Partial.NormalFormInduction` (N11-K1).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md` (package N11-K2).

* The Part 6 telescope (`bpN:p6:telescope`, `KAM.NormalForm.telescope`) is stated on
  `ℂⁿ × ℂⁿ` with `symplFormC`; it is generalized locally to the extended space `EC n k`, with
  the weighted canonical condition `ExtCanonical c` and arbitrary displacement functionals
  (`nnf_chain_*`). Only the composition `KAM.NormalForm.chain` itself is reused.
* Finite sums of class members (`nnf_sum_class`, `nnf_coeff_sum_zero`).
* The displacement sums (`nf-disp`): angles and fast actions from the Part 6 numerics, slow
  variables from `nnf_disp_T` (`∑ q Bᵢ/(ᾱσᵢ) ≤ (7/6) qKε/α`, so `∑ q Bᵢ/(16 k ᾱ σᵢ) ≤ qKε/(8α)`).
* `nnf_caseA`, `nnf_caseB` and the signed `nf`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-! ### The telescope on the extended space (`bpN:p6:telescope`, generalized) -/

section NnfChain

variable {U : ℕ → Set (EC n k)} {Φ : ℕ → EC n k → EC n k}

theorem nnf_chain_mapsTo {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i)) :
    MapsTo (KAM.NormalForm.chain Φ m) (U (m + 1)) (U 0) := by
  induction m with
  | zero => exact hmap 0 le_rfl
  | succ m ih =>
    exact (ih fun i hi => hmap i (hi.trans (Nat.le_succ _))).comp (hmap (m + 1) le_rfl)

theorem nnf_chain_diff {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hdiff : ∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U (i + 1))) :
    DifferentiableOn ℂ (KAM.NormalForm.chain Φ m) (U (m + 1)) := by
  induction m with
  | zero => exact hdiff 0 le_rfl
  | succ m ih =>
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hdiff i (hle i hi))
    exact h1.comp (hdiff (m + 1) le_rfl) (hmap (m + 1) le_rfl)

/-- The weighted canonical condition passes to compositions of holomorphic maps between open
sets (`symplectic_bracket` for the inner map, `ExtCanonical` of the outer one). -/
theorem nnf_chain_canon {c : ℝ} {m : ℕ} (hU : ∀ i, IsOpen (U i))
    (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hdiff : ∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U (i + 1)))
    (hcan : ∀ i ≤ m, ExtCanonical c (U (i + 1)) (Φ i)) :
    ExtCanonical c (U (m + 1)) (KAM.NormalForm.chain Φ m) := by
  induction m with
  | zero => exact hcan 0 le_rfl
  | succ m ih =>
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have hA := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hdiff i (hle i hi))
      (fun i hi => hcan i (hle i hi))
    have hdA : DifferentiableOn ℂ (KAM.NormalForm.chain Φ m) (U (m + 1)) :=
      nnf_chain_diff (fun i hi => hmap i (hle i hi)) (fun i hi => hdiff i (hle i hi))
    intro z hz u v
    have hu' : DifferentiableOn ℂ (fun y => u (KAM.NormalForm.chain Φ m y)) (U (m + 1)) :=
      u.differentiable.comp_differentiableOn hdA
    have hv' : DifferentiableOn ℂ (fun y => v (KAM.NormalForm.chain Φ m y)) (U (m + 1)) :=
      v.differentiable.comp_differentiableOn hdA
    have e1 := symplectic_bracket (hU (m + 1 + 1)) (hU (m + 1)) (hdiff (m + 1) le_rfl)
      (hmap (m + 1) le_rfl) (hcan (m + 1) le_rfl) hu' hv' z hz
    have e2 := hA (Φ (m + 1) z) (hmap (m + 1) le_rfl hz) u v
    exact e1.trans e2

theorem nnf_chain_inj {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hinj : ∀ i ≤ m, InjOn (Φ i) (U (i + 1))) :
    InjOn (KAM.NormalForm.chain Φ m) (U (m + 1)) := by
  induction m with
  | zero => exact hinj 0 le_rfl
  | succ m ih =>
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hinj i (hle i hi))
    exact h1.comp (hinj (m + 1) le_rfl) (hmap (m + 1) le_rfl)

/-- Integer angle translations commute with the composition. -/
theorem nnf_chain_translate {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (htr : ∀ i ≤ m, ∀ z ∈ U (i + 1), ∀ ℓ : Fin n → ℤ,
      Φ i (z.1 + (fun j => (ℓ j : ℂ)), z.2) = Φ i z + ((fun j => (ℓ j : ℂ)), 0)) :
    ∀ z ∈ U (m + 1), ∀ ℓ : Fin n → ℤ,
      KAM.NormalForm.chain Φ m (z.1 + (fun j => (ℓ j : ℂ)), z.2) =
        KAM.NormalForm.chain Φ m z + ((fun j => (ℓ j : ℂ)), 0) := by
  induction m with
  | zero => exact htr 0 le_rfl
  | succ m ih =>
    intro z hz ℓ
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => htr i (hle i hi))
    have hz' := hmap (m + 1) le_rfl hz
    show KAM.NormalForm.chain Φ m (Φ (m + 1) (z.1 + (fun j => (ℓ j : ℂ)), z.2)) =
      KAM.NormalForm.chain Φ m (Φ (m + 1) z) + ((fun j => (ℓ j : ℂ)), 0)
    rw [htr (m + 1) le_rfl z hz ℓ]
    have e : Φ (m + 1) z + ((fun j => (ℓ j : ℂ)), 0) =
        ((Φ (m + 1) z).1 + (fun j => (ℓ j : ℂ)), (Φ (m + 1) z).2) := by
      ext <;> simp
    rw [e]
    exact h1 (Φ (m + 1) z) hz' ℓ

/-- Real points go to real points along the composition. -/
theorem nnf_chain_real {m : ℕ} (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hreal : ∀ i ≤ m, ∀ z : ER n k, extCx z ∈ U (i + 1) →
      extCx (extRe (Φ i (extCx z))) = Φ i (extCx z)) :
    ∀ z : ER n k, extCx z ∈ U (m + 1) →
      extCx (extRe (KAM.NormalForm.chain Φ m (extCx z))) =
        KAM.NormalForm.chain Φ m (extCx z) := by
  induction m with
  | zero => exact hreal 0 le_rfl
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hreal i (hle i hi))
    have hw : extCx (extRe (Φ (m + 1) (extCx z))) = Φ (m + 1) (extCx z) :=
      hreal (m + 1) le_rfl z hz
    have hmem : extCx (extRe (Φ (m + 1) (extCx z))) ∈ U (m + 1) := by
      rw [hw]
      exact hmap (m + 1) le_rfl hz
    have h2 := h1 (extRe (Φ (m + 1) (extCx z))) hmem
    rw [hw] at h2
    exact h2

/-- The displacement of the composition, for any displacement functional `P`, is at most the
sum of the displacements of the factors (`bpN:p6:telescope`, the seminorms `|Π_θ ·|`, `|Π_I ·|`,
`|Π_x̃ ·|`). -/
theorem nnf_chain_disp {G : Type*} [SeminormedAddCommGroup G] (P : EC n k → G) {m : ℕ}
    (d : ℕ → ℝ) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hd : ∀ i ≤ m, ∀ z ∈ U (i + 1), ‖P (Φ i z) - P z‖ ≤ d i) :
    ∀ z ∈ U (m + 1),
      ‖P (KAM.NormalForm.chain Φ m z) - P z‖ ≤ ∑ i ∈ Finset.range (m + 1), d i := by
  induction m with
  | zero =>
    intro z hz
    simpa [KAM.NormalForm.chain] using hd 0 le_rfl z hz
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hmap i (hle i hi)) (fun i hi => hd i (hle i hi))
    have hz' : Φ (m + 1) z ∈ U (m + 1) := hmap (m + 1) le_rfl hz
    have h2 := h1 _ hz'
    have h3 := hd (m + 1) le_rfl z hz
    rw [Finset.sum_range_succ]
    show ‖P (KAM.NormalForm.chain Φ m (Φ (m + 1) z)) - P z‖ ≤ _
    calc ‖P (KAM.NormalForm.chain Φ m (Φ (m + 1) z)) - P z‖
        = ‖(P (KAM.NormalForm.chain Φ m (Φ (m + 1) z)) - P (Φ (m + 1) z)) +
            (P (Φ (m + 1) z) - P z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖P (KAM.NormalForm.chain Φ m (Φ (m + 1) z)) - P (Φ (m + 1) z)‖ +
            ‖P (Φ (m + 1) z) - P z‖ := norm_add_le _ _
      _ ≤ _ := add_le_add h2 h3

end NnfChain

/-! ### Finite sums of class members -/

section NnfSums

variable {D : Set (Fin (n + (k + k)) → ℂ)} {r s' : ℝ}

theorem nnf_coeff_zero_fn (I : Fin (n + (k + k)) → ℂ) (ι : Fin n → ℤ) :
    coeff (fun _ : EC n k => (0 : ℂ)) I ι = 0 := by
  simp [coeff, KAM.torusCoeffW, KAM.torusAverage]

theorem nnf_wbound_zero : WBound D r s' (fun _ : EC n k => (0 : ℂ)) 0 := by
  intro I _
  have h0 : ∀ ι : Fin n → ℤ, coeff (fun _ : EC n k => (0 : ℂ)) I ι = 0 :=
    fun ι => nnf_coeff_zero_fn I ι
  simp [WSummable, wsum, h0]

/-- A finite sum of class members with bounds `Mⱼ` is in the class with bound `∑ Mⱼ`. -/
theorem nnf_sum_class (hs : 0 < s') (u : ℕ → EC n k → ℂ) (M : ℕ → ℝ) (m : ℕ)
    (hu : ∀ j < m, InClass D r s' (u j) ∧ WBound D r s' (u j) (M j)) :
    InClass D r s' (fun z => ∑ j ∈ Finset.range m, u j z) ∧
      WBound D r s' (fun z => ∑ j ∈ Finset.range m, u j z) (∑ j ∈ Finset.range m, M j) := by
  induction m with
  | zero => exact ⟨⟨differentiableOn_const 0, fun _ _ _ => rfl⟩, by simpa using nnf_wbound_zero⟩
  | succ m ih =>
    have ih' := ih fun j hj => hu j (by omega)
    have hm := hu m (by omega)
    have e : (fun z => ∑ j ∈ Finset.range (m + 1), u j z) =
        fun z => (∑ j ∈ Finset.range m, u j z) + u m z := by
      funext z
      rw [Finset.sum_range_succ]
    rw [e, Finset.sum_range_succ]
    exact ⟨⟨ih'.1.differentiableOn.add hm.1.differentiableOn, fun j z hz => by
      simp only [ih'.1.periodic j z hz, hm.1.periodic j z hz]⟩,
      wbound_add_ext hs ih'.1 hm.1 ih'.2 hm.2⟩

/-- A finite sum of class members whose coefficients vanish off `S` has the same property. -/
theorem nnf_coeff_sum_zero (hs : 0 < s') (S : Set (Fin n → ℤ)) (u : ℕ → EC n k → ℂ)
    (M : ℕ → ℝ) (m : ℕ) (hu : ∀ j < m, InClass D r s' (u j) ∧ WBound D r s' (u j) (M j))
    (hz : ∀ j < m, ∀ I ∈ polyNbhd D r, ∀ ι, ι ∉ S → coeff (u j) I ι = 0) :
    ∀ I ∈ polyNbhd D r, ∀ ι, ι ∉ S → coeff (fun z => ∑ j ∈ Finset.range m, u j z) I ι = 0 := by
  induction m with
  | zero =>
    intro I _ ι _
    simpa using nnf_coeff_zero_fn (n := n) (k := k) I ι
  | succ m ih =>
    intro I hI ι hι
    have ih' := ih (fun j hj => hu j (by omega)) (fun j hj => hz j (by omega)) I hI ι hι
    have key := nnf_sum_class hs u M m (fun j hj => hu j (by omega))
    have e : (fun z => ∑ j ∈ Finset.range (m + 1), u j z) =
        fun z => (∑ j ∈ Finset.range m, u j z) + u m z := by
      funext z
      rw [Finset.sum_range_succ]
    rw [e, coeff_add_ext hs key.1 (hu m (by omega)).1 hI, ih', hz m (by omega) I hI ι hι,
      add_zero]

end NnfSums

/-! ### Displacement numerics (`nf-disp`) -/

section NnfDisp

/-- `∑ᵢ q Bᵢ/(ᾱ σᵢ) ≤ (7/6) qKε/α` (the sharper form of Part 6 `disp_I`, without `e`). -/
theorem nnf_disp_T {α p K s ε ε₁ : ℝ} {N : ℕ} (hp : 1 < p) (hα : 0 < α) (hK : 0 < K)
    (hs : 0 < s) (hε0 : 0 ≤ ε) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / 4)
    (hii : 6 ≤ 2 * Real.pi * K * s) (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1), conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfSig s N i) ≤
      7 / 6 * (K * conjExp p * ε / α) := by
  have hq := KAM.NormalForm.conjExp_pos' hp
  have hπ := Real.pi_pos
  have hY : 0 ≤ K * conjExp p * ε / α := by positivity
  have hT0 : conjExp p * nfB ε₁ ε 0 / (2 * Real.pi * α * nfSig s N 0) ≤
      K * conjExp p * ε / α := by
    have e0 : nfSig s N 0 = s / 6 := by simp [nfSig]
    rw [e0]
    show conjExp p * ε / (2 * Real.pi * α * (s / 6)) ≤ K * conjExp p * ε / α
    rw [div_le_div_iff₀ (by positivity) hα]
    have hA : 0 ≤ conjExp p * ε * α := by positivity
    linarith [mul_le_mul_of_nonneg_left hii hA]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [zero_add, Finset.sum_range_one]
    linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ']
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = conjExp p * ε₁ / (2 * Real.pi * α * (s / (4 * N))) :=
      ⟨_, rfl⟩
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    have hterm : ∀ j ∈ Finset.range N,
        conjExp p * nfB ε₁ ε (j + 1) / (2 * Real.pi * α * nfSig s N (j + 1)) =
          C * (1 / 4 ^ j) := by
      intro j _
      rw [nfSig_ne_zero (by omega : j + 1 ≠ 0), hC]
      show conjExp p * (ε₁ / 4 ^ j) / (2 * Real.pi * α * (s / (4 * N))) =
        conjExp p * ε₁ / (2 * Real.pi * α * (s / (4 * N))) * (1 / 4 ^ j)
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum := mul_le_mul_of_nonneg_left (KAM.NormalForm.sum_inv4_le N) hC0
    have hC1 : C * (4 / 3) ≤ (K * conjExp p * ε / α) / 6 := by
      have e : C = 4 * N * conjExp p * ε₁ / (2 * Real.pi * α * s) := by
        rw [hC, show 2 * Real.pi * α * (s / (4 * (N : ℝ))) = 2 * Real.pi * α * s / (4 * N) by
          ring, div_div_eq_mul_div]
        ring
      have h1 : C ≤ N * conjExp p * ε / (2 * Real.pi * α * s) := by
        rw [e]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ 4 * (N : ℝ) * conjExp p)
        linarith
      have h2 : N * conjExp p * ε / (2 * Real.pi * α * s) ≤ K * conjExp p * ε / (8 * α) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hA : 0 ≤ conjExp p * ε * α := by positivity
        linarith [mul_le_mul_of_nonneg_left h8 hA]
      have e3 : K * conjExp p * ε / (8 * α) = (K * conjExp p * ε / α) / 8 := by ring
      rw [e3] at h2
      linarith
    linarith

/-- `nf-disp`, slow variables, Case A: `∑ᵢ q Bᵢ/(16 k ᾱ σᵢ) ≤ (7/96) qKε/α ≤ qKε/(8α)`. -/
theorem nnf_disp_slow {α p K s ε ε₁ κk : ℝ} {N : ℕ} (hκk : 1 ≤ κk) (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hs : 0 < s) (hε0 : 0 ≤ ε) (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / 4)
    (hii : 6 ≤ 2 * Real.pi * K * s) (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (16 * κk * 2 * Real.pi * α * nfSig s N i) ≤
      conjExp p * K * ε / (8 * α) := by
  have hq := KAM.NormalForm.conjExp_pos' hp
  have hπ := Real.pi_pos
  have hT := nnf_disp_T hp hα hK hs hε0 hε₁0 hε₁ hii h8
  have hle : ∀ i ∈ Finset.range (N + 1),
      conjExp p * nfB ε₁ ε i / (16 * κk * 2 * Real.pi * α * nfSig s N i) ≤
        1 / 16 * (conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfSig s N i)) := by
    intro i hi
    have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
    have hσ : 0 < nfSig s N i := nfSig_pos hs hiN
    have hB : 0 ≤ nfB ε₁ ε i := nnf_B_nonneg hε₁0 hε0 i
    have e : 1 / 16 * (conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfSig s N i)) =
        conjExp p * nfB ε₁ ε i / (16 * 1 * 2 * Real.pi * α * nfSig s N i) := by ring
    rw [e]
    have hb : 16 * 1 * 2 * Real.pi * α * nfSig s N i ≤ 16 * κk * 2 * Real.pi * α * nfSig s N i := by
      have h0 : 0 ≤ 16 * 2 * Real.pi * α * nfSig s N i := by positivity
      have := mul_le_mul_of_nonneg_left hκk h0
      linarith
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hb
  have hY : 0 ≤ K * conjExp p * ε / α := by positivity
  calc ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (16 * κk * 2 * Real.pi * α * nfSig s N i)
      ≤ ∑ i ∈ Finset.range (N + 1),
          1 / 16 * (conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfSig s N i)) :=
        Finset.sum_le_sum hle
    _ = 1 / 16 * ∑ i ∈ Finset.range (N + 1),
          conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfSig s N i) := by
        rw [Finset.mul_sum]
    _ ≤ 1 / 16 * (7 / 6 * (K * conjExp p * ε / α)) :=
        mul_le_mul_of_nonneg_left hT (by norm_num)
    _ ≤ conjExp p * K * ε / (8 * α) := by
        have e : conjExp p * K * ε / (8 * α) = 1 / 8 * (K * conjExp p * ε / α) := by ring
        rw [e]
        linarith

/-- `nf-disp`, slow variables, Case B: `q ε/(16 k ᾱ (s/3)) ≤ qKε/(8α)`. -/
theorem nnf_disp_slow_B {α p K s ε κk : ℝ} (hκk : 1 ≤ κk) (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hs : 0 < s) (hε0 : 0 ≤ ε) (hii : 6 ≤ 2 * Real.pi * K * s) :
    conjExp p * ε / (16 * κk * 2 * Real.pi * α * (s / 3)) ≤ conjExp p * K * ε / (8 * α) := by
  have hq := KAM.NormalForm.conjExp_pos' hp
  have hπ := Real.pi_pos
  have hκk0 : 0 < κk := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : 0 ≤ conjExp p * ε * α := by positivity
  have h1 := mul_le_mul_of_nonneg_left hii hA
  have h2 : 0 ≤ conjExp p * ε * α * (2 * Real.pi * K * s) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hκk h2
  linarith

end NnfDisp

/-! ### The assembly -/

section NnfAssembly

variable {b : PartialBlock n k} {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} {N : ℕ}

/-- `nf-concl`: `H ∘ Ψₘ = h + g_m + f_{m+1}` for `Ψₘ = Φ₀ ∘ ⋯ ∘ Φₘ` (`H_{i+1} = H_i ∘ Φ_i`),
exact at every point. -/
theorem nnf_chain_identity (m : ℕ) : ∀ z : EC n k,
    liftFast h (KAM.NormalForm.chain (nnfPhi b s K Λ h f N) m z) +
        f (KAM.NormalForm.chain (nnfPhi b s K Λ h f N) m z) =
      liftFast h z + nnfG b s K Λ h f N (m + 1) z + nnfF b s K Λ h f N (m + 1) z := by
  induction m with
  | zero =>
    intro z
    have e : liftFast h (nnfPhi b s K Λ h f N 0 z) + 0 + f (nnfPhi b s K Λ h f N 0 z) =
        liftFast h z + nnfG b s K Λ h f N (0 + 1) z + nnfF b s K Λ h f N (0 + 1) z :=
      nnf_step_identity 0 z
    rw [add_zero] at e
    exact e
  | succ m ih =>
    intro z
    show liftFast h (KAM.NormalForm.chain (nnfPhi b s K Λ h f N) m
          (nnfPhi b s K Λ h f N (m + 1) z)) +
        f (KAM.NormalForm.chain (nnfPhi b s K Λ h f N) m (nnfPhi b s K Λ h f N (m + 1) z)) =
      liftFast h z + nnfG b s K Λ h f N (m + 1 + 1) z + nnfF b s K Λ h f N (m + 1 + 1) z
    rw [ih]
    exact nnf_step_identity (m + 1) z

/-- The parts `P_Λ T_K f_j` (`j ≤ N`) on the final domain `𝒟_{R/2,s/6}`: class, bound `Bⱼ`,
coefficients supported in `Λ ∩ Z_K`. -/
theorem nnf_parts (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hinv : NnfInv b s K α p ε Λ h f N (N + 1)) {j : ℕ} (hj : j ≤ N) :
    InClass b.base (b.rB / 2) (s / 6) (nnfPart b s K Λ h f N j) ∧
      WBound b.base (b.rB / 2) (s / 6) (nnfPart b s K Λ h f N j)
        (nfB (nfEps1 α p b.rB s ε) ε j) ∧
      ∀ I ∈ polyNbhd b.base (b.rB / 2), ∀ ι : Fin n → ℤ, ι ∉ Λ ∩ zBall n K →
        coeff (nnfPart b s K Λ h f N j) I ι = 0 := by
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hR : b.rB / 2 ≤ nfR b.rB N j :=
    (nfR_half_le hr N).trans (nfR_anti hr.le N (by omega))
  have hS : s / 6 ≤ nfS s N j := (nfS_sixth_le hs N).trans (nfS_anti hs.le N (by omega))
  have hSj : 0 < nfS s N j := lt_of_lt_of_le (by positivity) hS
  obtain ⟨c1, c2⟩ := hinv.1 j (by omega)
  obtain ⟨p1, p2, p3⟩ := nnf_proj (Λ := Λ) (K := K) hSj c1 c2
  exact ⟨nnf_inClass_mono p1 hR hS, p2.mono hR hS le_rfl,
    fun I hI ι hι => p3 I (polyNbhd_mono hR hI) ι hι⟩

end NnfAssembly

/-- The conclusion of `bpN:p11:nf` (the statement of the signed `nf` after its hypotheses). -/
def NnfConcl (b : PartialBlock n k) (s K α p ε : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) : Prop :=
  ∃ Ψ : EC n k → EC n k, ∃ g fs : EC n k → ℂ,
    DifferentiableOn ℂ Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
    MapsTo Ψ (Dom n b.base (b.rB/2) (s/6)) (Dom n b.base b.rB s) ∧
    Set.InjOn Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
    ExtCanonical b.c (Dom n b.base (b.rB/2) (s/6)) Ψ ∧
    (∀ z ∈ Dom n b.base (b.rB/2) (s/6), ∀ ℓ : Fin n → ℤ,
      Ψ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Ψ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z : ER n k, extCx z ∈ Dom n b.base (b.rB/2) (s/6) →
      extCx (extRe (Ψ (extCx z))) = Ψ (extCx z)) ∧
    ext_class b (b.rB/2) (s/6) g ∧ ext_class b (b.rB/2) (s/6) fs ∧
    (∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
      j ∉ Λ ∩ zBall n K → coeff g J j = 0) ∧
    (∀ z ∈ Dom n b.base (b.rB/2) (s/6), liftFast h (Ψ z)+f (Ψ z) = liftFast h z+g z+fs z) ∧
    WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f))
      (16*(2*conjExp p*K/(α*b.rB))*ε^2) ∧
    WBound b.base (b.rB/2) (s/6) fs (Real.exp (-(2*Real.pi*K*s)/6)*ε) ∧
    (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
      ‖fastAction (Ψ z)-fastAction z‖ ≤ conjExp p*K*ε/α ∧
      ‖(Ψ z).1-z.1‖ ≤ 10*conjExp p*ε/(2*Real.pi*α*b.rB) ∧
      ‖slowPair (Ψ z)-slowPair z‖ ≤ conjExp p*K*ε/(8*α))

section NnfCases

variable {b : PartialBlock n k} {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}

/-- `bpN:p11:nf` in Case A (`e^{-κ/6} ≤ u`, any `N ≥ 0`): `Ψ = Φ₀ ∘ ⋯ ∘ Φ_N`, `g = g_N`,
`f_* = f_{N+1}` (`nf-N`, `nf-induct`, `nf-concl`, `nf-disp`, `nf-real`). -/
theorem nnf_caseA (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (b.rB / 8) (s / 6)) :
    NnfConcl b s K α p ε Λ h f := by
  unfold NnfConcl
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊ := ⟨_, rfl⟩
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hK := ha.K_pos
  have hα := ha.alpha_pos
  have hε0 := ha.eps_pos.le
  have hq := KAM.NormalForm.conjExp_pos' ha.p_gt
  have hs6 : (0 : ℝ) < s / 6 := by positivity
  have hinv := nnf_inv_all ha hsm hN hA
  have props := fun i (hi : i ≤ N) => nnf_step_props ha hsm hN hi (hinv i (by omega))
  have hmap : ∀ i ≤ N, MapsTo (nnfPhi b s K Λ h f N i) (nnfU b s N (i + 1)) (nnfU b s N i) :=
    fun i hi => (props i hi).2.1
  have hU : ∀ i, IsOpen (nnfU b s N i) := fun i => isOpen_Dom _ _ _
  have hsub : Dom n b.base (b.rB / 2) (s / 6) ⊆ nnfU b s N (N + 1) :=
    Dom_mono (nfR_half_le hr N) (nfS_sixth_le hs N)
  have hdiff := nnf_chain_diff hmap fun i hi => (props i hi).1
  have hcan := nnf_chain_canon hU hmap (fun i hi => (props i hi).1)
    fun i hi => (props i hi).2.2.2.1
  have hinj := nnf_chain_inj hmap fun i hi => (props i hi).2.2.2.2.1
  have htr := nnf_chain_translate hmap fun i hi => (props i hi).2.2.1
  have hre := nnf_chain_real hmap fun i hi => (props i hi).2.2.2.2.2.2
  have hmc := nnf_chain_mapsTo hmap
  have hfl := nnf_floor ha hN
  have hε₁0 := nfEps1_nonneg ha.p_gt hα hr hs (ε := ε)
  have hε₁q := eps1_le_quarter ha.p_gt hα hK hr hs hε0 (nnf_hi hsm) ha.cutoff
  have hdθ := nnf_chain_disp Prod.fst
    (fun i => conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (2*Real.pi*α*nfRho b.rB N i)) hmap
    fun i hi z hz => ((props i hi).2.2.2.2.2.1 z hz).1
  have hdI := nnf_chain_disp fastAction
    (fun i => conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (Real.exp 1*2*Real.pi*α*nfSig s N i))
    hmap fun i hi z hz => ((props i hi).2.2.2.2.2.1 z hz).2.1
  have hdx := nnf_chain_disp slowPair
    (fun i => conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (16*k*2*Real.pi*α*nfSig s N i))
    hmap fun i hi z hz => ((props i hi).2.2.2.2.2.1 z hz).2.2
  have hfin := (hinv (N + 1) le_rfl).1 (N + 1) le_rfl
  refine ⟨KAM.NormalForm.chain (nnfPhi b s K Λ h f N) N, nnfG b s K Λ h f N (N + 1),
    nnfF b s K Λ h f N (N + 1), hdiff.mono hsub, fun z hz => hmc (hsub hz), hinj.mono hsub,
    fun z hz => hcan z (hsub hz), fun z hz ℓ => htr z (hsub hz) ℓ,
    fun z hz => hre z (hsub hz), ⟨?_, fun x hx => (hinv (N + 1) le_rfl).2.2 x (hsub hx)⟩,
    ⟨nnf_inClass_mono hfin.1 (nfR_half_le hr N) (nfS_sixth_le hs N),
      fun x hx => (hinv (N + 1) le_rfl).2.1 x (hsub hx)⟩,
    ?_, fun z _ => nnf_chain_identity N z, ?_,
    hfin.2.mono (nfR_half_le hr N) (nfS_sixth_le hs N) (final_b hε0 hε₁q hfl.2.1), ?_⟩
  · -- `g = g_N` is in the class: a finite sum of the parts
    rw [nnfG_eq_sum]
    exact (nnf_sum_class hs6 (nnfPart b s K Λ h f N) (fun j => nfB (nfEps1 α p b.rB s ε) ε j)
      (N + 1) fun j hj => ⟨(nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j ≤ N)).1,
        (nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j ≤ N)).2.1⟩).1
  · -- `ĝ_ι = 0` for `ι ∉ Λ ∩ Z_K`
    intro J hJ ι hι
    rw [nnfG_eq_sum]
    exact nnf_coeff_sum_zero hs6 (Λ ∩ zBall n K) (nnfPart b s K Λ h f N)
      (fun j => nfB (nfEps1 α p b.rB s ε) ε j) (N + 1)
      (fun j hj => ⟨(nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j ≤ N)).1,
        (nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j ≤ N)).2.1⟩)
      (fun j hj => (nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j ≤ N)).2.2) J hJ ι hι
  · -- (a): `g - g₀ = ∑_{1 ≤ j ≤ N} P_Λ T_K f_j`, `|g - g₀| ≤ (4/3) ε₁ ≤ 16 c₁ ε²`
    have e : nnfG b s K Λ h f N (N + 1) - projMode Λ (truncate K f) =
        fun z => ∑ j ∈ Finset.range N, nnfPart b s K Λ h f N (j + 1) z := by
      funext z
      rw [nnfG_eq_sum]
      show ∑ j ∈ Finset.range (N + 1), nnfPart b s K Λ h f N j z - projMode Λ (truncate K f) z =
        ∑ j ∈ Finset.range N, nnfPart b s K Λ h f N (j + 1) z
      rw [Finset.sum_range_succ' (fun j => nnfPart b s K Λ h f N j z) N]
      show ∑ j ∈ Finset.range N, nnfPart b s K Λ h f N (j + 1) z +
          projMode Λ (truncate K f) z - projMode Λ (truncate K f) z =
        ∑ j ∈ Finset.range N, nnfPart b s K Λ h f N (j + 1) z
      ring
    rw [e]
    have key := nnf_sum_class hs6 (fun j => nnfPart b s K Λ h f N (j + 1))
      (fun j => nfB (nfEps1 α p b.rB s ε) ε (j + 1)) N fun j hj =>
        ⟨(nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j + 1 ≤ N)).1,
          (nnf_parts ha (hinv (N + 1) le_rfl) (by omega : j + 1 ≤ N)).2.1⟩
    refine key.2.mono le_rfl le_rfl ?_
    have hsum : ∑ j ∈ Finset.range N, nfB (nfEps1 α p b.rB s ε) ε (j + 1) ≤
        4 / 3 * nfEps1 α p b.rB s ε := by
      have e2 : ∑ j ∈ Finset.range N, nfB (nfEps1 α p b.rB s ε) ε (j + 1) =
          nfEps1 α p b.rB s ε * ∑ j ∈ Finset.range N, (1 : ℝ) / 4 ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by simp only [nfB]; ring
      rw [e2]
      have := mul_le_mul_of_nonneg_left (KAM.NormalForm.sum_inv4_le N) hε₁0
      linarith
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · subst hN0
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine hsum.trans (concl_a ha.p_gt hα hK hr hs ?_)
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith [hfl.2.2]
  · -- (c): the displacement (`nf-disp`, telescope with `Π_I`, `Π_θ`, `Π_x̃`)
    intro z hz
    have hz' := hsub hz
    refine ⟨(hdI z hz').trans ?_, (hdθ z hz').trans ?_, (hdx z hz').trans ?_⟩
    · calc ∑ i ∈ Finset.range (N + 1),
            conjExp p * nfB (nfEps1 α p b.rB s ε) ε i / (Real.exp 1*2*Real.pi*α*nfSig s N i)
          = ∑ i ∈ Finset.range (N + 1), conjExp p * nfB (nfEps1 α p b.rB s ε) ε i /
              (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ ≤ conjExp p * K * ε / α :=
            disp_I ha.p_gt hα hK hs hε0 hε₁0 hε₁q ha.cutoff hfl.2.2
    · exact disp_theta ha.p_gt hα hK hr hs hε0 hε₁0
        (eps1_le_div ha.p_gt hα hK hr hs hε0 (nnf_hi hsm)) ha.cutoff hfl.2.2
    · exact nnf_disp_slow (by exact_mod_cast ha.k_pos) ha.p_gt hα hK hs hε0 hε₁0 hε₁q ha.cutoff
        hfl.2.2

/-- `bpN:p11:nf` in Case B (`u < e^{-κ/6}`): one step with the losses `(R/4, s/3)`,
`Ψ = Φ₀'`, `g = g₀ = P_Λ T_K f`, `f_* = f₁` (`nf-case`, `nf-disp`, `nf-real`). -/
theorem nnf_caseB (ha : ExtNFHyp b s K α L p ε Λ h f) (hsm : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (hB : iterU α p ε (b.rB / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) :
    NnfConcl b s K α p ε Λ h f := by
  unfold NnfConcl
  have hr := ha.radius_pos
  have hs := ha.s_pos
  have hK := ha.K_pos
  have hα := ha.alpha_pos
  have hε0 := ha.eps_pos.le
  have hq := KAM.NormalForm.conjExp_pos' ha.p_gt
  have st := nnf_caseB_step ha hsm
  have hsub : Dom n b.base (b.rB / 2) (s / 6) ⊆
      Dom n b.base (b.rB - 2 * (b.rB / 4)) (s - 2 * (s / 3)) :=
    Dom_mono (by linarith) (by linarith)
  obtain ⟨p1, -, p3⟩ := nnf_proj (Λ := Λ) (K := K) hs ha.pert.1 ha.bound
  refine ⟨nnfMap b b.rB s (b.rB / 4) (s / 3) K Λ h f, projMode Λ (truncate K f),
    nnfFp b b.rB s (b.rB / 4) (s / 3) K Λ h (fun _ => 0) f, st.nnf_diff.mono hsub,
    fun z hz => st.nnf_maps (hsub hz), st.nnf_inj.mono hsub, fun z hz => st.nnf_canon z (hsub hz),
    fun z hz ℓ => st.nnf_transl z (hsub hz) ℓ, fun z hz => st.nnf_real z (hsub hz),
    ⟨nnf_inClass_mono p1 (by linarith) (by linarith),
      nnf_extReal_congr (u := nnfGp K Λ (fun _ => (0 : ℂ)) f) (fun z _ => zero_add _)
        fun x hx => st.nnf_gp_real x (hsub hx)⟩,
    ⟨nnf_inClass_mono st.nnf_fp_class (by linarith) (by linarith),
      fun x hx => st.nnf_fp_real x (hsub hx)⟩,
    fun J hJ ι hι => p3 J (polyNbhd_mono (by linarith) hJ) ι hι, fun z _ => ?_, ?_, ?_, ?_⟩
  · -- the identity, with `g = 0`
    have e : liftFast h (nnfMap b b.rB s (b.rB / 4) (s / 3) K Λ h f z) + 0 +
        f (nnfMap b b.rB s (b.rB / 4) (s / 3) K Λ h f z) =
        liftFast h z + (0 + projMode Λ (truncate K f) z) +
          nnfFp b b.rB s (b.rB / 4) (s / 3) K Λ h (fun _ => 0) f z :=
      nnfFp_identity b b.rB s (b.rB / 4) (s / 3) K Λ h (fun _ => 0) f z
    rw [add_zero, zero_add] at e
    exact e
  · -- (a): `g = g₀`
    have e : projMode Λ (truncate K f) - projMode Λ (truncate K f) =
        fun _ : EC n k => (0 : ℂ) :=
      funext fun z => by simp
    rw [e]
    exact nnf_wbound_zero.mono le_rfl le_rfl (by positivity)
  · -- (b): `|f₁|_{R/2,s/3} ≤ e^{-κ/6} ε`
    have hb := st.nnf_fp_bound
    have e0 : starNorm b.rB s (b.rB / 4) (s / 3) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) = 0 := by
      simp [starNorm]
    rw [e0] at hb
    exact hb.mono (by linarith) (by linarith)
      (nnfBound_caseB ha.p_gt hα hK hr hs hε0 (nnf_hi hsm) ha.cutoff hB)
  · -- (c): the displacement of the single step
    intro z hz
    obtain ⟨d1, d2, d3⟩ := st.nnf_disp z (hsub hz)
    obtain ⟨c1, c2⟩ := disp_B ha.p_gt hα hK hr hs hε0 ha.cutoff
    have e : Real.exp 1*2*Real.pi*α*(s/3) = Real.exp 1 * (2 * Real.pi * α) * (s / 3) := by ring
    rw [e] at d2
    exact ⟨d2.trans c1, d1.trans c2, d3.trans (nnf_disp_slow_B (by exact_mod_cast ha.k_pos)
      ha.p_gt hα hK hs hε0 ha.cutoff)⟩

end NnfCases

/-- **Normal Form Lemma with slow parameters** (`bpN:p11:nf`). Signed statement (copied from
the N11 signature file). -/
theorem nf (b : PartialBlock n k) {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    ∃ Ψ : EC n k → EC n k, ∃ g fs : EC n k → ℂ,
      DifferentiableOn ℂ Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      MapsTo Ψ (Dom n b.base (b.rB/2) (s/6)) (Dom n b.base b.rB s) ∧
      Set.InjOn Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      ExtCanonical b.c (Dom n b.base (b.rB/2) (s/6)) Ψ ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), ∀ ℓ : Fin n → ℤ,
        Ψ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Ψ z+((fun i => (ℓ i:ℂ)),0)) ∧
      (∀ z : ER n k, extCx z ∈ Dom n b.base (b.rB/2) (s/6) →
        extCx (extRe (Ψ (extCx z))) = Ψ (extCx z)) ∧
      ext_class b (b.rB/2) (s/6) g ∧ ext_class b (b.rB/2) (s/6) fs ∧
      (∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
        j ∉ Λ ∩ zBall n K → coeff g J j = 0) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
        liftFast h (Ψ z)+f (Ψ z) = liftFast h z+g z+fs z) ∧
      WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f))
        (16*(2*conjExp p*K/(α*b.rB))*ε^2) ∧
      WBound b.base (b.rB/2) (s/6) fs (Real.exp (-(2*Real.pi*K*s)/6)*ε) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
        ‖fastAction (Ψ z)-fastAction z‖ ≤ conjExp p*K*ε/α ∧
        ‖(Ψ z).1-z.1‖ ≤ 10*conjExp p*ε/(2*Real.pi*α*b.rB) ∧
        ‖slowPair (Ψ z)-slowPair z‖ ≤ conjExp p*K*ε/(8*α)) := by
  by_cases hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (b.rB / 8) (s / 6)
  · exact nnf_caseA ha hsmall hA
  · exact nnf_caseB ha hsmall (not_le.1 hA)

end KAM.Nekhoroshev

end
