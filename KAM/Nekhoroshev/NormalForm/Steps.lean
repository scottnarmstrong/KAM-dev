/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.StepsInduct
public import KAM.Nekhoroshev.NormalForm.Telescope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: what the step sequence exposes to `NormalForm`

For `i ≤ N` (given `NFInv i`): the properties of the `i`-th map on `Uᵢ₊₁ = Dom rᵢ₊₁ sᵢ₊₁` (`nf_step_props`),
the identity `(h + f) ∘ Ψₘ = h + g_m + f_{m+1}` on `Uₘ₊₁` (`nf_chain_identity`), the sums of the
displacement bounds (`nf_disp_sums`), the final-state facts in Case A (`nf_final_f`, `nf_final_g`,
`nf_final_g_diff`), reality (`nf_real`, `nf_phi_real`) and Case B (`nfCaseB_*`). Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 1).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section Out

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}

/-- The properties of the `i`-th step on `Uᵢ₊₁ = Dom rᵢ₊₁ sᵢ₊₁` (Theorem `bpN:p6:iterative` (a), (b),
(c) transported to the schedule). -/
theorem nf_step_props (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N)
    (hinv : NFInv D r s K α p ε Λ h f N i) :
    DifferentiableOn ℂ (nfPhi D r s K Λ h f N i) (Dom n D (nfR r N (i + 1)) (nfS s N (i + 1))) ∧
    MapsTo (nfPhi D r s K Λ h f N i) (Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)))
      (Dom n D (nfR r N i) (nfS s N i)) ∧
    (∀ z ∈ Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)), ∀ v w,
      symplFormC (fderiv ℂ (nfPhi D r s K Λ h f N i) z v)
        (fderiv ℂ (nfPhi D r s K Λ h f N i) z w) = symplFormC v w) ∧
    (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)),
      nfPhi D r s K Λ h f N i (z.1 + (fun j => (k j : ℂ)), z.2) =
        nfPhi D r s K Λ h f N i z + ((fun j => (k j : ℂ)), 0)) ∧
    InjOn (nfPhi D r s K Λ h f N i) (Dom n D (nfR r N (i + 1)) (nfS s N (i + 1))) ∧
    (∀ z ∈ Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)),
      ‖(nfPhi D r s K Λ h f N i z).1 - z.1‖ ≤
        conjExp p * nfB (nfEps1 α p r s ε) ε i / (2 * Real.pi * α * nfRho r N i) ∧
      ‖(nfPhi D r s K Λ h f N i z).2 - z.2‖ ≤
        conjExp p * nfB (nfEps1 α p r s ε) ε i /
          (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i)) ∧
    (∀ z ∈ Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)),
      (fun w => h w.2 + nfG D r s K Λ h f N i w + nfF D r s K Λ h f N i w)
          (nfPhi D r s K Λ h f N i z) =
        h z.2 + nfG D r s K Λ h f N (i + 1) z + nfF D r s K Λ h f N (i + 1) z) := by
  have IH := nf_hyp H hN hi hinv
  have hρ := nfRho_pos H.hr hi
  have hσ := nfSig_pos H.hs hi
  have hsub : Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)) ⊆
      Dom n D (nfR r N i - 3 * nfRho r N i / 2) (nfS s N i - 3 * nfSig s N i / 2) :=
    Dom_mono (by show nfR r N i - 2 * nfRho r N i ≤ _; linarith)
      (by show nfS s N i - 2 * nfSig s N i ≤ _; linarith)
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := iterative_direct_a IH
  obtain ⟨b1, -⟩ := iterative_direct_b IH
  obtain ⟨c1, -⟩ := iterative_direct_c IH
  refine ⟨a1.mono hsub, fun z hz => ?_, fun z hz => a3 z (hsub hz),
    fun k z hz => a4 k z (hsub hz), a5, fun z hz => ?_, fun z hz => ?_⟩
  · have := a2 (hsub hz)
    exact Dom_mono (by linarith) (by linarith) this
  · exact (fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩) (b1 z (hsub hz))
  · exact c1 z hz

/-- `(h + f) ∘ Ψₘ = h + g_m + f_{m+1}` on `Uₘ₊₁` for `Ψₘ = Φ₀ ∘ ⋯ ∘ Φₘ` (`nf-concl`, `H ∘ Ψ = H_{N+1}`). -/
theorem nf_chain_identity (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hinv : ∀ i ≤ N, NFInv D r s K α p ε Λ h f N i) :
    ∀ m ≤ N, ∀ z ∈ Dom n D (nfR r N (m + 1)) (nfS s N (m + 1)),
      (fun w => h w.2 + f w) (chain (nfPhi D r s K Λ h f N) m z) =
        h z.2 + nfG D r s K Λ h f N (m + 1) z + nfF D r s K Λ h f N (m + 1) z := by
  intro m
  induction m with
  | zero =>
    intro hm z hz
    have := (nf_step_props H hN hm (hinv 0 hm)).2.2.2.2.2.2 z hz
    simpa [chain, nfG_zero, nfF_zero] using this
  | succ m ih =>
    intro hm z hz
    have hmN : m ≤ N := by omega
    have props := nf_step_props H hN hm (hinv (m + 1) hm)
    have hw : nfPhi D r s K Λ h f N (m + 1) z ∈ Dom n D (nfR r N (m + 1)) (nfS s N (m + 1)) :=
      props.2.1 hz
    show (fun w => h w.2 + f w) (chain (nfPhi D r s K Λ h f N) m
      (nfPhi D r s K Λ h f N (m + 1) z)) = _
    rw [ih hmN _ hw]
    exact props.2.2.2.2.2.2 z hz

/-- The sums of the displacement bounds (`nf-disp`, Case A): `∑ᵢ q Bᵢ/(e ᾱ σᵢ) ≤ qKε/α` and
`∑ᵢ q Bᵢ/(ᾱ ρᵢ) ≤ 10 q ε/(ᾱ r)`. -/
theorem nf_disp_sums (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) :
    ∑ i ∈ Finset.range (N + 1), conjExp p * nfB (nfEps1 α p r s ε) ε i /
        (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i) ≤ conjExp p * K * ε / α ∧
    ∑ i ∈ Finset.range (N + 1), conjExp p * nfB (nfEps1 α p r s ε) ε i /
        (2 * Real.pi * α * nfRho r N i) ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r) := by
  have hfl := nf_floor H hN
  have h0 := nfEps1_nonneg H.hp H.hα H.hr H.hs (ε := ε)
  exact ⟨disp_I H.hp H.hα H.hK H.hs H.hε0 h0
      (eps1_le_quarter H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii) H.hii hfl.2.2,
    disp_theta H.hp H.hα H.hK H.hr H.hs H.hε0 h0
      (eps1_le_div H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi) H.hii hfl.2.2⟩

/-! ### The final state in Case A -/

/-- (b): `f_* = f_{N+1}` is in the class on `(r/2, s/6)` with `|f_*| ≤ e^{-κ/6} ε`. -/
theorem nf_final_f (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hinv : NFInv D r s K α p ε Λ h f N (N + 1)) :
    InClass D (r / 2) (s / 6) (nfF D r s K Λ h f N (N + 1)) ∧
      WBound D (r / 2) (s / 6) (nfF D r s K Λ h f N (N + 1))
        (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) := by
  have hfl := nf_floor H hN
  have hr := nfR_half_le H.hr N
  have hs := nfS_sixth_le H.hs N
  obtain ⟨c1, c2, -⟩ := hinv
  refine ⟨⟨c1.differentiableOn.mono (Dom_mono hr hs), fun j z hz =>
    c1.periodic j z (Dom_mono hr hs hz)⟩, ?_⟩
  refine c2.mono hr hs ?_
  exact final_b H.hε0 (eps1_le_quarter H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii) hfl.2.1

/-- `g_N = g₀` when `N = 0`. -/
theorem nf_final_g_zero (hN0 : N = 0) :
    nfG D r s K Λ h f N (N + 1) = homRes K Λ f := by
  subst hN0
  funext z
  show iterG K Λ (fun _ => 0) f z = _
  simp [iterG]

private theorem wbound_zero' {D : Set (Fin n → ℂ)} {r s : ℝ} :
    WBound D r s (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) 0 := by
  intro I _
  have h0 : ∀ k : Fin n → ℤ, coeff (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) I k = 0 :=
    fun k => by simp [coeff, KAM.torusCoeffW, KAM.torusAverage]
  simp [WSummable, wsum, h0]

private theorem inClass_mono'' {D : Set (Fin n → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) :
    InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

/-- A finite sum of members of the class with bounds `Mⱼ` is in the class with bound `∑ Mⱼ`. -/
theorem sum_inClass_wbound {D : Set (Fin n → ℂ)} {r' s' : ℝ} (hs' : 0 < s')
    (u : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (M : ℕ → ℝ) (m : ℕ)
    (hu : ∀ j < m, InClass D r' s' (u j) ∧ WBound D r' s' (u j) (M j)) :
    InClass D r' s' (fun z => ∑ j ∈ Finset.range m, u j z) ∧
      WBound D r' s' (fun z => ∑ j ∈ Finset.range m, u j z) (∑ j ∈ Finset.range m, M j) := by
  induction m with
  | zero => exact ⟨⟨differentiableOn_const 0, fun _ _ _ => rfl⟩, by simpa using wbound_zero'⟩
  | succ m ih =>
    have ih' := ih fun j hj => hu j (by omega)
    have hm := hu m (by omega)
    have e : (fun z => ∑ j ∈ Finset.range (m + 1), u j z) =
        fun z => (∑ j ∈ Finset.range m, u j z) + u m z := by
      funext z; rw [Finset.sum_range_succ]
    rw [e, Finset.sum_range_succ]
    exact ⟨⟨ih'.1.differentiableOn.add hm.1.differentiableOn, fun j z hz => by
      simp only [ih'.1.periodic j z hz, hm.1.periodic j z hz]⟩,
      wbound_add hs' ih'.1 hm.1 ih'.2 hm.2⟩

/-- `g = g_N ∈ O(r/2, s/6)`: a finite sum of the parts. -/
theorem nf_final_g (H : NFHyp D r s K α L p ε Λ h f)
    (hinv : NFInv D r s K α p ε Λ h f N (N + 1)) :
    InClass D (r / 2) (s / 6) (nfG D r s K Λ h f N (N + 1)) := by
  have hr := nfR_half_le H.hr N
  have hs := nfS_sixth_le H.hs N
  have key := sum_inClass_wbound (D := D) (r' := r / 2) (s' := s / 6) (by have := H.hs; positivity)
    (fun j => homRes K Λ (nfF D r s K Λ h f N j)) (fun j => nfB (nfEps1 α p r s ε) ε j) (N + 1)
    (fun j hj => by
      have hjr : nfR r N (N + 1) ≤ nfR r N j := nfR_anti H.hr.le N (by omega)
      have hjs : nfS s N (N + 1) ≤ nfS s N j := nfS_anti H.hs.le N (by omega)
      obtain ⟨c1, c2⟩ := hinv.2.2 j hj
      exact ⟨inClass_mono'' c1 (by linarith) (by linarith),
        c2.mono (by linarith) (by linarith) le_rfl⟩)
  rw [nfG_eq_sum]
  exact key.1

/-- (a): `|g - g₀|_{r/2, s/6} ≤ 16 c ε²` with `c = 2qK/(αr)`, `g = g_N`, `g₀ = P_Λ T_K f`. -/
theorem nf_final_g_diff (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hinv : NFInv D r s K α p ε Λ h f N (N + 1)) :
    WBound D (r / 2) (s / 6) (fun z => nfG D r s K Λ h f N (N + 1) z - homRes K Λ f z)
      (16 * (2 * conjExp p * K / (α * r)) * ε ^ 2) := by
  have hfl := nf_floor H hN
  have hr := nfR_half_le H.hr N
  have hs := nfS_sixth_le H.hs N
  have hq : 0 < conjExp p := by
    unfold conjExp; exact div_pos (by linarith [H.hp]) (by linarith [H.hp])
  have h0 := nfEps1_nonneg H.hp H.hα H.hr H.hs (ε := ε)
  have e : (fun z => nfG D r s K Λ h f N (N + 1) z - homRes K Λ f z) =
      fun z => ∑ j ∈ Finset.range N, homRes K Λ (nfF D r s K Λ h f N (j + 1)) z := by
    funext z
    rw [nfG_eq_sum]
    show ∑ j ∈ Finset.range (N + 1), homRes K Λ (nfF D r s K Λ h f N j) z - _ = _
    rw [Finset.sum_range_succ' (fun j => homRes K Λ (nfF D r s K Λ h f N j) z) N, nfF_zero]
    ring
  have key := sum_inClass_wbound (D := D) (r' := r / 2) (s' := s / 6) (by have := H.hs; positivity)
    (fun j => homRes K Λ (nfF D r s K Λ h f N (j + 1)))
    (fun j => nfB (nfEps1 α p r s ε) ε (j + 1)) N
    (fun j hj => by
      have hjr : nfR r N (N + 1) ≤ nfR r N (j + 1) := nfR_anti H.hr.le N (by omega)
      have hjs : nfS s N (N + 1) ≤ nfS s N (j + 1) := nfS_anti H.hs.le N (by omega)
      obtain ⟨c1, c2⟩ := hinv.2.2 (j + 1) (by omega)
      exact ⟨inClass_mono'' c1 (by linarith) (by linarith),
        c2.mono (by linarith) (by linarith) le_rfl⟩)
  rw [e]
  refine key.2.mono le_rfl le_rfl ?_
  have hsum : ∑ j ∈ Finset.range N, nfB (nfEps1 α p r s ε) ε (j + 1) ≤
      4 / 3 * nfEps1 α p r s ε := by
    have : ∑ j ∈ Finset.range N, nfB (nfEps1 α p r s ε) ε (j + 1) =
        nfEps1 α p r s ε * ∑ j ∈ Finset.range N, (1 : ℝ) / 4 ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [nfB]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left (sum_inv4_le N) h0
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    simp only [Finset.range_zero, Finset.sum_empty]
    have := H.hα
    have := H.hr
    have := H.hK
    positivity
  · exact hsum.trans (concl_a H.hp H.hα H.hK H.hr H.hs (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith [hfl.2.2]))

end Out

end KAM.NormalForm

end
