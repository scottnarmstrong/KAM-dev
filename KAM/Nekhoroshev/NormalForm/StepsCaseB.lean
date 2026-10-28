/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.StepsOut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: reality along the steps and Case B

Reality of `g_i`, `f_i` and of the maps (`nf-real`), and Case B of `nf-case`: the single step
with the doubled losses `(r/4, s/3)` (`nfCaseB_hyp`, `nfCaseB_bound`, `nfCaseB_disp`). Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 1).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

section Real

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}

theorem realOn_mono' {U V : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : RealOn U u) (hV : V ⊆ U) : RealOn V u :=
  fun x hx => hu x (hV hx)

/-- Reality of `g_{i-1}` and `f_i` on `Uᵢ` (`nf-real`). -/
theorem nf_real (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊)
    (hinv : ∀ i ≤ N, NFInv D r s K α p ε Λ h f N i) (hΛ : ∀ k ∈ Λ, -k ∈ Λ)
    (hhr : RealOn (Dom n D r s) (fun w => h w.2)) (hfr : RealOn (Dom n D r s) f) :
    ∀ i ≤ N + 1, RealOn (Dom n D (nfR r N i) (nfS s N i)) (nfG D r s K Λ h f N i) ∧
      RealOn (Dom n D (nfR r N i) (nfS s N i)) (nfF D r s K Λ h f N i) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨fun x _ => by simp [nfG_zero], hfr⟩
  | succ i ih =>
    intro hi
    obtain ⟨hg, hf'⟩ := ih (by omega)
    have IH := nf_hyp H hN (show i ≤ N by omega) (hinv i (by omega))
    have hρ := nfRho_pos H.hr (show i ≤ N by omega)
    have hσ := nfSig_pos H.hs (show i ≤ N by omega)
    have hRle : nfR r N i ≤ r := nfR_anti H.hr.le N (Nat.zero_le i)
    have hSle : nfS s N i ≤ s := nfS_anti H.hs.le N (Nat.zero_le i)
    have hh' : RealOn (Dom n D (nfR r N i) (nfS s N i)) (fun w => h w.2) :=
      realOn_mono' hhr (Dom_mono hRle hSle)
    obtain ⟨-, e2, e3, -⟩ := iterative_direct_e IH hΛ hh' hg hf'
    have hsub : Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)) ⊆
        Dom n D (nfR r N i) (nfS s N i) :=
      Dom_mono (by show nfR r N i - 2 * nfRho r N i ≤ _; linarith)
        (by show nfS s N i - 2 * nfSig s N i ≤ _; linarith)
    exact ⟨realOn_mono' e2 hsub, e3⟩

/-- The `i`-th map sends real points of `Uᵢ₊₁` to real points (`nf-real`). -/
theorem nf_phi_real (H : NFHyp D r s K α L p ε Λ h f)
    (hN : N = ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊) {i : ℕ} (hi : i ≤ N)
    (hinv : NFInv D r s K α p ε Λ h f N i) (hΛ : ∀ k ∈ Λ, -k ∈ Λ)
    (hhr : RealOn (Dom n D (nfR r N i) (nfS s N i)) (fun w => h w.2))
    (hg : RealOn (Dom n D (nfR r N i) (nfS s N i)) (nfG D r s K Λ h f N i))
    (hf' : RealOn (Dom n D (nfR r N i) (nfS s N i)) (nfF D r s K Λ h f N i)) :
    ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ Dom n D (nfR r N (i + 1)) (nfS s N (i + 1)) →
      nfPhi D r s K Λ h f N i (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) := by
  have IH := nf_hyp H hN hi hinv
  have hρ := nfRho_pos H.hr hi
  have hσ := nfSig_pos H.hs hi
  obtain ⟨-, -, -, e4⟩ := iterative_direct_e IH hΛ hhr hg hf'
  intro x hx
  exact e4 x (Dom_mono (by show nfR r N i - 2 * nfRho r N i ≤ _; linarith)
    (by show nfS s N i - 2 * nfSig s N i ≤ _; linarith) hx |> fun h => h)

end Real

/-! ### Case B -/

section CaseB

variable {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The empty decomposition of `g = 0`. -/
theorem isDecomp_zero {r s : ℝ} (gj : Fin 0 → (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (rj sj Mj : Fin 0 → ℝ) : IsDecomp D r s (fun _ => (0 : ℂ)) gj rj sj Mj where
  eq_sum := by funext z; simp
  r_le j := j.elim0
  s_le j := j.elim0
  inClass j := j.elim0
  bound j := j.elim0

/-- Case B: the step with losses `(r/4, s/3)`, `g = 0`, `δ = ε` is admissible. -/
theorem nfCaseB_hyp (H : NFHyp D r s K α L p ε Λ h f) :
    IterHyp D r s (r / 4) (s / 3) K α p ε Λ h (fun _ => (0 : ℂ)) f (N := 0)
      (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) := by
  have hr := H.hr
  have hs := H.hs
  have hu := iterU_first H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii
  have hu0 := iterU_nonneg H.hp H.hα (by positivity : 0 < r / 8) (by positivity : 0 < s / 6)
    H.hε0
  have hd := iterU_double (p := p) (ε := ε) H.hα H.hr H.hs
  refine iterHyp_of_source H.hp H.hα H.hK.le H.hL H.hs (by positivity) (by linarith)
    (by positivity) (by linarith) H.hh H.hnr H.hlip H.hrad (isDecomp_zero _ _ _ _) H.hf H.hfb
    H.hε0 ((small_iff_iterU H.hp H.hα (by positivity) (by positivity)).2 ?_)
  linarith

/-- Case B, (b): `|f₁|_{r/2, s/3} ≤ e^{-κ/6} ε`, restricted to `(r/2, s/6)`. -/
theorem nfCaseB_bound (H : NFHyp D r s K α L p ε Λ h f)
    (hB : iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) :
    WBound D (r / 2) (s / 6) (iterF D r s (r / 4) (s / 3) K Λ h (fun _ => (0 : ℂ)) f)
      (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) := by
  have hr := H.hr
  have hs := H.hs
  have hd := iterative_direct_d (nfCaseB_hyp H)
  have e : starNorm r s (r / 4) (s / 3) (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
      (fun j : Fin 0 => j.elim0) = 0 := by simp [starNorm]
  have hd' : WBound D (r - 2 * (r / 4)) (s - 2 * (s / 3))
      (iterF D r s (r / 4) (s / 3) K Λ h (fun _ => (0 : ℂ)) f)
      (nfBound α p K (r / 4) (s / 3) ε
        (starNorm r s (r / 4) (s / 3) (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
          (fun j : Fin 0 => j.elim0))) := hd
  rw [e] at hd'
  exact hd'.mono (by linarith) (by linarith)
    (nfBound_caseB H.hp H.hα H.hK H.hr H.hs H.hε0 H.hi H.hii hB)

/-- Case B: `g₁ = P_Λ T_K f`. -/
theorem nfCaseB_g : iterG K Λ (fun _ => (0 : ℂ)) f = homRes K Λ f := by
  funext z
  simp [iterG]

/-- Case B, (c): the displacement of the single step on `Dom (r/2) (s/6)`. -/
theorem nfCaseB_disp (H : NFHyp D r s K α L p ε Λ h f) :
    ∀ z ∈ Dom n D (r / 2) (s / 6),
      ‖(iterMap D r s (r / 4) (s / 3) K Λ h f z).1 - z.1‖ ≤
        10 * conjExp p * ε / (2 * Real.pi * α * r) ∧
      ‖(iterMap D r s (r / 4) (s / 3) K Λ h f z).2 - z.2‖ ≤ conjExp p * K * ε / α := by
  have hr := H.hr
  have hs := H.hs
  obtain ⟨b1, -⟩ := iterative_direct_b (nfCaseB_hyp H)
  obtain ⟨d1, d2⟩ := disp_B H.hp H.hα H.hK H.hr H.hs H.hε0 H.hii
  intro z hz
  have hz' : z ∈ Dom n D (r - 3 * (r / 4) / 2) (s - 3 * (s / 3) / 2) :=
    Dom_mono (by linarith) (by linarith) hz
  obtain ⟨-, h2, h3⟩ := b1 z hz'
  exact ⟨h2.trans d2, h3.trans d1⟩

end CaseB

end KAM.NormalForm

end
