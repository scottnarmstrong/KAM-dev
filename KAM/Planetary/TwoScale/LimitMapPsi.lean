/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitActions
public import KAM.Planetary.TwoScale.LimitMapScale

/-!
# Two-scale KAM: the symplectic stage maps `Ψ_k` (`bpP:p3:psi-lip`, domains and displacement)

The private conditional interface of the local obligation `psi_lip` (design package P23-18).
`PsiSteps` collects exactly the outputs of `iterative` (P23-16) about the stage maps `Ψ_{j+1}`,
`Φ_j = Ψ_1 ∘ ⋯ ∘ Ψ_j` and the domains `D_j`, on the shared witnesses; `iterative_psiSteps` shows
they are projections of the output of `iterative` (together with `ActionSteps`, on the same
witnesses). Here: the real restriction `psiR` of `Ψ_{j+1}` maps the real half-radius domain
`𝒟_{j+1} × ℝⁿ` into `𝒟_j × ℝⁿ` (`stepP:p3:pl-dom`) and the scaled displacement is
`(3/4) Ê_j 12^{-j}` (`stepP:p3:pl-disp`).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The real restriction `Re ∘ Ψ ∘ ι` of a stage map. -/
def psiR {n : ℕ} (Ψ : CPhase n → CPhase n) (x : Phase n) : Phase n :=
  KAM.realPartCLM₂ n (Ψ (KAM.realInclusion₂ n x))

/-- The real half-radius stage domain `𝒟 × ℝⁿ`, angles first. -/
def phaseTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : Set (Phase n) := univ ×ˢ realTube D r

/-- The outputs of `iterative` concerning the stage maps `Ψ_{j+1}` and `Φ_j`, on the shared
witnesses. -/
structure PsiSteps {a b : ℕ} (sbar : ℝ) (p : ScaleData)
    (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
    (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)) : Prop where
  hyp : ∀ j, KamHyp (Ds j) sbar (seq p j) (hs j) (fs j)
  Phi_zero : Φ 0 = id
  Phi_succ : ∀ j, Φ (j + 1) = Φ j ∘ Ψ (j + 1)
  phi_diff : ∀ j, DifferentiableOn ℂ (Φ j)
    (coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s))
  phi_real : ∀ j, ∀ x : Phase (a + b),
    KAM.realInclusion₂ (a + b) x ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) →
    Φ j (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))
  phi_per : ∀ j, ∀ z ∈ coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s),
    ∀ k : Fin (a + b) → ℤ,
      Φ j (z + ((fun i => (k i : ℂ)), 0)) = Φ j z + ((fun i => (k i : ℂ)), 0)
  psi_diff : ∀ j, DifferentiableOn ℂ (Ψ (j + 1))
    (coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12))
  psi_real : ∀ j, ∀ x : Phase (a + b),
    KAM.realInclusion₂ (a + b) x ∈
      coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12) →
    Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))
  psi_per : ∀ j, ∀ z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16)
      (sbar + (seq p j).s / 12), ∀ k : Fin (a + b) → ℤ,
    Ψ (j + 1) (z + ((fun i => (k i : ℂ)), 0)) = Ψ (j + 1) z + ((fun i => (k i : ℂ)), 0)
  psi_bd : ∀ j, ∀ z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16)
      (sbar + (seq p j).s / 12),
    ‖firstBlock (b := b) ((Ψ (j + 1) z).2 - z.2)‖ ≤
      3 / 4 * (p.Mhat / p.M) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) ((Ψ (j + 1) z).2 - z.2)‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) ∧
    2 * π * ‖(Ψ (j + 1) z).1 - z.1‖ ≤ 3 / 4 * eHat (seq p j) * (seq p j).s
  tube : ∀ j, Ds (j + 1) ⊆ realTube (Ds j) (rhoHat (seq p j) / 16)
  eHat_sq : ∀ j, eHat (seq p (j + 1)) < eHat (seq p j) ^ 2
  rho_lo : ∀ j, rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) ≤ rhoHat (seq p (j + 1))
  rho_hi : ∀ j, rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16

/-- Applicability check: `ActionSteps` and `PsiSteps` are projections of the output of
`iterative`, on the same witnesses `(Ds, hs, fs, is, Ψ, Φ)`. -/
theorem iterative_steps {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is ∧ PsiSteps sbar p Ds hs fs Ψ Φ := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, h1, -, h3, h4, hK, hP, hI, hPh, ht, hΨ, hr⟩ := iterative H
  refine ⟨Ds, hs, fs, Ψ, Φ, is, h0, ⟨h1, hK, fun j => (hI j).2.1, fun j => (hI j).2.2.1,
    fun j => (hI j).2.2.2, fun j => (ht j).2.2, fun j => (hr j).1, fun j => (hr j).2.2.1⟩,
    ⟨hK, h3, hP, fun j => (hPh j).1, fun j => (hPh j).2.2.1, fun j => (hPh j).2.2.2.1,
      fun j => (hΨ j).1, fun j => (hΨ j).2.1, fun j => (hΨ j).2.2.1, fun j => (hΨ j).2.2.2.2.2,
      fun j => (ht j).1, fun j => (hr j).1, fun j => (hr j).2.1, fun j => (hr j).2.2.1⟩⟩

theorem mem_realTube_iff {n : ℕ} {D : Set (Fin n → ℝ)} {r : ℝ} {v : Fin n → ℝ} :
    v ∈ realTube D r ↔ ∃ J ∈ D, ‖v - J‖ < r := by
  constructor
  · rintro ⟨J, hJ, h⟩
    refine ⟨J, hJ, ?_⟩
    have : KAM.realInclusion n v - (fun i => (J i : ℂ)) = KAM.realInclusion n (v - J) := by
      ext i; simp
    rwa [this, KAM.norm_realInclusion] at h
  · rintro ⟨J, hJ, h⟩
    refine ⟨J, hJ, ?_⟩
    have : KAM.realInclusion n v - (fun i => (J i : ℂ)) = KAM.realInclusion n (v - J) := by
      ext i; simp
    rwa [this, KAM.norm_realInclusion]

theorem real_mem_coefDom {n : ℕ} {D : Set (Fin n → ℝ)} {r σ : ℝ} (hσ : 0 < σ) {x : Phase n}
    (hx : x.2 ∈ realTube D r) : KAM.realInclusion₂ n x ∈ coefficientDom D r σ := by
  rw [(conv_data D r σ).2]
  refine ⟨fun i => ?_, hx⟩
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero]
  positivity

theorem norm_le_of_blocks {a b : ℕ} {E : Type*} [SeminormedAddCommGroup E] {v : Fin (a + b) → E}
    {B : ℝ} (hB : 0 ≤ B) (h1 : ‖firstBlock (b := b) v‖ ≤ B) (h2 : ‖lastBlock (a := a) v‖ ≤ B) :
    ‖v‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact (norm_le_pi_norm (firstBlock (b := b) v) i).trans h1
  · exact (norm_le_pi_norm (lastBlock (a := a) v) i).trans h2

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

namespace PsiSteps

/-- Real displacement bound on the complex stage domain, in sup norm on the action block. -/
theorem action_bd (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {z : CPhase (a + b)}
    (hz : z ∈ coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12)) :
    ‖(Ψ (j + 1) z).2 - z.2‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) := by
  obtain ⟨b1, b2, -⟩ := P.psi_bd j z hz
  have hR := (P.hyp j).R_pos
  have he := (P.hyp j).eHat_nonneg
  have hM : p.Mhat ≤ p.M := (P.hyp 0).normalized.1
  have hM0 : 0 < p.M := (P.hyp 0).positive.2.2.2.2.1
  have hr : p.Mhat / p.M ≤ 1 := (div_le_one hM0).2 hM
  have hq : 0 ≤ eHat (seq p j) * rhoHat (seq p j) := by positivity
  refine norm_le_of_blocks (by positivity) ?_ b2
  refine b1.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right hr hq]

theorem psi_step (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2)) :
    KAM.realInclusion₂ (a + b) (psiR (Ψ (j + 1)) x) =
        Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∧
      psiR (Ψ (j + 1)) x ∈ phaseTube (Ds j) ((seq p j).ρ / 2) ∧
      ‖(psiR (Ψ (j + 1)) x - x).2‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) ∧
      2 * π * ‖(psiR (Ψ (j + 1)) x - x).1‖ ≤ 3 / 4 * eHat (seq p j) * (seq p j).s := by
  have hR := (P.hyp j).R_pos
  have he := (P.hyp j).eHat_nonneg
  have hes := (P.hyp j).eHat_lt_small
  have hρ := (P.hyp j).R_le_ρ
  have hs0 : 0 < (seq p j).s := (P.hyp j).positive.2.1
  have hsbar : 4 * (seq p j).s ≤ sbar := (P.hyp j).widths.1
  have hρ1 : (seq p (j + 1)).ρ = rhoHat (seq p j) / 16 := rfl
  rw [hρ1] at hx
  obtain ⟨-, hx2⟩ := hx
  obtain ⟨J, hJ, hxJ⟩ := mem_realTube_iff.1 hx2
  have hxV : KAM.realInclusion₂ (a + b) x ∈
      coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12) :=
    real_mem_coefDom (by linarith) (mem_realTube_iff.2 ⟨J, hJ, by linarith⟩)
  obtain ⟨y, hy⟩ := P.psi_real j x hxV
  have hyR : psiR (Ψ (j + 1)) x = y := by
    unfold psiR; rw [← hy, KAM.realPartCLM₂_realInclusion₂]
  have hd2 := P.action_bd j hxV
  obtain ⟨-, -, hd1⟩ := P.psi_bd j _ hxV
  rw [← hy] at hd2 hd1
  simp only [KAM.realInclusion₂_apply] at hd2 hd1
  rw [← map_sub, KAM.norm_realInclusion] at hd2 hd1
  rw [hyR]
  have hy2 : ‖y.2 - x.2‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) := hd2
  refine ⟨hy, ⟨trivial, ?_⟩, hy2, hd1⟩
  obtain ⟨J', hJ', hJJ⟩ := mem_realTube_iff.1 ((P.tube j) hJ)
  refine mem_realTube_iff.2 ⟨J', hJ', ?_⟩
  calc ‖y.2 - J'‖ = ‖(y.2 - x.2) + (x.2 - J) + (J - J')‖ := by congr 1; abel
    _ ≤ ‖y.2 - x.2‖ + ‖x.2 - J‖ + ‖J - J'‖ := norm_add₃_le
    _ < rhoHat (seq p j) / 8 := by nlinarith
    _ ≤ (seq p j).ρ / 2 := by linarith

end PsiSteps

end KAM.Planetary

end
