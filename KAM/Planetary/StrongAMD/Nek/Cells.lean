/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
public import KAM.Planetary.Exponential.Hamiltonian
public import KAM.Planetary.Exponential.Perturbation
public import KAM.Planetary.Exponential.KeplerData
public import KAM.Planetary.StrongAMD.Nek.Kepler

/-!
# The sealed partial-convexity theorem over a finite cell family, forward and backward in time

Source: the cellwise application of the sealed frozen `partialConvex_nekhoroshev`
planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.1, §2.4 steps 6–8 (infrastructure: no MAIN lemma
is transcribed); track LP, non-frozen.

One generic theorem in the number `k` of slow pairs (planar `k = n`, spatial `k = n + n`):

* `PartialConvexConclusion`: the conclusion of the frozen theorem for one `(h, G, D, μ, P)`
  (a transcription of the frozen conclusion, no new content);
* `cell_threshold_uniform`: one threshold `μ₀` for a finite family of cells, for `(h, P)` and for
  `(-h, -P)` (the premises are those of the frozen theorem, for `h` and `-h`);
* `isSolutionOn_reverse_neg`: time reversal `s ↦ w (-s)` turns a solution of the `(h, P)` field on
  `[t, 0]` into one of the `(-h, -P)` field on `[0, -t]`;
* `cell_drift_two_sided`: the two-sided drift bound on every cell (a conditional helper, not a
  source result);
* `kepler_cell_drift`: the instance `h = planetaryKeplerC ν`, fast premises from the Kepler cell data.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Set Metric KAM.Nekhoroshev

/-- The conclusion of the frozen `partialConvex_nekhoroshev` for fixed `(h, G, D, μ, P)`. -/
def PartialConvexConclusion {n k : ℕ} (h : (Fin n → ℂ) → ℂ) (G : Set (Fin n → ℝ))
    (D : Set (Phase k)) (μ : ℝ) (P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ z : ℝ → Phase (n + k),
    IsSolutionOn (degenerateHamiltonian (realPart h)
      (fun _ w => (P (complexifyPhase w)).re) μ) {I | fast (b := k) I ∈ G} (Icc 0 C) z →
    fast (b := k) (z 0).2 ∈ KAM.Nekhoroshev.innerCore G (μ ^ partialDriftExponent n) →
    ∀ t ∈ Icc 0 (min C (μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)))),
      (∀ u ∈ Icc 0 t, (slow (a := n) (z u).1, slow (a := n) (z u).2) ∈
        KAM.Nekhoroshev.innerCore D (μ ^ partialDriftExponent n)) →
      ‖fast (b := k) (z t).2 - fast (b := k) (z 0).2‖ ≤ μ ^ partialDriftExponent n / 2

/-- A finite family of positive numbers has a positive common lower bound. -/
theorem exists_pos_le_forall_fintype {ι : Type*} [Fintype ι] (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ δ i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min δ
    exact ⟨δ i0, hδ i0, hi0⟩

/-- **Uniform threshold over a finite cell family** (statement 1).  The premises are those of the
frozen theorem, for every cell `j`, for `h` (constants `gp, mp, Mp`) and for `-h` (constants
`gn, mn, Mn`).  One `μ₀` serves every cell, every `μ ∈ (0, μ₀)` and every `P`: the frozen
conclusion holds for `(h, P)` and for `(-h, -P)`. -/
theorem cell_threshold_uniform {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) {ι : Type*} [Fintype ι]
    (G G' : ι → Set (Fin n → ℝ)) (D : ι → Set (Phase k))
    (hG : ∀ j, IsOpen (G j)) (hGc : ∀ j, Convex ℝ (G j))
    (hG' : ∀ j, IsOpen (G' j)) (hGc' : ∀ j, Convex ℝ (G' j)) (hD : ∀ j, IsOpen (D j))
    (ρ gp mp Mp gn mn Mn : ι → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hMp : ∀ j, 0 < Mp j) (hMn : ∀ j, 0 < Mn j)
    (hcollar : ∀ j, ∀ I ∈ G j, closedBall I (ρ j) ⊆ G' j)
    (h : (Fin n → ℂ) → ℂ)
    (hhol : ∀ j, DifferentiableOn ℂ h (KAM.actionNbhd (G' j) (ρ j)))
    (hC2 : ∀ j, ContDiffOn ℂ 2 h (KAM.actionNbhd (G' j) (ρ j)))
    (hreal : ∀ j, ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (G' j) (ρ j) → (h (fun i => (I i : ℂ))).im = 0)
    (hHess : ∀ j, ∀ z ∈ KAM.actionNbhd (G' j) (ρ j), ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mp j)
    (hdef : ∀ j, HasDefiniteFastPart (G' j) (ρ j) (gp j) (mp j) h)
    (hholn : ∀ j, DifferentiableOn ℂ (-h) (KAM.actionNbhd (G' j) (ρ j)))
    (hC2n : ∀ j, ContDiffOn ℂ 2 (-h) (KAM.actionNbhd (G' j) (ρ j)))
    (hrealn : ∀ j, ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (G' j) (ρ j) → ((-h) (fun i => (I i : ℂ))).im = 0)
    (hHessn : ∀ j, ∀ z ∈ KAM.actionNbhd (G' j) (ρ j), ‖fderiv ℂ (fderiv ℂ (-h)) z‖ ≤ Mn j)
    (hdefn : ∀ j, HasDefiniteFastPart (G' j) (ρ j) (gn j) (mn j) (-h)) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ j : ι,
      ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
        IsPartialPerturbation (G' j) (D j) (ρ j) P →
        PartialConvexConclusion h (G j) (D j) μ P ∧
        PartialConvexConclusion (-h) (G j) (D j) μ (-P) := by
  have hp := fun j => partialConvex_nekhoroshev hn hk (G j) (G' j) (D j) (hG j) (hGc j) (hG' j)
    (hGc' j) (hD j) (ρ j) (gp j) (mp j) (Mp j) (hρ j) (hMp j) (hcollar j) h (hhol j) (hC2 j)
    (hreal j) (hHess j) (hdef j)
  have hm := fun j => partialConvex_nekhoroshev hn hk (G j) (G' j) (D j) (hG j) (hGc j) (hG' j)
    (hGc' j) (hD j) (ρ j) (gn j) (mn j) (Mn j) (hρ j) (hMn j) (hcollar j) (-h) (hholn j) (hC2n j)
    (hrealn j) (hHessn j) (hdefn j)
  choose μp hμp hNp using hp
  choose μn hμn hNn using hm
  obtain ⟨c1, hc1, hc1le⟩ := exists_pos_le_forall_fintype μp hμp
  obtain ⟨c2, hc2, hc2le⟩ := exists_pos_le_forall_fintype μn hμn
  refine ⟨min c1 c2, lt_min hc1 hc2, fun μ hμ hμlt j P hP => ⟨?_, ?_⟩⟩
  · exact hNp j μ hμ (hμlt.trans_le ((min_le_left _ _).trans (hc1le j))) P hP
  · exact hNn j μ hμ (hμlt.trans_le ((min_le_right _ _).trans (hc2le j))) (-P)
      (KAM.Planetary.isPartialPerturbation_neg_of hP)

/-- **Time reversal** (statement 2).  A solution `w` of the `(h, P)` field on `[t, 0]` gives the
solution `s ↦ w (-s)` of the `(-h, -P)` field on `[0, -t]`, with the same fast-action set. -/
theorem isSolutionOn_reverse_neg {n k : ℕ} (h : (Fin n → ℂ) → ℂ)
    (P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ) (μ : ℝ) (G : Set (Fin n → ℝ)) {t : ℝ}
    {w : ℝ → Phase (n + k)}
    (hw : IsSolutionOn (degenerateHamiltonian (realPart h)
      (fun _ x => (P (complexifyPhase x)).re) μ) {I | fast (b := k) I ∈ G} (Icc t 0) w) :
    IsSolutionOn (degenerateHamiltonian (realPart (-h))
      (fun _ x => ((-P) (complexifyPhase x)).re) μ) {I | fast (b := k) I ∈ G} (Icc 0 (-t))
      (fun s => w (-s)) := by
  intro s hs
  have hs' : -s ∈ Icc t 0 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨hU, hdiff, hder⟩ := hw (-s) hs'
  have hneg : degenerateHamiltonian (realPart (-h))
      (fun _ x => ((-P) (complexifyPhase x)).re) μ =
      fun x => -degenerateHamiltonian (realPart h)
        (fun _ x => (P (complexifyPhase x)).re) μ x := by
    funext x
    simp only [degenerateHamiltonian, KAM.Nekhoroshev.realPart, Pi.neg_apply, Complex.neg_re]
    ring
  rw [hneg]
  refine ⟨hU, hdiff.neg, ?_⟩
  have hcomp := hder.scomp s (hasDerivAt_neg' s)
  rw [neg_one_smul] at hcomp
  rw [hamiltonianVectorField_neg]
  exact hcomp

/-- **Two-sided drift on every cell** (statement 3, a conditional helper).  The orbit premises
are the frozen theorem's, transported to `uIcc 0 t`: a solution of the `(h, P)` field on
`uIcc 0 t` with fast actions in `G j`, slow pairs in the inner core of `D j` and initial fast
action in the inner core of `G j`. -/
theorem cell_drift_two_sided {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) {ι : Type*} [Fintype ι]
    (G G' : ι → Set (Fin n → ℝ)) (D : ι → Set (Phase k))
    (hG : ∀ j, IsOpen (G j)) (hGc : ∀ j, Convex ℝ (G j))
    (hG' : ∀ j, IsOpen (G' j)) (hGc' : ∀ j, Convex ℝ (G' j)) (hD : ∀ j, IsOpen (D j))
    (ρ gp mp Mp gn mn Mn : ι → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hMp : ∀ j, 0 < Mp j) (hMn : ∀ j, 0 < Mn j)
    (hcollar : ∀ j, ∀ I ∈ G j, closedBall I (ρ j) ⊆ G' j)
    (h : (Fin n → ℂ) → ℂ)
    (hhol : ∀ j, DifferentiableOn ℂ h (KAM.actionNbhd (G' j) (ρ j)))
    (hC2 : ∀ j, ContDiffOn ℂ 2 h (KAM.actionNbhd (G' j) (ρ j)))
    (hreal : ∀ j, ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (G' j) (ρ j) → (h (fun i => (I i : ℂ))).im = 0)
    (hHess : ∀ j, ∀ z ∈ KAM.actionNbhd (G' j) (ρ j), ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mp j)
    (hdef : ∀ j, HasDefiniteFastPart (G' j) (ρ j) (gp j) (mp j) h)
    (hholn : ∀ j, DifferentiableOn ℂ (-h) (KAM.actionNbhd (G' j) (ρ j)))
    (hC2n : ∀ j, ContDiffOn ℂ 2 (-h) (KAM.actionNbhd (G' j) (ρ j)))
    (hrealn : ∀ j, ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (G' j) (ρ j) → ((-h) (fun i => (I i : ℂ))).im = 0)
    (hHessn : ∀ j, ∀ z ∈ KAM.actionNbhd (G' j) (ρ j), ‖fderiv ℂ (fderiv ℂ (-h)) z‖ ≤ Mn j)
    (hdefn : ∀ j, HasDefiniteFastPart (G' j) (ρ j) (gn j) (mn j) (-h)) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ j : ι,
      ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
        IsPartialPerturbation (G' j) (D j) (ρ j) P →
      ∀ (w : ℝ → Phase (n + k)) (t : ℝ),
        |t| ≤ μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)) →
        IsSolutionOn (degenerateHamiltonian (realPart h)
          (fun _ x => (P (complexifyPhase x)).re) μ) {I | fast (b := k) I ∈ G j}
          (uIcc 0 t) w →
        fast (b := k) (w 0).2 ∈ KAM.Nekhoroshev.innerCore (G j) (μ ^ partialDriftExponent n) →
        (∀ u ∈ uIcc 0 t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
          KAM.Nekhoroshev.innerCore (D j) (μ ^ partialDriftExponent n)) →
        ‖fast (b := k) (w t).2 - fast (b := k) (w 0).2‖ ≤ μ ^ partialDriftExponent n / 2 := by
  obtain ⟨μ₀, hμ₀, H⟩ := cell_threshold_uniform hn hk G G' D hG hGc hG' hGc' hD ρ gp mp Mp gn mn
    Mn hρ hMp hMn hcollar h hhol hC2 hreal hHess hdef hholn hC2n hrealn hHessn hdefn
  refine ⟨μ₀, hμ₀, fun μ hμ hμlt j P hP w t ht hw h0 hslow => ?_⟩
  obtain ⟨Hp, Hn⟩ := H μ hμ hμlt j P hP
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · -- backward: reverse time and use `(-h, -P)` on `[0, -t]`
    have hI : uIcc 0 t = Icc t 0 := uIcc_of_ge htneg.le
    rw [hI] at hw hslow
    have hsol := isSolutionOn_reverse_neg h P μ (G j) hw
    have hN := Hn (-t) (by linarith) (fun s => w (-s)) hsol (by simpa using h0) (-t)
      ⟨by linarith, le_min le_rfl (by rw [abs_of_neg htneg] at ht; exact ht)⟩
      (fun u hu => hslow (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    simpa using hN
  · simp only [sub_self, norm_zero]
    exact div_nonneg (Real.rpow_nonneg hμ.le _) (by norm_num)
  · have hI : uIcc 0 t = Icc 0 t := uIcc_of_le htpos.le
    rw [hI] at hw hslow
    exact Hp t htpos w hw h0 t ⟨htpos.le, le_min le_rfl (by rwa [abs_of_pos htpos] at ht)⟩ hslow

/-- **Kepler instance** (statement 4).  For compact `U ⊆ chamber ν` the collar bound `ρ₀` depends
on `(ν, U)` only; for every finite cell family with `G' j ⊆ cthickening ρ₀ U` and
`ρ j ≤ ρ₀` the two-sided drift bound holds for `h = planetaryKeplerC ν`. -/
theorem kepler_cell_drift {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) {ν : Fin n → ℝ}
    (hν : ∀ i, 0 < ν i) {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ {ι : Type} [Fintype ι]
      (G G' : ι → Set (Fin n → ℝ)) (D : ι → Set (Phase k)) (ρ : ι → ℝ),
      (∀ j, IsOpen (G j)) → (∀ j, Convex ℝ (G j)) → (∀ j, IsOpen (G' j)) →
      (∀ j, Convex ℝ (G' j)) → (∀ j, IsOpen (D j)) → (∀ j, 0 < ρ j) →
      (∀ j, ∀ I ∈ G j, closedBall I (ρ j) ⊆ G' j) →
      (∀ j, G' j ⊆ cthickening ρ₀ U) → (∀ j, ρ j ≤ ρ₀) →
      ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ j : ι,
        ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
          IsPartialPerturbation (G' j) (D j) (ρ j) P →
        ∀ (w : ℝ → Phase (n + k)) (t : ℝ),
          |t| ≤ μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)) →
          IsSolutionOn (degenerateHamiltonian (realPart (planetaryKeplerC ν))
            (fun _ x => (P (complexifyPhase x)).re) μ) {I | fast (b := k) I ∈ G j}
            (uIcc 0 t) w →
          fast (b := k) (w 0).2 ∈ KAM.Nekhoroshev.innerCore (G j) (μ ^ partialDriftExponent n) →
          (∀ u ∈ uIcc 0 t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
            KAM.Nekhoroshev.innerCore (D j) (μ ^ partialDriftExponent n)) →
          ‖fast (b := k) (w t).2 - fast (b := k) (w 0).2‖ ≤
            μ ^ partialDriftExponent n / 2 := by
  obtain ⟨ρ₀, g, m, M, hρ₀, hg, hm, hM, hdata⟩ :=
    lp3_kepler_data (by omega) hν hUc hUch
  refine ⟨ρ₀, hρ₀, fun {ι} _ G G' D ρ hG hGc hG' hGc' hD hρ hcol hsub hle => ?_⟩
  have hd := fun j => hdata (G' j) (hsub j) (ρ j) (hρ j) (hle j)
  exact cell_drift_two_sided hn hk G G' D hG hGc hG' hGc' hD ρ (fun _ => g) (fun _ => m)
    (fun _ => M) (fun _ => g) (fun _ => m) (fun _ => M) hρ (fun _ => hM) (fun _ => hM) hcol
    (planetaryKeplerC ν) (fun j => (hd j).1.1) (fun j => (hd j).1.2.1)
    (fun j => (hd j).1.2.2.1) (fun j => (hd j).1.2.2.2.1) (fun j => (hd j).1.2.2.2.2)
    (fun j => (hd j).2.1) (fun j => (hd j).2.2.1) (fun j => (hd j).2.2.2.1)
    (fun j => (hd j).2.2.2.2.1) (fun j => (hd j).2.2.2.2.2)

end KAM.Planetary.StrongAMD

end
