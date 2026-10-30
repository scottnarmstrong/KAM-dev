/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Ham.BallsTrig

/-!
# Split bounds on the Hamiltonian

The landed `checkHamBounds` compares the five jet sums of `hamBoundsOk` with one rational `M`.
Here each sum is compared with its own rational, `HamSplit`:
`‖DH‖ ≤ dh`, `‖X_H‖ ≤ x` (`M₀`), `‖DX_H‖ ≤ dx` (`M₁`), `‖D²X_H‖ ≤ d2x` (`M₂`),
`‖D²H‖ ≤ d2h`, on the domain `D`, with the same slot magnitudes (the same row sums and
bridges). The v2 theorem consumes `M₀, M₁, M₂` separately.

* `hamBoundsOkSplit`, `HamSplit.const`: `hamBoundsOkSplit _ _ _ (.const M) = hamBoundsOk _ _ _ M`
  by `rfl`.
* `hamSums`: the five measured sums (for choosing the rationals; not used by any soundness
  statement).
* `HamBoundsConclusion c S`: the five bounds and the certified denominators.
* `ham_bounds_of_mags`: the bounds from slot magnitudes and the Bool; shared by the disc pass
  (`checkHamBoundsSplit`) and the cosh pass (`checkHamBoundsTrigSplit`).
* `checkHamBoundsTrig`: the drop-in for `checkHamBounds` (single `M`), with
  `checkHamBoundsTrig_sound` proving the same conclusion as `checkHamBounds_sound`.
* `HamBoundsConclusion.mono`: split bounds give the single-`M` conclusion for any `M ≥` all five.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

/-- The five rationals bounding `‖DH‖`, `‖X_H‖`, `‖DX_H‖`, `‖D²X_H‖`, `‖D²H‖`. -/
structure HamSplit where
  dh : ℚ
  x : ℚ
  dx : ℚ
  d2x : ℚ
  d2h : ℚ

/-- All five bounds equal `M`. -/
def HamSplit.const (M : ℚ) : HamSplit := ⟨M, M, M, M, M⟩

/-- `hamBoundsOk` with one rational per bound. -/
def hamBoundsOkSplit (m : ℕ) (J : HamJet) (bs : List (CC ℚ × ℚ)) (S : HamSplit) : Bool :=
  decide (sumRangeQ m (fun a => slotMagQ bs (J.d1.getD a 0)) ≤ S.dh) &&
    (List.range m).all (fun a => decide (slotMagQ bs (J.d1.getD a 0) ≤ S.x)) &&
    (List.range m).all (fun a =>
      decide (sumRangeQ m (fun b => slotMagQ bs ((J.d2.getD a []).getD b 0)) ≤ S.dx)) &&
    (List.range m).all (fun a => decide (sumRangeQ m (fun b => sumRangeQ m (fun e =>
      slotMagQ bs (((J.d3.getD a []).getD b []).getD e 0))) ≤ S.d2x)) &&
    decide (sumRangeQ m (fun a => sumRangeQ m (fun b =>
      slotMagQ bs ((J.d2.getD a []).getD b 0))) ≤ S.d2h)

theorem hamBoundsOkSplit_const (m : ℕ) (J : HamJet) (bs : List (CC ℚ × ℚ)) (M : ℚ) :
    hamBoundsOkSplit m J bs (.const M) = hamBoundsOk m J bs M := rfl

/-- The five measured sums: the smallest `HamSplit` that `hamBoundsOkSplit` accepts. -/
def hamSums (m : ℕ) (J : HamJet) (bs : List (CC ℚ × ℚ)) : HamSplit where
  dh := sumRangeQ m (fun a => slotMagQ bs (J.d1.getD a 0))
  x := ((List.range m).map (fun a => slotMagQ bs (J.d1.getD a 0))).foldr max 0
  dx := ((List.range m).map (fun a =>
    sumRangeQ m (fun b => slotMagQ bs ((J.d2.getD a []).getD b 0)))).foldr max 0
  d2x := ((List.range m).map (fun a => sumRangeQ m (fun b => sumRangeQ m (fun e =>
    slotMagQ bs (((J.d3.getD a []).getD b []).getD e 0))))).foldr max 0
  d2h := sumRangeQ m (fun a => sumRangeQ m (fun b => slotMagQ bs ((J.d2.getD a []).getD b 0)))

variable {n : ℕ} {α : Type} [CertArith α]

/-- Certified denominators and the five split bounds on `D`. -/
def HamBoundsConclusion (c : TorusCertificate n α) (S : HamSplit) : Prop :=
  c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ S.dh ∧
    ‖hamiltonianVectorFieldℂ c.H z‖ ≤ S.x ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ S.dx ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ S.d2x ∧
    ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ S.d2h

theorem HamBoundsConclusion.mono {c : TorusCertificate n α} {S : HamSplit}
    (h : HamBoundsConclusion c S) {M : ℚ} (h1 : S.dh ≤ M) (h2 : S.x ≤ M) (h3 : S.dx ≤ M)
    (h4 : S.d2x ≤ M) (h5 : S.d2h ≤ M) :
    c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ M := by
  refine ⟨h.1, fun z hz => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.2 z hz
  exact ⟨a1.trans (by exact_mod_cast h1), a2.trans (by exact_mod_cast h2),
    a3.trans (by exact_mod_cast h3), a4.trans (by exact_mod_cast h4),
    a5.trans (by exact_mod_cast h5)⟩

variable [LawfulCertArith α]

/-- The split bounds from slot magnitudes (`hmag`, the output of a sound ball pass), certified
denominators and the Bool `hamBoundsOkSplit`. -/
theorem ham_bounds_of_mags {c : TorusCertificate n α} {S : HamSplit} (hn : 1 ≤ n)
    (hx0 : 0 ≤ S.x) {bs : List (CC ℚ × ℚ)} (hnv : c.ham.NonvanishingOn c.D)
    (hmag : ∀ z ∈ c.D, ∀ i, ‖c.ham.jet.prog.val n z i‖ ≤ (slotMagQ bs i : ℝ))
    (h : hamBoundsOkSplit (n + n) c.ham.jet bs S = true) : HamBoundsConclusion c S := by
  simp only [hamBoundsOkSplit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hDH, hXH⟩, hDX⟩, hD2X⟩, hD2H⟩ := h
  have hD : IsOpen c.D := isOpen_certDomain _ _ _ _
  refine ⟨hnv, fun z hz => ?_⟩
  have hd1 (a : Fin n ⊕ Fin n) :
      ‖fderiv ℂ c.H z (phaseBasis a)‖ ≤ (slotMagQ bs (c.ham.jet.d1.getD (phaseNat a) 0) : ℝ) := by
    have := hmag z hz (c.ham.jet.d1.getD (phaseNat a) 0)
    rwa [c.ham.jet_d1 hD hnv hz a] at this
  have hd2 (a b : Fin n ⊕ Fin n) :
      ‖iteratedFDeriv ℂ 2 c.H z ![phaseBasis a, phaseBasis b]‖ ≤
        (slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) : ℝ) := by
    have := hmag z hz ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0)
    rwa [c.ham.jet_d2 hD hnv hz a b] at this
  have hd3 (a b e : Fin n ⊕ Fin n) :
      ‖iteratedFDeriv ℂ 3 c.H z ![phaseBasis a, phaseBasis b, phaseBasis e]‖ ≤
        (slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD
          (phaseNat e) 0) : ℝ) := by
    have := hmag z hz
      (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat e) 0)
    rwa [c.ham.jet_d3 hD hnv hz a b e] at this
  have hcd : ContDiffAt ℂ ⊤ c.H z :=
    (c.ham.contDiffOn_eval hD hnv).contDiffAt (hD.mem_nhds hz)
  have hM0 : (0 : ℝ) ≤ S.x := by exact_mod_cast hx0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_fderiv_le_sum_partials z).trans ((Finset.sum_le_sum fun a _ => hd1 a).trans ?_)
    rw [← Rat.cast_sum, sum_phaseNat_eq_sumRangeQ (fun i => slotMagQ bs (c.ham.jet.d1.getD i 0))]
    exact_mod_cast hDH
  · rw [← norm_sumVec]
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun a => ?_
    rw [hamiltonianVectorFieldℂ_sumVec]
    have key (b : Fin n ⊕ Fin n) : ‖fderiv ℂ c.H z (phaseBasis b)‖ ≤ S.x :=
      (hd1 b).trans (by exact_mod_cast hXH _ (phaseNat_lt_add b))
    rcases a with i | i
    · exact key _
    · rw [Sum.elim_inr, norm_neg]; exact key _
  · refine norm_fderiv_hamiltonianVectorFieldℂ_le hn (hcd.of_le (by simp)) fun a => ?_
    refine (Finset.sum_le_sum fun b _ => hd2 a.swap b).trans ?_
    rw [← Rat.cast_sum, sum_phaseNat_eq_sumRangeQ
      (fun i => slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a.swap) []).getD i 0))]
    exact_mod_cast hDX _ (phaseNat_lt_add a.swap)
  · refine norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le hn (hcd.of_le (by simp))
      fun a => ?_
    refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun e _ => hd3 a.swap b e).trans ?_
    have := hD2X _ (phaseNat_lt_add a.swap)
    rw [← sum_sum_phaseNat_eq_sumRangeQ
      (fun i j => slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a.swap) []).getD i []).getD j 0))]
      at this
    exact_mod_cast this
  · refine (norm_iteratedFDeriv_two_le_sum_partials z).trans
      ((Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hd2 a b).trans ?_)
    have := hD2H
    rw [← sum_sum_phaseNat_eq_sumRangeQ
      (fun i j => slotMagQ bs ((c.ham.jet.d2.getD i []).getD j 0))] at this
    exact_mod_cast this

/-! ### The checks -/

/-- The cosh pass and the five bounds against one `M`: the drop-in for `checkHamBounds`. -/
def checkHamBoundsTrig (c : TorusCertificate n α) : Bool :=
  match ballsTrig n c.ham.jet.prog c.weightH c.centre c.radius c.expOrder with
  | some bs => hamBoundsOk (n + n) c.ham.jet bs c.params.M
  | none => false

/-- The cosh pass and the five bounds against their own rationals. -/
def checkHamBoundsTrigSplit (c : TorusCertificate n α) (S : HamSplit) : Bool :=
  decide (0 ≤ S.x) &&
    match ballsTrig n c.ham.jet.prog c.weightH c.centre c.radius c.expOrder with
    | some bs => hamBoundsOkSplit (n + n) c.ham.jet bs S
    | none => false

/-- The landed disc pass and the five bounds against their own rationals. -/
def checkHamBoundsSplit (c : TorusCertificate n α) (S : HamSplit) : Bool :=
  decide (0 ≤ S.x) &&
    match c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
    | some bs => hamBoundsOkSplit (n + n) c.ham.jet bs S
    | none => false

theorem checkHamBoundsTrigSplit_sound {c : TorusCertificate n α} {S : HamSplit}
    (hs : checkStatic c = true) (h : checkHamBoundsTrigSplit c S = true) :
    HamBoundsConclusion c S := by
  have hS := checkStatic_sound hs
  unfold checkHamBoundsTrigSplit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hx0, h⟩ := h
  cases hb : ballsTrig n c.ham.jet.prog c.weightH c.centre c.radius c.expOrder with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bs =>
    rw [hb] at h
    exact ham_bounds_of_mags (by have := hS.hn; omega) hx0
      (nonvanishingOn_of_ballsTrig c.ham hS.hWH hb)
      (fun z hz i => norm_val_le_slotMagQ_trig hS.hWH hb hz i) h

theorem checkHamBoundsSplit_sound {c : TorusCertificate n α} {S : HamSplit}
    (hs : checkStatic c = true) (h : checkHamBoundsSplit c S = true) :
    HamBoundsConclusion c S := by
  have hS := checkStatic_sound hs
  unfold checkHamBoundsSplit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hx0, h⟩ := h
  cases hb : c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bs =>
    rw [hb] at h
    exact ham_bounds_of_mags (by have := hS.hn; omega) hx0
      (c.ham.nonvanishingOn_of_balls hS.hWH hb)
      (fun z hz i => Slp.norm_val_le_slotMagQ hS.hWH hb hz i) h

/-- **The contract of `checkHamBounds`**, proved for the cosh pass. -/
theorem checkHamBoundsTrig_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkHamBoundsTrig c = true) :
    c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M := by
  have hS := checkStatic_sound hs
  unfold checkHamBoundsTrig at h
  cases hb : ballsTrig n c.ham.jet.prog c.weightH c.centre c.radius c.expOrder with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bs =>
    rw [hb] at h
    exact ham_bounds_of_mags (S := .const c.params.M) (by have := hS.hn; omega)
      (by exact_mod_cast hS.hM.le)
      (nonvanishingOn_of_ballsTrig c.ham hS.hWH hb)
      (fun z hz i => norm_val_le_slotMagQ_trig hS.hWH hb hz i) h

end KAM.CertificateSharp

end
