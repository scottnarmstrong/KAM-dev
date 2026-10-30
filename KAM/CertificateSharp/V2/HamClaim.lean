/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RefinedFacts

/-!
# The refined bounds on `H`, by the landed disc pass

`checkHamClaim c R` compares the four jet sums the route A theorem reads with their own rationals,
over the slot balls of the landed `Slp.balls`.

This repeats the disc half of `KAM/CertificateSharp/Ham/SplitBounds.lean`. That module imports
`Ham.TrigBound`, which defines `KAM.CertificateSharp.expLoQ` as `Corner.SupBound` does, so no module
can import both it and the frame majorants of C4. `V2/HamTrig.lean` gives the cosh pass as
`HamFacts`, for use through `refinedCore_sound`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

/-- The four jet sums of `R`, over the slot balls `bs` (`m := 2n`). -/
def hamClaimOk (m : ℕ) (J : HamJet) (bs : List (CC ℚ × ℚ)) (R : RefClaim) : Bool :=
  decide (sumRangeQ m (fun a => slotMagQ bs (J.d1.getD a 0)) ≤ R.dh) &&
    (List.range m).all (fun a =>
      decide (sumRangeQ m (fun b => slotMagQ bs ((J.d2.getD a []).getD b 0)) ≤ R.dx)) &&
    (List.range m).all (fun a => decide (sumRangeQ m (fun b => sumRangeQ m (fun e =>
      slotMagQ bs (((J.d3.getD a []).getD b []).getD e 0))) ≤ R.d2x)) &&
    decide (sumRangeQ m (fun a => sumRangeQ m (fun b =>
      slotMagQ bs ((J.d2.getD a []).getD b 0))) ≤ R.d2h)

variable {n : ℕ} {α : Type} [CertArith α]

/-- The landed disc pass and the four bounds. -/
def checkHamClaim (c : TorusCertificate n α) (R : RefClaim) : Bool :=
  match c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
  | some bs => hamClaimOk (n + n) c.ham.jet bs R
  | none => false

variable [LawfulCertArith α]

/-- **Soundness of the disc pass.** -/
theorem checkHamClaim_sound {c : TorusCertificate n α} {R : RefClaim}
    (hs : checkStatic c = true) (h : checkHamClaim c R = true) : HamFacts c R := by
  have hS := checkStatic_sound hs
  have hn : 1 ≤ n := by have := hS.hn; omega
  unfold checkHamClaim at h
  cases hb : c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bs =>
    rw [hb] at h
    simp only [hamClaimOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨hDH, hDX⟩, hD2X⟩, hD2H⟩ := h
    have hnv := c.ham.nonvanishingOn_of_balls hS.hWH hb
    have hmag : ∀ z ∈ c.D, ∀ i, ‖c.ham.jet.prog.val n z i‖ ≤ (slotMagQ bs i : ℝ) :=
      fun z hz i => Slp.norm_val_le_slotMagQ hS.hWH hb hz i
    have hD : IsOpen c.D := isOpen_certDomain _ _ _ _
    have hd1 {z} (hz : z ∈ c.D) (a : Fin n ⊕ Fin n) :
        ‖fderiv ℂ c.H z (phaseBasis a)‖ ≤
          (slotMagQ bs (c.ham.jet.d1.getD (phaseNat a) 0) : ℝ) := by
      have := hmag z hz (c.ham.jet.d1.getD (phaseNat a) 0)
      rwa [c.ham.jet_d1 hD hnv hz a] at this
    have hd2 {z} (hz : z ∈ c.D) (a b : Fin n ⊕ Fin n) :
        ‖iteratedFDeriv ℂ 2 c.H z ![phaseBasis a, phaseBasis b]‖ ≤
          (slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) : ℝ) := by
      have := hmag z hz ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0)
      rwa [c.ham.jet_d2 hD hnv hz a b] at this
    have hd3 {z} (hz : z ∈ c.D) (a b e : Fin n ⊕ Fin n) :
        ‖iteratedFDeriv ℂ 3 c.H z ![phaseBasis a, phaseBasis b, phaseBasis e]‖ ≤
          (slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD
            (phaseNat e) 0) : ℝ) := by
      have := hmag z hz
        (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat e) 0)
      rwa [c.ham.jet_d3 hD hnv hz a b e] at this
    have hcd {z} (hz : z ∈ c.D) : ContDiffAt ℂ ⊤ c.H z :=
      (c.ham.contDiffOn_eval hD hnv).contDiffAt (hD.mem_nhds hz)
    refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · refine (norm_fderiv_le_sum_partials z).trans
        ((Finset.sum_le_sum fun a _ => hd1 hz a).trans ?_)
      rw [← Rat.cast_sum,
        sum_phaseNat_eq_sumRangeQ (fun i => slotMagQ bs (c.ham.jet.d1.getD i 0))]
      exact_mod_cast hDH
    · refine norm_fderiv_hamiltonianVectorFieldℂ_le hn ((hcd hz).of_le (by simp)) fun a => ?_
      refine (Finset.sum_le_sum fun b _ => hd2 hz a.swap b).trans ?_
      rw [← Rat.cast_sum, sum_phaseNat_eq_sumRangeQ
        (fun i => slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a.swap) []).getD i 0))]
      exact_mod_cast hDX _ (phaseNat_lt_add a.swap)
    · refine norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le hn ((hcd hz).of_le (by simp))
        fun a => ?_
      refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun e _ =>
        hd3 hz a.swap b e).trans ?_
      have := hD2X _ (phaseNat_lt_add a.swap)
      rw [← sum_sum_phaseNat_eq_sumRangeQ
        (fun i j => slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a.swap) []).getD i []).getD j 0))]
        at this
      exact_mod_cast this
    · refine (norm_iteratedFDeriv_two_le_sum_partials z).trans
        ((Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hd2 hz a b).trans ?_)
      have := hD2H
      rw [← sum_sum_phaseNat_eq_sumRangeQ
        (fun i j => slotMagQ bs ((c.ham.jet.d2.getD i []).getD j 0))] at this
      exact_mod_cast this

end KAM.CertificateSharp.V2

end
