/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain.Basic

/-!
# Chains of torus steps: holomorphy and bounds of the pushed-forward remainders (B4-TMULTI)

For a chain `l` of steps with `TChDomOK`:

* `differentiableOn_tchRem`: `tchRem l Q` is holomorphic on the open set `tchDom l`;
* `norm_tchRem_le`: on `TChBound r δc δc` points, `‖tchRem l Q‖ ≤ tchChainBound n l Q`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

variable {n : ℕ}

theorem differentiableOn_tchRem {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s) :
    ∀ Q : FTPoly, DifferentiableOn ℂ (tchRem (n := n) l Q) (tchDom l) := by
  induction l with
  | nil => intro Q; exact differentiableOn_const 0
  | cons s l ih =>
    intro Q
    have hl' : ∀ t ∈ l, TChStepOK n t := fun t ht => hl t (by simp [ht])
    obtain ⟨-, hd⟩ := tchDom_isOpen_and_differentiableOn hl'
    have hs := hl s (by simp)
    have hS := hs.tchSmallField
    have h1 : DifferentiableOn ℂ (fun z => torusRem s.gen Q (s.σ : ℝ) (s.ρ : ℝ) s.order
        (tchTheta l z)) (tchDom (n := n) (s :: l)) :=
      (differentiableOn_torusRem hS s.order).comp (hd.mono inter_subset_left) (fun z hz =>
        cstripSub_subset_gaugeInterior hs hz.2)
    exact h1.add ((ih hl' s.out).mono inter_subset_left)

theorem norm_tchRem_le {Nact P : FTPoly} {r b : Fin n → ℝ} {εb δc : ℝ} :
    ∀ {l : List TChStep} {Q : FTPoly}, FTFits n Q → TChChainOK n Nact P l Q →
      TChDomOK n b r εb δc l → ∀ {z : (Fin n → ℂ) × (Fin n → ℂ)}, TChBound r δc δc z →
      ‖tchRem l Q z‖ ≤ (tchChainBound n l Q : ℝ)
  | [], Q, _, _, _, z, _ => by simp [tchRem, tchChainBound]
  | s :: l, Q, hQ, hok, hD, z, hz => by
    obtain ⟨hs, -, hrest⟩ := hok
    obtain ⟨-, h2, h3, h4⟩ := hD
    obtain ⟨-, hzb⟩ := tchTheta_bound (TChChainOK.tchStepsOK hrest) h4 hz
    have hS := hs.tchSmallField
    have hmem : tchTheta l z ∈ cstripOpen (n := n) ((s.σ : ℝ) - (s.σ' : ℝ) / 2)
        ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2) := by
      intro i
      constructor <;> linarith [(hzb i).1, (hzb i).2, h2, h3 i]
    have h1 := norm_torusRem_le hs.fits_gen hQ hS pi_le_ftPiUB hs.tchLam_pos hs.stripLog
      (List.replicate n s.ρ) (fun i => by rw [replicate_getD_tchRad]) hs.order_pos
      (cstripSub_subset_gaugeInterior hs hmem)
    have h5 := norm_tchRem_le hs.fits_out hrest h4 hz
    show ‖torusRem s.gen Q (s.σ : ℝ) (s.ρ : ℝ) s.order (tchTheta l z) + tchRem l s.out z‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    simp only [tchChainBound]
    push_cast
    exact add_le_add (by simpa using h1) h5

end KAM.EffectiveStability
