/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.FForm
public import KAM.Wave.Birkhoff.LieReal
public import KAM.Wave.Birkhoff.LieSympl

/-!
# The trilinear map of the Lie series (blueprint-W `bpW:w3:lie-coeff`, `bpW:w3:flow`)

Package W3-FLOW, blueprint labels `bpW:w3:lie-coeff`, `bpW:w3:flow`.

`birkT = ι ∘ S : 𝔚³ → 𝔚` where `S = 4∇𝔉 : 𝔚³ → 𝔚⁺` and `ι` is the embedding of `𝔚⁺` in `𝔚`.
It is symmetric (`birkT_perm`), real (`birkT_rho`), bounded by `C_F` (`norm_birkT_le`, with
`C_F > 0`, `birkCF_pos`), and `Ω(T(ξ,y,y),η)` is symmetric in `(ξ,η)` (`birkT_omega_symm`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include hp in
theorem waveCubicConst_pos : 0 < waveCubicConst p := by
  unfold waveCubicConst waveAlgConst
  have hs : (1 / 2 : ℝ) < p + 1 / 2 := by linarith
  have h := wave_jap_hasSum_zeta hs
  have h0 : 0 < waveJap 0 ^ (-(2 * (p + 1 / 2))) :=
    Real.rpow_pos_of_pos (waveJap_pos 0) _
  have hS : 0 < 1 + 2 * (riemannZeta ((2 * (p + 1 / 2) : ℝ) : ℂ)).re :=
    lt_of_lt_of_le h0 (le_hasSum h 0 fun l _ => (Real.rpow_pos_of_pos (waveJap_pos l) _).le)
  positivity

include hm hp in
theorem birkCF_pos : 0 < birkCF m p := by
  unfold birkCF
  exact div_pos (waveCubicConst_pos hp) (birkDeltaStar_pos m hm)

/-- `T = ι ∘ S : 𝔚³ → 𝔚`. -/
def birkT : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace :=
  (birkEmbed a (p + 1) p (by linarith)).compContinuousMultilinearMap (birkS m hm ha hp)

theorem birkT_apply (w : Fin 3 → BirkSpace) :
    birkT m hm ha hp w = birkEmbed a (p + 1) p (by linarith) (birkS m hm ha hp w) := rfl

theorem norm_birkT_le (w : Fin 3 → BirkSpace) :
    ‖birkT m hm ha hp w‖ ≤ birkCF m p * ∏ t, ‖w t‖ := by
  rw [birkT_apply]
  refine ((birkEmbed a (p + 1) p (by linarith)).le_opNorm _).trans ?_
  calc ‖birkEmbed a (p + 1) p (by linarith)‖ * ‖birkS m hm ha hp w‖
      ≤ 1 * ‖birkS m hm ha hp w‖ :=
        mul_le_mul_of_nonneg_right (norm_birkEmbed_le _ _ _ _) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact norm_birkS_le m hm ha hp w

theorem birkT_perm (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → BirkSpace) :
    birkT m hm ha hp (fun i => w (σ i)) = birkT m hm ha hp w := by
  rw [birkT_apply, birkT_apply, birkS_perm]

theorem birkT_rho (w : Fin 3 → BirkSpace) :
    birkT m hm ha hp (fun i => birkRho (w i)) = birkRho (birkT m hm ha hp w) := by
  rw [birkT_apply, birkT_apply, birkS_rho, birkRho_birkEmbed]

theorem birkT_omega_symm (y ξ η : BirkSpace) :
    birkOmega ha (by linarith : 0 ≤ p) (birkT m hm ha hp ![ξ, y, y]) η =
      birkOmega ha (by linarith : 0 ≤ p) (birkT m hm ha hp ![η, y, y]) ξ := by
  have h : ∀ u v : BirkSpace, birkOmega ha (by linarith : 0 ≤ p) (birkT m hm ha hp ![u, y, y]) v =
      4 * birkFform m hm ha hp ![u, y, y, v] := fun u v => by
    have := birkS_pairing m hm ha hp ![u, y, y] v
    rw [birkT_apply]
    unfold birkOmegaPlus at this
    rw [this]
    congr 2
    funext i; fin_cases i <;> rfl
  rw [h, h]
  congr 1
  have hs := (birkF_isSmoothing m hm ha hp).symm (Equiv.swap (0 : Fin 4) 3) ![ξ, y, y, η]
  rw [← hs]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

end KAM.Wave

end
