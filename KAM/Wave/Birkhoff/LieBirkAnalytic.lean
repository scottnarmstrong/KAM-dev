/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieAnalyticPlus
public import KAM.Wave.Birkhoff.LieBirkPlus

/-!
# Analyticity of the flow of `X_F` (blueprint-W `bpW:w3:flow` (i))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`birkGamma_analyticOnNhd`: for `|t| < 2`, `w ↦ Γ_t(w)` is analytic on `‖w‖ < ρ₀ = (40 C_F)^{-1/2}`;
`birkGamma_sub_analytic`: `Γ_t - id` is analytic as a map `B_{ρ₀} → 𝔚⁺` (a point of `BirkSpace` read
at weight `p + 1`, `ι = birkEmbed`): there is an analytic `ψ` with `ι ψ(w) = Γ_t(w) - w` and
`‖ψ(w)‖₊ ≤ 3|t|C_F‖w‖³`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem norm_birkT_le_cf : ‖birkT m hm ha hp‖ ≤ birkCF m p :=
  ContinuousMultilinearMap.opNorm_le_bound (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)

include hm hp in
/-- (`bpW:w3:flow` (i)) `Γ_t` is analytic on `B_{ρ₀}` for `|t| < 2`. -/
theorem birkGamma_analyticOnNhd (t : ℝ) (ht : |t| < 2) :
    AnalyticOnNhd ℂ (birkGamma m hm ha hp t) {w | 40 * birkCF m p * ‖w‖ ^ 2 < 1} :=
  fun w hw => analyticAt_lieGamma (birkT m hm ha hp) (birkCF_pos m hm hp)
    (norm_birkT_le_cf (ha := ha)) t w ht hw

include hm hp in
/-- (`bpW:w3:flow` (i)) `Γ_t - id` is analytic `B_{ρ₀} → 𝔚⁺`, with `𝔚⁺`-norm
`≤ 3|t|C_F‖w‖³`. -/
theorem birkGamma_sub_analytic (t : ℝ) (ht : |t| < 2) :
    ∃ ψ : BirkSpace → BirkSpace,
      AnalyticOnNhd ℂ ψ {w | 40 * birkCF m p * ‖w‖ ^ 2 < 1} ∧
      ∀ w : BirkSpace, 40 * birkCF m p * ‖w‖ ^ 2 < 1 →
        birkEmbed a (p + 1) p (by linarith) (ψ w) = birkGamma m hm ha hp t w - w ∧
          ‖ψ w‖ ≤ 3 * |t| * birkCF m p * ‖w‖ ^ 3 := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  refine ⟨liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) t, ?_, ?_⟩
  · exact fun w hw => analyticAt_liePsiSum _ _ hCp.le (norm_birkEmbed_le _ _ _ _) hSn hCp t w ht hw
  · intro w hw
    have hq := birk_q_le (hm := hm) (hp := hp) t w ht hw
    refine ⟨map_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
      (norm_birkEmbed_le _ _ _ _) hSn t w hq, ?_⟩
    obtain ⟨ψ, hψ, hψn⟩ := birkGamma_sub_plus (ha := ha) (hm := hm) (hp := hp) t w hq
    have h2 := map_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
      (norm_birkEmbed_le _ _ _ _) hSn t w hq
    have : ψ = liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) t w :=
      birkEmbed_injective a (p + 1) p (by linarith) (hψ.trans h2.symm)
    rw [← this]; exact hψn

end KAM.Wave

end
