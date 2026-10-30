/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Transport
public import KAM.Wave.Normal.Analysis.PdeBase

/-!
# Bridges between `WaveEll` and the landed `KAM.Wave.Seq` transport API
(blueprint `bpW:w0:ellap`, `bpW:w1:transport`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For real sequences, `KAM.Wave.WaveEll a p c` is `KAM.Wave.IsEll a p c`
(`KAM.Wave.waveEll_iff_isEll`), `KAM.Wave.waveEllNorm` is `KAM.Wave.ellNorm`
(`KAM.Wave.waveEllNorm_eq_ellNorm`) and `KAM.Wave.waveEllToLp` is `KAM.Wave.tauLp`
(`KAM.Wave.waveEllToLp_eq_tauLp`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

theorem waveEll_iff_isEll (a p : ℝ) (c : ℕ+ → ℝ) : WaveEll a p c ↔ IsEll a p c := by
  constructor
  · intro h; simpa [IsEll] using memℓp_two_of_waveEll h
  · intro h
    have h' : Memℓp (fun j => ellWeight a p j * c j) 2 := by simpa [IsEll] using h
    have := (memℓp_gen_iff (by simp : 0 < (2 : ENNReal).toReal)).1 h'
    refine this.congr fun j => ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, mul_pow, sq_abs]

theorem waveEllNorm_eq_ellNorm {a p : ℝ} {c : ℕ+ → ℝ} (h : IsEll a p c) :
    waveEllNorm a p c = ellNorm a p c h := by
  rw [ellNorm_eq_ellTsumNorm, ellTsumNorm, ellTsumSq, waveEllNorm]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]

theorem waveEllToLp_eq_tauLp {a p : ℝ} {c : ℕ+ → ℝ} (h : IsEll a p c) :
    waveEllToLp a p c = tauLp a p c h := by
  have hw := (waveEll_iff_isEll a p c).2 h
  ext j
  rw [waveEllToLp_apply hw]
  simp

theorem coeff_isEll_one_one (y : lp (fun _ : ℕ+ => ℝ) 2) : IsEll 1 1 (coeff y) := by
  rw [← coeffW_one_one]; exact isEll_coeffW 1 1 y

end KAM.Wave

end
