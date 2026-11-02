/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.TriML
public import KAM.Wave.Analytic.ComplexificationCommute
public import KAM.Wave.Seq.Embed
public import KAM.Wave.Normal.Analysis.SeqBridge

/-!
# Real structure, compatibility and the frozen identification of `𝒯^{a,p}`
(blueprint `bpW:w1:trilinear` (ii)–(iv))

* (ii) `KAM.Wave.waveTriML_complexify`, `KAM.Wave.waveTriML_conj`: `𝒯_ℂ(ι y, ι y', ι y'') =
  ι 𝒯_ℝ(y,y',y'')` and `conj 𝒯_ℂ(z,z',z'') = 𝒯_ℂ(conj z, conj z', conj z'')`;
* (iii) `KAM.Wave.waveTriML_embed`: compatibility with the inclusions `ℓ^{a,p} ⊂ ℓ^{a',p'}`;
* (iv) `KAM.Wave.waveCubic_coeffW_eq_coeffW_triML`: `𝒢(κ_{a,p} y) = κ_{a,p+1} 𝒯^{a,p}_ℝ(y,y,y)`
  for `a > 0`, and `KAM.Wave.cubicGrad_eq_triML_div`: the frozen identification
  `cubicGrad y l = 𝒯^{1,1}_ℝ(y,y,y)_l / ω_{1,2}(l)`. The link to the older real trilinear map is
  `KAM.Wave.waveTrilinear_eq_waveTriSeq`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `T` over `ℝ` is the landed real trilinear map `waveTrilinear`. -/
theorem waveTrilinear_eq_waveTriSeq (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm q q' q'' l = waveTriSeq (K := ℝ) m hm q q' q'' l := by
  unfold waveTrilinear waveTriSeq waveSelSum
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  have h1 := wave_sqrt_lam_pos m hm t.1
  have h2 := wave_sqrt_lam_pos m hm t.2.1
  have h3 := wave_sqrt_lam_pos m hm t.2.2
  have h4 := wave_sqrt_lam_pos m hm l
  unfold waveTriCoef waveHat
  simp only [RCLike.ofReal_real_eq_id, id]
  field_simp

/-- (ii): coordinates of `T` commute with the inclusion `ι : ℓ²_ℝ → ℓ²_ℂ`. -/
theorem waveTriSeq_ofReal (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTriSeq (K := ℂ) m hm (fun j => (q j : ℂ)) (fun j => (q' j : ℂ)) (fun j => (q'' j : ℂ)) l =
      ((waveTriSeq (K := ℝ) m hm q q' q'' l : ℝ) : ℂ) := by
  unfold waveTriSeq waveSelSum
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun t => ?_
  simp only [RCLike.ofReal_real_eq_id, id, Complex.ofReal_mul]
  rfl

/-- (ii): coordinates of `T` commute with coordinatewise conjugation. -/
theorem waveTriSeq_conj (q q' q'' : ℕ+ → ℂ) (l : ℕ+) :
    waveTriSeq (K := ℂ) m hm (fun j => starRingEnd ℂ (q j)) (fun j => starRingEnd ℂ (q' j))
        (fun j => starRingEnd ℂ (q'' j)) l =
      starRingEnd ℂ (waveTriSeq (K := ℂ) m hm q q' q'' l) := by
  unfold waveTriSeq waveSelSum
  rw [Complex.conj_tsum]
  refine tsum_congr fun t => ?_
  simp only [map_mul, RCLike.conj_ofReal]

/-- `bpW:w1:trilinear` (ii): `𝒯_ℂ(ι y, ι y', ι y'') = ι 𝒯_ℝ(y, y', y'')`. -/
theorem waveTriML_complexify (y y' y'' : lp (fun _ : ℕ+ => ℝ) 2) :
    waveTriML (K := ℂ) m hm ha hp ![complexifyLp y, complexifyLp y', complexifyLp y''] =
      complexifyLp (waveTriML (K := ℝ) m hm ha hp ![y, y', y'']) := by
  refine coeffW_injective a (p + 1) (funext fun l => ?_)
  rw [coeffW_waveTriML, coeffW_complexifyLp, coeffW_waveTriML]
  have e := waveTriSeq_ofReal m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'') l
  have h1 : ∀ w : lp (fun _ : ℕ+ => ℝ) 2, coeffW (K := ℂ) a p (complexifyLp w) =
      fun j => ((coeffW (K := ℝ) a p w j : ℝ) : ℂ) := fun w => funext (coeffW_complexifyLp a p w)
  rw [h1, h1, h1]
  exact e

/-- `bpW:w1:trilinear` (ii): `conj 𝒯_ℂ(z, z', z'') = 𝒯_ℂ(conj z, conj z', conj z'')`. -/
theorem waveTriML_conj (z z' z'' : lp (fun _ : ℕ+ => ℂ) 2) :
    conjLp (waveTriML (K := ℂ) m hm ha hp ![z, z', z'']) =
      waveTriML (K := ℂ) m hm ha hp ![conjLp z, conjLp z', conjLp z''] := by
  refine coeffW_injective a (p + 1) (funext fun l => ?_)
  rw [coeffW_waveTriML, coeffW_conjLp, coeffW_waveTriML]
  have h1 : ∀ w : lp (fun _ : ℕ+ => ℂ) 2, coeffW (K := ℂ) a p (conjLp w) =
      fun j => starRingEnd ℂ (coeffW (K := ℂ) a p w j) := fun w => funext (coeffW_conjLp a p w)
  rw [h1, h1, h1]
  exact (waveTriSeq_conj m hm _ _ _ l).symm

/-- `bpW:w1:trilinear` (iii): compatibility with the inclusions
`ℓ^{a,p} ⊂ ℓ^{a',p'}`, `ℓ^{a,p+1} ⊂ ℓ^{a',p'+1}`. -/
theorem waveTriML_embed {K : Type*} [RCLike K] {a' p' : ℝ} (ha' : 0 ≤ a') (hp' : 1 / 2 ≤ p')
    (haa : a' ≤ a) (hpp : p' ≤ p) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha' hp'
        ![embedCLM a p a' p' haa hpp y, embedCLM a p a' p' haa hpp y',
          embedCLM a p a' p' haa hpp y''] =
      embedCLM a (p + 1) a' (p' + 1) haa (by linarith)
        (waveTriML (K := K) m hm ha hp ![y, y', y'']) := by
  refine coeffW_injective a' (p' + 1) ?_
  rw [coeffW_waveTriML, coeffW_embedCLM, coeffW_embedCLM, coeffW_embedCLM, coeffW_embedCLM,
    coeffW_waveTriML]

/-- `bpW:w1:trilinear` (iv): for `a > 0`, `𝒢(κ_{a,p} y) = κ_{a,p+1} 𝒯^{a,p}_ℝ(y,y,y)`. -/
theorem waveCubic_coeffW_eq_coeffW_triML (ha' : 0 < a) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    waveCubic m hm (coeffW a p y) =
      coeffW a (p + 1) (waveTriML (K := ℝ) m hm ha'.le hp ![y, y, y]) := by
  rw [coeffW_waveTriML]
  funext l
  rw [waveCubic_eq_trilinear m hm ha' ((waveEll_iff_isEll a p _).2 (isEll_coeffW a p y)) l,
    waveTrilinear_eq_waveTriSeq]

/-- `bpW:w1:trilinear` (iv), frozen identification:
`cubicGrad m hm y l = 𝒯^{1,1}_ℝ(y,y,y)_l / ω_{1,2}(l)`. -/
theorem cubicGrad_eq_triML_div (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    cubicGrad m hm y l =
      waveTriML (K := ℝ) m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) ![y, y, y] l /
        ellWeight 1 2 l := by
  have h := congrFun (waveCubic_coeffW_eq_coeffW_triML m hm (a := 1) (p := 1)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) one_pos y) l
  rw [coeffW_one_one] at h
  have e : (1 : ℝ) + 1 = 2 := by norm_num
  rw [e] at h
  rw [cubicGrad_eq_waveCubic, h]
  simp [coeffW]

end KAM.Wave

end
