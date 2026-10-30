/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import KAM.Wave.Normal.Analysis.SineSeries
public import KAM.Frozen.Wave.Defs.CubicGrad

/-!
# Products of sine series and the integrals `∫ U^3 φ_l`, `∫ U^4`
(blueprint `bpW:w0n:gradient`, first two formulas)

Infrastructure used by several nodes; the dependency graph is still being built.

Let `h : ℕ+ → ℝ` be absolutely summable and `U(x) = Σ_j h_j φ_j(x)`
(`KAM.Wave.waveSineSeries 0 h`). With `g_{ijkl} = ∫₀^π φ_i φ_j φ_k φ_l`
(`KAM.Wave.waveQuartic`):

* `KAM.Wave.hasSum_integral_cube_mul_sineMode`:
  `∫₀^π U^3 φ_l = Σ_{i,j,k} g_{ijkl} h_i h_j h_k`, absolutely convergent;
* `KAM.Wave.hasSum_integral_fourth_pow`: `∫₀^π U^4 = Σ_{i,j,k,l} g_{ijkl} h_i h_j h_k h_l`,
  absolutely convergent.

Both are proved by multiplying absolutely convergent series and integrating termwise by
dominated convergence (`KAM.Wave.waveHasSum_intervalIntegral`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The quartic overlap `g_{ijkl} = ∫₀^π φ_i φ_j φ_k φ_l` (blueprint `bpW:w0n:quartic-coeff`). -/
def waveQuartic (i j k l : ℕ+) : ℝ :=
  ∫ x in (0 : ℝ)..π, sineMode i x * sineMode j x * sineMode k x * sineMode l x

lemma wave_abs_sineMode_le (j : ℕ+) (x : ℝ) : |sineMode j x| ≤ Real.sqrt (2 / π) := by
  have := wave_abs_sineModeIter_le 0 j x
  simpa [sineModeIter_zero] using this

lemma wave_continuous_sineMode (j : ℕ+) : Continuous (sineMode j) := by
  unfold sineMode; fun_prop

lemma wave_sqrt_two_div_pi_sq : Real.sqrt (2 / π) ^ 2 = 2 / π :=
  Real.sq_sqrt (by positivity)

/-- `|g_{ijkl}| ≤ 4/π`. -/
lemma abs_waveQuartic_le (i j k l : ℕ+) : |waveQuartic i j k l| ≤ 4 / π := by
  have hpi := Real.pi_pos
  unfold waveQuartic
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (C := (Real.sqrt (2 / π)) ^ 4)
    (f := fun x => sineMode i x * sineMode j x * sineMode k x * sineMode l x) (fun x _ => by
      simp only [Real.norm_eq_abs, abs_mul]
      have h1 := wave_abs_sineMode_le i x
      have h2 := wave_abs_sineMode_le j x
      have h3 := wave_abs_sineMode_le k x
      have h4 := wave_abs_sineMode_le l x
      calc _ ≤ Real.sqrt (2 / π) * Real.sqrt (2 / π) * Real.sqrt (2 / π) * Real.sqrt (2 / π) := by
            gcongr
        _ = _ := by ring)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have h4 : Real.sqrt (2 / π) ^ 4 = (2 / π) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, wave_sqrt_two_div_pi_sq]
  rw [h4, sub_zero, abs_of_pos hpi]
  apply le_of_eq
  field_simp
  norm_num

/-- Products of two absolutely summable families. -/
lemma waveHasSum_mul_abs {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ} {s t : ℝ}
    (hf : HasSum f s) (hfa : Summable fun i => |f i|) (hg : HasSum g t)
    (hga : Summable fun j => |g j|) :
    HasSum (fun x : ι × κ => f x.1 * g x.2) (s * t) ∧
      Summable fun x : ι × κ => |f x.1 * g x.2| := by
  have hfa' : Summable fun i => ‖f i‖ := hfa
  have hga' : Summable fun j => ‖g j‖ := hga
  refine ⟨hf.mul hg (summable_mul_of_summable_norm hfa' hga'), ?_⟩
  have := hfa'.mul_norm hga'
  refine this.congr fun x => ?_
  simp [abs_mul]

lemma waveHasSum_cube {ι : Type*} {f : ι → ℝ} {s : ℝ} (hf : HasSum f s)
    (hfa : Summable fun i => |f i|) :
    HasSum (fun x : ι × ι × ι => f x.1 * (f x.2.1 * f x.2.2)) (s * (s * s)) ∧
      Summable fun x : ι × ι × ι => |f x.1 * (f x.2.1 * f x.2.2)| := by
  have h2 := waveHasSum_mul_abs hf hfa hf hfa
  exact waveHasSum_mul_abs hf hfa h2.1 h2.2

lemma waveHasSum_fourth {ι : Type*} {f : ι → ℝ} {s : ℝ} (hf : HasSum f s)
    (hfa : Summable fun i => |f i|) :
    HasSum (fun x : ι × ι × ι × ι => f x.1 * (f x.2.1 * (f x.2.2.1 * f x.2.2.2)))
        (s * (s * (s * s))) ∧
      Summable fun x : ι × ι × ι × ι => |f x.1 * (f x.2.1 * (f x.2.2.1 * f x.2.2.2))| := by
  have h3 := waveHasSum_cube hf hfa
  exact waveHasSum_mul_abs hf hfa h3.1 h3.2

section Core

variable {h : ℕ+ → ℝ}

lemma wave_summable_abs_mul_sineMode (hh : Summable fun j => |h j|) (x : ℝ) :
    Summable fun j => |h j * sineMode j x| := by
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_) (hh.mul_right (Real.sqrt (2 / π)))
  rw [abs_mul]
  gcongr
  exact wave_abs_sineMode_le j x

lemma hasSum_waveSineSeries_zero (hh : Summable fun j => |h j|) (x : ℝ) :
    HasSum (fun j => h j * sineMode j x) (waveSineSeries 0 h x) := by
  rw [waveSineSeries_zero_eq]
  exact (wave_summable_abs_mul_sineMode hh x).of_abs.hasSum

lemma continuous_waveSineSeries_zero (hh : Summable fun j => |h j|) :
    Continuous (waveSineSeries 0 h) := by
  have : waveSineSeries 0 h = fun x => ∑' j, h j * sineMode j x :=
    funext fun x => waveSineSeries_zero_eq h x
  rw [this]
  refine continuous_tsum (u := fun j => |h j| * Real.sqrt (2 / π))
    (fun j => (wave_continuous_sineMode j).const_mul _) (hh.mul_right _) fun j x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  gcongr
  exact wave_abs_sineMode_le j x

lemma abs_waveSineSeries_zero_le (hh : Summable fun j => |h j|) (x : ℝ) :
    |waveSineSeries 0 h x| ≤ Real.sqrt (2 / π) * ∑' j, |h j| := by
  have := waveSineSeries_abs_le_of_summable (c := h) (k := 0) (by simpa using hh) x
  simpa using this

/-- `∫₀^π U^3 φ_l = Σ_{i,j,k} g_{ijkl} h_i h_j h_k`, absolutely convergent
(`bpW:w0n:gradient`). -/
theorem hasSum_integral_cube_mul_sineMode (hh : Summable fun j => |h j|) (l : ℕ+) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ => (h t.1 * (h t.2.1 * h t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l)
      (∫ x in (0 : ℝ)..π, waveSineSeries 0 h x ^ 3 * sineMode l x) := by
  have hpi := Real.pi_pos
  set K := Real.sqrt (2 / π) with hK
  have hcube := waveHasSum_cube (hasSum_waveSineSeries_zero hh 0) (wave_summable_abs_mul_sineMode hh 0)
  have hcube0 := waveHasSum_cube hh.of_abs.hasSum hh
  have hb : Summable fun t : ℕ+ × ℕ+ × ℕ+ => |h t.1 * (h t.2.1 * h t.2.2)| * K ^ 4 :=
    hcube0.2.mul_right _
  have hs := waveHasSum_intervalIntegral (ι := ℕ+ × ℕ+ × ℕ+)
    (F := fun t x => (h t.1 * sineMode t.1 x * (h t.2.1 * sineMode t.2.1 x *
        (h t.2.2 * sineMode t.2.2 x))) * sineMode l x)
    (f := fun x => waveSineSeries 0 h x ^ 3 * sineMode l x) 0 π
    (b := fun t => |h t.1 * (h t.2.1 * h t.2.2)| * K ^ 4)
    (fun t => by
      have := wave_continuous_sineMode t.1; have := wave_continuous_sineMode t.2.1
      have := wave_continuous_sineMode t.2.2; have := wave_continuous_sineMode l
      fun_prop)
    hb
    (fun t x => by
      have h1 := wave_abs_sineMode_le t.1 x
      have h2 := wave_abs_sineMode_le t.2.1 x
      have h3 := wave_abs_sineMode_le t.2.2 x
      have h4 := wave_abs_sineMode_le l x
      simp only [abs_mul]
      calc |h t.1| * |sineMode t.1 x| * (|h t.2.1| * |sineMode t.2.1 x| *
            (|h t.2.2| * |sineMode t.2.2 x|)) * |sineMode l x|
          ≤ |h t.1| * K * (|h t.2.1| * K * (|h t.2.2| * K)) * K := by gcongr
        _ = _ := by ring)
    (fun x => by
      have := (waveHasSum_cube (hasSum_waveSineSeries_zero hh x)
        (wave_summable_abs_mul_sineMode hh x)).1.mul_right (sineMode l x)
      convert this using 1
      ring)
  have e : (fun t : ℕ+ × ℕ+ × ℕ+ => ∫ x in (0 : ℝ)..π, (h t.1 * sineMode t.1 x *
        (h t.2.1 * sineMode t.2.1 x * (h t.2.2 * sineMode t.2.2 x))) * sineMode l x) =
      fun t => (h t.1 * (h t.2.1 * h t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l := by
    funext t
    unfold waveQuartic
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [e] at hs
  exact hs

/-- The absolute convergence of the series of `hasSum_integral_cube_mul_sineMode`. -/
theorem summable_abs_cube_terms (hh : Summable fun j => |h j|) (l : ℕ+) :
    Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
      |(h t.1 * (h t.2.1 * h t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l| := by
  have hcube0 := waveHasSum_cube hh.of_abs.hasSum hh
  refine Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_)
    (hcube0.2.mul_right (4 / π))
  rw [abs_mul]
  gcongr
  exact abs_waveQuartic_le _ _ _ _

/-- `∫₀^π U^4 = Σ_{i,j,k,l} g_{ijkl} h_i h_j h_k h_l`, absolutely convergent (`bpW:w0n:gradient`). -/
theorem hasSum_integral_fourth_pow (hh : Summable fun j => |h j|) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ =>
        (h t.1 * (h t.2.1 * (h t.2.2.1 * h t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2)
      (∫ x in (0 : ℝ)..π, waveSineSeries 0 h x ^ 4) := by
  have hpi := Real.pi_pos
  set K := Real.sqrt (2 / π) with hK
  have hq0 := waveHasSum_fourth hh.of_abs.hasSum hh
  have hb : Summable fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ =>
      |h t.1 * (h t.2.1 * (h t.2.2.1 * h t.2.2.2))| * K ^ 4 := hq0.2.mul_right _
  have hs := waveHasSum_intervalIntegral (ι := ℕ+ × ℕ+ × ℕ+ × ℕ+)
    (F := fun t x => h t.1 * sineMode t.1 x * (h t.2.1 * sineMode t.2.1 x *
        (h t.2.2.1 * sineMode t.2.2.1 x * (h t.2.2.2 * sineMode t.2.2.2 x))))
    (f := fun x => waveSineSeries 0 h x ^ 4) 0 π
    (b := fun t => |h t.1 * (h t.2.1 * (h t.2.2.1 * h t.2.2.2))| * K ^ 4)
    (fun t => by
      have := wave_continuous_sineMode t.1; have := wave_continuous_sineMode t.2.1
      have := wave_continuous_sineMode t.2.2.1; have := wave_continuous_sineMode t.2.2.2
      fun_prop)
    hb
    (fun t x => by
      have h1 := wave_abs_sineMode_le t.1 x
      have h2 := wave_abs_sineMode_le t.2.1 x
      have h3 := wave_abs_sineMode_le t.2.2.1 x
      have h4 := wave_abs_sineMode_le t.2.2.2 x
      simp only [abs_mul]
      calc |h t.1| * |sineMode t.1 x| * (|h t.2.1| * |sineMode t.2.1 x| *
            (|h t.2.2.1| * |sineMode t.2.2.1 x| * (|h t.2.2.2| * |sineMode t.2.2.2 x|)))
          ≤ |h t.1| * K * (|h t.2.1| * K * (|h t.2.2.1| * K * (|h t.2.2.2| * K))) := by gcongr
        _ = _ := by ring)
    (fun x => by
      have := (waveHasSum_fourth (hasSum_waveSineSeries_zero hh x)
        (wave_summable_abs_mul_sineMode hh x)).1
      convert this using 1
      ring)
  have e : (fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => ∫ x in (0 : ℝ)..π, h t.1 * sineMode t.1 x *
        (h t.2.1 * sineMode t.2.1 x * (h t.2.2.1 * sineMode t.2.2.1 x *
          (h t.2.2.2 * sineMode t.2.2.2 x)))) =
      fun t => (h t.1 * (h t.2.1 * (h t.2.2.1 * h t.2.2.2))) *
        waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    funext t
    unfold waveQuartic
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [e] at hs
  exact hs

theorem summable_abs_fourth_terms (hh : Summable fun j => |h j|) :
    Summable fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ =>
      |(h t.1 * (h t.2.1 * (h t.2.2.1 * h t.2.2.2))) *
        waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2| := by
  have hq0 := waveHasSum_fourth hh.of_abs.hasSum hh
  refine Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_)
    (hq0.2.mul_right (4 / π))
  rw [abs_mul]
  gcongr
  exact abs_waveQuartic_le _ _ _ _

end Core

end KAM.Wave

end
