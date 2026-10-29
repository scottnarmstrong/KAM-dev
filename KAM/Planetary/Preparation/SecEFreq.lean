/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SecESource

/-!
# The frequency map of Step E (`bpP:p11:sec-E#data`, package P-SEC)

For the chosen slow datum and every point `I` of the action polydisc `{|r|<2, |ρ'|<π/2}` of `E`:

* `P11SlowSpecOf.preparedFreq_eq`: `ω̂_ε = ∇_{(r,ρ')} N_ε = (∂_J h, ∂_ρ̃ h)(A_ε(r, ρ'))`, `h = h₀ + g₂`;
* `P11SlowSpecOf.Z_eq_source`: the correction `Ẑ` of the datum is `Ĝ₀ - C - Σ Ω̃ ρ̃` on `V₂`;
* `P11SlowSpecOf.freq_source`: `ω̂_ε = (ω̂^{(1)}, ε ω̂^{(2)})` with
  `ω̂^{(1)} = ω + ε ∂_J Ĝ₀ + ∂_J g₂` and `ω̂^{(2)} = Ω̃ + ∂_ρ̃ Ẑ + ε⁻¹ ∂_ρ̃ g₂` (`Ω̃ = Ω/2π`).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped BigOperators Topology
namespace KAM.Planetary

section SecEFreq

variable {n : ℕ} {C : P11SecularData n} {Fast : P11FastData n} {nu eps c : ℝ}
  {A : P11SlowData n}

/-- The chosen datum's correction is the source one: `C + Σ Ω̃ ρ̃ + Ẑ = Ĝ₀` on `V₂`. -/
theorem P11SlowSpecOf.Z_eq_source (hA : P11SlowSpecOf C Fast nu eps c A) (heps : eps ≠ 0)
    {I : P11CVec (n + n)}
    (hI : I ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :
    p11SlowSec C I + A.Z I = p11GHat0 Fast (p11SlowJ I) (p11SlowR I) := by
  have h2 := hA.2.1 I hI
  have h3 := hA.2.2.1 I hI
  rw [h2] at h3
  have he : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps
  have h := mul_left_cancel₀ he (add_left_cancel h3)
  exact h.symm

/-- The slow-block projection `I ↦ J` as a continuous linear map. -/
def p11SlowJL (n : ℕ) : P11CVec (n + n) →L[ℂ] P11CVec n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd n i)

theorem p11SlowJL_apply (I : P11CVec (n + n)) : p11SlowJL n I = p11SlowJ I := rfl

theorem p11SlowJL_single_castAdd (i : Fin n) :
    p11SlowJL n (Pi.single (Fin.castAdd n i) 1) = Pi.single i 1 := by
  funext k
  simp [p11SlowJL, Pi.single_apply]

theorem p11SlowJL_single_natAdd (i : Fin n) :
    p11SlowJL n (Pi.single (Fin.natAdd n i) 1) = 0 := by
  funext k
  simp [p11SlowJL, Pi.single_apply, (p11_natAdd_ne_castAdd i k).symm]

/-- `ω̂_ε = ∇N_ε = (∇h)(A_ε)` with `h = h₀ + g₂`, on the whole polydisc of `E`. -/
theorem P11SlowSpecOf.preparedFreq_eq (hA : P11SlowSpecOf C Fast nu eps c A) (heps : 0 < eps)
    (h2 : 2 * eps ≤ p11s2 C nu eps / 2) (W : P11Vec (n + n) → P11Vec (n + n))
    {I : P11CVec (n + n)} (hI : I ∈ p11SecEPolydisc n) :
    p11PreparedFreq (p11PreparedCoreOf C Fast A eps W) I =
      fun i => fderiv ℂ (A.h0 + A.g2) (p11Rescale C.J0 eps (0, I)).2 (Pi.single i 1) := by
  obtain ⟨-, -, -, -, -, -, hdh0, hdg2, -⟩ := hA
  set y := (p11Rescale C.J0 eps (0, I)).2 with hy_def
  have hy : y ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) :=
    p11Rescale_mem_half C heps (z := (0, I)) h2 hI
  have hpe : 0 ≤ Real.pi * eps := by positivity
  have hyV : y ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps) :=
    ⟨fun i => (hy.1 i).trans_le (by linarith), fun i => (hy.2 i).trans_le (by linarith)⟩
  have hd0 : DifferentiableAt ℂ A.h0 y := hdh0.differentiableAt ((p11Box_isOpen _ _ _).mem_nhds hyV)
  have hd2 : DifferentiableAt ℂ A.g2 y := hdg2.differentiableAt ((p11Box_isOpen _ _ _).mem_nhds hy)
  have hh : HasFDerivAt (A.h0 + A.g2) (fderiv ℂ (A.h0 + A.g2) y) y := (hd0.add hd2).hasFDerivAt
  have hg : HasFDerivAt (fun J : P11CVec (n + n) => (p11Rescale C.J0 eps (0, J)).2)
      ((eps : ℂ) • ContinuousLinearMap.id ℂ (P11CVec (n + n))) I := by
    have : (fun J : P11CVec (n + n) => (p11Rescale C.J0 eps (0, J)).2) = fun J =>
        Fin.append (KAM.realInclusion n C.J0) (p11RhoTilde0 n eps) + (eps : ℂ) • J :=
      funext fun J => p11Rescale_snd C.J0 eps (0, J)
    rw [this]
    exact ((hasFDerivAt_id I).const_smul (eps : ℂ)).const_add _
  have hcomp := (hh.comp I hg).mul_const ((eps : ℂ)⁻¹)
  have hN : (p11PreparedCoreOf C Fast A eps W).N = fun J =>
      ((A.h0 + A.g2) ∘ fun J : P11CVec (n + n) => (p11Rescale C.J0 eps (0, J)).2) J *
        (eps : ℂ)⁻¹ := by
    funext J
    simp [p11PreparedCoreOf, div_eq_mul_inv]
  have he : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps.ne'
  funext i
  simp only [p11PreparedFreq]
  rw [hN, hcomp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  field_simp

variable {D : P11Physical n}

/-- The normalized source formulas: `ω̂_ε = (ω̂^{(1)}, ε ω̂^{(2)})`,
`ω̂^{(1)} = ω + ε ∂_J Ĝ₀ + ∂_J g₂`, `ω̂^{(2)} = Ω̃ + ∂_ρ̃ Ẑ + ε⁻¹ ∂_ρ̃ g₂`, arguments
`A_ε(r, ρ')`, on the whole polydisc of `E`. -/
theorem P11SlowSpecOf.freq_source (hC : P11SecularSpec D C)
    (hA : P11SlowSpecOf C Fast nu eps c A) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 64 * eps < C.rz ^ 2) (h2 : 2 * eps ≤ p11s2 C nu eps / 2)
    (W : P11Vec (n + n) → P11Vec (n + n)) {I : P11CVec (n + n)} (hI : I ∈ p11SecEPolydisc n)
    (i : Fin n) :
    let y := (p11Rescale C.J0 eps (0, I)).2
    p11PreparedFreq (p11PreparedCoreOf C Fast A eps W) I (Fin.castAdd n i) =
        C.omega (p11SlowJ y) i +
          eps * fderiv ℂ (fun w => p11GHat0 Fast (p11SlowJ w) (p11SlowR w)) y
            (Pi.single (Fin.castAdd n i) 1) +
          fderiv ℂ A.g2 y (Pi.single (Fin.castAdd n i) 1) ∧
      p11PreparedFreq (p11PreparedCoreOf C Fast A eps W) I (Fin.natAdd n i) =
        eps * (C.Omega (p11SlowJ y) i / (2 * Real.pi) +
          fderiv ℂ A.Z y (Pi.single (Fin.natAdd n i) 1) +
          (eps : ℂ)⁻¹ * fderiv ℂ A.g2 y (Pi.single (Fin.natAdd n i) 1)) := by
  intro y
  have hfreq := hA.preparedFreq_eq heps h2 W hI
  obtain ⟨-, hav, hsec, hdZ, -, -, hdh0, hdg2, -⟩ := hA
  obtain ⟨-, -, -, -, -, hdh, homega, -⟩ := hC
  have hs1 := p11s1_pos hC heps hεM
  have hrC := p11s1_le C eps
  have hs2 : p11s2 C nu eps ≤ p11s1 C eps / 4 := min_le_left _ _
  have hy : y ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) :=
    p11Rescale_mem_half C heps (z := (0, I)) h2 hI
  have hpe : 0 < Real.pi * eps := by positivity
  have hyV : y ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps) :=
    ⟨fun i => (hy.1 i).trans_le (by linarith), fun i => (hy.2 i).trans_le (by linarith)⟩
  have hVn : p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps) ∈ 𝓝 y :=
    (p11Box_isOpen _ _ _).mem_nhds hyV
  have hd0 : DifferentiableAt ℂ A.h0 y := hdh0.differentiableAt hVn
  have hd2 : DifferentiableAt ℂ A.g2 y := hdg2.differentiableAt ((p11Box_isOpen _ _ _).mem_nhds hy)
  have he : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps.ne'
  -- the slow action of `y` lies in the ball where `h̃` is holomorphic
  have hJ : ‖p11SlowJ y - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 2 := by
    refine (pi_norm_lt_iff (by linarith)).2 fun k => ?_
    have := hy.1 k
    simpa [p11SlowJ, p11SlowCenter, Fin.append_left] using this
  have hJb : p11SlowJ y ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hdh' : DifferentiableAt ℂ C.h (p11SlowJ y) :=
    hdh.differentiableAt (isOpen_ball.mem_nhds hJb)
  set Hh : P11CVec (n + n) → ℂ := fun w => C.h (p11SlowJ w) with hHh
  have hHh_fd : HasFDerivAt Hh ((fderiv ℂ C.h (p11SlowJ y)).comp (p11SlowJL n)) y :=
    hdh'.hasFDerivAt.comp y (p11SlowJL n).hasFDerivAt
  have hdHh : DifferentiableAt ℂ Hh y := hHh_fd.differentiableAt
  -- full gradient of `h = h₀ + g₂` splits
  have hsplit : ∀ e, fderiv ℂ (A.h0 + A.g2) y e = fderiv ℂ A.h0 y e + fderiv ℂ A.g2 y e :=
    fun e => by rw [fderiv_add hd0 hd2]; rfl
  refine ⟨?_, ?_⟩
  · -- `∂_J h₀ = ω + ε ∂_J Ĝ₀`
    set G0f : P11CVec (n + n) → ℂ := fun w => p11GHat0 Fast (p11SlowJ w) (p11SlowR w)
    have hev : A.h0 =ᶠ[𝓝 y] fun w => Hh w + eps * G0f w :=
      Filter.eventually_of_mem hVn fun w hw => hav w hw
    have hevG : G0f =ᶠ[𝓝 y] fun w => (A.h0 w - Hh w) * (eps : ℂ)⁻¹ :=
      Filter.eventually_of_mem hVn fun w hw => by
        simp only [hav w hw]; field_simp; ring
    have hdG : DifferentiableAt ℂ G0f y :=
      ((hd0.sub hdHh).mul_const _).congr_of_eventuallyEq hevG
    rw [hfreq, hsplit, hev.fderiv_eq, fderiv_add hdHh (hdG.const_mul _), fderiv_const_mul hdG,
      hHh_fd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, p11SlowJL_single_castAdd]
    rw [homega _ hJb]
  · -- `∂_ρ̃ h₀ = ε (Ω̃ + ∂_ρ̃ Ẑ)`
    set T : P11CVec (n + n) → ℂ := fun w => p11SlowSec C w + A.Z w
    have hev : A.h0 =ᶠ[𝓝 y] fun w => Hh w + eps * T w :=
      Filter.eventually_of_mem hVn fun w hw => hsec w hw
    have hevT : T =ᶠ[𝓝 y] fun w => (A.h0 w - Hh w) * (eps : ℂ)⁻¹ :=
      Filter.eventually_of_mem hVn fun w hw => by
        simp only [hsec w hw]; field_simp; ring
    have hdT : DifferentiableAt ℂ T y :=
      ((hd0.sub hdHh).mul_const _).congr_of_eventuallyEq hevT
    -- `Ẑ` is holomorphic at `y`
    have hZdom : IsOpen {I : P11CVec (n + n) |
        ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 ∧
        ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} :=
      (isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const)
    have hyZ : ‖(fun i : Fin n => y (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ <
        p11s1 C eps / 2 ∧ ‖(fun i : Fin n => y (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16 := by
      refine ⟨by have := hJ; simp only [p11SlowJ] at this; linarith, ?_⟩
      have h48 : 3 * (Real.pi * eps) < Real.pi * C.rz ^ 2 / 16 := by nlinarith [Real.pi_pos]
      refine (pi_norm_lt_iff (by positivity)).2 fun k => ?_
      have h := hy.2 k
      simp only [p11SlowCenter, Fin.append_right] at h
      have hle := norm_le_norm_sub_add (y (Fin.natAdd n k)) (2 * Real.pi * eps : ℂ)
      have h2n : ‖(2 * Real.pi * eps : ℂ)‖ = 2 * Real.pi * eps := by
        rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hdZy : DifferentiableAt ℂ A.Z y := hdZ.differentiableAt (hZdom.mem_nhds hyZ)
    have hdS : DifferentiableAt ℂ (p11SlowSec C) y := by
      have : p11SlowSec C = fun w => T w - A.Z w := by funext w; simp [T]
      rw [this]; exact hdT.sub hdZy
    -- `∂_ρ̃_i (C + Σ Ω̃ ρ̃) = Ω̃_i` along the line `y + t e`
    set e : P11CVec (n + n) := Pi.single (Fin.natAdd n i) 1
    have hcast : ∀ (t : ℂ) (k : Fin n), (y + t • e) (Fin.castAdd n k) = y (Fin.castAdd n k) :=
      fun t k => by simp [e, Pi.single_apply, (p11_natAdd_ne_castAdd i k).symm]
    have hnat : ∀ (t : ℂ) (k : Fin n),
        (y + t • e) (Fin.natAdd n k) = y (Fin.natAdd n k) + if k = i then t else 0 :=
      fun t k => by by_cases hk : k = i <;> simp [e, Pi.single_apply, hk]
    have hline : (fun t : ℂ => p11SlowSec C (y + t • e)) =
        fun t => p11SlowSec C y + t * (C.Omega (p11SlowJ y) i / (2 * Real.pi)) := by
      funext t
      simp only [p11SlowSec, hcast, hnat, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, p11SlowJ]
      ring
    have hl : HasDerivAt (fun t : ℂ => y + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add y
    have hd1 : HasDerivAt (fun t : ℂ => p11SlowSec C (y + t • e)) (fderiv ℂ (p11SlowSec C) y e) 0 :=
      hdS.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    have hd2' : HasDerivAt (fun t : ℂ => p11SlowSec C (y + t • e))
        (C.Omega (p11SlowJ y) i / (2 * Real.pi)) 0 := by
      rw [hline]
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const
        (C.Omega (p11SlowJ y) i / (2 * Real.pi))).const_add (p11SlowSec C y)
    have hSe := hd1.unique hd2'
    have hT : fderiv ℂ T y e = fderiv ℂ (p11SlowSec C) y e + fderiv ℂ A.Z y e := by
      rw [show T = p11SlowSec C + A.Z from rfl, fderiv_add hdS hdZy]; rfl
    rw [hfreq, hsplit, hev.fderiv_eq, fderiv_add hdHh (hdT.const_mul _), fderiv_const_mul hdT,
      hHh_fd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, p11SlowJL_single_natAdd, map_zero]
    rw [hT, hSe]
    field_simp

end SecEFreq

end KAM.Planetary

end
