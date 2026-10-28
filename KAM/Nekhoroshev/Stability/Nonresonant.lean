/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.NormalForm
public import KAM.Nekhoroshev.Stability.NonresonantAux
public import KAM.Nekhoroshev.Stability.Preimage
public import KAM.Nekhoroshev.Stability.Transfer
public import KAM.Canonical.TransformSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proposition 1: stability for nonresonant frequencies (`bpN:p7:nonresonant`)

Case `κ = 2πKs < 6`: the action drift of an orbit is bounded directly by `ε/(e s)`.
Case `κ ≥ 6`: `normal_form` with `Λ = {0}` gives `Ψ`, `g`, `f_*` with `g` independent of `θ`;
`transfer` (with `Nrm = ‖·‖`, `ϱ = 15r/32`) reduces to the drift of `H' = h + g + f_*`, whose
`θ`-gradient is that of `f_*`, of size `≤ e^{-κ/6} ε/(e s/6)`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {n : ℕ}

private theorem inClass_add' {D : Set (Fin n → ℂ)} {r s : ℝ} {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass D r s u) (hv : InClass D r s v) : InClass D r s (fun w => u w + v w) :=
  ⟨hu.differentiableOn.add hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

private theorem inClass_sub' {D : Set (Fin n → ℂ)} {r s : ℝ} {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass D r s u) (hv : InClass D r s v) : InClass D r s (fun w => u w - v w) :=
  ⟨hu.differentiableOn.sub hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

private theorem realOn_add' {U : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : RealOn U u) (hv : RealOn U v) :
    RealOn U (fun w => u w + v w) := fun x hx => by
  rw [Complex.add_im, hu x hx, hv x hx, add_zero]

private theorem realOn_mono' {U V : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hUV : U ⊆ V)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : RealOn V u) : RealOn U u := fun x hx => hu x (hUV hx)

/-- Time bound times the `θ`-gradient bound, case `κ < 6`. -/
private theorem arith_small {s r ε K t : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hκ : 2 * Real.pi * K * s < 6)
    (ht : |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6)) :
    |t| * (ε / (Real.exp 1 * s)) ≤ r / 2 := by
  have he : Real.exp (2 * Real.pi * K * s / 6) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by linarith)
  have hsr := mul_pos hs hr
  have hep := Real.exp_pos 1
  have h1 : |t| * (5 * ε) ≤ s * r * Real.exp 1 := ht.trans (by gcongr)
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hsr hep]

/-- Time bound times the `θ`-gradient bound, case `κ ≥ 6`. -/
private theorem arith_large {s r ε K t : ℝ} (hs : 0 < s) (hr : 0 < r)
    (ht : |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6)) :
    |t| * (Real.exp (-(2 * Real.pi * K * s) / 6) * ε / (Real.exp 1 * (s / 6))) <
      15 * r / 32 := by
  have hEE : Real.exp (-(2 * Real.pi * K * s) / 6) * Real.exp (2 * Real.pi * K * s / 6) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hEm : 0 < Real.exp (-(2 * Real.pi * K * s) / 6) := Real.exp_pos _
  have h1 : |t| * (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) ≤ s * r / 5 := by
    have := mul_le_mul_of_nonneg_right ht hEm.le
    have e2 : s * r * Real.exp (2 * Real.pi * K * s / 6) *
        Real.exp (-(2 * Real.pi * K * s) / 6) = s * r := by
      calc _ = s * r * (Real.exp (-(2 * Real.pi * K * s) / 6) *
            Real.exp (2 * Real.pi * K * s / 6)) := by ring
        _ = s * r := by rw [hEE, mul_one]
    nlinarith
  have he : (2.56 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hsr := mul_pos hs hr
  have e3 : |t| * (Real.exp (-(2 * Real.pi * K * s) / 6) * ε / (Real.exp 1 * (s / 6))) =
      6 * (|t| * (Real.exp (-(2 * Real.pi * K * s) / 6) * ε)) / (Real.exp 1 * s) := by
    field_simp
  rw [e3, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hsr (sub_pos.2 he)]

/-- `bpN:p7:nonresonant`. -/
theorem nonresonant (hn : 1 ≤ n) {D : Set (Fin n → ℝ)} {r s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hr : 0 < r)
    (hs : 0 < s) (hK : 0 < K) (hα : 0 < α) (hL : 0 ≤ L)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2))
    (hf : InClass (cpx D) r s f) (hfr : RealOn (Dom n (cpx D) r s) f)
    (hfb : WBound (cpx D) r s f ε) (hε0 : 0 ≤ ε)
    -- (i)
    (hnr : IsNonresonant (cpx D) K α {0} h)
    -- (ii)
    (hlip : FreqLipschitz (cpx D) r L h) (hrad : K * L * r ≤ α / p)
    -- (iii)
    (hiii : ε ≤ α * r / (2 ^ 7 * conjExp p * K)) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
      (z 0).2 ∈ D → ∀ t ∈ J, |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6) →
        ‖(z t).2 - (z 0).2‖ ≤ r / 2 := by
  intro J hJ h0 z hz hz0 t ht hadm
  by_cases hκ : 2 * Real.pi * K * s < 6
  · -- no normal form needed
    have hB : ∀ x ∈ realStrip D r, ‖thetaGradR (realH (fun w => h w.2 + f w)) x‖ ≤
        ε / (Real.exp 1 * s) := fun x hx => by
      rw [thetaGradR_h_add hs hh hhr hf hfr hx]
      exact norm_thetaGradR_le hs hf hfb hx
    exact (drift_bound hB hJ h0 hz ht).trans (arith_small hs hr hκ hadm)
  · have hii : 6 ≤ 2 * Real.pi * K * s := not_lt.1 hκ
    have hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K) := hiii.trans_eq (by ring)
    have hΛsym : ∀ k ∈ ({0} : Set (Fin n → ℤ)), -k ∈ ({0} : Set (Fin n → ℤ)) := fun k hk => by
      rw [mem_singleton_iff] at hk; simp [hk]
    obtain ⟨Ψ, g, fs, hΨd, -, hΨmap, hΨsympl, -, hg, hfs, hgco, hconj, hga, -, hfsb,
        hdisp, hreal⟩ :=
      normal_form (D := cpx D) (Λ := {0}) hp hα hK hL hr hs hh hnr hlip hrad hf hfb hε0 hi hii
    obtain ⟨hgr, hfsr, hΨreal⟩ := hreal hΛsym hhr hfr
    have hs6 : 0 < s / 6 := by positivity
    have hpre := preimage_nfl hp hα hK hr hs hε0 hi hii hΨd hΨreal hdisp
    obtain ⟨-, -, -, -, hdle⟩ := hpre (z 0) hz0
    have h128 : r / 2 ^ 7 = r / 128 := by norm_num
    rw [h128] at hdle
    -- the bound for `g`
    obtain ⟨-, hresIC, -, -, -, -, hresB, -⟩ :=
      homological hp hα hs hK.le hL hh hnr hlip hrad hf hfb
    have hresIC' : InClass (cpx D) (r / 2) (s / 6) (homRes K {0} f) :=
      inClass_mono_nf hresIC (by linarith) (by linarith)
    have hresB' : WBound (cpx D) (r / 2) (s / 6) (homRes K {0} f) ε :=
      hresB.mono (by linarith) (by linarith) le_rfl
    have hgB : WBound (cpx D) (r / 2) (s / 6) g
        (16 * (2 * conjExp p * K / (α * r)) * ε ^ 2 + ε) := by
      have := wbound_add hs6 (inClass_sub' hg hresIC') hresIC' hga hresB'
      have e : (fun z => (g z - homRes K {0} f z) + homRes K {0} f z) = g := by
        funext z; ring
      rwa [e] at this
    have hhr2 : RealOn (Dom n (cpx D) (r / 2) (s / 6)) (fun w => h w.2) :=
      realOn_mono' (Dom_mono (by linarith) (by linarith)) hhr
    have hh2 : DifferentiableOn ℂ h (polyNbhd (cpx D) (r / 2)) :=
      hh.mono (polyNbhd_mono (by linarith))
    -- the `θ`-gradient of `H' = h + g + f_*` is that of `f_*`
    have hgf : ∀ x ∈ realStrip D (r / 2),
        thetaGradR (realH (fun w => h w.2 + (g w + fs w))) x = thetaGradR (realH fs) x :=
      fun x hx => by
      rw [thetaGradR_h_add hs6 hh2 hhr2 (inClass_add' hg hfs) (realOn_add' hgr hfsr) hx,
        thetaGradR_realH_add hs6 hg hgr hfs hfsr hx]
      have h0 : thetaGradR (realH g) x = 0 := by
        have := resonant_gradient (Λ := {0}) hs6 hg hgr hgB
          (fun I hI k hk => hgco I hI k (fun hk' => hk hk'.1)) x hx
        have hbot : resSpan ({0} : Set (Fin n → ℤ)) = ⊥ := by
          rw [resSpan, Submodule.span_eq_bot]
          intro v hv
          obtain ⟨k, hk, rfl⟩ := hv
          rw [mem_singleton_iff] at hk
          subst hk
          ext i
          simp
        rwa [hbot, Submodule.mem_bot] at this
      rw [h0, zero_add]
    have hB' : ∀ x ∈ realStrip D (r / 2),
        ‖thetaGradR (realH (fun w => h w.2 + (g w + fs w))) x‖ ≤
          Real.exp (-(2 * Real.pi * K * s) / 6) * ε / (Real.exp 1 * (s / 6)) :=
      fun x hx => by rw [hgf x hx]; exact norm_thetaGradR_le hs6 hfs hfsb hx
    -- (T1), (T2), (T3)
    have hT1 : ∀ x ∈ realStrip D (r / 2), ‖(reMap Ψ x).2 - x.2‖ ≤ conjExp p * K * ε / α :=
      fun x hx => by
      have hxD := (realInclusion₂_mem_Dom_iff D hs6 x).2 hx
      have h1 := (hdisp _ hxD).1
      refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans h1)).2 fun i => ?_
      have h2 := (norm_le_pi_norm
        ((Ψ (KAM.realInclusion₂ n x)).2 - (KAM.realInclusion₂ n x).2) i).trans h1
      have e : (reMap Ψ x).2 i - x.2 i =
          ((Ψ (KAM.realInclusion₂ n x)).2 i - (KAM.realInclusion₂ n x).2 i).re := by
        simp [reMap]
      rw [Pi.sub_apply, Real.norm_eq_abs, e]
      exact (Complex.abs_re_le_norm _).trans (by simpa using h2)
    have hT2 : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D (r / 2),
        reMap Ψ x = y := fun y hy => by
      obtain ⟨x, hx, hxy, -, -⟩ := hpre y hy
      refine ⟨x, hx, ?_⟩
      unfold reMap
      rw [hxy]
      ext i <;> simp
    have hT3 : ∀ Iy ∈ D, ∀ J' : Set ℝ, J'.OrdConnected → (0 : ℝ) ∈ J' → ∀ z',
        IsOrbit (fun w => h w.2 + (g w + fs w)) D (r / 2) J' z' →
        ‖(z' 0).2 - Iy‖ ≤ conjExp p * K * ε / α → ∀ t ∈ J',
        |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6) →
        ‖(z' t).2 - (z' 0).2‖ ≤ 15 * r / 32 :=
      fun _ _ J' hJ' h0' z' hz' _ t' ht' hadm' =>
        (drift_bound hB' hJ' h0' hz' ht').trans (arith_large hs hr hadm').le
    have hT := transfer (D := D) (r := r) (s := s) (r' := r / 2) (s' := s / 6)
      (d := conjExp p * K * ε / α) (ϱ := 15 * r / 32) (Nrm := fun a => ‖a‖)
      (adm := fun _ t => |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6))
      (H := fun w => h w.2 + f w) (H' := fun w => h w.2 + (g w + fs w)) (Ψ := Ψ) hs hs6
      isActionNorm_norm
      (fun _ t t' ht' hadm' => (mul_le_mul_of_nonneg_right ht' (by linarith)).trans hadm')
      (inClass_add' (inClass_snd hh) hf) (realOn_add' hhr hfr)
      (inClass_add' (inClass_snd hh2) (inClass_add' hg hfs))
      (realOn_add' hhr2 (realOn_add' hgr hfsr)) hΨd hΨmap hΨreal hΨsympl
      (fun z hz => by
        have := hconj z hz
        simp only at this ⊢
        rw [this]; ring)
      hT1 hT2 (by positivity) (by linarith) hT3
    have := hT J hJ h0 z hz hz0 t ht hadm
    linarith

end KAM.Stability

end
