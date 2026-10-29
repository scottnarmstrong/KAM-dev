/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Measure.Lipschitz
public import KAM.Planetary.Preparation.SlowAverage

/-!
# Slow averaging: the zero angle-mode of `f₂` (P11A-P7d)

`p11_slow_coeff_zero`: for any `h₀`, `f₂` satisfying the fast identity and the polar-average
formula of `h₀` (clauses 1-2 of `P11SlowSpecOf`), the zero Fourier mode of `f₂` in the `2n`
angles is the zero mode of `f₁ ∘ Π`, hence of size `(ε M_F)³`: the polar average of `G ∘ Π`
cancels the `ε 𝒜 G` term of `h₀` exactly.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators
namespace KAM.Planetary

section Coeff

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Averaging over the `2n`-torus a function of the last `n` angles only. -/
theorem p11_torusAverage_natAdd (g : (Fin n → ℝ) → ℂ) :
    KAM.torusAverage (fun x : Fin (n + n) → ℝ => g (fun i => x (Fin.natAdd n i))) =
      KAM.torusAverage g := by
  unfold KAM.torusAverage
  have hp := KAM.measurePreserving_appendMeasurableEquiv n
  have hpre : (KAM.appendMeasurableEquiv n) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin (n + n) => Icc (0 : ℝ) 1)) =
      Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ×ˢ
        Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) := by
    ext p
    simp only [mem_preimage, KAM.appendMeasurableEquiv_apply, Set.mem_pi, mem_univ, true_implies,
      mem_prod, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  rw [← hp.setIntegral_preimage_emb (KAM.appendMeasurableEquiv n).measurableEmbedding, hpre]
  have h2 : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (fun i => (KAM.appendMeasurableEquiv n p) (Fin.natAdd n i))) = fun p => g p.2 := by
    funext p
    simp [KAM.appendMeasurableEquiv_apply]
  rw [h2, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_snd]
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, KAM.volume_unitCube]
  simp

/-- The zero angle-mode of `f₂` on the averaging box is that of `f₁ ∘ Π`. -/
theorem p11_slow_coeff_zero (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 64 * eps < C.rz ^ 2) {h0 : P11CVec (n + n) → ℂ} {f2 : P11Phase (n + n) → ℂ}
    (h1 : ∀ z ∈ KAM.complexStrip (n + n) (C.sigma / 12) ×ˢ p11SlowAvgBox C eps,
      h0 z.2 + f2 z = p11WorkingH C eps (Fast.map (p11PolarC z)))
    (h2 : ∀ I ∈ p11SlowAvgBox C eps, h0 I = C.h (fun i : Fin n => I (Fin.castAdd n i)) +
      eps * p11PolarAverage Fast.G ((fun i : Fin n => I (Fin.castAdd n i)),
        fun i : Fin n => I (Fin.natAdd n i)))
    {I : P11CVec (n + n)} (hI : I ∈ p11SlowAvgBox C eps) :
    ‖KAM.Weighted.coeff f2 I 0‖ ≤ (eps * C.MF) ^ 3 := by
  obtain ⟨-, -, -, -, -, hσ0, hσ1, -, -⟩ := fast_consts hC
  set θ : (Fin (n + n) → ℝ) → P11CVec (n + n) := fun x j => (x j : ℂ) with hθ
  have hθc : Continuous θ :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hstr : ∀ x, θ x ∈ KAM.complexStrip (n + n) (C.sigma / 6) := fun x =>
    KAM.ofReal_mem_complexStrip (by linarith) x
  have hstr12 : ∀ x, θ x ∈ KAM.complexStrip (n + n) (C.sigma / 12) := fun x =>
    KAM.ofReal_mem_complexStrip (by linarith) x
  have hpt := fun x => p11_slow_pt hC heps hεM hsm (z := (θ x, I)) ⟨hstr x, hI⟩
  have hxc : Continuous fun x => (θ x, I) := hθc.prodMk continuous_const
  have hPc : Continuous fun x => p11PolarC (θ x, I) :=
    (p11_polarC_differentiableOn (n := n)).continuousOn.comp_continuous hxc
      (fun x => (hpt x).2.2.1)
  have hPP : Continuous fun x => p11PolPt (θ x, I) := by
    unfold p11PolPt
    exact (continuous_pi fun i => (continuous_apply _).comp (continuous_fst.comp hPc)).prodMk
      (continuous_pi fun i => (continuous_apply _).comp (continuous_snd.comp hPc))
  have hGc : Continuous fun x => Fast.G (p11SlowJ I, p11PolPt (θ x, I)) :=
    hF.2.2.2.2.1.continuousOn.comp_continuous (continuous_const.prodMk hPP)
      (fun x => (hpt x).2.2.2.1)
  have hfc : Continuous fun x => Fast.f1 (p11PolarC (θ x, I)) :=
    hF.2.2.1.continuousOn.comp_continuous hPc (fun x => (hpt x).2.2.2.2)
  set PAI := p11PolarAverage Fast.G (p11SlowJ I, p11SlowR I) with hPAI
  have hid : ∀ x, f2 (θ x, I) = eps * Fast.G (p11SlowJ I, p11PolPt (θ x, I)) +
      Fast.f1 (p11PolarC (θ x, I)) - eps * PAI := by
    intro x
    have h := h1 (θ x, I) ⟨hstr12 x, hI⟩
    have hid' := hF.2.2.2.2.2.2.2.2.2.2.1 _ (hpt x).2.2.2.2
    have e1 : (fun i : Fin n => (p11PolarC (θ x, I)).2 (Fin.castAdd n i)) = p11SlowJ I := by
      funext i; simp [p11PolarC, p11SlowJ]
    have hPt : ((fun i : Fin n => (p11PolarC (θ x, I)).1 (Fin.natAdd n i)),
        fun i : Fin n => (p11PolarC (θ x, I)).2 (Fin.natAdd n i)) = p11PolPt (θ x, I) := rfl
    rw [e1, hPt] at hid'
    have h2' := h2 I hI
    simp only at h
    rw [hid'] at h
    change h0 I + f2 (θ x, I) = _ at h
    change h0 I = C.h (p11SlowJ I) + eps * PAI at h2'
    rw [h2'] at h
    linear_combination h
  have hGavg : KAM.torusAverage (fun x => Fast.G (p11SlowJ I, p11PolPt (θ x, I))) = PAI := by
    have := p11_torusAverage_natAdd (n := n) (fun θ' : Fin n → ℝ =>
      Fast.G (p11SlowJ I, ((fun i => Complex.sqrt (p11SlowR I i / Real.pi) *
        Complex.sin (2 * Real.pi * (θ' i))),
        fun i => Complex.sqrt (p11SlowR I i / Real.pi) * Complex.cos (2 * Real.pi * (θ' i)))))
    rw [hPAI]
    unfold p11PolarAverage
    rw [← this]
    congr 1
    funext x
    simp [p11PolPt, p11PolarC, p11SlowR, hθ]
  have hc0 : KAM.Weighted.coeff f2 I 0 = KAM.torusAverage (fun x => f2 (θ x, I)) := by
    unfold KAM.Weighted.coeff KAM.torusCoeffW
    simp only [neg_zero, KAM.character_zero, one_smul]
    rfl
  have hlin : KAM.torusAverage (fun x => f2 (θ x, I)) =
      KAM.torusAverage (fun x => Fast.f1 (p11PolarC (θ x, I))) := by
    have e : (fun x => f2 (θ x, I)) = fun x => eps * Fast.G (p11SlowJ I, p11PolPt (θ x, I)) +
        1 * (1 * Fast.f1 (p11PolarC (θ x, I)) + 1 * (-(eps * PAI))) := by
      funext x; rw [hid x]; ring
    have hg : Continuous fun x => 1 * Fast.f1 (p11PolarC (θ x, I)) + 1 * (-(eps * PAI)) := by
      fun_prop
    rw [e, p11_torusAverage_lin hGc hg, p11_torusAverage_lin hfc continuous_const,
      p11_torusAverage_const, hGavg]
    ring
  rw [hc0, hlin]
  refine KAM.norm_torusAverage_le fun x _ => ?_
  exact (hF.2.2.2.2.2.2.2.2.2.2.2.1) _ (hpt x).2.2.2.2

end Coeff

end KAM.Planetary

end
