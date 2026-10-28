/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepRemainder
public import KAM.Planetary.MaximalStep.ParameterFlow

/-!
# The canonical step in the maximal case (P11A-C8, `bpP:p11a:canonical-step`)

`canonical_step` is assembled from the fibrewise affine flow (`affine_flow`, `affine_flow_param`),
the homological stage (`StepHom`) and the integral Lie identity with its Cauchy bracket estimate
(`StepRemainder`). The output functions are the explicit `p11StepMap` and `p11StepRemainder`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n}
  {R : P11Family n → ℂ}

theorem step_normal_diff {B : Set (P11CVec n)} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n}
    (hh : DifferentiableOn ℂ h B) (hw : DifferentiableOn ℂ w B) :
    DifferentiableOn ℂ (p11Normal h w) (Set.univ ×ˢ B) := by
  have hm : MapsTo (fun z : P11Family n => z.2) (Set.univ ×ˢ B) B := fun z hz => hz.2
  refine (hh.comp differentiableOn_snd hm).add (DifferentiableOn.fun_sum fun i _ => ?_)
  exact (((differentiableOn_pi.1 hw) i).comp differentiableOn_snd hm).mul
    (by fun_prop : Differentiable ℂ (fun z : P11Family n => z.1.2 i)).differentiableOn

theorem step_U_mem {S : P11Step n} {z : P11Family n}
    (hz : z ∈ domain_def n (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s)
      (KAM.actionNbhd S.E S.t)) :
    z.1 ∈ KAM.Weighted.Dom n {0} (S.q * S.s) (S.r - S.d - S.delta - 2 * S.sigma) ∧
      z.2 ∈ KAM.actionNbhd S.E S.t := hz

theorem step_stepMap_diff (H : P11StepHyp S h w R) :
    DifferentiableOn ℂ (p11StepMap S w R) (domain_def n (S.r - S.d - S.delta - 2 * S.sigma)
      (S.q * S.s) (KAM.actionNbhd S.E S.t)) := by
  have h0 : DifferentiableOn ℂ (stepP0 S w R) (KAM.complexStrip n (S.r - S.d - S.delta) ×ˢ
      KAM.actionNbhd S.E S.t) := (step_hm0 H).1.1
  have h1 : DifferentiableOn ℂ (stepP1 S w R) (KAM.complexStrip n (S.r - S.d - S.delta) ×ˢ
      KAM.actionNbhd S.E S.t) := differentiableOn_pi.2 fun i => (step_hm1 H i).1.1
  have key := affine_flow_param (step_B_open S) (stepP0 S w R) (stepP1 S w R) h0 h1
    (fun b hb => step_affHyp H hb) (s := S.s) (sigma := S.sigma) (A := p11StepA S)
  refine key.comp (f := fun z : P11Family n => (z.2, z.1)) (by fun_prop) ?_
  intro z hz
  exact ⟨hz.2, step_z_mem S hz.1⟩

theorem step_mapsU (H : P11StepHyp S h w R) :
    ∀ z ∈ domain_def n (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s) (KAM.actionNbhd S.E S.t),
      (p11StepMap S w R z, z.2) ∈ domain_def n (S.r - S.d - S.delta - 2 * S.sigma + S.sigma) S.s
        (KAM.actionNbhd S.E S.t) := by
  intro z hz
  have := (affine_flow (step_affHyp H hz.2)).2.2.1 z.1 (step_z_mem S hz.1) 1 ⟨by norm_num, le_rfl⟩
  refine ⟨?_, hz.2⟩
  have e : S.r - S.d - S.delta - 2 * S.sigma + S.sigma = S.r - S.d - S.delta - S.sigma := by ring
  rw [e]
  exact this

theorem domain_def_mono {r r' s : ℝ} {B : Set (P11CVec n)} (h : r ≤ r') :
    domain_def n r s B ⊆ domain_def n r' s B := by
  rintro ⟨⟨θ, η⟩, b⟩ hz
  obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp hz
  exact p11_mem_domain_def.mpr ⟨fun i => (h1 i).trans_le h, h2, h3⟩

theorem step_Rp_admissible (H : P11StepHyp S h w R) :
    p11Admissible (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s) (KAM.actionNbhd S.E S.t)
      (p11StepRemainder S h w R) := by
  have hσ := S.sigma_pos
  have hmaps := step_mapsU H
  have hF := step_stepMap_diff H
  have hΔW : DifferentiableOn ℂ (p11DeltaW S.T R) (KAM.actionNbhd S.E S.t) :=
    differentiableOn_pi.2 fun i => (step_hm1 H i).2.2.1
  have hsub1 : domain_def n (S.r - S.d - S.delta - 2 * S.sigma + S.sigma) S.s
      (KAM.actionNbhd S.E S.t) ⊆ Set.univ ×ˢ KAM.actionNbhd S.E S.t := fun z hz => ⟨trivial, hz.2⟩
  have hsub2 : domain_def n (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s)
      (KAM.actionNbhd S.E S.t) ⊆ Set.univ ×ˢ KAM.actionNbhd S.E S.t := fun z hz => ⟨trivial, hz.2⟩
  have hR := H.admissible.1.mono (domain_def_mono (s := S.s) (B := KAM.actionNbhd S.E S.t)
    (show S.r - S.d - S.delta - 2 * S.sigma + S.sigma ≤ S.r by
      linarith [S.d_pos, S.delta_pos]))
  have hN := ((step_normal_diff H.holh H.holw).mono hsub1).add hR
  have hN2 := (step_normal_diff (H.holh.add (step_hm0 H).2.2.1) (H.holw.add hΔW)).mono hsub2
  refine ⟨?_, fun j z hz => ?_⟩
  · exact (hN.comp (hF.prodMk differentiableOn_snd) hmaps).sub hN2
  · set k : Fin n → ℤ := Pi.single j 1
    have hk : (fun i => (k i : ℂ)) = Pi.single j 1 := by
      ext i; by_cases h : i = j <;> simp [k, Pi.single_apply, h]
    have hper := (affine_flow (step_affHyp H hz.2)).2.2.2.2.2.2.2.1 z.1 (step_z_mem S hz.1) k
    have hF' : p11StepMap S w R ((z.1.1 + Pi.single j 1, z.1.2), z.2) =
        p11StepMap S w R z + (Pi.single j 1, 0) := by
      rw [← hk]; exact hper
    have hRp := H.admissible.2 j (p11StepMap S w R z, z.2)
      (domain_def_mono (show S.r - S.d - S.delta - 2 * S.sigma + S.sigma ≤ S.r by
        linarith [S.d_pos, S.delta_pos]) (step_mapsU H z hz))
    simp only [p11StepRemainder, hF']
    have e : p11StepMap S w R z + (Pi.single j 1, 0) =
        ((p11StepMap S w R z).1 + Pi.single j 1, (p11StepMap S w R z).2) := by ext <;> simp
    simp only [Pi.add_apply, p11Normal, Prod.fst_add, Prod.snd_add, add_zero,
      Pi.zero_apply] at hRp ⊢
    rw [e, hRp]

/-- `canonical_step` i-iii, complex form. The output functions are explicit, never assumed. -/
theorem canonical_step {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R) :
    let B := KAM.actionNbhd S.E S.t
    let rp := S.r-S.d-S.delta-2*S.sigma
    let U := domain_def n rp (S.q*S.s) B
    let F := p11StepMap S w R
    let Rp := p11StepRemainder S h w R
    DifferentiableOn ℂ (p11DeltaH S.T R) B ∧
    DifferentiableOn ℂ (p11DeltaW S.T R) B ∧
    p11Bound B (p11DeltaH S.T R) ((1+p11Error n S.T S.d)*S.eps) ∧
    p11Bound B (p11DeltaW S.T R) ((1+p11Error n S.T S.d)*S.eps/S.s) ∧
    DifferentiableOn ℂ F U ∧
    (∀ z ∈ U, (F z,z.2) ∈ domain_def n (rp+S.sigma) S.s B) ∧
    (∀ z ∈ U, ‖(F z).1-z.1.1‖ ≤ p11StepA S ∧
      ‖(F z).2-z.1.2‖ ≤ (n+1)*S.s*p11StepA S/S.sigma) ∧
    (∀ z ∈ U, p11GaugeBound (S.s/2) S.sigma
      (fderiv ℂ (fun x => F (x,z.2)) z.1-ContinuousLinearMap.id ℂ _) (2*p11StepKappa S)) ∧
    (∀ z ∈ U, ‖fderiv ℂ (fun x => F (x,z.2)) z.1-ContinuousLinearMap.id ℂ _‖ ≤
      2*p11StepKappa S+p11StepKappa S*S.s/S.sigma) ∧
    (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC
      (fderiv ℂ (fun x => F (x,z.2)) z.1 u) (fderiv ℂ (fun x => F (x,z.2)) z.1 v)=
        KAM.Canonical.symplFormC u v) ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ, F ((z.1.1+(fun i => (k i : ℂ)),z.1.2),z.2)=
      F z+((fun i => (k i : ℂ)),0)) ∧
    p11Admissible rp (S.q*S.s) B Rp ∧ p11Bound U Rp (p11StepRem S) ∧
    p11StepRem S ≤ S.eps*(2*S.q^2+2*p11Error n S.T S.d)+
      18*n*(4*n+5)*p11Lambda n S.delta*S.eps^2/(Real.pi*S.D*S.s*S.sigma) ∧
    (∀ z ∈ U, (p11Normal h w+R) (F z,z.2)=
      p11Normal (h+p11DeltaH S.T R) (w+p11DeltaW S.T R) z+Rp z) := by
  intro B rp U F Rp
  have hfam : ∀ b ∈ B, P11AffineHyp (fun θ => stepP0 S w R (θ, b)) (fun θ => stepP1 S w R (θ, b))
      (S.r - S.d - S.delta) S.s S.sigma (p11StepA S) := fun b hb => step_affHyp H hb
  have hE := step_E_nonneg S
  have hD := S.D_pos
  have hs := S.s_pos
  have hσ := S.sigma_pos
  have hΛ := step_lambda_nonneg S
  have hε := S.eps_nonneg
  have hΔW : DifferentiableOn ℂ (p11DeltaW S.T R) B :=
    differentiableOn_pi.2 fun i => (step_hm1 H i).2.2.1
  have hF := step_stepMap_diff H
  have hmapsU : ∀ z ∈ U, (F z, z.2) ∈ domain_def n (rp + S.sigma) S.s B := step_mapsU H
  refine ⟨(step_hm0 H).2.2.1, hΔW, (step_hm0 H).2.2.2.1, fun b hb =>
    (pi_norm_le_iff_of_nonneg (div_nonneg (step_M_nonneg S) hs.le)).2
      fun i => (step_hm1 H i).2.2.2.1 b hb, hF, hmapsU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (affine_flow (hfam z.2 hz.2)).2.1 z.1 (step_z_mem S hz.1)
  · intro z hz
    have hV : z.1 ∈ KAM.Weighted.Dom n {0} (S.s / 2) (S.r - S.d - S.delta - 2 * S.sigma) := by
      obtain ⟨h1, h2⟩ := (mem_Dom_iff z.1).1 hz.1
      exact (mem_Dom_iff z.1).2 ⟨h1, by nlinarith [S.q_le]⟩
    exact (affine_flow (hfam z.2 hz.2)).2.2.2.2.1 z.1 hV
  · intro z hz
    have hV : z.1 ∈ KAM.Weighted.Dom n {0} (S.s / 2) (S.r - S.d - S.delta - 2 * S.sigma) := by
      obtain ⟨h1, h2⟩ := (mem_Dom_iff z.1).1 hz.1
      exact (mem_Dom_iff z.1).2 ⟨h1, by nlinarith [S.q_le]⟩
    exact (affine_flow (hfam z.2 hz.2)).2.2.2.2.2.1 z.1 hV
  · intro z hz u v
    exact (affine_flow (hfam z.2 hz.2)).2.2.2.2.2.2.1 z.1 (step_z_mem S hz.1) u v
  · intro z hz k
    exact (affine_flow (hfam z.2 hz.2)).2.2.2.2.2.2.2.1 z.1 (step_z_mem S hz.1) k
  · exact step_Rp_admissible H
  · intro z hz
    exact step_remainder_le H hz.2 hz.1
  · have hP : 0 < Real.pi * S.D * S.s * S.sigma := by positivity
    unfold p11StepRem
    have hq0 := S.q_pos
    have hq1 := S.q_le
    have hq2 : S.q ^ 2 / (1 - S.q) ≤ 2 * S.q ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg S.q]
    have hE1 := S.cutoff_error
    have h18 : (5 + 4 * p11Error n S.T S.d) * (1 + p11Error n S.T S.d) ≤ 18 := by nlinarith
    have hn : (0 : ℝ) ≤ n * (4 * n + 5) := by positivity
    have : (n : ℝ) * (4 * n + 5) * (5 + 4 * p11Error n S.T S.d) * (1 + p11Error n S.T S.d) *
        p11Lambda n S.delta * S.eps ^ 2 / (Real.pi * S.D * S.s * S.sigma) ≤
        18 * n * (4 * n + 5) * p11Lambda n S.delta * S.eps ^ 2 /
          (Real.pi * S.D * S.s * S.sigma) := by
      rw [div_le_div_iff_of_pos_right hP]
      have h0 : 0 ≤ (n : ℝ) * (4 * n + 5) * p11Lambda n S.delta * S.eps ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h18 h0]
    have e : (n : ℝ) * (4 * n + 5) * (5 + 4 * p11Error n S.T S.d) * (1 + p11Error n S.T S.d) *
        p11Lambda n S.delta * S.eps ^ 2 / (Real.pi * S.D * S.s * S.sigma) =
        n * (4 * n + 5) * (5 + 4 * p11Error n S.T S.d) * (1 + p11Error n S.T S.d) *
        p11Lambda n S.delta * S.eps ^ 2 / (Real.pi * S.D * S.s * S.sigma) := rfl
    nlinarith [mul_le_mul_of_nonneg_left hq2 hε]
  · intro z hz
    simp only [Rp, p11StepRemainder]
    ring

end KAM.Planetary

end
