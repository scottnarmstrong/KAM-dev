/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Bracket
public import KAM.Weighted.SupWeighted
public import KAM.Canonical.Setting
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Rectangular bracket and field estimates (P11A-P3, `bpP:p11:aniso-bracket`)

The blockwise action domain `p11Box`, the weighted bound `p11WBound` over an arbitrary action set,
the field estimate `aniso_field` and the bracket estimate `aniso_bracket` with separate action
radii for the first `a` and last `b` actions.

Both are deduced from the isotropic estimates `KAM.Weighted.cauchy_loss`, `wbound_bracket` and
`sup_le_wbound`: with `V` the inner box and `m = min ρ₁ ρ₂`, the `m`-neighbourhood `V_m V` lies in
the outer box (`stepP:p11:ab-der`). The isotropic estimates are applied with a small slack `δ`
(the target `V` is the base set, so the loss radius is `m - δ`) and `δ → 0` is taken at the end
(`stepP:p11:ab-prod`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Blockwise radii on the existing action carrier; arbitrary center is complex. -/
def p11Box {a b : ℕ} (c : P11CVec (a+b)) (r1 r2 : ℝ) : Set (P11CVec (a+b)) :=
  {I | (∀ i : Fin a, ‖I (Fin.castAdd b i)-c (Fin.castAdd b i)‖ < r1) ∧
    ∀ i : Fin b, ‖I (Fin.natAdd a i)-c (Fin.natAdd a i)‖ < r2}
/-- Weighted bound over an arbitrary open action set, using existing wsum and WSummable. -/
def p11WBound {n m : ℕ} (V : Set (P11CVec m)) (s : ℝ)
    (f : P11CVec n × P11CVec m → ℂ) (M : ℝ) : Prop :=
  ∀ I ∈ V, KAM.Weighted.WSummable f s I ∧ KAM.Weighted.wsum f s I ≤ M

section Aux

open KAM.Weighted

/-- Letting the slack `δ` tend to `0` in a bound valid for all small `δ > 0`. -/
private theorem le_of_small {x ε : ℝ} (f : ℝ → ℝ) (hf : ContinuousAt f 0) (hε : 0 < ε)
    (h : ∀ δ, 0 < δ → δ < ε → x ≤ f δ) : x ≤ f 0 :=
  ge_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds) (by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ using h δ hδ.1 hδ.2)

private theorem wsum_nonneg' {n m : ℕ} (f : P11CVec n × P11CVec m → ℂ) (s : ℝ) (I : P11CVec m) :
    0 ≤ wsum f s I :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- A `t`-neighbourhood of an inner box lies in the outer box (`stepP:p11:ab-der`). -/
private theorem polyNbhd_box_subset {a b : ℕ} {c : P11CVec (a+b)} {a1 a2 R1 R2 t : ℝ}
    (h1 : a1 + t ≤ R1) (h2 : a2 + t ≤ R2) :
    polyNbhd (p11Box c a1 a2) t ⊆ p11Box c R1 R2 := by
  rintro I ⟨J, ⟨hJ1, hJ2⟩, hIJ⟩
  have key : ∀ j, ‖I j - c j‖ < t + ‖J j - c j‖ := fun j =>
    calc ‖I j - c j‖ = ‖(I j - J j) + (J j - c j)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖I j - J j‖ + ‖J j - c j‖ := norm_add_le _ _
      _ < t + ‖J j - c j‖ :=
        add_lt_add_of_lt_of_le ((norm_le_pi_norm (I - J) j).trans_lt hIJ) le_rfl
  exact ⟨fun i => (key _).trans (by linarith [hJ1 i]),
    fun i => (key _).trans (by linarith [hJ2 i])⟩

private theorem mem_polyNbhd_self {m : ℕ} {V : Set (P11CVec m)} {I : P11CVec m} (hI : I ∈ V)
    {ε : ℝ} (hε : 0 < ε) : I ∈ polyNbhd V ε :=
  ⟨I, hI, by rw [sub_self, norm_zero]; exact hε⟩

/-- A function holomorphic and periodic on a strip over a box is in the class over any base set
whose neighbourhood lies in the box. -/
private theorem inClass_of_box {a b : ℕ} {c : P11CVec (a+b)} {R1 R2 S s r : ℝ}
    {V : Set (P11CVec (a+b))} {u : P11Phase (a+b) → ℂ}
    (hu : DifferentiableOn ℂ u (KAM.complexStrip (a+b) S ×ˢ p11Box c R1 R2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) S ×ˢ p11Box c R1 R2,
      ∀ i : Fin (a+b), u (z.1+Pi.single i 1,z.2)=u z)
    (hsub : polyNbhd V r ⊆ p11Box c R1 R2) (hs : s ≤ S) : InClass V r s u :=
  have hD : Dom (a+b) V r s ⊆ KAM.complexStrip (a+b) S ×ˢ p11Box c R1 R2 :=
    prod_mono (fun _ hθ i => (hθ i).trans_le hs) hsub
  ⟨hu.mono hD, fun j z hz => hp z (hD hz) j⟩

/-- Pointwise derivative bounds of the field estimate. -/
private theorem field_bounds {a b : ℕ} {c : P11CVec (a+b)}
    {r1 r2 rho1 rho2 s sigma M : ℝ}
    (h1 : 0 < rho1) (h2 : 0 < rho2) (hs' : sigma < s) (hs : 0 < sigma)
    {phi : P11Phase (a+b) → ℂ}
    (hphi : DifferentiableOn ℂ phi (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), phi (z.1+Pi.single i 1,z.2)=phi z)
    (hM : p11WBound (p11Box c r1 r2) s phi M)
    {z : P11Phase (a+b)}
    (hz : z ∈ KAM.complexStrip (a+b) (s-sigma) ×ˢ p11Box c (r1-rho1) (r2-rho2)) :
    0 ≤ M ∧ (∀ j, ‖dtheta j phi z‖ ≤ M / (Real.exp 1 * sigma)) ∧
      ∀ i, ‖dI i phi z‖ ≤ M / min rho1 rho2 := by
  set m := min rho1 rho2 with hm
  have hm0 : 0 < m := lt_min h1 h2
  have hVm : polyNbhd (p11Box c (r1-rho1) (r2-rho2)) m ⊆ p11Box c r1 r2 :=
    polyNbhd_box_subset (by linarith [min_le_left rho1 rho2])
      (by linarith [min_le_right rho1 rho2])
  have hzs : ∀ i, |(z.1 i).im| < s := fun i => (hz.1 i).trans (by linarith)
  have hzI : ∀ ε, 0 < ε → z.2 ∈ polyNbhd (p11Box c (r1-rho1) (r2-rho2)) ε := fun ε hε =>
    mem_polyNbhd_self hz.2 hε
  have hIphi : InClass (p11Box c (r1-rho1) (r2-rho2)) m s phi := inClass_of_box hphi hp hVm le_rfl
  have hb : WBound (p11Box c (r1-rho1) (r2-rho2)) m s phi M := fun J hJ => hM J (hVm hJ)
  have hM0 : 0 ≤ M := (wsum_nonneg' phi s z.2).trans (hb z.2 (hzI m hm0)).2
  have hz0 : (z.1, z.2) ∈ Dom (a+b) (p11Box c (r1-rho1) (r2-rho2)) m (s-sigma) :=
    ⟨hz.1, hzI m hm0⟩
  refine ⟨hM0, ?_, ?_⟩
  · have hδ : (0:ℝ) < m / 2 := by positivity
    obtain ⟨-, hθ, -⟩ := cauchy_loss hIphi hb (ρ := m / 2) hδ (by linarith) hs hs'
    have hIc : InClass (p11Box c (r1-rho1) (r2-rho2)) m (s-sigma) phi :=
      inClass_of_box hphi hp hVm (by linarith)
    intro j
    exact sup_le_wbound (inClass_fderiv_apply hIc (Pi.single j 1, 0)) (hθ j) z hz0
  · intro i
    have hcont : ContinuousAt (fun δ : ℝ => M / (m - δ)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simp; exact hm0.ne')
    have := le_of_small (x := ‖dI i phi z‖) (fun δ : ℝ => M / (m - δ)) hcont hm0 (fun δ hδ hδm => by
      obtain ⟨-, -, hI⟩ := cauchy_loss hIphi hb (ρ := m - δ) (by linarith) (by linarith) hs hs'
      have hsub : polyNbhd (p11Box c (r1-rho1) (r2-rho2)) (m - (m - δ)) ⊆ p11Box c r1 r2 :=
        (polyNbhd_mono (by linarith)).trans hVm
      have hIc : InClass (p11Box c (r1-rho1) (r2-rho2)) (m - (m - δ)) s phi :=
        inClass_of_box hphi hp hsub le_rfl
      have hzd : (z.1, z.2) ∈ Dom (a+b) (p11Box c (r1-rho1) (r2-rho2)) (m - (m - δ)) s :=
        ⟨hzs, hzI _ (by linarith)⟩
      exact sup_le_wbound (inClass_fderiv_apply hIc (0, Pi.single i 1)) (hI i) z hzd)
    simpa using this

end Aux

-- `hr1`, `hr2` are part of the signature (not needed by the proof).
set_option linter.unusedVariables false in
open KAM.Weighted in
theorem aniso_field {a b : ℕ} {c : P11CVec (a+b)}
    {r1 r2 rho1 rho2 s sigma M : ℝ}
    (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2)
    (hs : 0 < sigma) (hs' : sigma < s)
    {phi : P11Phase (a+b) → ℂ}
    (hphi : DifferentiableOn ℂ phi
      (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), phi (z.1+Pi.single i 1,z.2)=phi z)
    (hM : p11WBound (p11Box c r1 r2) s phi M) :
    ∀ z ∈ KAM.complexStrip (a+b) (s-sigma) ×ˢ
      p11Box c (r1-rho1) (r2-rho2),
      let X := KAM.hamiltonianVectorFieldℂ phi z
      max (‖X.1‖/sigma)
        (max (‖(fun i : Fin a => X.2 (Fin.castAdd b i))‖/rho1)
          (‖(fun i : Fin b => X.2 (Fin.natAdd a i))‖/rho2)) ≤
        M/(min rho1 rho2*sigma) := by
  intro z hz X
  obtain ⟨hM0, hθ, hI⟩ := field_bounds (r1 := r1) (r2 := r2) h1 h2 hs' hs hphi hp hM hz
  set m := min rho1 rho2 with hm
  have hm0 : 0 < m := lt_min h1 h2
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  have hX1 : ‖X.1‖ ≤ M / m :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => hI i
  have hang : ∀ rho : ℝ, 0 < rho → m ≤ rho → ∀ {k : ℕ} (g : Fin k → ℂ),
      (∀ i, ‖g i‖ ≤ M / (Real.exp 1 * sigma)) → ‖g‖ / rho ≤ M / (m * sigma) := by
    intro rho hrho hmr k g hg
    have hg' : ‖g‖ ≤ M / (Real.exp 1 * sigma) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr hg
    calc ‖g‖ / rho ≤ M / (Real.exp 1 * sigma) / rho := by gcongr
      _ = M / (Real.exp 1 * rho * sigma) := by field_simp
      _ ≤ M / (m * sigma) := by
        apply div_le_div_of_nonneg_left hM0 (by positivity)
        have : m ≤ Real.exp 1 * rho := by nlinarith
        exact mul_le_mul_of_nonneg_right this hs.le
  have hX2 : ∀ i, ‖X.2 i‖ ≤ M / (Real.exp 1 * sigma) := fun i => by
    have : X.2 i = -dtheta i phi z := rfl
    rw [this, norm_neg]
    exact hθ i
  refine max_le ?_ (max_le ?_ ?_)
  · calc ‖X.1‖ / sigma ≤ M / m / sigma := by gcongr
      _ = M / (m * sigma) := by rw [div_div]
  · exact hang rho1 h1 (min_le_left _ _) _ fun i => hX2 _
  · exact hang rho2 h2 (min_le_right _ _) _ fun i => hX2 _

-- `hr1`, `hr2` are part of the signature (not needed by the proof).
set_option linter.unusedVariables false in
open KAM.Weighted in
theorem aniso_bracket {a b : ℕ} {c : P11CVec (a+b)} {r01 r02 r1 r2 rho1 rho2 s0 s sigma U W : ℝ}
    (h01 : r1 ≤ r01) (h02 : r2 ≤ r02) (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2) (hs : 0 < sigma) (hs' : sigma < s) (hs0 : s ≤ s0)
    {u w : P11Phase (a+b) → ℂ}
    (hu : DifferentiableOn ℂ u (KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02))
    (hw : DifferentiableOn ℂ w (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hup : ∀ z ∈ KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02,
      ∀ i : Fin (a+b), u (z.1+Pi.single i 1,z.2)=u z)
    (hwp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), w (z.1+Pi.single i 1,z.2)=w z)
    (hU : p11WBound (p11Box c r01 r02) s0 u U) (hW : p11WBound (p11Box c r1 r2) s w W) :
    p11WBound (p11Box c (r1-rho1) (r2-rho2)) (s-sigma) (KAM.Canonical.poissonBracket u w)
      ((sigma/(s0-s+sigma)+min rho1 rho2/min (r01-r1+rho1) (r02-r2+rho2)) /
        (Real.exp 1*min rho1 rho2*sigma)*U*W) := by
  intro I hI
  set m := min rho1 rho2 with hm
  set d := min (r01-r1+rho1) (r02-r2+rho2) with hd
  set V := p11Box c (r1-rho1) (r2-rho2) with hV
  have hm0 : 0 < m := lt_min h1 h2
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hS : 0 < s0 - s + sigma := by linarith
  have hVm : polyNbhd V m ⊆ p11Box c r1 r2 :=
    polyNbhd_box_subset (by linarith [min_le_left rho1 rho2])
      (by linarith [min_le_right rho1 rho2])
  have hVd : polyNbhd V d ⊆ p11Box c r01 r02 :=
    polyNbhd_box_subset (by linarith [min_le_left (r01-r1+rho1) (r02-r2+rho2)])
      (by linarith [min_le_right (r01-r1+rho1) (r02-r2+rho2)])
  have hIu : InClass V d s0 u := inClass_of_box hu hup hVd le_rfl
  have hIw : InClass V m s w := inClass_of_box hw hwp hVm le_rfl
  have hbu : WBound V d s0 u U := fun J hJ => hU J (hVd hJ)
  have hbw : WBound V m s w W := fun J hJ => hW J (hVm hJ)
  have key : ∀ δ, 0 < δ → δ < min m d →
      WSummable (KAM.Canonical.poissonBracket u w) (s - sigma) I ∧
      wsum (KAM.Canonical.poissonBracket u w) (s - sigma) I ≤
        1 / Real.exp 1 * (1 / ((d - δ) * sigma) + 1 / ((s0 - s + sigma) * (m - δ))) * U * W := by
    intro δ hδ hδ'
    have hδm : δ < m := hδ'.trans_le (min_le_left _ _)
    have hδd : δ < d := hδ'.trans_le (min_le_right _ _)
    have hbr := (wbound_bracket hIu hIw hbu hbw (ρ := m - δ) (σ := sigma) (by linarith)
      (by linarith) hs hs' (by linarith) (by linarith)).2
    obtain ⟨hws, hwle⟩ := hbr I (mem_polyNbhd_self hI (by linarith))
    have e1 : d - m + (m - δ) = d - δ := by ring
    rw [e1] at hwle
    exact ⟨hws, hwle⟩
  have hδ0 : 0 < min m d / 2 := by positivity
  have hδ1 : min m d / 2 < min m d := by linarith [lt_min hm0 hd0]
  refine ⟨(key _ hδ0 hδ1).1, ?_⟩
  have hcont : ContinuousAt (fun δ : ℝ =>
      1 / Real.exp 1 * (1 / ((d - δ) * sigma) + 1 / ((s0 - s + sigma) * (m - δ))) * U * W) 0 := by
    refine ((continuousAt_const.mul (ContinuousAt.add ?_ ?_)).mul continuousAt_const).mul
      continuousAt_const
    · exact continuousAt_const.div ((continuousAt_const.sub continuousAt_id).mul continuousAt_const)
        (by simp; exact ⟨hd0.ne', hs.ne'⟩)
    · exact continuousAt_const.div (continuousAt_const.mul
        (continuousAt_const.sub continuousAt_id)) (by simp; exact ⟨hS.ne', hm0.ne'⟩)
  refine (le_of_small _ hcont (lt_min hm0 hd0) fun δ hδ hδ' => (key δ hδ hδ').2).trans
    (le_of_eq ?_)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  simp only [sub_zero]
  field_simp
  ring

end KAM.Planetary

end
