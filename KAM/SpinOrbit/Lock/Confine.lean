/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Barrier
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A librational barrier confines (LOCK-CONF)

Unfrozen helper code (design SO-LOCK §5).

* `libAction Ω ψ x = π (Ω X² + Y²/Ω)`, `X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`: the elliptic
  libration action around a curve `ψ`.
* `LockBarrier Ω c Iin Iout`: an **explicitly conditional** certificate structure: an invariant
  graph `I = P(α, φ)` of the polar action around `c`, with `α` the polar angle of
  `(√Ω X, Y/√Ω)` in turns, `Iin ≤ P ≤ Iout`, `0 < Iin`. Its invariance is a field of this helper
  structure only; it is produced from the certifier by LOCK-GRAPH, never assumed by a source
  theorem.
* `lockW`: the complex point `Y/√Ω + i √Ω X`; `continuousOn_P_arg`: `P(arg(lockW)/2π, φ)` is
  continuous on `{libAction > 0}` despite the cut of `Complex.arg` (period one in `α`).
* `lockRegion`: the solid torus `{𝓘 < Iin} ∪ {Iin/2 < 𝓘 < P}`; `isOpen_lockRegion`,
  `frontier_lockRegion_subset` (the frontier lies on the barrier graph).
* `lock_confinement`: the solution through a point with `𝓘 < Iin` is global, unique, and keeps
  `𝓘 < Iout` for all real times (`gen_barrier`, `so_global_exists_unique`).
-/

@[expose] public noncomputable section

open Set Real Topology

namespace KAM.SpinOrbit.Lock

/-- The elliptic libration action around a curve `ψ`: `π(Ω X² + Y²/Ω)` with
`X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

/-- A librational barrier: an invariant graph `I = P(α, φ)` of the polar action around a curve
`c`, transported to `soField`. `α` is the polar angle of `(√Ω X, Y/√Ω)` in turns. -/
structure LockBarrier (Ω : ℝ) (c : ℝ → ℝ) (Iin Iout : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_α : ∀ a φ, P (a + 1) φ = P a φ
  periodic_φ : ∀ a φ, P a (φ + 1) = P a φ
  invariant : KAM.ODE.IsInvariantSet soField Set.univ
    {x | 0 < libAction Ω c x ∧ libAction Ω c x =
      P (Complex.arg (((√Ω * (x.1 - x.2.2 - c x.2.2) : ℝ) : ℂ) * Complex.I +
          (((x.2.1 - 1 - deriv c x.2.2) / √Ω : ℝ) : ℂ)) / (2 * π)) x.2.2}
  lower : ∀ a φ, Iin ≤ P a φ
  upper : ∀ a φ, P a φ ≤ Iout
  pos : 0 < Iin

/-- The complex point `Y/√Ω + i √Ω X` whose argument is the polar angle. -/
def lockW (Ω : ℝ) (c : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  ((√Ω * (x.1 - x.2.2 - c x.2.2) : ℝ) : ℂ) * Complex.I +
    (((x.2.1 - 1 - deriv c x.2.2) / √Ω : ℝ) : ℂ)

variable {Ω Iin Iout : ℝ} {c : ℝ → ℝ}

/-- The barrier value `P(α(x), φ)` at a physical point. -/
def LockBarrier.value (B : LockBarrier Ω c Iin Iout) (x : ℝ × ℝ × ℝ) : ℝ :=
  B.P (Complex.arg (lockW Ω c x) / (2 * π)) x.2.2

theorem continuous_libAction (hc : ContDiff ℝ 2 c) : Continuous (libAction Ω c) := by
  have h0 := hc.continuous
  have h1 := hc.continuous_deriv (by norm_num)
  unfold libAction
  fun_prop

theorem continuous_lockW (hc : ContDiff ℝ 2 c) : Continuous (lockW Ω c) := by
  have h0 := hc.continuous
  have h1 := hc.continuous_deriv (by norm_num)
  unfold lockW
  fun_prop

theorem lockW_ne_zero (hΩ : 0 < Ω) {x : ℝ × ℝ × ℝ} (hx : 0 < libAction Ω c x) :
    lockW Ω c x ≠ 0 := by
  intro h
  have hs : 0 < √Ω := Real.sqrt_pos.2 hΩ
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [lockW, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.zero_im] at hre him
  have hY : x.2.1 - 1 - deriv c x.2.2 = 0 := by
    have : (x.2.1 - 1 - deriv c x.2.2) / √Ω = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hs.ne'
  have hX : x.1 - x.2.2 - c x.2.2 = 0 := by
    have : √Ω * (x.1 - x.2.2 - c x.2.2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hs.ne'
    · exact h
  rw [libAction, hX, hY] at hx
  simp at hx

/-- Rotating by a half turn: `P(arg w / 2π) = P(arg(-w)/2π + 1/2)` for `w ≠ 0`. -/
theorem LockBarrier.P_arg_neg (B : LockBarrier Ω c Iin Iout) {w : ℂ} (hw : w ≠ 0) (φ : ℝ) :
    B.P (Complex.arg w / (2 * π)) φ = B.P (Complex.arg (-w) / (2 * π) + 1 / 2) φ := by
  have hπ := Real.pi_pos
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hi,
      show (Complex.arg w + π) / (2 * π) + 1 / 2 = Complex.arg w / (2 * π) + 1 by
        field_simp; ring, B.periodic_α]
  · have hre : w.re ≠ 0 := fun h => hw (Complex.ext h hi)
    rcases lt_or_gt_of_ne hre with hr | hr
    · rw [Complex.arg_eq_pi_iff.2 ⟨hr, hi⟩,
        Complex.arg_eq_zero_iff.2 ⟨by simp; linarith, by simp [hi]⟩]
      congr 1; field_simp; ring
    · rw [Complex.arg_eq_zero_iff.2 ⟨hr.le, hi⟩,
        Complex.arg_eq_pi_iff.2 ⟨by simp [hr], by simp [hi]⟩,
        show π / (2 * π) + 1 / 2 = 0 + 1 by field_simp; ring, B.periodic_α, zero_div]
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi]
    congr 1; field_simp; ring

/-- `P(α, φ)` is continuous where the libration action is positive: the cut of `Complex.arg` is
removed by the period one of `P` in `α`. -/
theorem continuousOn_P_arg (hΩ : 0 < Ω) (hc : ContDiff ℝ 2 c) (B : LockBarrier Ω c Iin Iout) :
    ContinuousOn B.value {x | 0 < libAction Ω c x} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hw := lockW_ne_zero hΩ hx
  have hW := (continuous_lockW (Ω := Ω) hc)
  have hP : Continuous fun p : ℝ × ℝ => B.P p.1 p.2 := B.continuous
  have hφ : Continuous fun y : ℝ × ℝ × ℝ => y.2.2 := by fun_prop
  by_cases hs : lockW Ω c x ∈ Complex.slitPlane
  · have ha : ContinuousAt (fun y => Complex.arg (lockW Ω c y) / (2 * π)) x :=
      ((Complex.continuousAt_arg hs).comp hW.continuousAt).div_const _
    exact hP.continuousAt.comp (f := fun y => (Complex.arg (lockW Ω c y) / (2 * π), y.2.2))
      (ha.prodMk hφ.continuousAt)
  · have hs' : -lockW Ω c x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      have hre : (lockW Ω c x).re ≠ 0 := fun h => hw (Complex.ext h hs.2)
      left; simp only [Complex.neg_re]; exact neg_pos.2 (lt_of_le_of_ne hs.1 hre)
    have ha : ContinuousAt (fun y => Complex.arg (-lockW Ω c y) / (2 * π) + 1 / 2) x :=
      (((Complex.continuousAt_arg hs').comp (f := fun y => -lockW Ω c y)
        hW.neg.continuousAt).div_const _).add_const _
    have hcont := hP.continuousAt.comp
      (f := fun y => (Complex.arg (-lockW Ω c y) / (2 * π) + 1 / 2, y.2.2))
      (ha.prodMk hφ.continuousAt)
    refine hcont.congr ?_
    filter_upwards [hW.continuousAt.eventually_ne hw] with y hy
    exact (B.P_arg_neg hy y.2.2).symm

/-- The solid torus `{𝓘 < Iin} ∪ {Iin/2 < 𝓘 < P(α, φ)}`. -/
def lockRegion (B : LockBarrier Ω c Iin Iout) : Set (ℝ × ℝ × ℝ) :=
  {x | libAction Ω c x < Iin} ∪ {x | Iin / 2 < libAction Ω c x ∧ libAction Ω c x < B.value x}

theorem isOpen_lockRegion (hΩ : 0 < Ω) (hc : ContDiff ℝ 2 c) (B : LockBarrier Ω c Iin Iout) :
    IsOpen (lockRegion B) := by
  have hA := continuous_libAction (Ω := Ω) hc
  have hU : IsOpen {x | Iin / 2 < libAction Ω c x} := isOpen_lt continuous_const hA
  have hcon : ContinuousOn (fun x => B.value x - libAction Ω c x)
      {x | Iin / 2 < libAction Ω c x} :=
    ((continuousOn_P_arg hΩ hc B).mono fun x (hx : Iin / 2 < _) =>
      (show (0 : ℝ) < libAction Ω c x by linarith [B.pos])).sub hA.continuousOn
  have h2 := hcon.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
  have : {x | Iin / 2 < libAction Ω c x ∧ libAction Ω c x < B.value x} =
      {x | Iin / 2 < libAction Ω c x} ∩
        (fun x => B.value x - libAction Ω c x) ⁻¹' Ioi 0 := by
    ext x; simp [sub_pos]
  rw [lockRegion, this]
  exact (isOpen_lt hA continuous_const).union h2

/-- The frontier of the solid torus lies on the barrier graph. -/
theorem frontier_lockRegion_subset (hΩ : 0 < Ω) (hc : ContDiff ℝ 2 c)
    (B : LockBarrier Ω c Iin Iout) :
    frontier (lockRegion B) ⊆
      {x | 0 < libAction Ω c x ∧ libAction Ω c x = B.value x} := by
  intro x hx
  have hVo := isOpen_lockRegion hΩ hc B
  have hxV : x ∉ lockRegion B := fun h => hx.2 (by rwa [hVo.interior_eq])
  simp only [lockRegion, mem_union, mem_ofPred_eq, not_or, not_and, not_lt] at hxV
  obtain ⟨h1, h2⟩ := hxV
  have hpos : 0 < libAction Ω c x := lt_of_lt_of_le B.pos h1
  have hge : B.value x ≤ libAction Ω c x := h2 (by linarith [B.pos])
  refine ⟨hpos, le_antisymm ?_ hge⟩
  by_contra hlt
  push Not at hlt
  have hA := continuous_libAction (Ω := Ω) hc
  have hopen : IsOpen {y | 0 < libAction Ω c y} := isOpen_lt continuous_const hA
  have hcont : ContinuousAt (fun y => B.value y - libAction Ω c y) x :=
    ((continuousOn_P_arg hΩ hc B).continuousAt (hopen.mem_nhds hpos)).sub hA.continuousAt
  have hev : {y | B.value y - libAction Ω c y < 0} ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨y, hy, hyV⟩ := mem_closure_iff_nhds.1 hx.1 _ hev
  simp only [mem_ofPred_eq] at hy
  rcases hyV with hyV | hyV
  · have : Iin ≤ B.value y := B.lower _ _
    simp only [mem_ofPred_eq] at hyV
    linarith
  · linarith [hyV.2]

/-- LOCK-CONF: a librational barrier confines (solid torus, `gen_barrier`). -/
theorem lock_confinement {Ω Iin Iout : ℝ} {c : ℝ → ℝ} (hΩ : 0 < Ω) (hc : ContDiff ℝ 2 c)
    (B : LockBarrier Ω c Iin Iout) (x₀ : ℝ × ℝ × ℝ) (h₀ : libAction Ω c x₀ < Iin) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = x₀ ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, libAction Ω c (z t) < Iout) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = x₀ ∧ ∀ t, HasDerivAt y (soField (y t)) t) → y = z := by
  obtain ⟨z, hz0, hzd, huniq⟩ := so_global_exists_unique x₀
  refine ⟨z, ⟨hz0, hzd⟩, ?_, fun y hy => huniq y hy.1 hy.2⟩
  have hsol : KAM.ODE.IsSolutionIn soField univ univ z := KAM.ODE.isSolutionIn_univ_iff.2
    fun t _ => hzd t
  have key := KAM.ODE.gen_barrier (F := soField) (W := univ) ordConnected_univ (mem_univ (0 : ℝ))
    hsol (isOpen_lockRegion hΩ hc B) (by rw [hz0]; exact Or.inl h₀) (G := univ)
    (subset_univ _) B.invariant
    (fun x hx => frontier_lockRegion_subset hΩ hc B hx.1)
    (by
      rw [hz0]
      rintro ⟨-, h⟩
      have : Iin ≤ B.value x₀ := B.lower _ _
      unfold LockBarrier.value lockW at this
      linarith)
  intro t
  rcases key t (mem_univ t) with h | h
  · exact lt_of_lt_of_le h ((B.lower 0 0).trans (B.upper 0 0))
  · exact lt_of_lt_of_le h.2 (B.upper _ _)

end KAM.SpinOrbit.Lock

end
