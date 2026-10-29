/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Domains
public import KAM.Fourier.Derivative
public import KAM.Strip.Bridges
public import KAM.Strip.Fourier
import Mathlib.Tactic.Positivity

/-!
# The weighted Fourier norm (`bpN:p4:norm`, `bpN:p4:norm#monotone`)

Carriers. A function `u : (Fin n → ℂ) × (Fin m → ℂ) → W` of (angles, actions) is a *total*
function; the class `O(r,s)` is the proposition `InClass D r s u` (holomorphic on `Dom n D r s` and
`1`-periodic in every angle there). The coefficients `û_k(I)` are `KAM.torusCoeffW` of the
restriction of `u(·, I)` to the real unit torus (entrywise for vector and matrix valued `W`).

The weighted norm is a *bound predicate*: `WBound D r s u M` says `|u|_{r,s} ≤ M`, i.e. for every
`I ∈ V_r D` the coefficient series `∑ₖ ‖û_k(I)‖ e^{2π s |k|₁}` is summable with sum `≤ M`. No
`sSup` or junk `tsum` value occurs in a statement; `wnorm`, `HasFiniteWNorm` and `wbound_iff` relate
the predicate to the supremum over `I ∈ V_r D` on the finite locus. The weight is `e^{2π s |k|₁}`
with geometric width `s` (`docs/fourier-conventions.md`).

Also here: `coth`, used by the strip-to-weighted conversion (`bpN:p4:sup-weighted`) and by the
constants of Part 1.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Weighted

variable {n m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]

/-- `Os r s`: holomorphic on `𝒟_{r,s}` and `1`-periodic in each `θⱼ` (on `𝒟_{r,s}`). -/
structure InClass (D : Set (Fin m → ℂ)) (r s : ℝ) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) : Prop where
  differentiableOn : DifferentiableOn ℂ u (Dom n D r s)
  periodic : ∀ j : Fin n, ∀ z ∈ Dom n D r s, u (z.1 + Pi.single j 1, z.2) = u z

/-- `û_k(I) = ∫_{[0,1]ⁿ} u(x, I) e^{-2πi k·x} dx` (entrywise for vector/matrix `W`;
`torusCoeffW`). -/
def coeff (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (I : Fin m → ℂ) (k : Fin n → ℤ) : W :=
  KAM.torusCoeffW (fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I)) k

/-- The weight `e^{2π s |k|₁}`. -/
def modeWeight (s : ℝ) (k : Fin n → ℤ) : ℝ := Real.exp (2 * Real.pi * s * KAM.Fourier.modeSize k)

/-- `|u|_{I,s} = ∑ₖ |û_k(I)| e^{2π|k|₁ s}` (junk `0` if not summable; use `WSummable` alongside). -/
def wsum (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (s : ℝ) (I : Fin m → ℂ) : ℝ :=
  ∑' k : Fin n → ℤ, ‖coeff u I k‖ * modeWeight s k

def WSummable (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (s : ℝ) (I : Fin m → ℂ) : Prop :=
  Summable fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k

/-- `|u|_{r,s} ≤ M`: every coefficient series over `I ∈ V_r D` is summable with sum `≤ M`. -/
def WBound (D : Set (Fin m → ℂ)) (r s : ℝ) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (M : ℝ) : Prop :=
  ∀ I ∈ polyNbhd D r, WSummable u s I ∧ wsum u s I ≤ M

def HasFiniteWNorm (D : Set (Fin m → ℂ)) (r s : ℝ) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) : Prop :=
  ∃ M, WBound D r s u M

/-- `|u|_{r,s} = sup_{I ∈ V_r D} |u|_{I,s}` (meaningful only under `HasFiniteWNorm`). -/
def wnorm (D : Set (Fin m → ℂ)) (r s : ℝ) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) : ℝ :=
  ⨆ I : polyNbhd D r, wsum u s I

omit [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem wbound_iff {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W} {M : ℝ}
    (hM : 0 ≤ M) :
    WBound D r s u M ↔ HasFiniteWNorm D r s u ∧ wnorm D r s u ≤ M := by
  constructor
  · intro h
    exact ⟨⟨M, h⟩, Real.iSup_le (fun I => (h I.1 I.2).2) hM⟩
  · rintro ⟨⟨M₀, h₀⟩, hle⟩ I hI
    refine ⟨(h₀ I hI).1, ?_⟩
    have hbdd : BddAbove (Set.range fun J : polyNbhd D r => wsum u s J) :=
      ⟨M₀, by rintro _ ⟨J, rfl⟩; exact (h₀ J.1 J.2).2⟩
    exact (le_ciSup hbdd ⟨I, hI⟩).trans hle

theorem modeWeight_mono {s s' : ℝ} (hs : s' ≤ s) (k : Fin n → ℤ) :
    modeWeight s' k ≤ modeWeight s k := by
  unfold modeWeight
  refine Real.exp_le_exp.mpr ?_
  have hk := KAM.Fourier.modeSize_nonneg k
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hpi) hk

omit [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W] in
/-- `bpN:p4:norm#monotone`: restriction to smaller widths and a larger bound. -/
theorem WBound.mono {D : Set (Fin m → ℂ)} {r r' s s' : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    {M M' : ℝ} (h : WBound D r s u M) (hr : r' ≤ r) (hs : s' ≤ s) (hM : M ≤ M') :
    WBound D r' s' u M' := by
  intro I hI
  obtain ⟨hsum, hle⟩ := h I (polyNbhd_mono hr hI)
  have hmono : ∀ k : Fin n → ℤ,
      ‖coeff u I k‖ * modeWeight s' k ≤ ‖coeff u I k‖ * modeWeight s k := fun k =>
    mul_le_mul_of_nonneg_left (modeWeight_mono hs k) (norm_nonneg _)
  have hsum' : WSummable u s' I :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hmono hsum
  exact ⟨hsum', (hsum'.tsum_le_tsum hmono hsum).trans (hle.trans hM)⟩

/-! ### Vector-valued comparison -/

/-- The coefficient of the `a`-th component is the `a`-th component of the coefficient. -/
theorem coeff_apply_pi {d : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → Fin d → ℂ} (hs : 0 < s) (hu : InClass D r s u)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) (a : Fin d) :
    coeff u I k a = coeff (fun z => u z a) I k := by
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hcont : Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
    hu.differentiableOn.continuousOn.comp_continuous (hL.prodMk continuous_const)
      fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp hL
  have hint := KAM.integrableOn_unitCube_of_continuous (hchar.smul hcont)
  have hcomm := ((ContinuousLinearMap.proj a : (Fin d → ℂ) →L[ℝ] ℂ)).integral_comp_comm hint
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  simpa using hcomm.symm

/-- `bpN:p4:norm#monotone`, vector values: `max_a |u_a| ≤ |u| ≤ ∑_a |u_a|` (max norm of the
coefficient). -/
theorem wbound_pi_apply {d : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → Fin d → ℂ} {M : ℝ} (hs : 0 < s) (hu : InClass D r s u)
    (h : WBound D r s u M) (a : Fin d) :
    WBound D r s (fun z => u z a) M := by
  intro I hI
  obtain ⟨hsum, hle⟩ := h I hI
  have hk : ∀ k : Fin n → ℤ, ‖coeff (fun z => u z a) I k‖ * modeWeight s k ≤
      ‖coeff u I k‖ * modeWeight s k := fun k => by
    rw [← coeff_apply_pi hs hu hI k a]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm _ a) (Real.exp_pos _).le
  have hsum' : WSummable (fun z => u z a) s I :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hk hsum
  exact ⟨hsum', (hsum'.tsum_le_tsum hk hsum).trans hle⟩

theorem wbound_pi_of_components {d : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → Fin d → ℂ} {M : Fin d → ℝ} (hs : 0 < s) (hu : InClass D r s u)
    (h : ∀ a, WBound D r s (fun z => u z a) (M a)) : WBound D r s u (∑ a, M a) := by
  intro I hI
  have hk : ∀ k : Fin n → ℤ, ‖coeff u I k‖ * modeWeight s k ≤
      ∑ a, ‖coeff (fun z => u z a) I k‖ * modeWeight s k := fun k => by
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr fun a => ?_
    rw [coeff_apply_pi hs hu hI k a]
    exact Finset.single_le_sum (f := fun b => ‖coeff (fun z => u z b) I k‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hsumA : Summable fun k : Fin n → ℤ =>
      ∑ a, ‖coeff (fun z => u z a) I k‖ * modeWeight s k :=
    summable_sum fun a _ => (h a I hI).1
  have hsum : WSummable u s I :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hk hsumA
  refine ⟨hsum, (hsum.tsum_le_tsum hk hsumA).trans ?_⟩
  rw [Summable.tsum_finsetSum fun a _ => (h a I hI).1]
  exact Finset.sum_le_sum fun a _ => (h a I hI).2

/-- `coth x = cosh x / sinh x` (no Mathlib name; K writes it this way). -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

end KAM.Weighted

end
