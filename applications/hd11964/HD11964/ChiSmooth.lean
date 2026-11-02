/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Generator
public import HD11964.ParamIntegral

/-!
# Smoothness of the exact generator (HD11964-CHI, piece 1)

`χ*(w)` integrates a chart function over every fast angle at the slow variables and actions of
`w`, so it is smooth on an open set `U` that is **angle-saturated** and on which the function is
smooth.

* `IsAngleSaturated U`; `withAngles` lemmas (`withAngles_withAngles`, `chartCoeff_withAngles`, …).
* `projS S P`: the Fourier projection `Re Σ_{k ∈ S} P̂_k e^{i k·λ}`.
* `contDiffOn_chartCoeff` (1a): the Fourier coefficients are `C^∞` on `U` (two applications of
  `contDiffOn_intervalIntegral`).
* `IsModeSet S ω U` (AUDIT-HD11964-LEMMAS-1, L1): `S = -S`, `0 ∉ S`, `k·ω(Λ) ≠ 0` on `U`.
* `contDiffOn_chiStar`, `contDiffOn_projS` (1b): `χ*` and `Π_S P` are `C^∞` on `U` when the
  frequency map is smooth and `S` is a mode set.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-- A set of chart states closed under changing the fast angles. -/
def IsAngleSaturated (U : Set (Phase (2 + 2))) : Prop := ∀ w ∈ U, ∀ lam, withAngles w lam ∈ U

/-- **The conditions on a mode set** (AUDIT-HD11964-LEMMAS-1, L1): `S = -S`, `0 ∉ S`, and no
divisor `k·ω(Λ)`, `k ∈ S`, vanishes on `U`. Without them `χ*` is not the generator: Lean's
`0⁻¹ = 0` drops resonant modes, and `.re` halves a mode whose partner `-k` is missing. -/
def IsModeSet (S : Finset (Fin 2 → ℤ)) (frq : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (U : Set (Phase (2 + 2))) : Prop :=
  (∀ k ∈ S, -k ∈ S) ∧ (0 : Fin 2 → ℤ) ∉ S ∧ ∀ k ∈ S, ∀ w ∈ U, ∑ i, (k i : ℝ) * frq (fast w.2) i ≠ 0

/-- The Fourier projection `Π_S P = Re Σ_{k ∈ S} P̂_k e^{i k·λ}` (for a symmetric `S`, the sum is
real). -/
def projS (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2)) : ℝ :=
  (∑ k ∈ S, chartCoeff P k w * charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))).re

/-! ### `withAngles` -/

theorem fast_append' {a b : ℕ} (u : Fin a → ℝ) (v : Fin b → ℝ) : fast (Fin.append u v) = u := by
  funext i
  simp only [fast, Fin.append_left]

theorem withAngles_fst_fast (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) :
    fast (withAngles w lam).1 = lam := by
  simp only [withAngles, assemble, fast_append']

theorem withAngles_fst_slow (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) :
    slow (withAngles w lam).1 = slow w.1 := by
  simp only [withAngles, assemble, slow_append']

theorem withAngles_snd (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) : (withAngles w lam).2 = w.2 := by
  simp only [withAngles, assemble]
  exact Fin.append_castAdd_natAdd

theorem withAngles_withAngles (w : Phase (2 + 2)) (lam mu : Fin 2 → ℝ) :
    withAngles (withAngles w lam) mu = withAngles w mu :=
  calc withAngles (withAngles w lam) mu =
      assemble (fast (withAngles w lam).2) mu (slow (withAngles w lam).2)
        (slow (withAngles w lam).1) := rfl
    _ = withAngles w mu := by rw [withAngles_snd, withAngles_fst_slow]; rfl

theorem chartCoeff_withAngles (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2))
    (lam : Fin 2 → ℝ) : chartCoeff P k (withAngles w lam) = chartCoeff P k w := by
  simp only [chartCoeff, withAngles_withAngles]

theorem chartAMD_withAngles (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) :
    chartAMD (withAngles w lam) = chartAMD w := by
  simp only [chartAMD, withAngles_fst_slow, withAngles_snd]

/-- A coordinate of `ι → ℝ` is smooth. -/
theorem contDiff_coord {ι : Type} [Fintype ι] (j : ι) : ContDiff ℝ ∞ fun x : ι → ℝ => x j :=
  contDiff_pi.1 contDiff_id j

/-- `(w, λ) ↦ withAngles w λ` is smooth (linear). -/
theorem contDiff_withAngles :
    ContDiff ℝ ∞ (fun p : Phase (2 + 2) × (Fin 2 → ℝ) => withAngles p.1 p.2) := by
  refine ContDiff.prodMk ?_ ?_
  swap
  · convert contDiff_snd.comp contDiff_fst using 1
    funext p
    exact Fin.append_castAdd_natAdd
  refine contDiff_pi.2 fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    simp only [Fin.append_left]
    exact (contDiff_coord j).comp contDiff_snd
  | right j =>
    simp only [Fin.append_right, slow]
    exact (contDiff_coord _).comp (contDiff_fst.comp contDiff_fst)

/-- The characters in `t` are smooth. -/
theorem contDiff_charE_vec {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : Fin 2 → ℤ)
    {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun x => charE k ![(f x : ℂ), (g x : ℂ)] := by
  unfold charE
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hf' : ContDiff ℝ ∞ fun x => (f x : ℂ) := Complex.ofRealCLM.contDiff.comp hf
  have hg' : ContDiff ℝ ∞ fun x => (g x : ℂ) := Complex.ofRealCLM.contDiff.comp hg
  exact Complex.contDiff_exp.comp (contDiff_const.mul ((contDiff_const.mul hf').add
    (contDiff_const.mul hg')))

/-! ### (1a) The Fourier coefficients -/

/-- **The Fourier coefficients are smooth** on an open angle-saturated set where `P` is (1a). -/
theorem contDiffOn_chartCoeff {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U)
    (k : Fin 2 → ℤ) : ContDiffOn ℝ ∞ (fun w => chartCoeff P k w) U := by
  set I : Phase (2 + 2) × ℝ → ℝ → ℂ := fun q t₁ =>
    (P (withAngles q.1 ![2 * π * q.2, 2 * π * t₁]) : ℂ) * charE (-k) ![(q.2 : ℂ), (t₁ : ℂ)]
    with hIdef
  have hvec : ContDiff ℝ ∞ fun p : (Phase (2 + 2) × ℝ) × ℝ =>
      (![2 * π * p.1.2, 2 * π * p.2] : Fin 2 → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact contDiff_const.mul (contDiff_snd.comp contDiff_fst)
    · exact contDiff_const.mul contDiff_snd
  have hΦ : ContDiff ℝ ∞ fun p : (Phase (2 + 2) × ℝ) × ℝ =>
      withAngles p.1.1 ![2 * π * p.1.2, 2 * π * p.2] :=
    contDiff_withAngles.comp ((contDiff_fst.comp contDiff_fst).prodMk hvec)
  have hPc : ContDiffOn ℝ ∞ (fun p : (Phase (2 + 2) × ℝ) × ℝ =>
      P (withAngles p.1.1 ![2 * π * p.1.2, 2 * π * p.2])) ((U ×ˢ univ) ×ˢ univ) :=
    hP.comp hΦ.contDiffOn fun p hp => hsat _ hp.1.1 _
  have hI : ContDiffOn ℝ ∞ (fun p : (Phase (2 + 2) × ℝ) × ℝ => I p.1 p.2)
      ((U ×ˢ univ) ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hPc).mul
      (contDiff_charE_vec (-k) (contDiff_snd.comp contDiff_fst) contDiff_snd).contDiffOn
  have hin := contDiffOn_intervalIntegral (H := Phase (2 + 2) × ℝ) (hU.prod isOpen_univ) hI 0 1
  exact contDiffOn_intervalIntegral (H := Phase (2 + 2))
    (G := fun w t₀ => ∫ t₁ in (0 : ℝ)..1, I (w, t₀) t₁) hU hin 0 1

/-! ### (1b) `χ*` and `Π_S P` -/

/-- The characters of the fast angles are smooth. -/
theorem contDiff_charE_angles (k : Fin 2 → ℤ) :
    ContDiff ℝ ∞ fun y : Phase (2 + 2) => charE k (fun i => ((fast y.1 i / (2 * π) : ℝ) : ℂ)) := by
  have hc : ∀ i : Fin 2, ContDiff ℝ ∞ fun y : Phase (2 + 2) => fast y.1 i / (2 * π) := fun i =>
    ((contDiff_coord (Fin.castAdd 2 i)).comp contDiff_fst).div_const _
  convert contDiff_charE_vec k (hc 0) (hc 1) using 1
  funext y
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The inverse divisor `(i k·ω(Λ))⁻¹` is smooth where `ω` is and the divisor does not vanish. -/
theorem contDiffAt_divisorInv {frq : (Fin 2 → ℝ) → Fin 2 → ℝ} {k : Fin 2 → ℤ}
    {w : Phase (2 + 2)} (hfrq : ContDiffAt ℝ ∞ frq (fast w.2))
    (hk : ∑ i, (k i : ℝ) * frq (fast w.2) i ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Phase (2 + 2) => (Complex.I * ∑ i, (k i : ℂ) * frq (fast y.2) i)⁻¹)
      w := by
  have hlin : ContDiff ℝ ∞ fun y : Phase (2 + 2) => fast y.2 :=
    contDiff_pi.2 fun i => (contDiff_coord (Fin.castAdd 2 i)).comp contDiff_snd
  have hcomp : ContDiffAt ℝ ∞ (fun y : Phase (2 + 2) => frq (fast y.2)) w :=
    hfrq.comp w hlin.contDiffAt
  have hcomp' : ∀ i, ContDiffAt ℝ ∞ (fun y : Phase (2 + 2) => ((frq (fast y.2) i : ℝ) : ℂ)) w :=
    fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((contDiff_coord i).contDiffAt.comp w hcomp)
  have hsum : ContDiffAt ℝ ∞ (fun y : Phase (2 + 2) =>
      Complex.I * ∑ i, (k i : ℂ) * frq (fast y.2) i) w :=
    contDiffAt_const.mul (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hcomp' i))
  refine hsum.inv ?_
  have hc : (∑ i, (k i : ℂ) * (frq (fast w.2) i : ℂ)) =
      ((∑ i, (k i : ℝ) * frq (fast w.2) i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc]
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)

/-- **`χ*` is smooth** on an open angle-saturated set where `P` and `ω` are, for a mode set `S`
(`IsModeSet`: symmetric, without `0`, no vanishing divisor on `U`) (1b). -/
theorem contDiffOn_chiStar {U : Set (Phase (2 + 2))} (hU : IsOpen U) (hsat : IsAngleSaturated U)
    {S : Finset (Fin 2 → ℤ)} {frq : (Fin 2 → ℝ) → Fin 2 → ℝ} {P : Phase (2 + 2) → ℝ}
    (hP : ContDiffOn ℝ ∞ P U) (hfrq : ∀ w ∈ U, ContDiffAt ℝ ∞ frq (fast w.2))
    (hS : IsModeSet S frq U) :
    ContDiffOn ℝ ∞ (chiStar S frq P) U := by
  have hdiv := hS.2.2
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  have hc : ∀ k, ContDiffAt ℝ ∞ (fun y => chartCoeff P k y) w := fun k =>
    (contDiffOn_chartCoeff hU hsat hP k).contDiffAt (hU.mem_nhds hw)
  exact Complex.reCLM.contDiff.contDiffAt.comp w (ContDiffAt.sum fun k hk =>
    ((hc k).mul (contDiffAt_divisorInv (hfrq w hw) (hdiv k hk w hw))).mul
      (contDiff_charE_angles k).contDiffAt)

/-- **`Π_S P` is smooth** on an open angle-saturated set where `P` is (1b). -/
theorem contDiffOn_projS {U : Set (Phase (2 + 2))} (hU : IsOpen U) (hsat : IsAngleSaturated U)
    (S : Finset (Fin 2 → ℤ)) {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) :
    ContDiffOn ℝ ∞ (projS S P) U := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  have hc : ∀ k, ContDiffAt ℝ ∞ (fun y => chartCoeff P k y) w := fun k =>
    (contDiffOn_chartCoeff hU hsat hP k).contDiffAt (hU.mem_nhds hw)
  exact Complex.reCLM.contDiff.contDiffAt.comp w (ContDiffAt.sum fun k _ =>
    (hc k).mul (contDiff_charE_angles k).contDiffAt)

end HD11964.Cover

end
