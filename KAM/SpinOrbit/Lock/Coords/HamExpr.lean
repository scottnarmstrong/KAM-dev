/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Coords.Complex
public import KAM.SpinOrbit.Rotated

/-!
# SO-LOCK coordinates: the transformed Hamiltonian as an expression

Design SO-LOCK §3. `lockHamExpr Ω cs` is
`K = J̃ + Y²/2 − c′²/2 + X c″ + V(φ + c + X, φ) − 1/2` in the expression language, with the two
square roots `X = √((1/Ω · I)/π) sin 2πα`, `Y = √((Ω · I)/π) cos 2πα` and the potential split
by the addition formula, `A = 4π(c + X)`:
`V = −cos A · Σ_m εA_m cos 2π(2−m)φ + sin A · Σ_{m≠2} εA_m sin 2π(2−m)φ`.
The node order is that of the LOCK-GEN-2 emitter (`scripts/spin_orbit/lock_ham.py`, form
`"design"`): sums are right-nested (`lockAddAll`), the centre sums run over `j < cs.length` with
keys `(0, j + 1)`, the forcing sums over `m = 1, …, 7` (the sine sum skips `m = 2`).

* `lockHamExpr_eval`: for every `Ω` and `z`, `eval = soRotHC ∘ lockToRotC` (purely algebraic);
* `nonvanishingOn_lockHamExpr`: both square-root operands have positive real part on
  `lockCertRegion = {0 < Re I}` for `0 < Ω`;
* `lockHamExpr_clock`: `∂_{J̃} K ≡ 1` where `0 < Re I`, for `0 < Ω`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

open KAM.Certificate

/-! ### The tree -/

/-- The right-nested sum `t₀ + (t₁ + (⋯ + tₗ))` (`0` for the empty list). -/
def lockAddAll : List (HamExpr 2) → HamExpr 2
  | [] => .const 0
  | [t] => t
  | t :: ts => .add t (lockAddAll ts)

@[simp] theorem lockAddAll_singleton (t : HamExpr 2) : lockAddAll [t] = t := rfl

@[simp] theorem lockAddAll_cons_cons (t u : HamExpr 2) (us : List (HamExpr 2)) :
    lockAddAll (t :: u :: us) = .add t (lockAddAll (u :: us)) := rfl

/-- `2πk` as an expression. -/
def lockTwoPiExpr (k : ℚ) : HamExpr 2 := .mul (.const (2 * k)) .pi

/-- `X = √((1/Ω · I)/π) sin 2πα`. -/
def lockXExpr (Ω : ℚ) : HamExpr 2 :=
  .mul (.sqrt (.div (.mul (.const (1 / Ω)) (.action 0)) .pi)) (.sinMode [1, 0])

/-- `Y = √((Ω · I)/π) cos 2πα`. -/
def lockYExpr (Ω : ℚ) : HamExpr 2 :=
  .mul (.sqrt (.div (.mul (.const Ω) (.action 0)) .pi)) (.cosMode [1, 0])

/-- The centre `c = Σ_j cs_j sin 2π(j+1)φ`. -/
def lockCentreExpr (cs : List ℚ) : HamExpr 2 :=
  lockAddAll ((List.range cs.length).map fun j =>
    .mul (.const (cs.getD j 0)) (.sinMode [0, (j : ℤ) + 1]))

/-- `c′ = Σ_j cs_j 2π(j+1) cos 2π(j+1)φ`. -/
def lockCentreDExpr (cs : List ℚ) : HamExpr 2 :=
  lockAddAll ((List.range cs.length).map fun j =>
    .mul (.mul (.const (cs.getD j 0)) (lockTwoPiExpr ((j : ℚ) + 1))) (.cosMode [0, (j : ℤ) + 1]))

/-- `c″ = Σ_j (−cs_j) (2π(j+1))² sin 2π(j+1)φ`. -/
def lockCentreDDExpr (cs : List ℚ) : HamExpr 2 :=
  lockAddAll ((List.range cs.length).map fun j =>
    .mul (.mul (.const (-cs.getD j 0)) (.pow (lockTwoPiExpr ((j : ℚ) + 1)) 2))
      (.sinMode [0, (j : ℤ) + 1]))

/-- The forcing modes `m = 1, …, 7`. -/
def lockForcingModes : List ℕ := (List.range 7).map (· + 1)

/-- `εA_m cos 2π(2−m)φ` (the constant `εA_2` for `m = 2`). -/
def lockForcingCosTerm (m : ℕ) : HamExpr 2 :=
  if m = 2 then .const (soEpsQ * soAQ m)
  else .mul (.const (soEpsQ * soAQ m)) (.cosMode [0, 2 - (m : ℤ)])

/-- `εA_m sin 2π(2−m)φ`. -/
def lockForcingSinTerm (m : ℕ) : HamExpr 2 :=
  .mul (.const (soEpsQ * soAQ m)) (.sinMode [0, 2 - (m : ℤ)])

/-- `Σ_m εA_m cos 2π(2−m)φ`. -/
def lockForcingCos : HamExpr 2 := lockAddAll (lockForcingModes.map lockForcingCosTerm)

/-- `Σ_{m≠2} εA_m sin 2π(2−m)φ`. -/
def lockForcingSin : HamExpr 2 :=
  lockAddAll ((lockForcingModes.filter (· ≠ 2)).map lockForcingSinTerm)

/-- `V(φ + c + X, φ) = −cos A · Σ εA_m cos 2π(2−m)φ + sin A · Σ εA_m sin 2π(2−m)φ`,
`A = 4π(c + X)`. -/
def lockPotentialExpr (Ω : ℚ) (cs : List ℚ) : HamExpr 2 :=
  let A : HamExpr 2 := .mul (lockTwoPiExpr 2) (.add (lockCentreExpr cs) (lockXExpr Ω))
  .add (.mul (.const (-1)) (.mul (.cos A) lockForcingCos)) (.mul (.sin A) lockForcingSin)

/-- The transformed Hamiltonian `K = J̃ + Y²/2 − c′²/2 + X c″ + V(φ + c + X, φ) − 1/2` as an
expression (two square roots; LOCK-GEN-2 node order). -/
def lockHamExpr (Ω : ℚ) (cs : List ℚ) : HamExpr 2 :=
  lockAddAll [.action 1, .mul (.const (1 / 2)) (.pow (lockYExpr Ω) 2),
    .mul (.const (-1 / 2)) (.pow (lockCentreDExpr cs) 2),
    .mul (lockXExpr Ω) (lockCentreDDExpr cs), lockPotentialExpr Ω cs, .const (-1 / 2)]

/-! ### Evaluation -/

theorem eval_lockAddAll (l : List (HamExpr 2)) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockAddAll l).eval z = (l.map fun e => e.eval z).sum := by
  induction l with
  | nil => simp [lockAddAll, HamExpr.eval]
  | cons t ts ih =>
    cases ts with
    | nil => simp [lockAddAll]
    | cons u us => simp [lockAddAll, HamExpr.eval, ih]

theorem eval_lockAddAll_map {α : Type*} (f : α → HamExpr 2) (l : List α)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockAddAll (l.map f)).eval z = (l.map fun a => (f a).eval z).sum := by
  rw [eval_lockAddAll, List.map_map]
  rfl

theorem modePhase_zero_key (k : ℤ) (θ : Fin 2 → ℂ) :
    modePhase 2 [0, k] θ = 2 * π * ((k : ℂ) * θ 1) := by
  simp [modePhase, certKeyFun, Fin.sum_univ_two]

theorem modePhase_alpha (θ : Fin 2 → ℂ) : modePhase 2 [1, 0] θ = 2 * π * θ 0 := by
  simp [modePhase, certKeyFun, Fin.sum_univ_two]

theorem eval_lockXExpr (Ω : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockXExpr Ω).eval z = sqrtE (z.2 0 / (π * (Ω : ℂ))) * Complex.sin (2 * π * z.1 0) := by
  simp only [lockXExpr, HamExpr.eval, modePhase_alpha]
  congr 2
  push_cast
  ring

theorem eval_lockYExpr (Ω : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockYExpr Ω).eval z = sqrtE (z.2 0 * (Ω : ℂ) / π) * Complex.cos (2 * π * z.1 0) := by
  simp only [lockYExpr, HamExpr.eval, modePhase_alpha]
  congr 2
  ring

theorem eval_lockCentreExpr (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockCentreExpr cs).eval z = lockCentreC cs (z.1 1) := by
  rw [lockCentreExpr, eval_lockAddAll_map, lockCentreC]
  refine congrArg List.sum <| List.map_congr_left fun j _ => ?_
  simp only [HamExpr.eval, modePhase_zero_key]
  push_cast
  ring_nf

theorem eval_lockCentreDExpr (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockCentreDExpr cs).eval z = lockCentreDC cs (z.1 1) := by
  rw [lockCentreDExpr, eval_lockAddAll_map, lockCentreDC]
  refine congrArg List.sum <| List.map_congr_left fun j _ => ?_
  simp only [HamExpr.eval, lockTwoPiExpr, modePhase_zero_key]
  push_cast
  ring_nf

theorem eval_lockCentreDDExpr (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockCentreDDExpr cs).eval z = lockCentreDDC cs (z.1 1) := by
  rw [lockCentreDDExpr, eval_lockAddAll_map, lockCentreDDC]
  refine congrArg List.sum <| List.map_congr_left fun j _ => ?_
  simp only [HamExpr.eval, lockTwoPiExpr, modePhase_zero_key]
  push_cast
  ring_nf

theorem eval_lockForcingCosTerm (m : ℕ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockForcingCosTerm m).eval z =
      ((soEpsQ * soAQ m : ℚ) : ℂ) * Complex.cos (2 * π * ((2 - (m : ℂ)) * z.1 1)) := by
  unfold lockForcingCosTerm
  split_ifs with h
  · subst h
    simp [HamExpr.eval]
  · simp only [HamExpr.eval, modePhase_zero_key]
    push_cast
    rfl

theorem eval_lockForcingSinTerm (m : ℕ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockForcingSinTerm m).eval z =
      ((soEpsQ * soAQ m : ℚ) : ℂ) * Complex.sin (2 * π * ((2 - (m : ℂ)) * z.1 1)) := by
  simp only [lockForcingSinTerm, HamExpr.eval, modePhase_zero_key]
  push_cast
  rfl

theorem sum_map_filter_ne_two (l : List ℕ) (f : ℕ → ℂ) (h : f 2 = 0) :
    ((l.filter (· ≠ 2)).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    split_ifs with hp
    · simp only [List.map_cons, List.sum_cons, ih]
    · have ha : a = 2 := by simpa using hp
      subst ha
      simp only [List.map_cons, List.sum_cons, ih, h, zero_add]

/-- The addition formula, summed:
`−cos A Σ c_m cos B_m + sin A Σ c_m sin B_m = −Σ c_m cos(A + B_m)`. -/
theorem lock_addition_sum (l : List ℕ) (A : ℂ) (c B : ℕ → ℂ) :
    -1 * (Complex.cos A * (l.map fun m => c m * Complex.cos (B m)).sum) +
      Complex.sin A * (l.map fun m => c m * Complex.sin (B m)).sum =
    -(l.map fun m => c m * Complex.cos (A + B m)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Complex.cos_add A (B a)]
    linear_combination ih

/-- The potential part: `V(Q₀ + Q₁, Q₁)` at `Q₀ = c + X`, `Q₁ = φ`. -/
theorem eval_lockPotentialExpr (Ω : ℚ) (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockPotentialExpr Ω cs).eval z =
      soVC ((lockCentreExpr cs).eval z + (lockXExpr Ω).eval z + z.1 1) (z.1 1) := by
  set u := (lockCentreExpr cs).eval z + (lockXExpr Ω).eval z
  have hA : (lockTwoPiExpr 2).eval z * ((lockCentreExpr cs).eval z + (lockXExpr Ω).eval z) =
      4 * π * u := by
    simp only [HamExpr.eval, lockTwoPiExpr, u]
    push_cast
    ring
  have hC : lockForcingCos.eval z = (lockForcingModes.map fun m =>
      ((soEpsQ * soAQ m : ℚ) : ℂ) * Complex.cos (2 * π * ((2 - (m : ℂ)) * z.1 1))).sum := by
    rw [lockForcingCos, eval_lockAddAll_map]
    simp only [eval_lockForcingCosTerm]
  have hS : lockForcingSin.eval z = (lockForcingModes.map fun m =>
      ((soEpsQ * soAQ m : ℚ) : ℂ) * Complex.sin (2 * π * ((2 - (m : ℂ)) * z.1 1))).sum := by
    rw [lockForcingSin, eval_lockAddAll_map]
    simp only [eval_lockForcingSinTerm]
    exact sum_map_filter_ne_two _ _ (by norm_num)
  have hV : soVC (u + z.1 1) (z.1 1) = -(lockForcingModes.map fun m =>
      ((soEpsQ * soAQ m : ℚ) : ℂ) *
        Complex.cos (4 * π * u + 2 * π * ((2 - (m : ℂ)) * z.1 1))).sum := by
    have hm : soModes = Finset.image (· + 1) (Finset.range 7) := by decide
    rw [soVC, hm, Finset.sum_image (by intro a _ b _ h; simpa using h), lockForcingModes,
      List.map_map, soHamExpr_list_sum_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [soA_eq_ratCast, soEps_eq_ratCast, Function.comp_apply]
    push_cast
    rw [show 2 * (π : ℂ) * (2 * (u + z.1 1) - ((m : ℂ) + 1) * z.1 1) =
      4 * π * u + 2 * π * ((2 - ((m : ℂ) + 1)) * z.1 1) by ring]
    ring
  simp only [lockPotentialExpr, HamExpr.eval]
  rw [hA, hC, hS, hV, Rat.cast_neg, Rat.cast_one]
  exact lock_addition_sum lockForcingModes (4 * π * u) (fun m => ((soEpsQ * soAQ m : ℚ) : ℂ))
    (fun m => 2 * π * ((2 - (m : ℂ)) * z.1 1))

/-- **Eval identity**, for every `Ω` and every `z`: purely algebraic (total `sqrtE`, no
`sqrtE² = z` used). It carries no analyticity claim. -/
theorem lockHamExpr_eval (Ω : ℚ) (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockHamExpr Ω cs).eval z = soRotHC (lockToRotC Ω cs z) := by
  rw [lockHamExpr, eval_lockAddAll]
  simp only [eval_lockPotentialExpr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    HamExpr.eval,
    eval_lockXExpr, eval_lockYExpr, eval_lockCentreExpr, eval_lockCentreDExpr,
    eval_lockCentreDDExpr, soRotHC, soHC, soRotMap, lockToRotC]
  simp
  ring

/-! ### The clock -/

theorem nonvanishingOn_lockAddAll {S : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))} (l : List (HamExpr 2))
    (h : ∀ e ∈ l, e.NonvanishingOn S) : (lockAddAll l).NonvanishingOn S := by
  induction l with
  | nil => simp [lockAddAll, HamExpr.NonvanishingOn]
  | cons t ts ih =>
    cases ts with
    | nil => simpa [lockAddAll] using h
    | cons u us =>
      exact ⟨h t (by simp), ih fun e he => h e (List.mem_cons_of_mem _ he)⟩

/-- The certified region `0 < Re I`. -/
def lockCertRegion : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ)) := {z | 0 < (z.2 0).re}

theorem isOpen_lockCertRegion : IsOpen lockCertRegion :=
  isOpen_lt continuous_const (Complex.continuous_re.comp ((continuous_apply 0).comp continuous_snd))

theorem re_ratCast_mul_div_pi_pos {q : ℚ} (hq : 0 < q) {w : ℂ} (hw : 0 < w.re) :
    0 < ((q : ℂ) * w / π).re := by
  have e : (q : ℂ) * w / π = (((q : ℝ) / π : ℝ) : ℂ) * w := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  have : (0 : ℝ) < q := by exact_mod_cast hq
  have := Real.pi_pos
  positivity

theorem nonvanishingOn_lockXExpr {Ω : ℚ} (hΩ : 0 < Ω) :
    (lockXExpr Ω).NonvanishingOn lockCertRegion := by
  simp only [lockXExpr, HamExpr.NonvanishingOn, HamExpr.eval]
  refine ⟨⟨⟨⟨trivial, trivial⟩, trivial, fun _ _ => by exact_mod_cast Real.pi_ne_zero⟩,
    fun z hz => re_ratCast_mul_div_pi_pos (by positivity) hz⟩, trivial⟩

theorem nonvanishingOn_lockYExpr {Ω : ℚ} (hΩ : 0 < Ω) :
    (lockYExpr Ω).NonvanishingOn lockCertRegion := by
  simp only [lockYExpr, HamExpr.NonvanishingOn, HamExpr.eval]
  exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, fun _ _ => by exact_mod_cast Real.pi_ne_zero⟩,
    fun z hz => re_ratCast_mul_div_pi_pos hΩ hz⟩, trivial⟩

theorem nonvanishingOn_lockPotentialExpr {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ) :
    (lockPotentialExpr Ω cs).NonvanishingOn lockCertRegion := by
  have hc : (lockCentreExpr cs).NonvanishingOn lockCertRegion :=
    nonvanishingOn_lockAddAll _ fun e he => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 he
      exact ⟨trivial, trivial⟩
  have hC : lockForcingCos.NonvanishingOn lockCertRegion :=
    nonvanishingOn_lockAddAll _ fun e he => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
      unfold lockForcingCosTerm
      split_ifs
      · trivial
      · exact ⟨trivial, trivial⟩
  have hS : lockForcingSin.NonvanishingOn lockCertRegion :=
    nonvanishingOn_lockAddAll _ fun e he => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
      exact ⟨trivial, trivial⟩
  have hA : (HamExpr.mul (lockTwoPiExpr 2) (.add (lockCentreExpr cs) (lockXExpr Ω))).NonvanishingOn
      lockCertRegion := ⟨⟨trivial, trivial⟩, hc, nonvanishingOn_lockXExpr hΩ⟩
  exact ⟨⟨trivial, hA, hC⟩, hA, hS⟩

theorem nonvanishingOn_lockHamExpr {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ) :
    (lockHamExpr Ω cs).NonvanishingOn lockCertRegion := by
  have hD : (lockCentreDExpr cs).NonvanishingOn lockCertRegion :=
    nonvanishingOn_lockAddAll _ fun e he => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 he
      exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  have hDD : (lockCentreDDExpr cs).NonvanishingOn lockCertRegion :=
    nonvanishingOn_lockAddAll _ fun e he => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 he
      exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  refine nonvanishingOn_lockAddAll _ fun e he => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · exact ⟨trivial, nonvanishingOn_lockYExpr hΩ⟩
  · exact ⟨trivial, hD⟩
  · exact ⟨nonvanishingOn_lockXExpr hΩ, hDD⟩
  · exact nonvanishingOn_lockPotentialExpr hΩ cs
  · trivial

/-- Clock: `∂_{J̃} K ≡ 1` on the certified region. Needs `0 < Ω`: for `Ω < 0` both sqrt operands
lie on the cut at real `I > 0` and `eval` is discontinuous there. -/
theorem lockHamExpr_clock (Ω : ℚ) (hΩ : 0 < Ω) (cs : List ℚ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : 0 < (z.2 0).re) :
    fderiv ℂ (lockHamExpr Ω cs).eval z (KAM.Certificate.phaseBasis (.inr 1)) = 1 := by
  have hd : DifferentiableAt ℂ (lockHamExpr Ω cs).eval z :=
    (((lockHamExpr Ω cs).contDiffOn_eval isOpen_lockCertRegion
      (nonvanishingOn_lockHamExpr hΩ cs)).contDiffAt
        (isOpen_lockCertRegion.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_apply_eq_deriv_line hd, phaseBasis_inr]
  have h : (fun t : ℂ => (lockHamExpr Ω cs).eval (z + t • ((0 : Fin 2 → ℂ), Pi.single 1 1))) =
      fun t => (lockHamExpr Ω cs).eval z + t := by
    funext t
    simp only [lockHamExpr_eval, soRotHC, soHC, soRotMap, lockToRotC]
    simp
    ring
  rw [h]
  simp

end KAM.SpinOrbit.Lock

end
