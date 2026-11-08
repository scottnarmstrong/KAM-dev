/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailMain
public import KAM.EffectiveStability.Tube.Check.HSplit
public import KAM.EffectiveStability.SJSU.Confinement.Shift
public import KAM.EffectiveStability.SJSU.Obs.Main
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst
public import KAM.EffectiveStability.SJSU.Ham.PolarForm
public import KAM.EffectiveStability.SJSU.Ledger.H.Main
public import KAM.EffectiveStability.SJSU.Ledger.Br.Main

/-!
# The rate check of the SJSU tube (T2-CONF, N9 (C))

For the observables `f_j = sjsuObs j` (N8) and N5a's `h̃ = sjsuHTilde sjsuB`, on the box
`|u_l| ≤ 2·10⁻⁶` (`sjsu_rate_le`):

  `|{f_j, h̃}(u, φ)| ≤ KEPT_j + DROP_j + ERR_j + TAIL_j`,

from N9 (B) with `h = h̃` (`reducedBracket_hTilde_bound`), fed by

* the monomial list `sjsuMons` (all `|t| ≤ 9`, each once) and N7's `h` certificates
  (`sjsu_hcerts`, `sjsu_hIdx_ne`), with N5a-2's bridge `sjsuHD_Ht_eq_hCoef` identifying N7's Horner
  sums with N5a's Taylor coefficients;
* N7's kept bounds `sjsuG` (`sjsu_G_bound`, degree `≤ 8`) and dropped bound `sjsuDrop`
  (`sjsu_drop_bound`);
* N8's partial bounds `sjsuFuMax`, `sjsuFphiMax`, and the remainder budget `sjsuRu`, `sjsuRp`
  (`sjsu_hRem_bounds`).

The four budgets are rational (`sjsuKeptQ`, `sjsuDrop`, `sjsuErrQ`, `sjsuTailQ`); the kernel checks
their sum against the literal rates `sjsuRateQ = (6, 23, 22)·10⁻¹⁹` (`sjsuRate_ok`; `sjsuEta` is its
cast to `ℝ`, not to be confused with the initial coordinate `sjsuEtaQ`), and
`5·10⁹ η_j < 10⁻⁶ / 2` (`sjsu_hTη`). These are the two hypotheses of the ordinary theorem's last
step (`sjsu_hη`, `sjsu_hTη`).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-! ### `sjsuMons` enumerates the monomials of degree `≤ 9` -/

theorem monOf_injective : Function.Injective monOf := fun a b h => by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [monOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem sjsuMons_nodup : (sjsuMons.map monOf).Nodup :=
  (List.nodup_map_iff monOf_injective).2 (by decide +kernel)

theorem sjsuMons_mem : ∀ t ∈ sjsuMons, t.1 + t.2.1 + t.2.2 ≤ 9 := by decide +kernel

theorem sjsuMons_cov' : ((List.range 10).all fun a => (List.range 10).all fun b =>
    (List.range 10).all fun c => !decide (a + b + c ≤ 9) || sjsuMons.contains (a, b, c)) =
      true := by
  decide +kernel

theorem sjsuMons_cov (a b c : ℕ) (h : a + b + c ≤ 9) : (a, b, c) ∈ sjsuMons := by
  have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 sjsuMons_cov' a
    (List.mem_range.2 (by omega))) b (List.mem_range.2 (by omega))) c (List.mem_range.2 (by omega))
  simpa [h] using this

/-! ### Models, true coefficients and certificates -/

/-- The model of `h_t` (N7's literal). -/
noncomputable def sjsuK (t : ℕ × ℕ × ℕ) : (Fin 2 → ℝ) → ℝ :=
  ((sjsuHD.H t).opd sjsuHD.P).eval sjsuHD.P.S

/-- The true coefficient `h_t` (N7's Horner sum). -/
noncomputable def sjsuHc (t : ℕ × ℕ × ℕ) : (Fin 2 → ℝ) → ℝ := sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt t

theorem sjsu_hcert : ∀ t ∈ sjsuMons, C1Close (sjsuHc t) (sjsuK t)
    (((sjsuHD.Hc t).e₀ : ℚ) : ℝ) (((sjsuHD.Hc t).e₁ : ℚ) : ℝ) := fun t ht =>
  (sjsu_hcerts ht (sjsu_hIdx_ne t ht)).close

theorem sjsu_hbr : ∀ t ∈ sjsuMons, ∀ φ,
    sjsuHc t φ = hCoef sjsuE sjsuN sjsuHwAll sjsuB (monOf t) φ := fun t _ φ =>
  sjsuHD_Ht_eq_hCoef t φ

/-! ### The budgets in `ℚ` -/

/-- `Fd_a = FuMax_a + FuMax_2`. -/
def sjsuFdQ (j : Fin 3) (a : Fin 2) : ℚ := sjsuFuMax j a.castSucc + sjsuFuMax j 2

/-- `Fp_a = FphiMax_a`. -/
def sjsuFpQ (j : Fin 3) (a : Fin 2) : ℚ := sjsuFphiMax j a

/-- `KEPT_j = Σ_{|p| ≤ 8} r^{|p|} G_{j,p}`. -/
def sjsuKeptQ (j : Fin 3) : ℚ :=
  ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 9, ∑ c ∈ Finset.range 9,
    if a + b + c ≤ 8 then sjsuTailR ^ (a + b + c) * sjsuG j (a, b, c) else 0

/-- `ERR_j` (the certificate errors of the `h` literals). -/
def sjsuErrQ (j : Fin 3) : ℚ :=
  ∑ a : Fin 2, (sjsuFdQ j a * (sjsuMons.map fun t =>
      sjsuTailR ^ mdeg (monOf t) * (sjsuHD.Hc t).e₁).sum +
    sjsuFpQ j a * ((sjsuMons.map fun t => (monOf t a.castSucc : ℚ) *
        sjsuTailR ^ mdeg (monOf t - Pi.single a.castSucc 1) * (sjsuHD.Hc t).e₀).sum +
      (sjsuMons.map fun t => (monOf t 2 : ℚ) * sjsuTailR ^ mdeg (monOf t - Pi.single 2 1) *
        (sjsuHD.Hc t).e₀).sum))

/-- `TAIL_j` (the Taylor remainder of `h̃`). -/
def sjsuTailQ (j : Fin 3) : ℚ :=
  ∑ a : Fin 2, (sjsuFdQ j a * sjsuRp + sjsuFpQ j a * (sjsuRu a.castSucc + sjsuRu 2))

/-! ### The rate bound -/

theorem sjsuHTilde_eq : sjsuHTilde sjsuB = hTildeOf sjsuE sjsuN sjsuHwAll sjsuB := rfl

theorem sjsuObs_eq (j : Fin 3) : sjsuObs j = listObs (Ftab j) (fun e => monOf e.1)
    (fun e => (e.2.opd Fprm.w Fprm.S).eval Fprm.S) := rfl

theorem sjsu_kept_cast (j : Fin 3) :
    bracketKept 8 ((sjsuTailR : ℚ) : ℝ) (fun p => ((sjsuG j (p 0, p 1, p 2) : ℚ) : ℝ)) =
      ((sjsuKeptQ j : ℚ) : ℝ) := by
  rw [bracketKept, sum_truncSet_fin3, sjsuKeptQ]
  simp only [Rat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp [mdeg, Fin.sum_univ_three]

theorem sjsu_err_cast (j : Fin 3) :
    bracketErr sjsuMons (fun t => monOf t) ((sjsuTailR : ℚ) : ℝ)
        (fun t => (((sjsuHD.Hc t).e₀ : ℚ) : ℝ)) (fun t => (((sjsuHD.Hc t).e₁ : ℚ) : ℝ))
        (fun a => (sjsuFdQ j a : ℝ)) (fun a => (sjsuFpQ j a : ℝ)) = ((sjsuErrQ j : ℚ) : ℝ) := by
  simp only [bracketErr, sjsuErrQ, Rat.cast_sum, Rat.cast_add, Rat.cast_mul, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_pow, Rat.cast_natCast]

theorem sjsu_tail_cast (j : Fin 3) :
    bracketTail (fun a => (sjsuFdQ j a : ℝ)) (fun a => (sjsuFpQ j a : ℝ))
        (fun i => (sjsuRu i : ℝ)) (sjsuRp : ℝ) = ((sjsuTailQ j : ℚ) : ℝ) := by
  simp only [bracketTail, sjsuTailQ, Rat.cast_sum, Rat.cast_add, Rat.cast_mul]

/-- **The rate bound** on the box, as the cast of `KEPT + DROP + ERR + TAIL`. -/
theorem sjsu_rate_le (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ)
    (hu : ∀ l, |u l| ≤ 2 / 10 ^ 6) :
    |reducedBracket (sjsuObs j) (sjsuHTilde sjsuB) (u, φ)| ≤
      ((sjsuKeptQ j + sjsuDrop j + sjsuErrQ j + sjsuTailQ j : ℚ) : ℝ) := by
  have hu' : ∀ l, |u l| ≤ ((sjsuTailR : ℚ) : ℝ) := fun l => by
    rw [sjsuTailR]; push_cast; linarith [hu l]
  have hpu : ∀ l, 0 < sjsuB φ l + u l := fun l => by
    have h1 := (sjsuB_bounds φ l).1
    have h2 := sjsu_rho_lt_bmin l
    have h3 := (abs_le.1 (hu l)).1
    linarith
  have hR := sjsu_hRem_bounds φ u fun l => by linarith [hu l]
  rw [sjsuObs_eq, sjsuHTilde_eq, Rat.cast_add, Rat.cast_add, Rat.cast_add, ← sjsu_kept_cast,
    ← sjsu_err_cast, ← sjsu_tail_cast]
  refine reducedBracket_hTilde_bound sjsuE sjsuN (Ftab j) _ _
    (fun e _ => Opd.differentiable_eval _ _) sjsuHwAll sjsuB differentiable_sjsuB sjsuB_pos
    sjsuMons sjsuMons_nodup sjsuMons_mem sjsuMons_cov sjsuK sjsuHc sjsu_hbr sjsu_hcert
    (L' := 8) (G := fun p => ((sjsuG j (p 0, p 1, p 2) : ℚ) : ℝ)) (sjsu_G_bound j) hu' φ
    (sjsu_drop_bound j hu' φ) (Fd := fun a => (sjsuFdQ j a : ℝ))
    (Fp := fun a => (sjsuFpQ j a : ℝ)) (fun a => ?_) (fun a => ?_) hpu hR.1 hR.2
  · have h1 := sjsu_hFu j u φ hu a.castSucc
    have h2 := sjsu_hFu j u φ hu 2
    simp only [sjsuFdQ, Rat.cast_add]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  · exact sjsu_hFφ j u φ hu a

/-! ### The rate check -/

/-- **The rates** `η = (6, 23, 22)·10⁻¹⁹` (rounded up from `KEPT + DROP + ERR + TAIL`). -/
def sjsuRateQ : Fin 3 → ℚ := ![6 / 10 ^ 19, 23 / 10 ^ 19, 22 / 10 ^ 19]

theorem sjsuRate_ok0 : sjsuKeptQ 0 + sjsuDrop 0 + sjsuErrQ 0 + sjsuTailQ 0 ≤ sjsuRateQ 0 := by
  decide +kernel

theorem sjsuRate_ok1 : sjsuKeptQ 1 + sjsuDrop 1 + sjsuErrQ 1 + sjsuTailQ 1 ≤ sjsuRateQ 1 := by
  decide +kernel

theorem sjsuRate_ok2 : sjsuKeptQ 2 + sjsuDrop 2 + sjsuErrQ 2 + sjsuTailQ 2 ≤ sjsuRateQ 2 := by
  decide +kernel

theorem sjsuRate_ok (j : Fin 3) :
    sjsuKeptQ j + sjsuDrop j + sjsuErrQ j + sjsuTailQ j ≤ sjsuRateQ j := by
  fin_cases j
  exacts [sjsuRate_ok0, sjsuRate_ok1, sjsuRate_ok2]

/-- **The rates** `η_j` of the bracket check, in `ℝ`. -/
noncomputable def sjsuEta (j : Fin 3) : ℝ := ((sjsuRateQ j : ℚ) : ℝ)

/-- **The rate check**: `|{f_j, h̃}| ≤ η_j` on the box. -/
theorem sjsu_hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    |reducedBracket (sjsuObs j) (sjsuHTilde sjsuB) (u, φ)| ≤ sjsuEta j := fun j u φ hu =>
  (sjsu_rate_le j u φ hu).trans (Rat.cast_le.2 (sjsuRate_ok j))

/-- **The time check**: `T η_j < δ / 2` with `T = 5·10⁹`, `δ = 10⁻⁶`. -/
theorem sjsu_hTη : ∀ j, 5 * 10 ^ 9 * sjsuEta j < 1 / 10 ^ 6 / 2 := fun j => by
  have h : 5 * 10 ^ 9 * sjsuRateQ j < 1 / 10 ^ 6 / 2 := by
    fin_cases j <;> simp [sjsuRateQ] <;> norm_num
  have h' := (Rat.cast_lt (K := ℝ)).2 h
  push_cast at h'
  exact h'

end KAM.EffectiveStability.SJSU

end
