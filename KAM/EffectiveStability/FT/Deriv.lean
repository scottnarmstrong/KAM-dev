/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FT.Basic
public import KAM.EffectiveStability.Poly.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.RCLike.Basic

/-!
# Fourier–Taylor polynomials: formal derivatives and periodicity (track B, B4-FT)

* `ftDφ i`, `ftDJ i`: formal partial derivatives (`ftDφ` raises the `2π`-tag `e` by one and maps
  `(c, s) ↦ (k_i s, -k_i c)`);
* over `𝕜 ∈ {ℝ, ℂ}`: `ftEvalR_contDiff`, `ftEvalC_contDiff`, and the `fderiv` formulas
  `ftEvalR_fderiv_dφ`, `ftEvalR_fderiv_dJ`, `ftEvalC_fderiv_dφ`, `ftEvalC_fderiv_dJ`;
* periodicity: `ftEvalR_add_period`, `ftEvalC_add_period`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- Formal derivative of a monomial in the angle `φ_i`. -/
def ftMonoDφ (i : ℕ) (m : FTMono) : FTMono :=
  ⟨m.k, m.α, m.e + 1, (m.k.getD i 0 : ℚ) * m.s, -((m.k.getD i 0 : ℚ) * m.c)⟩

/-- Formal derivative of a monomial in the action `J_i`. -/
def ftMonoDJ (i : ℕ) (m : FTMono) : FTPoly :=
  if m.α.getD i 0 = 0 then [] else
    [⟨m.k, m.α.set i (m.α.getD i 0 - 1), m.e, m.c * (m.α.getD i 0 : ℚ),
      m.s * (m.α.getD i 0 : ℚ)⟩]

/-- Formal partial derivative in `φ_i`. -/
def ftDφ (i : ℕ) (P : FTPoly) : FTPoly := P.map (ftMonoDφ i)

/-- Formal partial derivative in `J_i`. -/
def ftDJ (i : ℕ) (P : FTPoly) : FTPoly := P.flatMap (ftMonoDJ i)

@[simp] theorem ftDφ_nil (i : ℕ) : ftDφ i ([] : FTPoly) = [] := rfl
@[simp] theorem ftDJ_nil (i : ℕ) : ftDJ i ([] : FTPoly) = [] := rfl
theorem ftDφ_cons (i : ℕ) (m : FTMono) (P : FTPoly) :
    ftDφ i (m :: P) = ftMonoDφ i m :: ftDφ i P := rfl
theorem ftDJ_cons (i : ℕ) (m : FTMono) (P : FTPoly) :
    ftDJ i (m :: P) = ftMonoDJ i m ++ ftDJ i P := rfl

section Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : ℕ} (cf sf : 𝕜 → 𝕜) (p : 𝕜)

/-- The `J_i`-derivative of `∏ J_k^{α_k}`. -/
def ftJDeriv (α : List ℕ) (J : Fin n → 𝕜) (i : Fin n) : 𝕜 :=
  (α.getD i 0 : 𝕜) * (J i ^ (α.getD i 0 - 1) * ∏ k ∈ Finset.univ.erase i, J k ^ α.getD k 0)

theorem ftEvalG_dJ_mono (i : Fin n) (m : FTMono) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftMonoDJ i m) z = (2 * p) ^ m.e * ((m.c : 𝕜) * cf (2 * p * ftPhase m.k z.1) +
      (m.s : 𝕜) * sf (2 * p * ftPhase m.k z.1)) * ftJDeriv m.α z.2 i := by
  unfold ftMonoDJ
  by_cases h : m.α.getD i 0 = 0
  · simp only [h, ↓reduceIte]
    simp only [ftEvalG_nil, ftJDeriv, h, Nat.cast_zero, zero_mul, mul_zero]
  · have hprod : ∏ k ∈ Finset.univ.erase i,
        z.2 k ^ (m.α.set i (m.α.getD i 0 - 1)).getD k 0 =
        ∏ k ∈ Finset.univ.erase i, z.2 k ^ m.α.getD k 0 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      rw [getD_set_of_ne_zero _ _ _ _ h]
      simp only [hk', ite_false]
    simp only [h, ↓reduceIte, ftEvalG_cons, ftEvalG_nil, add_zero, ftMonoEvalG, ftJProd, ftJDeriv]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hprod,
      getD_set_of_ne_zero _ _ _ _ h]
    simp only [ite_true]
    push_cast
    ring

theorem ftMonoEvalG_dφ (i : ℕ) (m : FTMono) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftMonoEvalG cf sf p (ftMonoDφ i m) z = (2 * p) ^ (m.e + 1) *
      (((m.k.getD i 0 : ℤ) : 𝕜) * ((m.s : 𝕜) * cf (2 * p * ftPhase m.k z.1) -
        (m.c : 𝕜) * sf (2 * p * ftPhase m.k z.1))) * ftJProd m.α z.2 := by
  simp only [ftMonoDφ, ftMonoEvalG]
  push_cast
  ring

omit [CharZero 𝕜] in
theorem ftPhase_lin (k : List ℤ) (a b : Fin n → 𝕜) (t : 𝕜) :
    ftPhase k (a + t • b) = ftPhase k a + t * ftPhase k b := by
  unfold ftPhase
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Generic

section Calculus

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (cf sf : 𝕜 → 𝕜) (p : 𝕜)

theorem hasDerivAt_ftJProd (α : List ℕ) (J w : Fin n → 𝕜) :
    HasDerivAt (fun t : 𝕜 => ftJProd α (J + t • w)) (∑ i : Fin n, w i * ftJDeriv α J i) 0 := by
  have hg : ∀ i : Fin n, HasDerivAt (fun t : 𝕜 => (J i + t * w i) ^ α.getD i 0)
      ((α.getD i 0 : 𝕜) * J i ^ (α.getD i 0 - 1) * w i) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : 𝕜 => J i + t * w i) (w i) 0 :=
      HasDerivAt.congr_deriv (HasDerivAt.const_add (J i)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : 𝕜)) (w i))) (one_mul _)
    exact HasDerivAt.congr_deriv (HasDerivAt.pow h1 (α.getD i 0)) (by simp)
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : 𝕜)) fun i _ => hg i
  have hfun : (fun t : 𝕜 => ftJProd α (J + t • w)) =
      fun t : 𝕜 => ∏ i : Fin n, (J i + t * w i) ^ α.getD i 0 := by
    funext t; simp [ftJProd]
  rw [hfun]
  refine HasDerivAt.congr_deriv hp ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ftJDeriv, smul_eq_mul, zero_mul, add_zero]
  ring

variable {cf sf}

/-- The line-derivative of one monomial. -/
theorem hasDerivAt_ftMonoEvalG (hcf : ∀ x, HasDerivAt cf (-sf x) x)
    (hsf : ∀ x, HasDerivAt sf (cf x) x) (m : FTMono) (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    HasDerivAt (fun t : 𝕜 => ftMonoEvalG cf sf p m (z + t • v))
      (∑ i : Fin n, (v.1 i * ftMonoEvalG cf sf p (ftMonoDφ i m) z +
        v.2 i * ftEvalG cf sf p (ftMonoDJ i m) z)) 0 := by
  set ph0 := ftPhase m.k z.1 with hph0
  set phv := ftPhase m.k v.1 with hphv
  have hg : HasDerivAt (fun t : 𝕜 => 2 * p * (ph0 + t * phv)) (2 * p * phv) 0 := by
    have := ((((hasDerivAt_id (0 : 𝕜)).mul_const phv).const_add ph0).const_mul (2 * p))
    simpa using this
  have hc := (hcf (2 * p * (ph0 + 0 * phv))).comp (0 : 𝕜) hg
  have hs := (hsf (2 * p * (ph0 + 0 * phv))).comp (0 : 𝕜) hg
  have hj := hasDerivAt_ftJProd m.α z.2 v.2
  have hmain := ((((hc.const_mul (m.c : 𝕜)).add (hs.const_mul (m.s : 𝕜))).const_mul
    ((2 * p) ^ m.e)).mul hj)
  have hfun : (fun t : 𝕜 => ftMonoEvalG cf sf p m (z + t • v)) =
      fun t : 𝕜 => (2 * p) ^ m.e * ((m.c : 𝕜) * (cf ∘ fun t : 𝕜 => 2 * p * (ph0 + t * phv)) t +
        (m.s : 𝕜) * (sf ∘ fun t : 𝕜 => 2 * p * (ph0 + t * phv)) t) *
        ftJProd m.α (z.2 + t • v.2) := by
    funext t
    simp only [ftMonoEvalG, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      ftPhase_lin, Function.comp]
    rfl
  rw [hfun]
  refine HasDerivAt.congr_deriv hmain ?_
  have e1 : ∑ i : Fin n, v.1 i * ftMonoEvalG cf sf p (ftMonoDφ i m) z =
      (2 * p) ^ m.e * (2 * p * phv) * ((m.s : 𝕜) * cf (2 * p * ph0) -
        (m.c : 𝕜) * sf (2 * p * ph0)) * ftJProd m.α z.2 := by
    have hterm : ∀ i : Fin n, v.1 i * ftMonoEvalG cf sf p (ftMonoDφ i m) z =
        (((m.k.getD i 0 : ℤ) : 𝕜) * v.1 i) * ((2 * p) ^ m.e * (2 * p) *
          ((m.s : 𝕜) * cf (2 * p * ph0) - (m.c : 𝕜) * sf (2 * p * ph0)) * ftJProd m.α z.2) :=
      fun i => by rw [ftMonoEvalG_dφ, pow_succ]; ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul]
    have hs : ∑ i : Fin n, ((m.k.getD i 0 : ℤ) : 𝕜) * v.1 i = phv := rfl
    rw [hs]; ring
  have e2 : ∑ i : Fin n, v.2 i * ftEvalG cf sf p (ftMonoDJ i m) z =
      (2 * p) ^ m.e * ((m.c : 𝕜) * cf (2 * p * ph0) + (m.s : 𝕜) * sf (2 * p * ph0)) *
        ∑ i : Fin n, v.2 i * ftJDeriv m.α z.2 i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ftEvalG_dJ_mono]
    ring
  rw [Finset.sum_add_distrib, e1, e2]
  simp only [Function.comp, Pi.add_apply, zero_smul, add_zero, zero_mul]
  ring

theorem hasDerivAt_ftEvalG (hcf : ∀ x, HasDerivAt cf (-sf x) x)
    (hsf : ∀ x, HasDerivAt sf (cf x) x) (P : FTPoly) (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    HasDerivAt (fun t : 𝕜 => ftEvalG cf sf p P (z + t • v))
      (∑ i : Fin n, (v.1 i * ftEvalG cf sf p (ftDφ i P) z +
        v.2 i * ftEvalG cf sf p (ftDJ i P) z)) 0 := by
  induction P with
  | nil => simpa using hasDerivAt_const (0 : 𝕜) (0 : 𝕜)
  | cons m P ih =>
    have hfun : (fun t : 𝕜 => ftEvalG cf sf p (m :: P) (z + t • v)) =
        fun t : 𝕜 => ftMonoEvalG cf sf p m (z + t • v) + ftEvalG cf sf p P (z + t • v) :=
      funext fun t => ftEvalG_cons cf sf p _ _ _
    rw [hfun]
    refine HasDerivAt.congr_deriv (HasDerivAt.add (hasDerivAt_ftMonoEvalG p hcf hsf m z v) ih) ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ftDφ_cons, ftDJ_cons, ftEvalG_cons, ftEvalG_append]
    ring

theorem contDiff_ftMonoEvalG {k : WithTop ℕ∞} (hcf : ContDiff 𝕜 k cf) (hsf : ContDiff 𝕜 k sf)
    (m : FTMono) :
    ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftMonoEvalG cf sf p m z) := by
  have hph : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftPhase m.k z.1) := by
    unfold ftPhase
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_pi.1 contDiff_fst i)
  have hj : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftJProd m.α z.2) := by
    unfold ftJProd
    exact contDiff_prod fun i _ => (contDiff_pi.1 contDiff_snd i).pow _
  have hg : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => 2 * p * ftPhase m.k z.1) :=
    contDiff_const.mul hph
  unfold ftMonoEvalG
  exact (contDiff_const.mul ((contDiff_const.mul (hcf.comp hg)).add
    (contDiff_const.mul (hsf.comp hg)))).mul hj

theorem contDiff_ftEvalG {k : WithTop ℕ∞} (hcf : ContDiff 𝕜 k cf) (hsf : ContDiff 𝕜 k sf)
    (P : FTPoly) :
    ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) := by
  induction P with
  | nil => simpa using contDiff_const
  | cons m P ih =>
    have : (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p (m :: P) z) =
        fun z => ftMonoEvalG cf sf p m z + ftEvalG cf sf p P z :=
      funext fun z => ftEvalG_cons cf sf p m P z
    rw [this]
    exact (contDiff_ftMonoEvalG p hcf hsf m).add ih

/-- The general derivative formula. -/
theorem fderiv_ftEvalG_apply (hcf : ContDiff 𝕜 1 cf) (hsf : ContDiff 𝕜 1 sf)
    (hcf' : ∀ x, HasDerivAt cf (-sf x) x) (hsf' : ∀ x, HasDerivAt sf (cf x) x) (P : FTPoly)
    (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) z v =
      ∑ i : Fin n, (v.1 i * ftEvalG cf sf p (ftDφ i P) z +
        v.2 i * ftEvalG cf sf p (ftDJ i P) z) := by
  have hd : DifferentiableAt 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) z :=
    ((contDiff_ftEvalG p hcf hsf P).differentiable one_ne_zero).differentiableAt
  have hl : HasDerivAt (fun t : 𝕜 => z + t • v) v 0 := by
    exact HasDerivAt.congr_deriv (HasDerivAt.const_add z
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) v)) (one_smul _ _)
  have hd' : HasFDerivAt (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z)
      (fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) z)
      (z + (0 : 𝕜) • v) := by
    simpa using hd.hasFDerivAt
  have h2 := hd'.comp_hasDerivAt (0 : 𝕜) hl
  exact ((hasDerivAt_ftEvalG p hcf' hsf' P z v).unique h2).symm

theorem fderiv_ftEvalG_dφ (hcf : ContDiff 𝕜 1 cf) (hsf : ContDiff 𝕜 1 sf)
    (hcf' : ∀ x, HasDerivAt cf (-sf x) x) (hsf' : ∀ x, HasDerivAt sf (cf x) x) (P : FTPoly)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (i : Fin n) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) z (Pi.single i 1, 0) =
      ftEvalG cf sf p (ftDφ i P) z := by
  rw [fderiv_ftEvalG_apply p hcf hsf hcf' hsf', Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem fderiv_ftEvalG_dJ (hcf : ContDiff 𝕜 1 cf) (hsf : ContDiff 𝕜 1 sf)
    (hcf' : ∀ x, HasDerivAt cf (-sf x) x) (hsf' : ∀ x, HasDerivAt sf (cf x) x) (P : FTPoly)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (i : Fin n) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => ftEvalG cf sf p P z) z (0, Pi.single i 1) =
      ftEvalG cf sf p (ftDJ i P) z := by
  rw [fderiv_ftEvalG_apply p hcf hsf hcf' hsf', Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

end Calculus

/-! ### Periodicity -/

section Periodic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : ℕ} {cf sf : 𝕜 → 𝕜} {p : 𝕜}

omit [CharZero 𝕜] in
theorem ftPhase_add_int (k : List ℤ) (φ : Fin n → 𝕜) (m : Fin n → ℤ) :
    ftPhase k (φ + fun i => (m i : 𝕜)) =
      ftPhase k φ + ((∑ i : Fin n, k.getD i 0 * m i : ℤ) : 𝕜) := by
  unfold ftPhase
  push_cast
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

omit [CharZero 𝕜] in
/-- Periodicity of the evaluation under integer angle shifts, given a periodic `cos`/`sin`. -/
theorem ftEvalG_add_period (hc : ∀ (a : 𝕜) (N : ℤ), cf (a + N * (2 * p)) = cf a)
    (hs : ∀ (a : 𝕜) (N : ℤ), sf (a + N * (2 * p)) = sf a) (P : FTPoly)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (m : Fin n → ℤ) :
    ftEvalG cf sf p P (z + ((fun i => (m i : 𝕜), 0) : (Fin n → 𝕜) × (Fin n → 𝕜))) =
      ftEvalG cf sf p P z := by
  induction P with
  | nil => simp
  | cons mo P ih =>
    rw [ftEvalG_cons, ftEvalG_cons, ih]
    congr 1
    simp only [ftMonoEvalG, Prod.fst_add, Prod.snd_add, add_zero, ftPhase_add_int]
    have e : ∀ N : ℤ, 2 * p * (ftPhase mo.k z.1 + (N : 𝕜)) =
        2 * p * ftPhase mo.k z.1 + N * (2 * p) := fun N => by ring
    rw [e, hc, hs]

end Periodic

/-! ### Real and complex instances -/

variable {n : ℕ}

theorem ftEvalR_contDiff (P : FTPoly) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) :=
  contDiff_ftEvalG Real.pi Real.contDiff_cos Real.contDiff_sin P

theorem ftEvalC_contDiff (P : FTPoly) (k : WithTop ℕ∞) :
    ContDiff ℂ k (fun z : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC P z) :=
  contDiff_ftEvalG (Real.pi : ℂ) Complex.contDiff_cos Complex.contDiff_sin P

theorem ftEvalC_differentiable (P : FTPoly) :
    Differentiable ℂ (fun z : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC P z) :=
  (ftEvalC_contDiff P 1).differentiable one_ne_zero

theorem ftEvalR_fderiv_dφ (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) x (Pi.single i 1, 0) =
      ftEvalR (ftDφ i P) x :=
  fderiv_ftEvalG_dφ Real.pi Real.contDiff_cos Real.contDiff_sin Real.hasDerivAt_cos
    Real.hasDerivAt_sin P x i

theorem ftEvalR_fderiv_dJ (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) x (0, Pi.single i 1) =
      ftEvalR (ftDJ i P) x :=
  fderiv_ftEvalG_dJ Real.pi Real.contDiff_cos Real.contDiff_sin Real.hasDerivAt_cos
    Real.hasDerivAt_sin P x i

theorem ftEvalC_fderiv_dφ (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) (i : Fin n) :
    fderiv ℂ (fun z : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC P z) z (Pi.single i 1, 0) =
      ftEvalC (ftDφ i P) z :=
  fderiv_ftEvalG_dφ (Real.pi : ℂ) Complex.contDiff_cos Complex.contDiff_sin Complex.hasDerivAt_cos
    Complex.hasDerivAt_sin P z i

theorem ftEvalC_fderiv_dJ (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) (i : Fin n) :
    fderiv ℂ (fun z : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC P z) z (0, Pi.single i 1) =
      ftEvalC (ftDJ i P) z :=
  fderiv_ftEvalG_dJ (Real.pi : ℂ) Complex.contDiff_cos Complex.contDiff_sin Complex.hasDerivAt_cos
    Complex.hasDerivAt_sin P z i

theorem ftEvalR_add_period (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) (m : Fin n → ℤ) :
    ftEvalR P (x + ((fun i => (m i : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ))) = ftEvalR P x :=
  ftEvalG_add_period (fun a N => by
      simpa [mul_comm] using Real.cos_add_int_mul_two_pi a N)
    (fun a N => by simpa [mul_comm] using Real.sin_add_int_mul_two_pi a N) P x m

theorem ftEvalC_add_period (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) (m : Fin n → ℤ) :
    ftEvalC P (z + ((fun i => (m i : ℂ), 0) : (Fin n → ℂ) × (Fin n → ℂ))) = ftEvalC P z :=
  ftEvalG_add_period (fun a N => by
      simpa [mul_comm] using Complex.cos_add_int_mul_two_pi a N)
    (fun a N => by simpa [mul_comm] using Complex.sin_add_int_mul_two_pi a N) P z m

end KAM.EffectiveStability
