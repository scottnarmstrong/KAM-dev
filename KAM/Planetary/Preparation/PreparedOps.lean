/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowCauchy
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Coordinate partials versus iterated derivatives (P11A-P8b2, brick for `pr-b`, `pr-c`, `pr-d`)

* `p11PartialVec_single`: `p11PartialVec (single j) f = fun x => fderiv ℂ f x (single j 1)`.
* `p11_iteratedFDeriv_eq_partial`: for `f` holomorphic on an open `U`, the iterated Fréchet
  derivative on the standard basis vectors `e_{k 1}, …, e_{k m}` is the coordinate partial
  `p11PartialVec α f` with `α c = #{i | k i = c}`.
* `p11_norm_iteratedFDeriv_le`: `‖D^m f x a‖ ≤ n^m * B` when every coordinate partial of order `m`
  is `≤ B` and `‖a i‖ ≤ 1`.
* `p11op_re_le`, `p11dg_re_le`: the real operator and diagonal jet norms of the real part of the
  real slice of `f`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section PartialIter

variable {n m : ℕ}

private theorem ops_step_congr {U : Set (P11CVec n)} (hU : IsOpen U) {f f' : P11CVec n → P11CVec m}
    (h : EqOn f f' U) (i : Fin n) : EqOn (p11Step i f) (p11Step i f') U := by
  intro x hx
  have : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  simp only [p11Step, this.fderiv_eq]

private theorem ops_foldl_congr {U : Set (P11CVec n)} (hU : IsOpen U) (l : List (Fin n)) :
    ∀ {f f' : P11CVec n → P11CVec m}, EqOn f f' U →
      EqOn (l.foldl (fun g i => p11Step i g) f) (l.foldl (fun g i => p11Step i g) f') U := by
  induction l with
  | nil => intro f f' h; exact h
  | cons a l ih => intro f f' h; exact ih (ops_step_congr hU h a)

private theorem ops_step_comm {U : Set (P11CVec n)} (hU : IsOpen U) {h : P11CVec n → P11CVec m}
    (hh : DifferentiableOn ℂ h U) (i j : Fin n) :
    EqOn (p11Step i (p11Step j h)) (p11Step j (p11Step i h)) U := by
  intro x hx
  have han := KAM.analyticOnNhd_of_differentiableOn hU hh
  have hca : ContDiffAt ℂ ω h x := (han x hx).contDiffAt
  have hsym := hca.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℂ (fderiv ℂ h) x := ((han.fderiv) x hx).differentiableAt
  have h1 : ∀ a b : Fin n, p11Step a (p11Step b h) x =
      fderiv ℂ (fderiv ℂ h) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    show fderiv ℂ (fun y => fderiv ℂ h y (Pi.single b 1)) x (Pi.single a 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [h1, h1]
  exact hsym _ _

private theorem ops_foldl_perm {U : Set (P11CVec n)} (hU : IsOpen U) {l l' : List (Fin n)}
    (hp : l.Perm l') : ∀ {h : P11CVec n → P11CVec m}, DifferentiableOn ℂ h U →
      EqOn (l.foldl (fun g i => p11Step i g) h) (l'.foldl (fun g i => p11Step i g) h) U := by
  induction hp with
  | nil => intro h _; exact fun _ _ => rfl
  | cons a _ ih =>
    intro h hh
    exact ih (p11Step_differentiableOn hU hh a)
  | swap a b l =>
    intro h hh
    exact ops_foldl_congr hU l (ops_step_comm hU hh a b)
  | trans _ _ ih1 ih2 =>
    intro h hh
    exact fun x hx => (ih1 hh hx).trans (ih2 hh hx)

private theorem ops_foldl_ofFn {U : Set (P11CVec n)} (hU : IsOpen U) {h : P11CVec n → P11CVec m}
    (hh : DifferentiableOn ℂ h U) : ∀ (r : ℕ) (k : Fin r → Fin n), ∀ x ∈ U,
      (List.ofFn k).foldl (fun g i => p11Step i g) h x =
        iteratedFDeriv ℂ r h x (fun i => Pi.single (k (Fin.rev i)) 1) := by
  have han := KAM.analyticOnNhd_of_differentiableOn hU hh
  intro r
  induction r with
  | zero => intro k x _; simp
  | succ r ih =>
    intro k x hx
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    set F := (List.ofFn fun i : Fin r => k i.castSucc).foldl (fun g i => p11Step i g) h with hF
    have hFG : F =ᶠ[𝓝 x] fun y => iteratedFDeriv ℂ r h y
        (fun i : Fin r => Pi.single (k (Fin.rev i).castSucc) 1) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => ih _ y hy
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ r h) x :=
      ((han.iteratedFDeriv r) x hx).differentiableAt
    show fderiv ℂ F x (Pi.single (k (Fin.last r)) 1) = _
    rw [hFG.fderiv_eq, iteratedFDeriv_succ_apply_left]
    have hG : fderiv ℂ (fun y => iteratedFDeriv ℂ r h y
        (fun i : Fin r => Pi.single (k (Fin.rev i).castSucc) 1)) x =
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin r => P11CVec n) (P11CVec m)
          (fun i : Fin r => Pi.single (k (Fin.rev i).castSucc) 1)).comp
            (fderiv ℂ (iteratedFDeriv ℂ r h) x) :=
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin r => P11CVec n) (P11CVec m)
        (fun i : Fin r => Pi.single (k (Fin.rev i).castSucc) 1)).hasFDerivAt.comp x
          hd.hasFDerivAt).fderiv
    rw [hG]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.apply_apply]
    congr 1
    ext i
    simp [Fin.tail, Fin.rev_succ]

private theorem ops_count_flatten (α : Fin n → ℕ) (c : Fin n) :
    (List.ofFn fun i : Fin n => List.replicate (α i) i).flatten.count c = α c := by
  rw [List.count_flatten, List.map_ofFn, List.sum_ofFn]
  simp [List.count_replicate, Finset.sum_ite_eq']

private theorem ops_count_ofFn : ∀ {r : ℕ} (k : Fin r → Fin n) (c : Fin n),
    (List.ofFn k).count c = ∑ i, if k i = c then 1 else 0 := by
  intro r
  induction r with
  | zero => intro k c; simp
  | succ r ih =>
    intro k c
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    simp [add_comm]

/-- The coordinate partial of order `α c = #{i | k i = c}` is the iterated derivative on the basis
vectors `e_{k i}`. -/
theorem p11_partial_eq_iteratedFDeriv {U : Set (P11CVec n)} (hU : IsOpen U)
    {f : P11CVec n → P11CVec m} (hf : DifferentiableOn ℂ f U) {r : ℕ} (k : Fin r → Fin n)
    {x : P11CVec n} (hx : x ∈ U) :
    p11PartialVec (fun c => ∑ i, if k i = c then 1 else 0) f x =
      iteratedFDeriv ℂ r f x (fun i => Pi.single (k i) 1) := by
  have hperm : (List.ofFn fun i : Fin n =>
      List.replicate (∑ j, if k j = i then 1 else 0) i).flatten.Perm
        (List.ofFn fun i : Fin r => k (Fin.rev i)) := by
    rw [List.perm_iff_count]
    intro c
    rw [ops_count_flatten, ops_count_ofFn]
    exact (Equiv.sum_comp Fin.revPerm fun i => if k i = c then 1 else 0).symm
  have h1 := ops_foldl_perm hU hperm hf hx
  have h2 := ops_foldl_ofFn hU hf r (fun i => k (Fin.rev i)) x hx
  simp only [Fin.rev_rev] at h2
  exact h1.trans h2

theorem p11PartialVec_single (f : P11CVec n → P11CVec m) (j : Fin n) :
    p11PartialVec (Pi.single j 1) f = fun x => fderiv ℂ f x (Pi.single j 1) := by
  have hl : (List.ofFn fun i : Fin n => List.replicate ((Pi.single j 1 : Fin n → ℕ) i) i).flatten
      = [j] := by
    have hp : (List.ofFn fun i : Fin n =>
        List.replicate ((Pi.single j 1 : Fin n → ℕ) i) i).flatten.Perm [j] := by
      rw [List.perm_iff_count]
      intro c
      rw [ops_count_flatten]
      rcases eq_or_ne c j with rfl | h
      · simp
      · simp [h, h.symm]
    exact List.Perm.eq_singleton hp
  unfold p11PartialVec
  rw [hl]
  rfl

/-- Order-`r` bound by the sup of the coordinate partials of order `r`. -/
theorem p11_norm_iteratedFDeriv_le {U : Set (P11CVec n)} (hU : IsOpen U)
    {f : P11CVec n → P11CVec m} (hf : DifferentiableOn ℂ f U) {x : P11CVec n} (hx : x ∈ U)
    {r : ℕ} {B : ℝ} (hB : ∀ α : Fin n → ℕ, ∑ i, α i = r → ‖p11PartialVec α f x‖ ≤ B)
    (a : Fin r → P11CVec n) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ‖iteratedFDeriv ℂ r f x a‖ ≤ (n : ℝ) ^ r * B := by
  have hexp : a = fun i => ∑ c : Fin n, a i c • (Pi.single c 1 : P11CVec n) := by
    funext i
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : iteratedFDeriv ℂ r f x a = ∑ k : Fin r → Fin n,
      (∏ i, a i (k i)) • iteratedFDeriv ℂ r f x (fun i => Pi.single (k i) 1) := by
    conv_lhs => rw [hexp]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr (by simp) fun k _ => ?_
    exact ContinuousMultilinearMap.map_smul_univ _ _ _
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k : Fin r → Fin n, ‖(∏ i, a i (k i)) •
      iteratedFDeriv ℂ r f x (fun i => Pi.single (k i) 1)‖ ≤ B := by
    intro k
    rw [norm_smul, ← p11_partial_eq_iteratedFDeriv hU hf k hx]
    have hprod : ‖∏ i, a i (k i)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun i _ => (norm_le_pi_norm (a i) (k i)).trans (ha i)
    have hα : ∑ c, (∑ i, if k i = c then 1 else 0) = r := by
      rw [Finset.sum_comm]; simp
    have := hB _ hα
    calc ‖∏ i, a i (k i)‖ * ‖p11PartialVec (fun c => ∑ i, if k i = c then 1 else 0) f x‖
        ≤ 1 * B := by
          exact mul_le_mul hprod this (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  calc ∑ k : Fin r → Fin n, ‖(∏ i, a i (k i)) •
        iteratedFDeriv ℂ r f x (fun i => Pi.single (k i) 1)‖
      ≤ ∑ _k : Fin r → Fin n, B := Finset.sum_le_sum fun k _ => hterm k
    _ = (n : ℝ) ^ r * B := by simp

end PartialIter

section RealSlice

variable {n m : ℕ}

/-- Coordinatewise real part as a real continuous linear map. -/
private def opsRe (m : ℕ) : P11CVec m →L[ℝ] P11Vec m :=
  ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i)

private theorem opsRe_apply (w : P11CVec m) (i : Fin m) : opsRe m w i = (w i).re := rfl

/-- The real jet of the coordinatewise real part of the real slice of `g` is the real part of the
complex jet on real vectors. -/
theorem p11_iteratedFDeriv_real_slice {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {y : P11Vec n}
    (hy : KAM.realInclusion n y ∈ U) (r : ℕ) (a : Fin r → P11Vec n) (i : Fin m) :
    iteratedFDeriv ℝ r (fun x : P11Vec n => fun l => (g (KAM.realInclusion n x) l).re) y a i =
      (iteratedFDeriv ℂ r g (KAM.realInclusion n y) (fun l => KAM.realInclusion n (a l)) i).re := by
  set ι := KAM.realInclusion n with hι
  have hcdC : ContDiffOn ℂ r g U :=
    (KAM.analyticOnNhd_of_differentiableOn hU hg).contDiffOn hU.uniqueDiffOn
  have hcdR : ContDiffOn ℝ r g U := hcdC.restrict_scalars ℝ
  have hUo : IsOpen (ι ⁻¹' U) := hU.preimage ι.continuous
  have h1 : iteratedFDeriv ℝ r (g ∘ ι) y =
      (iteratedFDeriv ℝ r g (ι y)).compContinuousLinearMap fun _ => ι := by
    have := ι.iteratedFDerivWithin_comp_right hcdR hU.uniqueDiffOn hUo.uniqueDiffOn hy le_rfl
    rwa [iteratedFDerivWithin_of_isOpen _ hUo, iteratedFDerivWithin_of_isOpen _ hU] at this
  have hat : ContDiffAt ℝ r (g ∘ ι) y :=
    (hcdR.contDiffAt (hU.mem_nhds hy)).comp y ι.contDiff.contDiffAt
  have h2 : (fun x : P11Vec n => fun l => (g (ι x) l).re) = opsRe m ∘ (g ∘ ι) := rfl
  rw [h2, (opsRe m).iteratedFDeriv_comp_left hat le_rfl, h1]
  have h3 := (hcdC.contDiffAt (hU.mem_nhds hy)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  simp only [Function.comp_apply] at h3
  simp [opsRe_apply, ← h3]

/-- Real jet norms of the real part of the real slice from the coordinate partials. -/
theorem p11_euclid_jet_re_le {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {y : P11Vec n}
    (hy : KAM.realInclusion n y ∈ U) {j : ℕ} {B : ℝ}
    (hB : ∀ α : Fin n → ℕ, ∑ i, α i = j → ‖p11PartialVec α g (KAM.realInclusion n y)‖ ≤ B)
    (a : Fin j → P11Vec n) (ha : ∀ i, p11euclid (a i) ≤ 1) :
    p11euclid (iteratedFDeriv ℝ j (fun x : P11Vec n => fun l => (g (KAM.realInclusion n x) l).re)
      y a) ≤ Real.sqrt m * ((n : ℝ) ^ j * B) := by
  have hcomp : ‖iteratedFDeriv ℂ j g (KAM.realInclusion n y)
      (fun l => KAM.realInclusion n (a l))‖ ≤ (n : ℝ) ^ j * B := by
    refine p11_norm_iteratedFDeriv_le hU hg hy hB _ fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => ?_
    have h1 : ‖a i c‖ ≤ p11euclid (a i) :=
      (norm_le_pi_norm (a i) c).trans (KAM.Nekhoroshev.norm_le_euclid (a i)).1
    simpa using h1.trans (ha i)
  refine (KAM.Nekhoroshev.norm_le_euclid _).2.1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hcomp)).2 fun l => ?_
  rw [p11_iteratedFDeriv_real_slice hU hg hy]
  exact ((Complex.abs_re_le_norm _).trans (norm_le_pi_norm _ l)).trans hcomp

theorem p11op_re_le {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {y : P11Vec n}
    (hy : KAM.realInclusion n y ∈ U) {j : ℕ} {B : ℝ}
    (hB : ∀ α : Fin n → ℕ, ∑ i, α i = j → ‖p11PartialVec α g (KAM.realInclusion n y)‖ ≤ B) :
    p11op (fun x : P11Vec n => fun l => (g (KAM.realInclusion n x) l).re) j y ≤
      Real.sqrt m * ((n : ℝ) ^ j * B) := by
  obtain ⟨a, ha, hval⟩ := p11op_attained (n := n) (m := m) (f := fun x : P11Vec n =>
    fun l => (g (KAM.realInclusion n x) l).re) (j := j) (y := y)
  rw [hval]
  exact p11_euclid_jet_re_le hU hg hy hB a ha

theorem p11dg_re_le (hn : 1 ≤ n) {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {y : P11Vec n}
    (hy : KAM.realInclusion n y ∈ U) {j : ℕ} {B : ℝ}
    (hB : ∀ α : Fin n → ℕ, ∑ i, α i = j → ‖p11PartialVec α g (KAM.realInclusion n y)‖ ≤ B) :
    p11dg (fun x : P11Vec n => fun l => (g (KAM.realInclusion n x) l).re) j y ≤
      Real.sqrt m * ((n : ℝ) ^ j * B) := by
  obtain ⟨a, ha, hval⟩ := p11dg_attained (n := n) (m := m) hn (f := fun x : P11Vec n =>
    fun l => (g (KAM.realInclusion n x) l).re) (j := j) (y := y)
  rw [hval]
  exact p11_euclid_jet_re_le hU hg hy hB _ fun _ => ha.le

end RealSlice

section PartialCalc

variable {n m : ℕ}

/-- Raising the multi-index by `e_c` is one more outer derivative `p11Step c`. -/
theorem p11_partial_step {U : Set (P11CVec n)} (hU : IsOpen U) {F : P11CVec n → P11CVec m}
    (hF : DifferentiableOn ℂ F U) (α : Fin n → ℕ) (c : Fin n) :
    EqOn (p11PartialVec α (p11Step c F)) (p11PartialVec (α + Pi.single c 1) F) U := by
  have hperm : (c :: (List.ofFn fun i : Fin n => List.replicate (α i) i).flatten).Perm
      (List.ofFn fun i : Fin n =>
        List.replicate ((α + Pi.single c 1 : Fin n → ℕ) i) i).flatten := by
    rw [List.perm_iff_count]
    intro d
    rw [List.count_cons, ops_count_flatten, ops_count_flatten]
    rcases eq_or_ne c d with rfl | h
    · simp
    · simp [h, Ne.symm h]
  exact ops_foldl_perm hU hperm hF

theorem p11_partial_congr {U : Set (P11CVec n)} (hU : IsOpen U) {F F' : P11CVec n → P11CVec m}
    (h : EqOn F F' U) (α : Fin n → ℕ) : EqOn (p11PartialVec α F) (p11PartialVec α F') U :=
  ops_foldl_congr hU _ h

/-- The partial derivatives of the sum of two holomorphic functions. -/
theorem p11_partial_add {U : Set (P11CVec n)} (hU : IsOpen U) {F G : P11CVec n → P11CVec m}
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U) (α : Fin n → ℕ) :
    EqOn (p11PartialVec α (F + G)) (p11PartialVec α F + p11PartialVec α G) U := by
  have key : ∀ (L : List (Fin n)) (F G : P11CVec n → P11CVec m), DifferentiableOn ℂ F U →
      DifferentiableOn ℂ G U → EqOn (L.foldl (fun g i => p11Step i g) (F + G))
        (L.foldl (fun g i => p11Step i g) F + L.foldl (fun g i => p11Step i g) G) U := by
    intro L
    induction L with
    | nil => intro F G _ _ x _; rfl
    | cons a L ih =>
      intro F G hF hG
      have h1 : EqOn (p11Step a (F + G)) (p11Step a F + p11Step a G) U := by
        intro x hx
        have hFa := (hF.differentiableAt (hU.mem_nhds hx))
        have hGa := (hG.differentiableAt (hU.mem_nhds hx))
        simp only [p11Step, Pi.add_apply]
        rw [fderiv_add hFa hGa]; rfl
      intro x hx
      exact (ops_foldl_congr hU L h1 hx).trans
        (ih _ _ (p11Step_differentiableOn hU hF a) (p11Step_differentiableOn hU hG a) hx)
  exact key _ F G hF hG

private theorem ops_foldl_clm {U : Set (P11CVec n)} (hU : IsOpen U) {m' : ℕ}
    (T : P11CVec m →L[ℂ] P11CVec m') :
    ∀ (L : List (Fin n)) (F : P11CVec n → P11CVec m), DifferentiableOn ℂ F U →
      EqOn (L.foldl (fun g i => p11Step i g) (fun x => T (F x)))
        (fun x => T (L.foldl (fun g i => p11Step i g) F x)) U := by
  intro L
  induction L with
  | nil => intro F _ x _; rfl
  | cons a L ih =>
    intro F hF
    have h1 : EqOn (p11Step a (fun x => T (F x))) (fun x => T (p11Step a F x)) U := by
      intro x hx
      have hFa := (hF.differentiableAt (hU.mem_nhds hx))
      simp only [p11Step]
      have := (T.hasFDerivAt.comp x hFa.hasFDerivAt).fderiv
      rw [show (fun x => T (F x)) = T ∘ F from rfl, this]
      rfl
    intro x hx
    exact (ops_foldl_congr hU L h1 hx).trans (ih _ (p11Step_differentiableOn hU hF a) hx)

/-- Linear maps commute with the partial derivatives. -/
theorem p11_partial_clm {U : Set (P11CVec n)} (hU : IsOpen U) {F : P11CVec n → P11CVec m}
    (hF : DifferentiableOn ℂ F U) {m' : ℕ} (T : P11CVec m →L[ℂ] P11CVec m') (α : Fin n → ℕ) :
    EqOn (p11PartialVec α (fun x => T (F x))) (fun x => T (p11PartialVec α F x)) U :=
  ops_foldl_clm hU T _ F hF

end PartialCalc

section Slice

variable {n m : ℕ}

/-- The linear part of the slice `J ↦ (J, ρ)`: extension by zero. -/
private def opsExt (n : ℕ) : P11CVec n →L[ℂ] P11CVec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Fin.append v (0 : P11CVec n)
      map_add' := fun v w => by
        funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := fun a v => by
        funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

private theorem opsExt_apply (v : P11CVec n) : opsExt n v = Fin.append v (0 : P11CVec n) := rfl

private theorem opsExt_single (a : Fin n) :
    opsExt n (Pi.single a 1) = Pi.single (Fin.castAdd n a) 1 := by
  rw [opsExt_apply]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Pi.single_apply]
  · have := a.isLt
    simp [Pi.single_apply, Fin.ext_iff]
    omega

private theorem ops_slice_hasFDerivAt (ρ : P11CVec n) (J : P11CVec n) :
    HasFDerivAt (fun J : P11CVec n => (Fin.append J ρ : P11CVec (n + n))) (opsExt n) J := by
  have h : (fun J : P11CVec n => (Fin.append J ρ : P11CVec (n + n))) =
      fun J => opsExt n J + Fin.append (0 : P11CVec n) ρ := by
    funext J i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [opsExt_apply]
  rw [h]
  exact (opsExt n).hasFDerivAt.add_const _

private theorem ops_slice_foldl {U : Set (P11CVec (n + n))} (hU : IsOpen U) (ρ : P11CVec n) :
    ∀ (L : List (Fin n)) (F : P11CVec (n + n) → P11CVec m), DifferentiableOn ℂ F U →
      ∀ J : P11CVec n, (Fin.append J ρ : P11CVec (n + n)) ∈ U →
        L.foldl (fun g i => p11Step i g) (fun J => F (Fin.append J ρ)) J =
          (L.map (Fin.castAdd n)).foldl (fun g i => p11Step i g) F (Fin.append J ρ) := by
  intro L
  induction L with
  | nil => intro F _ J _; rfl
  | cons a L ih =>
    intro F hF J hJ
    have hcont : Continuous fun J : P11CVec n => (Fin.append J ρ : P11CVec (n + n)) := by
      refine continuous_pi fun i => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop
    have hU' : IsOpen {J : P11CVec n | (Fin.append J ρ : P11CVec (n + n)) ∈ U} :=
      hU.preimage hcont
    have h1 : EqOn (p11Step a (fun J => F (Fin.append J ρ)))
        (fun J => p11Step (Fin.castAdd n a) F (Fin.append J ρ))
        {J : P11CVec n | (Fin.append J ρ : P11CVec (n + n)) ∈ U} := by
      intro J' hJ'
      have hFa := hF.differentiableAt (hU.mem_nhds hJ')
      simp only [p11Step]
      have := (hFa.hasFDerivAt.comp J' (ops_slice_hasFDerivAt ρ J')).fderiv
      rw [show (fun J => F (Fin.append J ρ)) =
        F ∘ (fun J : P11CVec n => (Fin.append J ρ : P11CVec (n + n))) from rfl, this]
      simp [opsExt_single]
    have h2 := ops_foldl_congr hU' L h1 hJ
    simp only [List.foldl_cons, List.map_cons]
    refine h2.trans ?_
    exact ih _ (p11Step_differentiableOn hU hF _) J hJ

/-- Partial derivatives in `J` of a slice of a holomorphic function of `(J, ρ)`. -/
theorem p11_partial_slice {U : Set (P11CVec (n + n))} (hU : IsOpen U)
    {F : P11CVec (n + n) → P11CVec m} (hF : DifferentiableOn ℂ F U) (ρ : P11CVec n)
    (α : Fin n → ℕ) {J : P11CVec n} (hJ : (Fin.append J ρ : P11CVec (n + n)) ∈ U) :
    p11PartialVec α (fun J => F (Fin.append J ρ)) J =
      p11PartialVec (Fin.append α (0 : Fin n → ℕ)) F (Fin.append J ρ) := by
  have hperm : ((List.ofFn fun i : Fin n => List.replicate (α i) i).flatten.map
      (Fin.castAdd n)).Perm
      (List.ofFn fun i : Fin (n + n) =>
        List.replicate ((Fin.append α (0 : Fin n → ℕ) : Fin (n + n) → ℕ) i) i).flatten := by
    rw [List.perm_iff_count]
    intro d
    rw [ops_count_flatten]
    refine Fin.addCases (fun e => ?_) (fun e => ?_) d
    · rw [List.count_map_of_injective _ _ (Fin.castAdd_injective n n), ops_count_flatten]
      simp
    · rw [List.count_eq_zero.2]
      · simp
      · simp only [List.mem_map, not_exists, not_and]
        intro a _ h
        have h' := congrArg Fin.val h
        simp at h'
        have := e.isLt
        omega
  exact (ops_slice_foldl hU ρ _ F hF J hJ).trans (ops_foldl_perm hU hperm hF hJ)

end Slice

section Affine

variable {n m : ℕ}

private theorem ops_affine_foldl {U : Set (P11CVec n)} (hU : IsOpen U) (b : P11CVec n) (t : ℂ) :
    ∀ (L : List (Fin n)) (F : P11CVec n → P11CVec m), DifferentiableOn ℂ F U →
      ∀ x : P11CVec n, b + t • x ∈ U →
        L.foldl (fun g i => p11Step i g) (fun r => F (b + t • r)) x =
          t ^ L.length • L.foldl (fun g i => p11Step i g) F (b + t • x) := by
  intro L
  induction L with
  | nil => intro F _ x _; simp
  | cons a L ih =>
    intro F hF x hx
    have hcont : Continuous fun r : P11CVec n => b + t • r := by fun_prop
    have hU' : IsOpen {r : P11CVec n | b + t • r ∈ U} := hU.preimage hcont
    have hdiffG : DifferentiableOn ℂ (fun r => p11Step a F (b + t • r))
        {r : P11CVec n | b + t • r ∈ U} :=
      (p11Step_differentiableOn hU hF a).comp (by fun_prop) fun r hr => hr
    have h1 : EqOn (p11Step a (fun r => F (b + t • r)))
        (fun r => t • p11Step a F (b + t • r)) {r : P11CVec n | b + t • r ∈ U} := by
      intro r hr
      have hFa := hF.differentiableAt (hU.mem_nhds hr)
      have hd : HasFDerivAt (fun r : P11CVec n => b + t • r) (t • ContinuousLinearMap.id ℂ _) r :=
        ((hasFDerivAt_id r).const_smul t).const_add b
      have := (hFa.hasFDerivAt.comp r hd).fderiv
      simp only [p11Step]
      rw [show (fun r => F (b + t • r)) = F ∘ (fun r : P11CVec n => b + t • r) from rfl, this]
      simp
    have h2 := ops_foldl_congr hU' L h1 hx
    simp only [List.foldl_cons, List.length_cons]
    refine h2.trans ?_
    have h3 := ops_foldl_clm hU' (t • ContinuousLinearMap.id ℂ (P11CVec m)) L _ hdiffG hx
    refine h3.trans ?_
    have h4 := ih (p11Step a F) (p11Step_differentiableOn hU hF a) x hx
    simp only [smul_apply, ContinuousLinearMap.id_apply]
    rw [h4, smul_smul, pow_succ, mul_comm]

/-- Partial derivatives of an affine pullback `r ↦ F (b + t r)` scale by `t ^ |α|`. -/
theorem p11_partial_affine {U : Set (P11CVec n)} (hU : IsOpen U) {F : P11CVec n → P11CVec m}
    (hF : DifferentiableOn ℂ F U) (b : P11CVec n) (t : ℂ) (α : Fin n → ℕ) {x : P11CVec n}
    (hx : b + t • x ∈ U) :
    p11PartialVec α (fun r => F (b + t • r)) x =
      t ^ (∑ i, α i) • p11PartialVec α F (b + t • x) := by
  have hlen : (List.ofFn fun i : Fin n => List.replicate (α i) i).flatten.length = ∑ i, α i := by
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    simp
  have := ops_affine_foldl hU b t (List.ofFn fun i : Fin n => List.replicate (α i) i).flatten
    F hF x hx
  rw [hlen] at this
  exact this

end Affine

end KAM.Planetary

end
