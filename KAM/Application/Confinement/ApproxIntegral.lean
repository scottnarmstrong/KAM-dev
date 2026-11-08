/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.ODE.Exit
public import KAM.ODE.Hamiltonian

/-!
# Confinement from approximate integrals: first exit and continuation

Design `docs/explorations/sjsu-effective-stability.md` §2, equations (1)–(3) (the SJSU
effective-stability lane). A generic first-exit confinement theorem for an autonomous field
`X : E → E`, `C¹` on an open `W` of a proper real normed space `E` (e.g. a finite-dimensional
one), from finitely many *approximate integrals* `F j` (`j : Fin m`) on an open `D` with compact
closure `closure D ⊆ W`:

* (1) `|dF_j(z) X(z)| ≤ η_j` on `closure D` (`η_j = 0`: exact integrals), and
  `a_j ≤ F_j ≤ b_j` on an initial set `Q ⊆ D`;
* (2) every point of `frontier D` violates an enlarged range: `F_j < a_j - T η_j` or
  `b_j + T η_j < F_j` for some `j`.

Then every solution through `z₀ ∈ Q` stays in `D` for `|t| ≤ T`, with
`|F_j(z(t)) - F_j(z₀)| ≤ η_j |t|`, and the maximal solution through `z₀` lives on an open interval
containing `[-T, T]`.

Proof. Along a solution the chain rule and the mean value inequality give the drift bound while
the orbit is in `closure D`; a first hit of `frontier D` (`KAM.ODE.gen_exit`) at a time
`0 < t* ≤ T` would contradict (2); backward times follow by time reversal
(`KAM.ODE.gen_symmetry_neg`); compactness of `closure D` continues the maximal solution past `±T`
(`KAM.ODE.gen_continuation_compact`). Independence of the `F j` is not needed.

## Main results

* `approxIntegrals_apriori`: the a priori confinement and drift bound, for every solution through
  `z₀` on every order-connected interval (no regularity of `X` is used).
* `approxIntegrals_confinement`: the maximal solution through `z₀` lives past `±T`, stays in `D`
  for `|t| ≤ T`, and has drift `|F_j(z(t)) - F_j(z₀)| ≤ η_j |t|`.
* `approxIntegrals_confinement_interval`: the same with an open order-connected interval
  `U ⊇ [-T, T]`; every solution through `z₀` lives in `U` and agrees with the given one.
* `observable_sub_le_of_approxIntegrals`, `approxIntegrals_confinement_observables`: (3), the drift
  `|A_i(z(t)) - A_i(z₀)| ≤ 2 d_i + |t| Σ_j |B_ij| η_j` of observables with
  `|A_i - c_i - Σ_j B_ij F_j| ≤ d_i` on `D`.
* `hamiltonian_approxIntegrals_confinement`: `X = X_H` for `H` of class `C²` on `W`, with rates
  `fderiv ℝ (F j) z (X_H z)` (the bracket `KAM.Application.LambdaDrift.pb (F j) H z`).
* `hamiltonian_approxIntegrals_confinement_univ`,
  `hamiltonian_approxIntegrals_confinement_univ_observables`: the whole-space instance
  `W = ℝⁿ × ℝⁿ` (e.g. a polynomial `H`), with `D` bounded.
-/

public section

open Set KAM.ODE

namespace KAM.Application.Confinement

section Observable

/-- Design §2 (3), pointwise: an observable `A` with `|A - c - Σ_j B_j F_j| ≤ d` on `D` changes
between two points of `D` by at most `2 d + s Σ_j |B_j| η_j` when every `F j` changes by at most
`η_j s`. -/
theorem observable_sub_le_of_approxIntegrals {α : Type*} {D : Set α} {m : ℕ}
    {F : Fin m → α → ℝ} {A : α → ℝ} {c d : ℝ} {B : Fin m → ℝ}
    (hA : ∀ z ∈ D, |A z - c - ∑ j, B j * F j z| ≤ d) {z w : α} (hz : z ∈ D) (hw : w ∈ D)
    {η : Fin m → ℝ} {s : ℝ} (hF : ∀ j, |F j w - F j z| ≤ η j * s) :
    |A w - A z| ≤ 2 * d + s * ∑ j, |B j| * η j := by
  have hsum : |∑ j, B j * (F j w - F j z)| ≤ s * ∑ j, |B j| * η j := by
    calc |∑ j, B j * (F j w - F j z)| ≤ ∑ j, |B j * (F j w - F j z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |B j| * |F j w - F j z| := by simp only [abs_mul]
      _ ≤ ∑ j, |B j| * (η j * s) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hF j) (abs_nonneg _)
      _ = s * ∑ j, |B j| * η j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : A w - A z = (A w - c - ∑ j, B j * F j w) - (A z - c - ∑ j, B j * F j z) +
      ∑ j, B j * (F j w - F j z) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  obtain ⟨h1l, h1u⟩ := abs_le.1 (hA w hw)
  obtain ⟨h2l, h2u⟩ := abs_le.1 (hA z hz)
  obtain ⟨h3l, h3u⟩ := abs_le.1 hsum
  rw [hsplit, abs_le]
  constructor <;> linarith

end Observable

section ApproxIntegrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper: the mean value step along a solution, in a general space (the analogue of
`KAM.Application.LambdaDrift.abs_sub_le_of_fderiv_bound`, which is stated on `Phase (n + n)`). -/
private theorem approxConf_abs_sub_le {G : E → ℝ} {W R : Set E} (hW : IsOpen W) (hRW : R ⊆ W)
    (hG : DifferentiableOn ℝ G W) {X : E → E} {η : ℝ}
    (hη : ∀ w ∈ R, |fderiv ℝ G w (X w)| ≤ η) {y : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hy : ∀ u ∈ Icc a b, y u ∈ R ∧ HasDerivAt y (X (y u)) u) :
    |G (y b) - G (y a)| ≤ η * (b - a) := by
  have hderiv : ∀ u ∈ Icc a b,
      HasDerivAt (fun s => G (y s)) (fderiv ℝ G (y u) (X (y u))) u := fun u hu =>
    ((hG.differentiableAt (hW.mem_nhds (hRW (hy u hu).1))).hasFDerivAt).comp_hasDerivAt u
      (hy u hu).2
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => G (y s))
    (fun u hu => (hderiv u hu).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hη _ (hy u (Ico_subset_Icc_self hu)).1) b ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs] at h

/-- Helper: the forward half of `approxIntegrals_apriori`, for an arbitrary field `X`. -/
private theorem approxConf_forward {X : E → E} {W D : Set E} {m : ℕ} {F : Fin m → E → ℝ}
    {η a b : Fin m → ℝ} {T : ℝ} (hW : IsOpen W) (hD : IsOpen D) (hDW : closure D ⊆ W)
    (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (X z)| ≤ η j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : E} (hz₀ : z₀ ∈ D) (ha : ∀ j, a j ≤ F j z₀) (hb : ∀ j, F j z₀ ≤ b j)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → E}
    (hy : IsSolutionIn X W J y) (hy0 : y 0 = z₀) :
    ∀ t ∈ J, 0 ≤ t → t ≤ T → y t ∈ D ∧ ∀ j, |F j (y t) - F j z₀| ≤ η j * t := by
  have hη0 : ∀ j, 0 ≤ η j := fun j => (abs_nonneg _).trans (hη j z₀ (subset_closure hz₀))
  -- the drift along a segment `[0, s]` spent in `closure D`
  have hdrift : ∀ s ∈ J, 0 ≤ s → (∀ u ∈ Icc 0 s, y u ∈ closure D) →
      ∀ j, |F j (y s) - F j z₀| ≤ η j * s := by
    intro s hs hs0 hcl j
    have hsub : Icc 0 s ⊆ J := hJ.out h0 hs
    have h := approxConf_abs_sub_le (y := y) (a := 0) (b := s) hW hDW (hF j) (hη j) hs0
      (fun u hu => ⟨hcl u hu, (hy u (hsub hu)).2⟩)
    rwa [hy0, sub_zero] at h
  -- the first exit from `D` on `J ∩ (-∞, T]`
  have hJT : (J ∩ Iic T).OrdConnected := hJ.inter ordConnected_Iic
  have h0T : (0 : ℝ) ∈ J ∩ Iic T := ⟨h0, hT⟩
  have hy0D : y 0 ∈ D := by rw [hy0]; exact hz₀
  rcases gen_exit hJT h0T (hy.continuousOn.mono inter_subset_left) hD hy0D with
    ⟨-, hall⟩ | ⟨-, ts, -, hts0, htsJ, hbefore, hfr, -⟩
  · intro t ht ht0 htT
    have hin : ∀ u ∈ Icc 0 t, y u ∈ D := fun u hu =>
      hall u ⟨hJ.out h0 ht hu, hu.2.trans htT⟩ hu.1
    exact ⟨hin t ⟨ht0, le_rfl⟩, hdrift t ht ht0 fun u hu => subset_closure (hin u hu)⟩
  · -- a first boundary hit at `0 < ts ≤ T` contradicts the separation
    exfalso
    have htsT : ts ≤ T := htsJ.2
    have hcl : ∀ u ∈ Icc 0 ts, y u ∈ closure D := fun u hu => by
      rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h]
        exact frontier_subset_closure hfr
      · exact subset_closure (hbefore u ⟨hu.1, h⟩)
    have hdr := hdrift ts htsJ.1 hts0.le hcl
    obtain ⟨j, hj⟩ := hsep _ hfr
    have h1 := abs_le.1 (hdr j)
    have h2 : η j * ts ≤ T * η j := by
      rw [mul_comm T]
      exact mul_le_mul_of_nonneg_left htsT (hη0 j)
    rcases hj with hj | hj
    · linarith [ha j, h1.1]
    · linarith [hb j, h1.2]

/-- **A priori confinement from approximate integrals** (design §2, (1)–(2)). Let `F j` be
differentiable on the open `W ⊇ closure D`, with `|dF_j(z) X(z)| ≤ η_j` on `closure D`, let
`z₀ ∈ D` satisfy `a_j ≤ F_j(z₀) ≤ b_j`, and let every point of `frontier D` have some `j` with
`F_j < a_j - T η_j` or `b_j + T η_j < F_j`. Then every solution of `ẋ = X x` in `W` through `z₀`
at time `0` stays in `D` and has `|F_j(y(t)) - F_j(z₀)| ≤ η_j |t|` for every `t` of its interval
with `|t| ≤ T`. No regularity of `X` is used. -/
theorem approxIntegrals_apriori {X : E → E} {W D : Set E} {m : ℕ} {F : Fin m → E → ℝ}
    {η a b : Fin m → ℝ} {T : ℝ} (hW : IsOpen W) (hD : IsOpen D) (hDW : closure D ⊆ W)
    (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (X z)| ≤ η j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : E} (hz₀ : z₀ ∈ D) (ha : ∀ j, a j ≤ F j z₀) (hb : ∀ j, F j z₀ ≤ b j)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → E}
    (hy : IsSolutionIn X W J y) (hy0 : y 0 = z₀) :
    ∀ t ∈ J, |t| ≤ T → y t ∈ D ∧ ∀ j, |F j (y t) - F j z₀| ≤ η j * |t| := by
  intro t ht htT
  rcases le_total 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at htT ⊢
    exact approxConf_forward hW hD hDW hF hη hT hsep hz₀ ha hb hJ h0 hy hy0 t ht ht0 htT
  · rw [abs_of_nonpos ht0] at htT ⊢
    -- time reversal: the field `-X` has the same rate bounds
    have hη' : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (-X z)| ≤ η j := fun j z hz => by
      rw [map_neg, abs_neg]
      exact hη j z hz
    have hJ' : (Neg.neg ⁻¹' J).OrdConnected :=
      hJ.preimage_anti (fun u v huv => neg_le_neg huv)
    have h := approxConf_forward (X := fun x => -X x) (J := Neg.neg ⁻¹' J)
      (y := fun s => y (-s)) hW hD hDW hF hη' hT hsep hz₀ ha hb hJ' (by simpa using h0)
      (gen_symmetry_neg hy) (by simpa using hy0) (-t) (by simpa using ht) (by linarith) htT
    simp only [neg_neg] at h
    exact h

/-- **Confinement from approximate integrals** (design §2): under the hypotheses of
`approxIntegrals_apriori`, with `X` of class `C¹` on `W`, `closure D` compact and `T ≥ 0`, the
maximal solution `(Tm, Tp, z)` of `ẋ = X x` in `W` through any `z₀ ∈ Q` has `Tm < -T` and
`T < Tp`, stays in `D` for `|t| ≤ T`, and satisfies `|F_j(z(t)) - F_j(z₀)| ≤ η_j |t|` there.
Every solution through `z₀` lives in `(Tm, Tp)` and agrees with `z` (`IsMaximalSolution`). -/
theorem approxIntegrals_confinement [ProperSpace E] {X : E → E} {W D Q : Set E} {m : ℕ}
    {F : Fin m → E → ℝ} {η a b : Fin m → ℝ} {T : ℝ} (hW : IsOpen W)
    (hX : ContDiffOn ℝ 1 X W) (hD : IsOpen D) (hDc : IsCompact (closure D))
    (hDW : closure D ⊆ W) (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (X z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : E} (hz₀ : z₀ ∈ Q) :
    ∃ (Tm Tp : EReal) (z : ℝ → E), IsMaximalSolution X W z₀ Tm Tp z ∧
      Tm < ((-T : ℝ) : EReal) ∧ ((T : ℝ) : EReal) < Tp ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ ∀ j, |F j (z t) - F j z₀| ≤ η j * |t| := by
  have hz₀D : z₀ ∈ D := hQD hz₀
  obtain ⟨Tm, Tp, z, hz⟩ := (gen_maximal hW hX (hDW (subset_closure hz₀D))).1
  have hconf : ∀ t ∈ eIoo Tm Tp, |t| ≤ T →
      z t ∈ D ∧ ∀ j, |F j (z t) - F j z₀| ≤ η j * |t| :=
    approxIntegrals_apriori hW hD hDW hF hη hT hsep hz₀D (fun j => (hQ z₀ hz₀ j).1)
      (fun j => (hQ z₀ hz₀ j).2) (ordConnected_eIoo _ _) (zero_mem_eIoo hz) hz.isSolution
      hz.init
  have hK : ∀ t ∈ eIoo Tm Tp, |t| ≤ T → z t ∈ closure D := fun t ht htT =>
    subset_closure (hconf t ht htT).1
  obtain ⟨hcp, hcm⟩ := gen_continuation_compact hW hX hz hDc hDW
  have hTp : ((T : ℝ) : EReal) < Tp := by
    by_contra hle
    rw [not_lt] at hle
    have := hcp ⟨0, le_rfl, hz.pos_lt, fun t ht0 htT =>
      hK t ⟨lt_of_lt_of_le hz.neg_lt (by exact_mod_cast ht0), htT⟩
        (by rw [abs_of_nonneg ht0]; exact EReal.coe_le_coe_iff.1 (htT.le.trans hle))⟩
    rw [this] at hle
    exact absurd hle (by simp)
  have hTm : Tm < ((-T : ℝ) : EReal) := by
    by_contra hle
    rw [not_lt] at hle
    have := hcm ⟨0, le_rfl, hz.neg_lt, fun t htT ht0 =>
      hK t ⟨htT, lt_of_le_of_lt (by exact_mod_cast ht0) hz.pos_lt⟩
        (by rw [abs_of_nonpos ht0]; exact neg_le.1 (EReal.coe_le_coe_iff.1 (hle.trans htT.le)))⟩
    rw [this] at hle
    exact absurd hle (by simp)
  have hIcc : Icc (-T) T ⊆ eIoo Tm Tp := fun t ht =>
    ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 ht.1),
      lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ht.2) hTp⟩
  exact ⟨Tm, Tp, z, hz, hTm, hTp, fun t ht => hconf t (hIcc (abs_le.1 ht)) ht⟩

/-- **Confinement from approximate integrals, interval form**: under the hypotheses of
`approxIntegrals_confinement`, for every `z₀ ∈ Q` there is a solution `z` through `z₀` on an open
order-connected interval `U ⊇ [-T, T]`, staying in `D` with `|F_j(z(t)) - F_j(z₀)| ≤ η_j |t|` for
`|t| ≤ T`; every solution through `z₀` on an order-connected interval `J ∋ 0` has `J ⊆ U` and
agrees with `z` on `J`. -/
theorem approxIntegrals_confinement_interval [ProperSpace E] {X : E → E} {W D Q : Set E}
    {m : ℕ} {F : Fin m → E → ℝ} {η a b : Fin m → ℝ} {T : ℝ} (hW : IsOpen W)
    (hX : ContDiffOn ℝ 1 X W) (hD : IsOpen D) (hDc : IsCompact (closure D))
    (hDW : closure D ⊆ W) (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (X z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : E} (hz₀ : z₀ ∈ Q) :
    ∃ (U : Set ℝ) (z : ℝ → E), IsOpen U ∧ U.OrdConnected ∧ Icc (-T) T ⊆ U ∧ z 0 = z₀ ∧
      IsSolutionIn X W U z ∧
      (∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ ∀ j, |F j (z t) - F j z₀| ≤ η j * |t|) ∧
      ∀ (J : Set ℝ) (y : ℝ → E), J.OrdConnected → (0 : ℝ) ∈ J → y 0 = z₀ →
        IsSolutionIn X W J y → J ⊆ U ∧ EqOn y z J := by
  obtain ⟨Tm, Tp, z, hz, hTm, hTp, hconf⟩ :=
    approxIntegrals_confinement hW hX hD hDc hDW hF hη hQD hQ hT hsep hz₀
  refine ⟨eIoo Tm Tp, z, isOpen_eIoo _ _, ordConnected_eIoo _ _, fun t ht =>
    ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 ht.1),
      lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ht.2) hTp⟩, hz.init, hz.isSolution, hconf, ?_⟩
  exact hz.maximal

/-- **Confinement with observable drift** (design §2, (1)–(3)): `approxIntegrals_confinement`,
together with `|A_i(z(t)) - A_i(z₀)| ≤ 2 d_i + |t| Σ_j |B_ij| η_j` for `|t| ≤ T`, for observables
`A_i` with `|A_i - c_i - Σ_j B_ij F_j| ≤ d_i` on `D`. -/
theorem approxIntegrals_confinement_observables [ProperSpace E] {X : E → E} {W D Q : Set E}
    {m : ℕ} {F : Fin m → E → ℝ} {η a b : Fin m → ℝ} {T : ℝ} {ι : Type*} {A : ι → E → ℝ}
    {c d : ι → ℝ} {B : ι → Fin m → ℝ} (hW : IsOpen W) (hX : ContDiffOn ℝ 1 X W)
    (hD : IsOpen D) (hDc : IsCompact (closure D)) (hDW : closure D ⊆ W)
    (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (X z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    (hA : ∀ i, ∀ z ∈ D, |A i z - c i - ∑ j, B i j * F j z| ≤ d i) {z₀ : E} (hz₀ : z₀ ∈ Q) :
    ∃ (Tm Tp : EReal) (z : ℝ → E), IsMaximalSolution X W z₀ Tm Tp z ∧
      Tm < ((-T : ℝ) : EReal) ∧ ((T : ℝ) : EReal) < Tp ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ (∀ j, |F j (z t) - F j z₀| ≤ η j * |t|) ∧
        ∀ i, |A i (z t) - A i z₀| ≤ 2 * d i + |t| * ∑ j, |B i j| * η j := by
  obtain ⟨Tm, Tp, z, hz, hTm, hTp, hconf⟩ :=
    approxIntegrals_confinement hW hX hD hDc hDW hF hη hQD hQ hT hsep hz₀
  refine ⟨Tm, Tp, z, hz, hTm, hTp, fun t ht => ⟨(hconf t ht).1, (hconf t ht).2, fun i => ?_⟩⟩
  exact observable_sub_le_of_approxIntegrals (hA i) (hQD hz₀) (hconf t ht).1 (hconf t ht).2

end ApproxIntegrals

section Hamiltonian

variable {n m : ℕ}

/-- **Hamiltonian confinement from approximate integrals**: `approxIntegrals_confinement` for the
Hamiltonian field `X_H = KAM.hamiltonianVectorField H` of an `H` of class `C²` on the open `W`, the
rates being the brackets `fderiv ℝ (F j) z (X_H z)`. -/
theorem hamiltonian_approxIntegrals_confinement {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {W D Q : Set ((Fin n → ℝ) × (Fin n → ℝ))} {F : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {η a b : Fin m → ℝ} {T : ℝ} (hW : IsOpen W) (hH : ContDiffOn ℝ 2 H W) (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ W) (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (KAM.hamiltonianVectorField H z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : z₀ ∈ Q) :
    ∃ (Tm Tp : EReal) (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      IsMaximalSolution (KAM.hamiltonianVectorField H) W z₀ Tm Tp z ∧
      Tm < ((-T : ℝ) : EReal) ∧ ((T : ℝ) : EReal) < Tp ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ ∀ j, |F j (z t) - F j z₀| ≤ η j * |t| :=
  approxIntegrals_confinement hW (ham_smooth_c1 hW hH) hD hDc hDW hF hη hQD hQ hT hsep hz₀

/-- **Hamiltonian confinement from approximate integrals, whole phase space**: the instance
`W = ℝⁿ × ℝⁿ` of `hamiltonian_approxIntegrals_confinement`, for `H` of class `C²` on all of
`ℝⁿ × ℝⁿ` (e.g. a polynomial), `F j` differentiable everywhere and `D` open and bounded. -/
theorem hamiltonian_approxIntegrals_confinement_univ {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {D Q : Set ((Fin n → ℝ) × (Fin n → ℝ))} {F : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {η a b : Fin m → ℝ} {T : ℝ} (hH : ContDiff ℝ 2 H) (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (hF : ∀ j, Differentiable ℝ (F j))
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (KAM.hamiltonianVectorField H z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : z₀ ∈ Q) :
    ∃ (Tm Tp : EReal) (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      IsMaximalSolution (KAM.hamiltonianVectorField H) univ z₀ Tm Tp z ∧
      Tm < ((-T : ℝ) : EReal) ∧ ((T : ℝ) : EReal) < Tp ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ ∀ j, |F j (z t) - F j z₀| ≤ η j * |t| :=
  hamiltonian_approxIntegrals_confinement isOpen_univ hH.contDiffOn hD hDb.isCompact_closure
    (subset_univ _) (fun j => (hF j).differentiableOn) hη hQD hQ hT hsep hz₀

/-- **Hamiltonian confinement with observable drift, whole phase space** (design §2, (1)–(3)):
`hamiltonian_approxIntegrals_confinement_univ` together with the drift
`|A_i(z(t)) - A_i(z₀)| ≤ 2 d_i + |t| Σ_j |B_ij| η_j` of observables `A_i` with
`|A_i - c_i - Σ_j B_ij F_j| ≤ d_i` on `D`. -/
theorem hamiltonian_approxIntegrals_confinement_univ_observables
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {D Q : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {F : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {η a b : Fin m → ℝ} {T : ℝ} {ι : Type*}
    {A : ι → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {c d : ι → ℝ} {B : ι → Fin m → ℝ}
    (hH : ContDiff ℝ 2 H) (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (hF : ∀ j, Differentiable ℝ (F j))
    (hη : ∀ j, ∀ z ∈ closure D, |fderiv ℝ (F j) z (KAM.hamiltonianVectorField H z)| ≤ η j)
    (hQD : Q ⊆ D) (hQ : ∀ z ∈ Q, ∀ j, a j ≤ F j z ∧ F j z ≤ b j) (hT : 0 ≤ T)
    (hsep : ∀ z ∈ frontier D, ∃ j, F j z < a j - T * η j ∨ b j + T * η j < F j z)
    (hA : ∀ i, ∀ z ∈ D, |A i z - c i - ∑ j, B i j * F j z| ≤ d i)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : z₀ ∈ Q) :
    ∃ (Tm Tp : EReal) (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      IsMaximalSolution (KAM.hamiltonianVectorField H) univ z₀ Tm Tp z ∧
      Tm < ((-T : ℝ) : EReal) ∧ ((T : ℝ) : EReal) < Tp ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ D ∧ (∀ j, |F j (z t) - F j z₀| ≤ η j * |t|) ∧
        ∀ i, |A i (z t) - A i z₀| ≤ 2 * d i + |t| * ∑ j, |B i j| * η j :=
  approxIntegrals_confinement_observables isOpen_univ (ham_smooth_c1 isOpen_univ hH.contDiffOn)
    hD hDb.isCompact_closure (subset_univ _) (fun j => (hF j).differentiableOn) hη hQD hQ hT
    hsep hA hz₀

end Hamiltonian

end KAM.Application.Confinement

end
