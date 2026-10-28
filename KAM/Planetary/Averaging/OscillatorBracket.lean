/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorSetting
public import KAM.Weighted.Algebra
public import KAM.Weighted.Cauchy
public import KAM.Weighted.Parametric
public import KAM.Weighted.SupWeighted
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Parts 2-3: the oscillator Poisson bracket (`bpP:p2:osc-bracket`)

Flat layer: the Cauchy estimates of `KAM.Weighted` at a fixed flat parameter, with a separate
loss in each coordinate direction (one-dimensional discs), for a function on a strip times an
arbitrary open parameter set. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-11.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Flat

variable {n N : ℕ}

theorem polyNbhd_singleton (x : Fin N → ℂ) (δ : ℝ) :
    polyNbhd ({x} : Set (Fin N → ℂ)) δ = ball x δ := by
  ext I
  simp [polyNbhd, mem_ball, dist_eq_norm]

/-- Holomorphic and `1`-periodic on the strip times the parameter set `P`. -/
def FClass (S : ℝ) (P : Set (Fin N → ℂ)) (F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ F (KAM.complexStrip n S ×ˢ P) ∧
    ∀ j : Fin n, ∀ z ∈ KAM.complexStrip n S ×ˢ P, F (z.1 + Pi.single j 1, z.2) = F z

theorem FClass.inClass {S s δ : ℝ} {x : Fin N → ℂ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (h : FClass S P F) (hb : ball x δ ⊆ P) (hs : s ≤ S) :
    InClass ({x} : Set (Fin N → ℂ)) δ s F := by
  have hsub : Dom n ({x} : Set (Fin N → ℂ)) δ s ⊆ KAM.complexStrip n S ×ˢ P := by
    rintro z ⟨h1, h2⟩
    rw [polyNbhd_singleton] at h2
    exact ⟨fun i => (h1 i).trans_le hs, hb h2⟩
  exact ⟨h.1.mono hsub, fun j z hz => h.2 j z (hsub hz)⟩

theorem FClass.mono_width {S s : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (h : FClass S P F) (hs : s ≤ S) : FClass s P F := by
  have hsub : KAM.complexStrip n s ×ˢ P ⊆ KAM.complexStrip n S ×ˢ P :=
    prod_mono (fun θ hθ i => (hθ i).trans_le hs) subset_rfl
  exact ⟨h.1.mono hsub, fun j z hz => h.2 j z (hsub hz)⟩

theorem FClass.mono_set {S : ℝ} {P Q : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (h : FClass S P F) (hQ : Q ⊆ P) : FClass S Q F :=
  ⟨h.1.mono (prod_mono subset_rfl hQ), fun j z hz => h.2 j z (prod_mono subset_rfl hQ hz)⟩

theorem coeff_differentiableAt_of {S : ℝ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hS : 0 < S) (hP : IsOpen P) (hF : FClass S P F)
    {J : Fin N → ℂ} (hJ : J ∈ P) (k : Fin n → ℤ) :
    DifferentiableAt ℂ (fun I => coeff F I k) J := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP J hJ
  have hd := coeff_differentiableOn hS (hF.inClass hball le_rfl) k
  refine hd.differentiableAt ((isOpen_polyNbhd _ _).mem_nhds ?_)
  rw [polyNbhd_singleton]
  exact mem_ball_self hδ

theorem coeff_dI_eq_of {S : ℝ} {P : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hS : 0 < S) (hP : IsOpen P) (hF : FClass S P F)
    {J : Fin N → ℂ} (hJ : J ∈ P) (i : Fin N) (k : Fin n → ℤ) :
    coeff (dI i F) J k = fderiv ℂ (fun I => coeff F I k) J (Pi.single i 1) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP J hJ
  refine ((coefficients_deriv hS (hF.inClass hball le_rfl)).2 i).2 J ?_ k
  rw [polyNbhd_singleton]
  exact mem_ball_self hδ

/-- Angular Cauchy estimate at a fixed parameter, summed over the angles. -/
theorem wsum_dtheta_le {S₀ s A : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (hF : FClass S₀ P F) (hb : ∀ I ∈ P, WSummable F S₀ I ∧ wsum F S₀ I ≤ A)
    (hs0 : 0 < s) (hs : s < S₀) {x : Fin N → ℂ} (hx : x ∈ P) :
    (∀ j, WSummable (dtheta j F) s x) ∧
      ∑ j, wsum (dtheta j F) s x ≤ A / (Real.exp 1 * (S₀ - s)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP x hx
  have hmem : x ∈ polyNbhd ({x} : Set (Fin N → ℂ)) δ := by
    rw [polyNbhd_singleton]; exact mem_ball_self hδ
  have hb' : WBound ({x} : Set (Fin N → ℂ)) δ S₀ F A := fun I hI => by
    rw [polyNbhd_singleton] at hI
    exact hb I (hball hI)
  obtain ⟨hj, hle⟩ := (cauchy_theta (hF.inClass hball le_rfl) hb' hs0 hs).1 x hmem
  refine ⟨hj, hle.trans ?_⟩
  exact div_le_div_of_nonneg_right (hb x hx).2 (by have := Real.exp_pos 1; nlinarith)

/-- Action Cauchy estimate in one coordinate direction `i` with its own loss `R`: a
one-dimensional disc `t ↦ x + t eᵢ` inside `P` suffices. -/
theorem wsum_dI_le {S A R : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (hS : 0 < S) (hF : FClass S P F)
    (hb : ∀ I ∈ P, WSummable F S I ∧ wsum F S I ≤ A) {x : Fin N → ℂ} (hx : x ∈ P) (i : Fin N)
    (hR : 0 < R) (hline : ∀ t : ℂ, ‖t‖ < R → x + t • (Pi.single i 1 : Fin N → ℂ) ∈ P) :
    WSummable (dI i F) S x ∧ wsum (dI i F) S x ≤ A / R := by
  have hnn : ∀ k, 0 ≤ ‖coeff (dI i F) x k‖ * modeWeight S k := fun k =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  suffices hpart : ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k ≤ A / R from
    ⟨summable_of_sum_le hnn hpart, (summable_of_sum_le hnn hpart).tsum_le_of_sum_le hpart⟩
  intro Λ
  choose g hgn hgv using fun k => exists_dual_vector'' ℂ (coeff (dI i F) x k)
  set e : Fin N → ℂ := Pi.single i 1 with he
  set w : (Fin n → ℤ) → ℝ := fun k => modeWeight S k with hw
  set H : ℂ → ℂ := fun t => ∑ k ∈ Λ, (w k : ℂ) * g k (coeff F (x + t • e) k) with hH
  have hline_d : ∀ t : ℂ, HasDerivAt (fun t : ℂ => x + t • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have hcd : ∀ t : ℂ, ‖t‖ < R → ∀ k, DifferentiableAt ℂ (fun t : ℂ => coeff F (x + t • e) k) t :=
    fun t ht k =>
      DifferentiableAt.comp (g := fun I => coeff F I k) t
        (coeff_differentiableAt_of hS hP hF (hline t ht) k) (hline_d t).differentiableAt
  have hHdiff : DifferentiableOn ℂ H (ball 0 R) := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    refine DifferentiableAt.differentiableWithinAt ?_
    exact DifferentiableAt.fun_sum fun k _ =>
      ((g k).differentiableAt.comp t (hcd t ht k)).const_mul _
  have hHbound : ∀ t ∈ ball (0 : ℂ) R, ‖H t‖ ≤ A := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    obtain ⟨hsm, hle⟩ := hb _ (hline t ht)
    calc ‖H t‖ ≤ ∑ k ∈ Λ, ‖(w k : ℂ) * g k (coeff F (x + t • e) k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Λ, ‖coeff F (x + t • e) k‖ * modeWeight S k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (show 0 ≤ w k from (Real.exp_pos _).le)]
          have h1 : ‖g k (coeff F (x + t • e) k)‖ ≤ ‖coeff F (x + t • e) k‖ :=
            ((g k).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hgn k))
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right h1 (show 0 ≤ w k from (Real.exp_pos _).le)
      _ ≤ ∑' k, ‖coeff F (x + t • e) k‖ * modeWeight S k :=
          hsm.sum_le_tsum Λ fun k _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ A := hle
  have hcauchy := general_cauchy hR hHdiff hHbound
  have hcoef : ∀ k, coeff (dI i F) x k = fderiv ℂ (fun I => coeff F I k) x e :=
    fun k => coeff_dI_eq_of hS hP hF hx i k
  have hder : HasDerivAt H (((∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k : ℝ)) : ℂ) 0 := by
    have hk : ∀ k ∈ Λ, HasDerivAt (fun t : ℂ => (w k : ℂ) * g k (coeff F (x + t • e) k))
        ((w k : ℂ) * ‖coeff (dI i F) x k‖) 0 := by
      intro k _
      have h0 : HasFDerivAt (fun I => coeff F I k) (fderiv ℂ (fun I => coeff F I k) x)
          (x + (0 : ℂ) • e) := by
        simpa using (coeff_differentiableAt_of hS hP hF hx k).hasFDerivAt
      have h1 := h0.comp_hasDerivAt (0 : ℂ) (hline_d 0)
      have h2 := ((g k).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1).const_mul (w k : ℂ)
      rw [← hcoef k, hgv k] at h2
      exact h2
    have := HasDerivAt.fun_sum hk
    convert this using 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hw, mul_comm]
  have hnorm : ‖deriv H 0‖ ≤ A / R := by
    rw [← fderiv_apply_one_eq_deriv]
    calc ‖fderiv ℂ H 0 1‖ ≤ ‖fderiv ℂ H 0‖ * ‖(1 : ℂ)‖ := (fderiv ℂ H 0).le_opNorm _
      _ ≤ A / R * 1 := by
          rw [norm_one]; exact mul_le_mul_of_nonneg_right hcauchy zero_le_one
      _ = A / R := mul_one _
  have hsum_nn : 0 ≤ ∑ k ∈ Λ, ‖coeff (dI i F) x k‖ * modeWeight S k :=
    Finset.sum_nonneg fun k _ => hnn k
  rw [hder.deriv, Complex.norm_real, Real.norm_of_nonneg hsum_nn] at hnorm
  exact hnorm

/-- The derivative of a function periodic under the shift `a` (on an open set) is `a`-periodic. -/
theorem fderiv_shift_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hU : IsOpen U) {u : E → ℂ} (a : E) (hper : ∀ w ∈ U, u (w + a) = u w) {z : E} (hz : z ∈ U) :
    fderiv ℂ u (z + a) = fderiv ℂ u z := by
  have hev : (fun w => u (w + a)) =ᶠ[nhds z] u := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hper w hw
  rw [← fderiv_comp_add_right (f := u) (x := z) a]
  exact hev.fderiv_eq

theorem FClass.fderiv_apply {S : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (h : FClass S P F) (v : (Fin n → ℂ) × (Fin N → ℂ)) :
    FClass S P (fun z => fderiv ℂ F z v) := by
  have hU : IsOpen (KAM.complexStrip n S ×ˢ P) := (KAM.isOpen_complexStrip n S).prod hP
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hU h.1
  refine ⟨hreg.1.clm_apply (differentiableOn_const v), fun j z hz => ?_⟩
  set a : (Fin n → ℂ) × (Fin N → ℂ) := (Pi.single j 1, 0) with ha
  have hza : (z.1 + Pi.single j 1, z.2) = z + a := by ext <;> simp [ha]
  have hper : ∀ w ∈ KAM.complexStrip n S ×ˢ P, F (w + a) = F w := fun w hw => by
    have hwa : w + a = (w.1 + Pi.single j 1, w.2) := by ext <;> simp [ha]
    rw [hwa]; exact h.2 j w hw
  show fderiv ℂ F (z.1 + Pi.single j 1, z.2) v = fderiv ℂ F z v
  rw [hza, fderiv_shift_eq hU a hper hz]

/-- Pointwise sup bound from the weighted bound, at fixed width. -/
theorem norm_le_of_wsum {s M : ℝ} {P : Set (Fin N → ℂ)} {G : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hP : IsOpen P) (hG : FClass s P G)
    (hb : ∀ I ∈ P, WSummable G s I ∧ wsum G s I ≤ M) :
    ∀ z ∈ KAM.complexStrip n s ×ˢ P, ‖G z‖ ≤ M := by
  rintro ⟨θ, x⟩ ⟨hθ, hx⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP x hx
  have hb' : WBound ({x} : Set (Fin N → ℂ)) δ s G M := fun I hI => by
    rw [polyNbhd_singleton] at hI
    exact hb I (hball hI)
  refine sup_le_wbound (hG.inClass hball le_rfl) hb' (θ, x) ⟨hθ, ?_⟩
  rw [polyNbhd_singleton]
  exact mem_ball_self hδ

/-- A one-dimensional Cauchy estimate on a target set, individually per parameter. -/
theorem wsum_dI_le_on {S s A R : ℝ} {P Pt : Set (Fin N → ℂ)}
    {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hP : IsOpen P) (hS : 0 < S) (hs : s ≤ S)
    (hF : FClass S P F) (hb : ∀ I ∈ P, WSummable F S I ∧ wsum F S I ≤ A) (i : Fin N)
    (hR : 0 < R) (hPt : ∀ x ∈ Pt, ∀ t : ℂ, ‖t‖ < R → x + t • (Pi.single i 1 : Fin N → ℂ) ∈ P) :
    ∀ x ∈ Pt, WSummable (dI i F) s x ∧ wsum (dI i F) s x ≤ A / R := by
  intro x hx
  have hxP : x ∈ P := by simpa using hPt x hx 0 (by simpa using hR)
  obtain ⟨h1, h2⟩ := wsum_dI_le hP hS hF hb hxP i hR (hPt x hx)
  have hmono : ∀ k, ‖coeff (dI i F) x k‖ * modeWeight s k ≤ ‖coeff (dI i F) x k‖ * modeWeight S k :=
    fun k => mul_le_mul_of_nonneg_left (modeWeight_mono hs k) (norm_nonneg _)
  have h1' : WSummable (dI i F) s x := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hmono h1
  exact ⟨h1', (h1'.tsum_le_tsum hmono h1).trans h2⟩

theorem nonneg_of_wsum {S A : ℝ} {P : Set (Fin N → ℂ)} {F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hb : ∀ I ∈ P, WSummable F S I ∧ wsum F S I ≤ A) {x : Fin N → ℂ} (hx : x ∈ P) : 0 ≤ A :=
  (tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hb x hx).2

end Flat

section Transport

variable {n m : ℕ}

theorem oscPack_oscUnpack (y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) :
    oscPack (m := m) (oscUnpack y) = y := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [oscUnpack, oscPack, firstBlock, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [oscUnpack, oscPack, firstBlock, Fin.append_left]
    · refine Fin.addCases (fun a => ?_) (fun a => ?_) j
      · simp only [oscUnpack, oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right]
      · simp only [oscUnpack, oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right]

/-- `oscUnpack` as a continuous linear map. -/
def oscUnpackL : ((Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) →L[ℂ] CPhase (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := oscUnpack
      map_add' := fun a b => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [oscUnpack, firstBlock, lastBlock]
      map_smul' := fun c a => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [oscUnpack, firstBlock, lastBlock] }

theorem oscUnpackL_apply (y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) :
    (oscUnpackL (m := m) y) = oscUnpack y := rfl

/-- Index bookkeeping for the four coordinate directions. -/
local macro "pack_tac" : tactic =>
  `(tactic| (refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    (try refine Fin.addCases (fun a => ?_) (fun a => ?_) i) <;>
    (try refine Fin.addCases (fun b => ?_) (fun b => ?_) a) <;>
    simp only [oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right,
      Pi.single_apply, Pi.zero_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] <;>
    first | rfl | (split_ifs <;> first | rfl | omega)))

theorem oscPack_theta (j : Fin n) :
    oscPack (m := m) (Pi.single (Fin.castAdd m j) 1, 0) = (Pi.single j 1, 0) := by
  pack_tac

theorem oscPack_I (j : Fin n) :
    oscPack (m := m) (0, Pi.single (Fin.castAdd m j) 1) =
      (0, Pi.single (Fin.castAdd (m + m) j) 1) := by
  pack_tac

theorem oscPack_p (j : Fin m) :
    oscPack (m := m) (0, Pi.single (Fin.natAdd n j) 1) =
      (0, Pi.single (Fin.natAdd n (Fin.castAdd m j)) 1) := by
  pack_tac

theorem oscPack_q (j : Fin m) :
    oscPack (m := m) (Pi.single (Fin.natAdd n j) 1, 0) =
      (0, Pi.single (Fin.natAdd n (Fin.natAdd m j)) 1) := by
  pack_tac

end Transport

section OscTransport

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem oscUnpack_theta (j : Fin n) :
    oscUnpack (m := m) (Pi.single j 1, 0) = (Pi.single (Fin.castAdd m j) 1, 0) := by
  have := s_osc_data (m := m) (Pi.single (Fin.castAdd m j) 1, 0)
  rwa [oscPack_theta] at this

/-- `oscPack` as a continuous linear map. -/
def oscPackL : CPhase (n + m) →L[ℂ] (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := oscPack
      map_add' := fun a b => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        (try refine Fin.addCases (fun j => ?_) (fun j => ?_) i) <;>
        (try refine Fin.addCases (fun a => ?_) (fun a => ?_) j) <;>
        simp only [oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right,
          Prod.fst_add, Prod.snd_add, Pi.add_apply]
      map_smul' := fun c a => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        (try refine Fin.addCases (fun j => ?_) (fun j => ?_) i) <;>
        (try refine Fin.addCases (fun a => ?_) (fun a => ?_) j) <;>
        simp only [oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right,
          Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }

theorem isOpen_actionNbhd (D : Set (Fin n → ℝ)) (r : ℝ) : IsOpen (KAM.actionNbhd D r) := by
  rw [actionNbhd_eq_polyNbhd]
  exact isOpen_polyNbhd _ _

theorem isOpen_oscParams (D : Set (Fin n → ℝ)) (r rp rq : ℝ) :
    IsOpen (oscParams (m := m) D r rp rq) := by
  have c1 : Continuous fun x : Fin (n + (m + m)) → ℂ => firstBlock (b := m + m) x :=
    continuous_pi fun i => continuous_apply _
  have c2 : Continuous fun x : Fin (n + (m + m)) → ℂ => lastBlock (a := n) x :=
    continuous_pi fun i => continuous_apply _
  have c3 : Continuous fun x : Fin (m + m) → ℂ => firstBlock (b := m) x :=
    continuous_pi fun i => continuous_apply _
  have c4 : Continuous fun x : Fin (m + m) → ℂ => lastBlock (a := m) x :=
    continuous_pi fun i => continuous_apply _
  unfold oscParams
  simp only [Set.setOf_and]
  exact ((isOpen_actionNbhd D r).preimage c1).inter
    ((isOpen_lt (continuous_norm.comp (c3.comp c2)) continuous_const).inter
      (isOpen_lt (continuous_norm.comp (c4.comp c2)) continuous_const))

theorem oscParams_mono {a a' b b' c c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    oscParams (m := m) D a b c ⊆ oscParams D a' b' c' := by
  rintro x ⟨h1, h2, h3⟩
  refine ⟨?_, h2.trans_le hb, h3.trans_le hc⟩
  obtain ⟨J, hJ, h⟩ := h1
  exact ⟨J, hJ, h.trans_le ha⟩

theorem isOpen_oscDom (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) :
    IsOpen (oscDom (m := m) D r rp rq S) :=
  ((KAM.isOpen_complexStrip n S).prod (isOpen_oscParams D r rp rq)).preimage
    (oscPackL (m := m)).continuous

theorem oscUnpack_mem_oscDom {r rp rq S : ℝ} {y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)} :
    oscUnpack y ∈ oscDom (m := m) D r rp rq S ↔
      y ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq := by
  simp [oscDom, oscPack_oscUnpack]

theorem oscClass.flat {r rp rq S : ℝ} {u : CHam (n + m)} (hu : oscClass D r rp rq S u) :
    FClass S (oscParams (m := m) D r rp rq) (oscFunction u) := by
  refine ⟨?_, fun j z hz => ?_⟩
  · have h : oscFunction u = u ∘ oscUnpackL := rfl
    rw [h]
    exact hu.1.comp (oscUnpackL (m := m)).differentiableOn fun y hy =>
      oscUnpack_mem_oscDom.2 hy
  · have hz' : oscUnpack z ∈ oscDom (m := m) D r rp rq S := oscUnpack_mem_oscDom.2 hz
    have hadd : oscUnpack (z.1 + Pi.single j 1, z.2) =
        ((oscUnpack z).1 + Pi.single (Fin.castAdd m j) 1, (oscUnpack z).2) := by
      have h1 : ((z.1 + Pi.single j 1, z.2) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) =
          z + (Pi.single j 1, 0) := by ext <;> simp
      rw [h1]
      have h2 := (oscUnpackL (m := m)).map_add z (Pi.single j 1, 0)
      change oscUnpack (z + (Pi.single j 1, 0)) = oscUnpack z + oscUnpack (Pi.single j 1, 0) at h2
      rw [h2, oscUnpack_theta]
      ext <;> simp
    show u (oscUnpack (z.1 + Pi.single j 1, z.2)) = u (oscUnpack z)
    rw [hadd]
    exact hu.2 j _ hz'

theorem fderiv_oscFunction {r rp rq S : ℝ} {u : CHam (n + m)} (hu : oscClass D r rp rq S u)
    {y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)}
    (hy : y ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq) (a : CPhase (n + m)) :
    fderiv ℂ (oscFunction u) y (oscPack a) = fderiv ℂ u (oscUnpack y) a := by
  have hd : DifferentiableAt ℂ u (oscUnpack y) :=
    hu.1.differentiableAt ((isOpen_oscDom D r rp rq S).mem_nhds (oscUnpack_mem_oscDom.2 hy))
  have h : oscFunction u = u ∘ oscUnpackL := rfl
  rw [h, fderiv_comp y (g := u) (f := ⇑(oscUnpackL (m := m))) hd
    (oscUnpackL (m := m)).differentiableAt, ContinuousLinearMap.fderiv]
  simp [oscUnpackL_apply, s_osc_data]

theorem coeff_congr_real {N : ℕ} {F G : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {I : Fin N → ℂ}
    (h : ∀ θ : Fin n → ℝ, F (fun j => (θ j : ℂ), I) = G (fun j => (θ j : ℂ), I))
    (k : Fin n → ℤ) : coeff F I k = coeff G I k := by
  unfold coeff
  congr 1
  funext θ
  exact h θ

theorem oscBound_of_flat {r rp rq S M : ℝ} {g : CHam (n + m)}
    {G : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ} (hS : 0 < S)
    (hG : ∀ y ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq, oscFunction g y = G y)
    (hb : ∀ x ∈ oscParams (m := m) D r rp rq, WSummable G S x ∧ wsum G S x ≤ M) :
    oscBound D r rp rq S g M := by
  intro x hx
  have hc : ∀ k, coeff (oscFunction g) x k = coeff G x k := fun k =>
    coeff_congr_real (fun θ => hG _ ⟨KAM.ofReal_mem_complexStrip hS θ, hx⟩) k
  obtain ⟨h1, h2⟩ := hb x hx
  refine ⟨?_, ?_⟩
  · unfold WSummable; simp only [hc]; exact h1
  · unfold wsum; simp only [hc]; exact h2

end OscTransport

section OscLines

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem norm_smul_single {N : ℕ} (t : ℂ) (i : Fin N) :
    ‖t • (Pi.single i 1 : Fin N → ℂ)‖ = ‖t‖ := by
  rw [norm_smul, Pi.norm_single, norm_one, mul_one]

theorem mem_actionNbhd_add {I : Fin n → ℂ} {a R : ℝ} (hI : I ∈ KAM.actionNbhd D a) (j : Fin n)
    {t : ℂ} (ht : ‖t‖ < R) : I + t • Pi.single j 1 ∈ KAM.actionNbhd D (a + R) := by
  obtain ⟨J, hJ, h⟩ := hI
  refine ⟨J, hJ, ?_⟩
  calc ‖I + t • Pi.single j 1 - fun i => (J i : ℂ)‖
      = ‖(I - fun i => (J i : ℂ)) + t • (Pi.single j 1 : Fin n → ℂ)‖ := by congr 1; abel
    _ ≤ ‖I - fun i => (J i : ℂ)‖ + ‖t • (Pi.single j 1 : Fin n → ℂ)‖ := norm_add_le _ _
    _ < a + R := by rw [norm_smul_single]; linarith

/-- Moving the point along an `I` coordinate by less than `R` enlarges `r` by `R`. -/
theorem line_I {a b c R : ℝ} {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D a b c)
    (j : Fin n) {t : ℂ} (ht : ‖t‖ < R) :
    x + t • Pi.single (Fin.castAdd (m + m) j) 1 ∈ oscParams (m := m) D (a + R) b c := by
  obtain ⟨h1, h2, h3⟩ := hx
  have e1 : firstBlock (b := m + m) (x + t • (Pi.single (Fin.castAdd (m + m) j) 1 :
      Fin (n + (m + m)) → ℂ)) = firstBlock (b := m + m) x + t • Pi.single j 1 := by
    funext i
    simp [firstBlock, Pi.single_apply]
  have e2 : lastBlock (a := n) (x + t • (Pi.single (Fin.castAdd (m + m) j) 1 :
      Fin (n + (m + m)) → ℂ)) = lastBlock (a := n) x := by
    funext i
    simp only [lastBlock, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [if_neg (by omega)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact mem_actionNbhd_add h1 j ht
  · rw [e2]; exact h2
  · rw [e2]; exact h3

theorem line_p {a b c R : ℝ} {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D a b c)
    (j : Fin m) {t : ℂ} (ht : ‖t‖ < R) :
    x + t • Pi.single (Fin.natAdd n (Fin.castAdd m j)) 1 ∈ oscParams (m := m) D a (b + R) c := by
  obtain ⟨h1, h2, h3⟩ := hx
  have e1 : firstBlock (b := m + m) (x + t • (Pi.single (Fin.natAdd n (Fin.castAdd m j)) 1 :
      Fin (n + (m + m)) → ℂ)) = firstBlock (b := m + m) x := by
    funext i
    simp only [firstBlock, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [if_neg (by omega)]
    simp
  have e2 : firstBlock (b := m) (lastBlock (a := n) (x + t • (Pi.single
      (Fin.natAdd n (Fin.castAdd m j)) 1 : Fin (n + (m + m)) → ℂ))) =
      firstBlock (b := m) (lastBlock (a := n) x) + t • Pi.single j 1 := by
    funext i
    simp [firstBlock, lastBlock, Pi.single_apply, Fin.ext_iff]
  have e3 : lastBlock (a := m) (lastBlock (a := n) (x + t • (Pi.single
      (Fin.natAdd n (Fin.castAdd m j)) 1 : Fin (n + (m + m)) → ℂ))) =
      lastBlock (a := m) (lastBlock (a := n) x) := by
    funext i
    simp only [lastBlock, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [if_neg (by omega)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact h1
  · rw [e2]
    calc ‖firstBlock (b := m) (lastBlock (a := n) x) + t • (Pi.single j 1 : Fin m → ℂ)‖
        ≤ ‖firstBlock (b := m) (lastBlock (a := n) x)‖ + ‖t • (Pi.single j 1 : Fin m → ℂ)‖ :=
          norm_add_le _ _
      _ < b + R := by rw [norm_smul_single]; linarith
  · rw [e3]; exact h3

theorem line_q {a b c R : ℝ} {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D a b c)
    (j : Fin m) {t : ℂ} (ht : ‖t‖ < R) :
    x + t • Pi.single (Fin.natAdd n (Fin.natAdd m j)) 1 ∈ oscParams (m := m) D a b (c + R) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have e1 : firstBlock (b := m + m) (x + t • (Pi.single (Fin.natAdd n (Fin.natAdd m j)) 1 :
      Fin (n + (m + m)) → ℂ)) = firstBlock (b := m + m) x := by
    funext i
    simp only [firstBlock, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [if_neg (by omega)]
    simp
  have e2 : firstBlock (b := m) (lastBlock (a := n) (x + t • (Pi.single
      (Fin.natAdd n (Fin.natAdd m j)) 1 : Fin (n + (m + m)) → ℂ))) =
      firstBlock (b := m) (lastBlock (a := n) x) := by
    funext i
    simp only [firstBlock, lastBlock, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [if_neg (by omega)]
    simp
  have e3 : lastBlock (a := m) (lastBlock (a := n) (x + t • (Pi.single
      (Fin.natAdd n (Fin.natAdd m j)) 1 : Fin (n + (m + m)) → ℂ))) =
      lastBlock (a := m) (lastBlock (a := n) x) + t • Pi.single j 1 := by
    funext i
    simp [lastBlock, Pi.single_apply, Fin.ext_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact h1
  · rw [e2]; exact h2
  · rw [e3]
    calc ‖lastBlock (a := m) (lastBlock (a := n) x) + t • (Pi.single j 1 : Fin m → ℂ)‖
        ≤ ‖lastBlock (a := m) (lastBlock (a := n) x)‖ + ‖t • (Pi.single j 1 : Fin m → ℂ)‖ :=
          norm_add_le _ _
      _ < c + R := by rw [norm_smul_single]; linarith

end OscLines

section ObDer

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

/-- A directional action derivative, with its own loss `R`. -/
theorem ob_der_dir {r₀ rp₀ rq₀ S₀ r' rp' rq' S' A R : ℝ} {u : CHam (n + m)}
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hA : oscBound D r₀ rp₀ rq₀ S₀ u A) (hpos : 0 < S')
    (hSS : S' < S₀) (hR : 0 < R) (a : CPhase (n + m)) (i : Fin (n + (m + m)))
    (ha : oscPack a = (0, Pi.single i 1))
    (hline : ∀ x ∈ oscParams (m := m) D r' rp' rq', ∀ t : ℂ, ‖t‖ < R →
      x + t • (Pi.single i 1 : Fin (n + (m + m)) → ℂ) ∈ oscParams (m := m) D r₀ rp₀ rq₀) :
    oscBound D r' rp' rq' S' (fun z => fderiv ℂ u z a) (A / R) := by
  have hS₀ : 0 < S₀ := hpos.trans hSS
  have hb := wsum_dI_le_on (isOpen_oscParams (m := m) D r₀ rp₀ rq₀) hS₀ hSS.le hu.flat hA i hR hline
  refine oscBound_of_flat hpos (G := dI i (oscFunction u)) (fun y hy => ?_) hb
  have hsub : oscParams (m := m) D r' rp' rq' ⊆ oscParams D r₀ rp₀ rq₀ := fun x hx => by
    simpa using hline x hx 0 (by simpa using hR)
  have hy' : y ∈ KAM.complexStrip n S₀ ×ˢ oscParams (m := m) D r₀ rp₀ rq₀ :=
    ⟨fun j => (hy.1 j).trans hSS, hsub hy.2⟩
  have := fderiv_oscFunction hu hy' a
  rw [ha] at this
  exact this.symm

theorem ob_der_theta {r₀ rp₀ rq₀ S₀ r' rp' rq' S' A : ℝ} {u : CHam (n + m)}
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hA : oscBound D r₀ rp₀ rq₀ S₀ u A) (hpos : 0 < S')
    (hSS : S' < S₀) (hsub : oscParams (m := m) D r' rp' rq' ⊆ oscParams D r₀ rp₀ rq₀) (j : Fin n) :
    oscBound D r' rp' rq' S' (fun z => fderiv ℂ u z (Pi.single (Fin.castAdd m j) 1, 0))
      (A / (Real.exp 1 * (S₀ - S'))) := by
  have hS₀ : 0 < S₀ := hpos.trans hSS
  refine oscBound_of_flat hpos (G := dtheta j (oscFunction u)) (fun y hy => ?_) (fun x hx => ?_)
  · have hy' : y ∈ KAM.complexStrip n S₀ ×ˢ oscParams (m := m) D r₀ rp₀ rq₀ :=
      ⟨fun j => (hy.1 j).trans hSS, hsub hy.2⟩
    have := fderiv_oscFunction hu hy' (Pi.single (Fin.castAdd m j) 1, 0)
    rw [oscPack_theta] at this
    exact this.symm
  · obtain ⟨h1, h2⟩ := wsum_dtheta_le (isOpen_oscParams (m := m) D r₀ rp₀ rq₀) hu.flat hA hpos
      hSS (hsub hx)
    refine ⟨h1 j, (Finset.single_le_sum (f := fun j' => wsum (dtheta j' (oscFunction u)) S' x)
      (fun j' _ => tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (Finset.mem_univ j)).trans h2⟩

theorem ob_der {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ A : ℝ} {u : CHam (n + m)}
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hA : oscBound D r₀ rp₀ rq₀ S₀ u A)
    (hpos : 0 < r - ρ ∧ 0 < rp - ρp ∧ 0 < rq - ρq ∧ 0 < S - σ)
    (houter : r - ρ < r₀ ∧ rp - ρp < rp₀ ∧ rq - ρq < rq₀ ∧ S - σ < S₀) :
    (∀ j : Fin n, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (Pi.single (Fin.castAdd m j) 1, 0)) (A / (exp 1 * (S₀ - S + σ)))) ∧
    (∀ j : Fin n, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (0, Pi.single (Fin.castAdd m j) 1)) (A / (r₀ - r + ρ))) ∧
    (∀ j : Fin m, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (0, Pi.single (Fin.natAdd n j) 1)) (A / (rp₀ - rp + ρp))) ∧
    (∀ j : Fin m, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (Pi.single (Fin.natAdd n j) 1, 0)) (A / (rq₀ - rq + ρq))) := by
  obtain ⟨hr, hrp, hrq, hS⟩ := hpos
  obtain ⟨hr₀, hrp₀, hrq₀, hS₀⟩ := houter
  have hsub : oscParams (m := m) D (r - ρ) (rp - ρp) (rq - ρq) ⊆ oscParams D r₀ rp₀ rq₀ :=
    oscParams_mono hr₀.le hrp₀.le hrq₀.le
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have h := ob_der_theta hu hA hS hS₀ hsub j
    have e : S₀ - (S - σ) = S₀ - S + σ := by ring
    rwa [e] at h
  · refine ob_der_dir hu hA hS hS₀ (by linarith) _ (Fin.castAdd (m + m) j) (oscPack_I j)
      (fun x hx t ht => ?_)
    have h := line_I hx j ht
    have e : r - ρ + (r₀ - r + ρ) = r₀ := by ring
    rw [e] at h
    exact oscParams_mono le_rfl hrp₀.le hrq₀.le h
  · refine ob_der_dir hu hA hS hS₀ (by linarith) _ (Fin.natAdd n (Fin.castAdd m j)) (oscPack_p j)
      (fun x hx t ht => ?_)
    have h := line_p hx j ht
    have e : rp - ρp + (rp₀ - rp + ρp) = rp₀ := by ring
    rw [e] at h
    exact oscParams_mono hr₀.le le_rfl hrq₀.le h
  · refine ob_der_dir hu hA hS hS₀ (by linarith) _ (Fin.natAdd n (Fin.natAdd m j)) (oscPack_q j)
      (fun x hx t ht => ?_)
    have h := line_q hx j ht
    have e : rq - ρq + (rq₀ - rq + ρq) = rq₀ := by ring
    rw [e] at h
    exact oscParams_mono hr₀.le hrp₀.le le_rfl h

end ObDer

section ObField

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem oscDom_mono {a a' b b' c c' S S' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hS : S ≤ S') : oscDom (m := m) D a b c S ⊆ oscDom D a' b' c' S' := fun z hz =>
  ⟨fun i => (hz.1 i).trans_le hS, oscParams_mono ha hb hc hz.2⟩

theorem oscClass.mono {a a' b b' c c' S S' : ℝ} {u : CHam (n + m)} (hu : oscClass D a' b' c' S' u)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hS : S ≤ S') : oscClass D a b c S u :=
  ⟨hu.1.mono (oscDom_mono ha hb hc hS), fun j z hz => hu.2 j z (oscDom_mono ha hb hc hS hz)⟩

theorem oscClass.fderiv_apply {r rp rq S : ℝ} {u : CHam (n + m)} (hu : oscClass D r rp rq S u)
    (a : CPhase (n + m)) : oscClass D r rp rq S (fun z => fderiv ℂ u z a) := by
  have hU := isOpen_oscDom (m := m) D r rp rq S
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hU hu.1
  refine ⟨hreg.1.clm_apply (differentiableOn_const a), fun j z hz => ?_⟩
  set e : CPhase (n + m) := (Pi.single (Fin.castAdd m j) 1, 0) with he
  have hper : ∀ w ∈ oscDom (m := m) D r rp rq S, u (w + e) = u w := fun w hw => by
    have hwe : w + e = (w.1 + Pi.single (Fin.castAdd m j) 1, w.2) := by ext <;> simp [he]
    rw [hwe]; exact hu.2 j w hw
  have hze : (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) = z + e := by ext <;> simp [he]
  show fderiv ℂ u (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) a = fderiv ℂ u z a
  rw [hze, fderiv_shift_eq hU e hper hz]

theorem oscBound.norm_le {r rp rq S M : ℝ} {g : CHam (n + m)} (hg : oscClass D r rp rq S g)
    (hb : oscBound D r rp rq S g M) : ∀ z ∈ oscDom (m := m) D r rp rq S, ‖g z‖ ≤ M := by
  intro z hz
  have h := norm_le_of_wsum (isOpen_oscParams (m := m) D r rp rq) hg.flat hb (oscPack z) hz
  simpa [oscFunction, s_osc_data] using h

theorem ob_field {r rp rq S ρ ρp ρq σ E : ℝ} {φ : CHam (n + m)}
    (hφ : oscClass D r rp rq S φ) (hE : oscBound D r rp rq S φ E)
    (hρ : 0 < ρ ∧ ρ < r) (hρp : 0 < ρp ∧ ρp < rp) (hρq : 0 < ρq ∧ ρq < rq)
    (hσ : 0 < σ ∧ σ < S) :
    ∀ z ∈ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ),
      oscGauge ρ ρp ρq σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ E / min (ρ * σ) (ρp * ρq) := by
  intro z hz
  obtain ⟨hρ0, hρr⟩ := hρ
  obtain ⟨hρp0, hρpr⟩ := hρp
  obtain ⟨hρq0, hρqr⟩ := hρq
  obtain ⟨hσ0, hσS⟩ := hσ
  obtain ⟨hθ, hI, hp, hq⟩ := ob_der (n := n) (m := m) (D := D) (r₀ := r) (rp₀ := rp) (rq₀ := rq)
    (S₀ := S) (r := r) (rp := rp) (rq := rq) (S := S) (ρ := ρ) (ρp := ρp) (ρq := ρq) (σ := σ)
    hφ hE ⟨by linarith, by linarith, by linarith, by linarith⟩
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hT : ∀ a : CPhase (n + m), oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ φ z a) := fun a =>
    (hφ.fderiv_apply a).mono (by linarith) (by linarith) (by linarith) (by linarith)
  have hx : (oscPack z).2 ∈ oscParams (m := m) D r rp rq :=
    oscParams_mono (by linarith) (by linarith) (by linarith) hz.2
  have hE0 : 0 ≤ E := nonneg_of_wsum (F := oscFunction φ) hE hx
  set M := min (ρ * σ) (ρp * ρq) with hM
  have hMpos : 0 < M := lt_min (by positivity) (by positivity)
  have hM1 : M ≤ ρ * σ := min_le_left _ _
  have hM2 : M ≤ ρp * ρq := min_le_right _ _
  have key : ∀ {x a b : ℝ}, 0 < a → 0 < b → x ≤ E / a → M ≤ a * b → x / b ≤ E / M :=
    fun {x a b} ha hb hx hab => by
      calc x / b ≤ E / a / b := div_le_div_of_nonneg_right hx hb.le
        _ = E / (a * b) := div_div _ _ _
        _ ≤ E / M := div_le_div_of_nonneg_left hE0 hMpos hab
  have hexp : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have bθ : ∀ j : Fin n, ‖fderiv ℂ φ z (Pi.single (Fin.castAdd m j) 1, 0)‖ ≤ E / σ := fun j => by
    have h := oscBound.norm_le (hT _) (hθ j) z hz
    have e : S - S + σ = σ := by ring
    rw [e] at h
    refine h.trans ?_
    exact div_le_div_of_nonneg_left hE0 hσ0 (by nlinarith)
  have bI : ∀ j : Fin n, ‖fderiv ℂ φ z (0, Pi.single (Fin.castAdd m j) 1)‖ ≤ E / ρ := fun j => by
    have h := oscBound.norm_le (hT _) (hI j) z hz
    have e : r - r + ρ = ρ := by ring
    rwa [e] at h
  have bp : ∀ j : Fin m, ‖fderiv ℂ φ z (0, Pi.single (Fin.natAdd n j) 1)‖ ≤ E / ρp := fun j => by
    have h := oscBound.norm_le (hT _) (hp j) z hz
    have e : rp - rp + ρp = ρp := by ring
    rwa [e] at h
  have bq : ∀ j : Fin m, ‖fderiv ℂ φ z (Pi.single (Fin.natAdd n j) 1, 0)‖ ≤ E / ρq := fun j => by
    have h := oscBound.norm_le (hT _) (hq j) z hz
    have e : rq - rq + ρq = ρq := by ring
    rwa [e] at h
  unfold oscGauge
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · refine key hρ0 hσ0 ?_ hM1
    exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => bI j
  · refine key hσ0 hρ0 ?_ (by linarith)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    simpa [KAM.hamiltonianVectorFieldℂ, firstBlock] using bθ j
  · refine key hρp0 hρq0 ?_ hM2
    exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => bp j
  · refine key hρq0 hρp0 ?_ (by linarith)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    simpa [KAM.hamiltonianVectorFieldℂ, lastBlock] using bq j

end ObField

section ObBracketAux

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

/-- The four coordinate derivatives of a class function, in flat coordinates. -/
theorem osc_deriv_eqs {r rp rq S : ℝ} {u : CHam (n + m)} (hu : oscClass D r rp rq S u)
    {y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)}
    (hy : y ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq) :
    (∀ j : Fin n, fderiv ℂ u (oscUnpack y) (Pi.single (Fin.castAdd m j) 1, 0) =
      dtheta j (oscFunction u) y) ∧
    (∀ j : Fin n, fderiv ℂ u (oscUnpack y) (0, Pi.single (Fin.castAdd m j) 1) =
      dI (Fin.castAdd (m + m) j) (oscFunction u) y) ∧
    (∀ j : Fin m, fderiv ℂ u (oscUnpack y) (0, Pi.single (Fin.natAdd n j) 1) =
      dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction u) y) ∧
    (∀ j : Fin m, fderiv ℂ u (oscUnpack y) (Pi.single (Fin.natAdd n j) 1, 0) =
      dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction u) y) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have := fderiv_oscFunction hu hy (Pi.single (Fin.castAdd m j) 1, 0)
    rw [oscPack_theta] at this
    exact this.symm
  · have := fderiv_oscFunction hu hy (0, Pi.single (Fin.castAdd m j) 1)
    rw [oscPack_I] at this
    exact this.symm
  · have := fderiv_oscFunction hu hy (0, Pi.single (Fin.natAdd n j) 1)
    rw [oscPack_p] at this
    exact this.symm
  · have := fderiv_oscFunction hu hy (Pi.single (Fin.natAdd n j) 1, 0)
    rw [oscPack_q] at this
    exact this.symm

theorem comp_aux {c X d a b Mn : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hd : 0 < d) (ha : 0 < a)
    (hMn : 0 < Mn) (h : Mn ≤ a * b) : c * X / (d * a) ≤ c * (b / d) * X / Mn := by
  rw [div_le_div_iff₀ (by positivity) hMn]
  have : c * (b / d) * X * (d * a) = c * X * (a * b) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg hc hX)

/-- The weighted sum is subadditive for finite linear combinations (coefficients are linear). -/
theorem wsum_sum_le' {N : ℕ} {ι : Type*} [Fintype ι] {s : ℝ} {I : Fin N → ℂ} (a : ι → ℂ)
    (g : ι → (Fin n → ℂ) × (Fin N → ℂ) → ℂ)
    (hc : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun l => (x l : ℂ), I))
    (hg : ∀ j, WSummable (g j) s I) :
    WSummable (fun z => ∑ j, a j * g j z) s I ∧
      wsum (fun z => ∑ j, a j * g j z) s I ≤ ∑ j, ‖a j‖ * wsum (g j) s I := by
  have hcoeff : ∀ k, coeff (fun z => ∑ j, a j * g j z) I k = ∑ j, a j * coeff (g j) I k :=
    fun k => KAM.torusCoeff_finset_sum_mul Finset.univ hc a k
  have hterm : ∀ k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k ≤
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := fun k => by
    rw [hcoeff]
    calc ‖∑ j, a j * coeff (g j) I k‖ * modeWeight s k
        ≤ (∑ j, ‖a j * coeff (g j) I k‖) * modeWeight s k :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, mul_assoc]
  have hsum : Summable fun k : Fin n → ℤ =>
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
    summable_sum fun j _ => (hg j).mul_left _
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k :=
    fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsum, ?_⟩
  unfold wsum
  calc ∑' k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k
      ≤ ∑' k, ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnn hterm hsum) hsum
    _ = ∑ j, ‖a j‖ * ∑' k, ‖coeff (g j) I k‖ * modeWeight s k := by
        rw [Summable.tsum_finsetSum fun j _ => (hg j).mul_left _]
        exact Finset.sum_congr rfl fun j _ => tsum_mul_left

end ObBracketAux

section ObBracket

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem lineI' {a b c a₀ b₀ c₀ : ℝ} {x : Fin (n + (m + m)) → ℂ}
    (hx : x ∈ oscParams (m := m) D a b c) (hb : b ≤ b₀) (hc : c ≤ c₀) (j : Fin n) {t : ℂ}
    (ht : ‖t‖ < a₀ - a) :
    x + t • Pi.single (Fin.castAdd (m + m) j) 1 ∈ oscParams (m := m) D a₀ b₀ c₀ := by
  have h := line_I hx j ht
  rw [add_sub_cancel] at h
  exact oscParams_mono le_rfl hb hc h

theorem lineP' {a b c a₀ b₀ c₀ : ℝ} {x : Fin (n + (m + m)) → ℂ}
    (hx : x ∈ oscParams (m := m) D a b c) (ha : a ≤ a₀) (hc : c ≤ c₀) (j : Fin m) {t : ℂ}
    (ht : ‖t‖ < b₀ - b) :
    x + t • Pi.single (Fin.natAdd n (Fin.castAdd m j)) 1 ∈ oscParams (m := m) D a₀ b₀ c₀ := by
  have h := line_p hx j ht
  rw [add_sub_cancel] at h
  exact oscParams_mono ha le_rfl hc h

theorem lineQ' {a b c a₀ b₀ c₀ : ℝ} {x : Fin (n + (m + m)) → ℂ}
    (hx : x ∈ oscParams (m := m) D a b c) (ha : a ≤ a₀) (hb : b ≤ b₀) (j : Fin m) {t : ℂ}
    (ht : ‖t‖ < c₀ - c) :
    x + t • Pi.single (Fin.natAdd n (Fin.natAdd m j)) 1 ∈ oscParams (m := m) D a₀ b₀ c₀ := by
  have h := line_q hx j ht
  rw [add_sub_cancel] at h
  exact oscParams_mono ha hb le_rfl h

/-- Index set and coefficients of the bracket as a signed finite sum of products. -/
abbrev BIdx (n m : ℕ) := (Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin m)

def brCoeff : BIdx n m → ℂ :=
  Sum.elim (Sum.elim (fun _ => 1) (fun _ => -1)) (Sum.elim (fun _ => 1) (fun _ => -1))

def brFun (F G : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ) :
    BIdx n m → (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ :=
  Sum.elim
    (Sum.elim (fun j y => dtheta j F y * dI (Fin.castAdd (m + m) j) G y)
      (fun j y => dI (Fin.castAdd (m + m) j) F y * dtheta j G y))
    (Sum.elim (fun j y => dI (Fin.natAdd n (Fin.natAdd m j)) F y *
        dI (Fin.natAdd n (Fin.castAdd m j)) G y)
      (fun j y => dI (Fin.natAdd n (Fin.castAdd m j)) F y *
        dI (Fin.natAdd n (Fin.natAdd m j)) G y))

theorem bracket_flat_eq {r₀ rp₀ rq₀ S₀ r rp rq S : ℝ} {u w : CHam (n + m)}
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hw : oscClass D r rp rq S w)
    {y : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)}
    (hyu : y ∈ KAM.complexStrip n S₀ ×ˢ oscParams (m := m) D r₀ rp₀ rq₀)
    (hyw : y ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq) :
    oscFunction (poissonBracket u w) y =
      ∑ ι, brCoeff ι * brFun (oscFunction u) (oscFunction w) ι y := by
  obtain ⟨t1, t2, t3, t4⟩ := osc_deriv_eqs hu hyu
  obtain ⟨s1, s2, s3, s4⟩ := osc_deriv_eqs hw hyw
  show poissonBracket u w (oscUnpack y) = _
  unfold poissonBracket
  rw [Fin.sum_univ_add]
  simp only [brCoeff, brFun, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul,
    neg_one_mul, Finset.sum_neg_distrib, t1, t2, t3, t4, s1, s2, s3, s4, Finset.sum_sub_distrib]
  ring

theorem prod_term {N : ℕ} {x : Fin N → ℂ} {δ s : ℝ} (hs : 0 < s) {f g : (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    (hf : InClass ({x} : Set (Fin N → ℂ)) δ s f) (hg : InClass ({x} : Set (Fin N → ℂ)) δ s g)
    (hx : x ∈ polyNbhd ({x} : Set (Fin N → ℂ)) δ) (hf' : WSummable f s x)
    (hg' : WSummable g s x) :
    Continuous (fun θ : Fin n → ℝ => (f (fun l => (θ l : ℂ), x) * g (fun l => (θ l : ℂ), x))) ∧
      WSummable (fun z => f z * g z) s x ∧
      wsum (fun z => f z * g z) s x ≤ wsum f s x * wsum g s x := by
  obtain ⟨hcls, -, -, hws, hle⟩ := coeff_mul hs hf hg hx hf' hg'
  refine ⟨?_, hws, hle⟩
  exact (hcls.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun θ => ⟨KAM.ofReal_mem_complexStrip hs θ, hx⟩)

end ObBracket

section ObBracketBound

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

theorem bracket_bound {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ A B : ℝ} {u w : CHam (n + m)}
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hw : oscClass D r rp rq S w)
    (hA : oscBound D r₀ rp₀ rq₀ S₀ u A) (hB : oscBound D r rp rq S w B)
    (hρ : 0 < ρ ∧ ρ < r) (hρp : 0 < ρp ∧ ρp < rp) (hρq : 0 < ρq ∧ ρq < rq)
    (hσ : 0 < σ ∧ σ < S) (houter : r - ρ < r₀ ∧ rp - ρp < rp₀ ∧ rq - ρq < rq₀ ∧ S - σ < S₀) :
    oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket u w)
      (((1 / exp 1) * (ρ / (r₀ - r + ρ) + σ / (S₀ - S + σ)) +
        m * (ρq / (rq₀ - rq + ρq) + ρp / (rp₀ - rp + ρp))) /
          min (ρ * σ) (ρp * ρq) * A * B) := by
  obtain ⟨hρ0, hρr⟩ := hρ
  obtain ⟨hρp0, hρpr⟩ := hρp
  obtain ⟨hρq0, hρqr⟩ := hρq
  obtain ⟨hσ0, hσS⟩ := hσ
  obtain ⟨hr₀, hrp₀, hrq₀, hS₀⟩ := houter
  have hS' : 0 < S - σ := by linarith
  have hSS : S - σ < S := by linarith
  have hPu := isOpen_oscParams (m := m) D r₀ rp₀ rq₀
  have hPw := isOpen_oscParams (m := m) D r rp rq
  have hsubu : oscParams (m := m) D (r - ρ) (rp - ρp) (rq - ρq) ⊆ oscParams D r₀ rp₀ rq₀ :=
    oscParams_mono hr₀.le hrp₀.le hrq₀.le
  have hsubw : oscParams (m := m) D (r - ρ) (rp - ρp) (rq - ρq) ⊆ oscParams D r rp rq :=
    oscParams_mono (by linarith) (by linarith) (by linarith)
  have hFu := hu.flat
  have hFw := hw.flat
  have hS₀pos : 0 < S₀ := hS'.trans hS₀
  have hSpos : 0 < S := hS'.trans hSS
  have e1 : S₀ - (S - σ) = S₀ - S + σ := by ring
  have e2 : S - (S - σ) = σ := by ring
  have e3 : r₀ - (r - ρ) = r₀ - r + ρ := by ring
  have e4 : rp₀ - (rp - ρp) = rp₀ - rp + ρp := by ring
  have e5 : rq₀ - (rq - ρq) = rq₀ - rq + ρq := by ring
  have e6 : r - (r - ρ) = ρ := by ring
  have e7 : rp - (rp - ρp) = ρp := by ring
  have e8 : rq - (rq - ρq) = ρq := by ring
  have hd1 : 0 < r₀ - r + ρ := by linarith
  have hd2 : 0 < S₀ - S + σ := by linarith
  have hd3 : 0 < rq₀ - rq + ρq := by linarith
  have hd4 : 0 < rp₀ - rp + ρp := by linarith
  have hMn : 0 < min (ρ * σ) (ρp * ρq) := lt_min (by positivity) (by positivity)
  have hM1 : min (ρ * σ) (ρp * ρq) ≤ ρ * σ := min_le_left _ _
  have hM2 : min (ρ * σ) (ρp * ρq) ≤ ρp * ρq := min_le_right _ _
  have hexp := Real.exp_pos 1
  refine oscBound_of_flat hS' (G := fun z => ∑ ι, brCoeff ι *
    brFun (oscFunction u) (oscFunction w) ι z) (fun y hy => ?_) (fun x hx => ?_)
  · exact bracket_flat_eq hu hw ⟨fun j => (hy.1 j).trans hS₀, hsubu hy.2⟩
      ⟨fun j => (hy.1 j).trans hSS, hsubw hy.2⟩
  have hxu := hsubu hx
  have hxw := hsubw hx
  have hA0 : 0 ≤ A := nonneg_of_wsum (F := oscFunction u) hA hxu
  have hB0 : 0 ≤ B := nonneg_of_wsum (F := oscFunction w) hB hxw
  -- flat Cauchy estimates at `x`
  obtain ⟨hθu, hθu'⟩ := wsum_dtheta_le hPu hFu hA hS' hS₀ hxu
  obtain ⟨hθw, hθw'⟩ := wsum_dtheta_le hPw hFw hB hS' hSS hxw
  rw [e1] at hθu'
  rw [e2] at hθw'
  have hIu : ∀ j : Fin n, WSummable (dI (Fin.castAdd (m + m) j) (oscFunction u)) (S - σ) x ∧
      wsum (dI (Fin.castAdd (m + m) j) (oscFunction u)) (S - σ) x ≤ A / (r₀ - r + ρ) := fun j => by
    have := wsum_dI_le_on hPu hS₀pos hS₀.le hFu hA (Fin.castAdd (m + m) j)
      (show 0 < r₀ - (r - ρ) by linarith)
      (fun x hx t ht => lineI' hx hrp₀.le hrq₀.le j ht) x hx
    rwa [e3] at this
  have hPu' : ∀ j : Fin m, WSummable (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction u))
      (S - σ) x ∧ wsum (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction u)) (S - σ) x ≤
        A / (rp₀ - rp + ρp) := fun j => by
    have := wsum_dI_le_on hPu hS₀pos hS₀.le hFu hA (Fin.natAdd n (Fin.castAdd m j))
      (show 0 < rp₀ - (rp - ρp) by linarith)
      (fun x hx t ht => lineP' hx hr₀.le hrq₀.le j ht) x hx
    rwa [e4] at this
  have hQu : ∀ j : Fin m, WSummable (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction u))
      (S - σ) x ∧ wsum (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction u)) (S - σ) x ≤
        A / (rq₀ - rq + ρq) := fun j => by
    have := wsum_dI_le_on hPu hS₀pos hS₀.le hFu hA (Fin.natAdd n (Fin.natAdd m j))
      (show 0 < rq₀ - (rq - ρq) by linarith)
      (fun x hx t ht => lineQ' hx hr₀.le hrp₀.le j ht) x hx
    rwa [e5] at this
  have hIw : ∀ j : Fin n, WSummable (dI (Fin.castAdd (m + m) j) (oscFunction w)) (S - σ) x ∧
      wsum (dI (Fin.castAdd (m + m) j) (oscFunction w)) (S - σ) x ≤ B / ρ := fun j => by
    have := wsum_dI_le_on hPw hSpos hSS.le hFw hB (Fin.castAdd (m + m) j)
      (show 0 < r - (r - ρ) by linarith)
      (fun x hx t ht => lineI' hx (by linarith) (by linarith) j ht) x hx
    rwa [e6] at this
  have hPw' : ∀ j : Fin m, WSummable (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction w))
      (S - σ) x ∧ wsum (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction w)) (S - σ) x ≤
        B / ρp := fun j => by
    have := wsum_dI_le_on hPw hSpos hSS.le hFw hB (Fin.natAdd n (Fin.castAdd m j))
      (show 0 < rp - (rp - ρp) by linarith)
      (fun x hx t ht => lineP' hx (by linarith) (by linarith) j ht) x hx
    rwa [e7] at this
  have hQw : ∀ j : Fin m, WSummable (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction w))
      (S - σ) x ∧ wsum (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction w)) (S - σ) x ≤
        B / ρq := fun j => by
    have := wsum_dI_le_on hPw hSpos hSS.le hFw hB (Fin.natAdd n (Fin.natAdd m j))
      (show 0 < rq - (rq - ρq) by linarith)
      (fun x hx t ht => lineQ' hx (by linarith) (by linarith) j ht) x hx
    rwa [e8] at this
  -- local classes
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hPu.inter hPw) x ⟨hxu, hxw⟩
  have hbu : ball x δ ⊆ oscParams (m := m) D r₀ rp₀ rq₀ := fun y hy => (hball hy).1
  have hbw : ball x δ ⊆ oscParams (m := m) D r rp rq := fun y hy => (hball hy).2
  have hxδ : x ∈ polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) δ := by
    rw [polyNbhd_singleton]; exact mem_ball_self hδ
  have cu : ∀ v, InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) δ (S - σ)
      (fun z => fderiv ℂ (oscFunction u) z v) := fun v =>
    ((hFu.fderiv_apply hPu v).inClass hbu hS₀.le)
  have cw : ∀ v, InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) δ (S - σ)
      (fun z => fderiv ℂ (oscFunction w) z v) := fun v =>
    ((hFw.fderiv_apply hPw v).inClass hbw hSS.le)
  have hprod : ∀ ι, (Continuous fun θ : Fin n → ℝ =>
        brFun (oscFunction u) (oscFunction w) ι (fun l => (θ l : ℂ), x)) ∧
      WSummable (brFun (oscFunction u) (oscFunction w) ι) (S - σ) x ∧
      wsum (brFun (oscFunction u) (oscFunction w) ι) (S - σ) x ≤
        (match ι with
          | Sum.inl (Sum.inl j) => wsum (dtheta j (oscFunction u)) (S - σ) x *
              wsum (dI (Fin.castAdd (m + m) j) (oscFunction w)) (S - σ) x
          | Sum.inl (Sum.inr j) => wsum (dI (Fin.castAdd (m + m) j) (oscFunction u)) (S - σ) x *
              wsum (dtheta j (oscFunction w)) (S - σ) x
          | Sum.inr (Sum.inl j) =>
              wsum (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction u)) (S - σ) x *
              wsum (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction w)) (S - σ) x
          | Sum.inr (Sum.inr j) =>
              wsum (dI (Fin.natAdd n (Fin.castAdd m j)) (oscFunction u)) (S - σ) x *
              wsum (dI (Fin.natAdd n (Fin.natAdd m j)) (oscFunction w)) (S - σ) x) := by
    rintro ((j | j) | (j | j))
    · exact prod_term hS' (cu _) (cw _) hxδ (hθu j) (hIw j).1
    · exact prod_term hS' (cu _) (cw _) hxδ (hIu j).1 (hθw j)
    · exact prod_term hS' (cu _) (cw _) hxδ (hQu j).1 (hPw' j).1
    · exact prod_term hS' (cu _) (cw _) hxδ (hPu' j).1 (hQw j).1
  obtain ⟨hws, hwle⟩ := wsum_sum_le' (s := S - σ) (I := x) brCoeff
    (brFun (oscFunction u) (oscFunction w)) (fun ι => (hprod ι).1) (fun ι => (hprod ι).2.1)
  refine ⟨hws, hwle.trans ?_⟩
  have hnn : ∀ f : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ, 0 ≤ wsum f (S - σ) x := fun f =>
    tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hnorm : ∀ ι : BIdx n m, ‖brCoeff ι‖ = 1 := by
    rintro ((j | j) | (j | j)) <;> simp [brCoeff]
  simp only [hnorm, one_mul, Fintype.sum_sum_type]
  have h1 : ∑ j : Fin n, wsum (brFun (oscFunction u) (oscFunction w) (Sum.inl (Sum.inl j)))
      (S - σ) x ≤ A / (exp 1 * (S₀ - S + σ)) * (B / ρ) := by
    calc _ ≤ ∑ j : Fin n, wsum (dtheta j (oscFunction u)) (S - σ) x * (B / ρ) :=
          Finset.sum_le_sum fun j _ => ((hprod (Sum.inl (Sum.inl j))).2.2).trans
            (mul_le_mul_of_nonneg_left (hIw j).2 (hnn _))
      _ = (∑ j : Fin n, wsum (dtheta j (oscFunction u)) (S - σ) x) * (B / ρ) := by
          rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hθu' (by positivity)
  have h2 : ∑ j : Fin n, wsum (brFun (oscFunction u) (oscFunction w) (Sum.inl (Sum.inr j)))
      (S - σ) x ≤ A / (r₀ - r + ρ) * (B / (exp 1 * σ)) := by
    calc _ ≤ ∑ j : Fin n, A / (r₀ - r + ρ) * wsum (dtheta j (oscFunction w)) (S - σ) x :=
          Finset.sum_le_sum fun j _ => ((hprod (Sum.inl (Sum.inr j))).2.2).trans
            (mul_le_mul_of_nonneg_right (hIu j).2 (hnn _))
      _ = A / (r₀ - r + ρ) * ∑ j : Fin n, wsum (dtheta j (oscFunction w)) (S - σ) x := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hθw' (by positivity)
  have h3 : ∑ j : Fin m, wsum (brFun (oscFunction u) (oscFunction w) (Sum.inr (Sum.inl j)))
      (S - σ) x ≤ m * (A / (rq₀ - rq + ρq) * (B / ρp)) := by
    calc _ ≤ ∑ _j : Fin m, A / (rq₀ - rq + ρq) * (B / ρp) :=
          Finset.sum_le_sum fun j _ => ((hprod (Sum.inr (Sum.inl j))).2.2).trans
            (mul_le_mul (hQu j).2 (hPw' j).2 (hnn _) (by positivity))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : ∑ j : Fin m, wsum (brFun (oscFunction u) (oscFunction w) (Sum.inr (Sum.inr j)))
      (S - σ) x ≤ m * (A / (rp₀ - rp + ρp) * (B / ρq)) := by
    calc _ ≤ ∑ _j : Fin m, A / (rp₀ - rp + ρp) * (B / ρq) :=
          Finset.sum_le_sum fun j _ => ((hprod (Sum.inr (Sum.inr j))).2.2).trans
            (mul_le_mul (hPu' j).2 (hQw j).2 (hnn _) (by positivity))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hX : 0 ≤ A * B := mul_nonneg hA0 hB0
  have c1 := comp_aux (c := 1 / exp 1) (X := A * B) (d := S₀ - S + σ) (a := ρ) (b := σ)
    (by positivity) hX hd2 hρ0 hMn hM1
  have c2 := comp_aux (c := 1 / exp 1) (X := A * B) (d := r₀ - r + ρ) (a := σ) (b := ρ)
    (by positivity) hX hd1 hσ0 hMn (hM1.trans_eq (mul_comm _ _))
  have c3 := comp_aux (c := (m : ℝ)) (X := A * B) (d := rq₀ - rq + ρq) (a := ρp) (b := ρq)
    hm0 hX hd3 hρp0 hMn hM2
  have c4 := comp_aux (c := (m : ℝ)) (X := A * B) (d := rp₀ - rp + ρp) (a := ρq) (b := ρp)
    hm0 hX hd4 hρq0 hMn (hM2.trans_eq (mul_comm _ _))
  have q1 : A / (exp 1 * (S₀ - S + σ)) * (B / ρ) = 1 / exp 1 * (A * B) / ((S₀ - S + σ) * ρ) := by
    field_simp
  have q2 : A / (r₀ - r + ρ) * (B / (exp 1 * σ)) = 1 / exp 1 * (A * B) / ((r₀ - r + ρ) * σ) := by
    field_simp
  have q3 : (m : ℝ) * (A / (rq₀ - rq + ρq) * (B / ρp)) = m * (A * B) / ((rq₀ - rq + ρq) * ρp) := by
    field_simp
  have q4 : (m : ℝ) * (A / (rp₀ - rp + ρp) * (B / ρq)) = m * (A * B) / ((rp₀ - rp + ρp) * ρq) := by
    field_simp
  rw [q1] at h1
  rw [q2] at h2
  rw [q3] at h3
  rw [q4] at h4
  have hfin : (1 / exp 1 * (σ / (S₀ - S + σ)) * (A * B) / min (ρ * σ) (ρp * ρq) +
      1 / exp 1 * (ρ / (r₀ - r + ρ)) * (A * B) / min (ρ * σ) (ρp * ρq)) +
      (m * (ρq / (rq₀ - rq + ρq)) * (A * B) / min (ρ * σ) (ρp * ρq) +
        m * (ρp / (rp₀ - rp + ρp)) * (A * B) / min (ρ * σ) (ρp * ρq)) =
      ((1 / exp 1) * (ρ / (r₀ - r + ρ) + σ / (S₀ - S + σ)) +
        m * (ρq / (rq₀ - rq + ρq) + ρp / (rp₀ - rp + ρp))) /
          min (ρ * σ) (ρp * ρq) * A * B := by
    field_simp
    ring
  linarith


end ObBracketBound

section OscBracket

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

-- `hn`, `hm` are part of the signature (the proof does not need them).
set_option linter.unusedVariables false in
/-- `bpP:p2:osc-bracket`: the bracket of oscillator-class functions, with the four-radius losses
and the factor `m` from the `m` pairs of fast coordinates. -/
theorem osc_bracket {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ A B : ℝ}
    {u w : CHam (n + m)} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hw : oscClass D r rp rq S w)
    (hA : oscBound D r₀ rp₀ rq₀ S₀ u A) (hB : oscBound D r rp rq S w B)
    (hρ : 0 < ρ ∧ ρ < r) (hρp : 0 < ρp ∧ ρp < rp) (hρq : 0 < ρq ∧ ρq < rq)
    (hσ : 0 < σ ∧ σ < S) (houter : r - ρ < r₀ ∧ rp - ρp < rp₀ ∧ rq - ρq < rq₀ ∧ S - σ < S₀) :
    let W := (1 / exp 1) * (ρ / (r₀ - r + ρ) + σ / (S₀ - S + σ)) +
      m * (ρq / (rq₀ - rq + ρq) + ρp / (rp₀ - rp + ρp))
    oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket u w) ∧
    oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket u w)
      (W / min (ρ * σ) (ρp * ρq) * A * B) := by
  intro W
  refine ⟨?_, bracket_bound hu hw hA hB hρ hρp hρq hσ houter⟩
  obtain ⟨hρ0, hρr⟩ := hρ
  obtain ⟨hρp0, hρpr⟩ := hρp
  obtain ⟨hρq0, hρqr⟩ := hρq
  obtain ⟨hσ0, hσS⟩ := hσ
  obtain ⟨hr₀, hrp₀, hrq₀, hS₀⟩ := houter
  have hu' : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) u :=
    hu.mono hr₀.le hrp₀.le hrq₀.le hS₀.le
  have hw' : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) w :=
    hw.mono (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨KAM.Canonical.differentiableOn_poissonBracket (isOpen_oscDom D _ _ _ _) hu'.1 hw'.1,
    fun j z hz => ?_⟩
  have pu : ∀ a, fderiv ℂ u (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) a = fderiv ℂ u z a :=
    fun a => (hu'.fderiv_apply a).2 j z hz
  have pw : ∀ a, fderiv ℂ w (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) a = fderiv ℂ w z a :=
    fun a => (hw'.fderiv_apply a).2 j z hz
  simp only [poissonBracket, pu, pw]

end OscBracket

end KAM.Planetary

end
