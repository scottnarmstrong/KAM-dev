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

end KAM.Planetary

end
