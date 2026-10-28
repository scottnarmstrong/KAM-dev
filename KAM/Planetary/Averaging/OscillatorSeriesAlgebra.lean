/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorClassAlgebra
public import KAM.Planetary.Averaging.OscillatorGen
public import KAM.Weighted.Parametric
public import KAM.Weighted.Projections
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Parts 2-3: scalar algebra of the oscillator class (`stepP:p2:oi-transfer`)

`oscTruncate`, and the scalar multiple, sum, series and truncation-tail estimates for
`oscClass`/`oscBound`, proved at each flat parameter `x ∈ oscParams`, retaining summability in
every bound. The proofs port `Canonical.wbound_add`, `wbound_tsum`, `hasSum_coeff` to an
independent parameter dimension, and reuse `Weighted.projections`/`truncation_tail` on local
parameter balls.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13b.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Filter Finset

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The existing Fourier truncation, pulled back through the existing oscillator packing. -/
def oscTruncate {n m : ℕ} (K : ℝ) (f : CHam (n + m)) : CHam (n + m) :=
  fun z => truncate K (oscFunction f) (oscPack z)

section Flat

variable {n N : ℕ}

private abbrev cube' (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

private theorem continuous_realPt' : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

private theorem coeff_const_mul_flat (c : ℂ) (F : (Fin n → ℂ) × (Fin N → ℂ) → ℂ)
    (I : Fin N → ℂ) (k : Fin n → ℤ) : coeff (fun z => c * F z) I k = c * coeff F I k := by
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  have : ∀ x : Fin n → ℝ, KAM.character (-k) (fun j => (x j : ℂ)) •
      (c * F (fun j => (x j : ℂ), I)) =
      c * (KAM.character (-k) (fun j => (x j : ℂ)) • F (fun j => (x j : ℂ), I)) := by
    intro x
    simp only [smul_eq_mul]
    ring
  simp_rw [this]
  exact MeasureTheory.integral_const_mul c _

private theorem coeff_add_flat {F G : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {I : Fin N → ℂ}
    (hF : Continuous fun x : Fin n → ℝ => F (fun j => (x j : ℂ), I))
    (hG : Continuous fun x : Fin n → ℝ => G (fun j => (x j : ℂ), I)) (k : Fin n → ℤ) :
    coeff (fun z => F z + G z) I k = coeff F I k + coeff G I k := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt'
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  simp only [smul_add]
  exact integral_add (KAM.integrableOn_unitCube_of_continuous (hchar.smul hF))
    (KAM.integrableOn_unitCube_of_continuous (hchar.smul hG))

private theorem hasSum_coeff_flat {s : ℝ} {g : ℕ → (Fin n → ℂ) × (Fin N → ℂ) → ℂ}
    {T : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {b : ℕ → ℝ} {I : Fin N → ℂ}
    (hcont : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun l => (x l : ℂ), I))
    (hbd : ∀ j, ∀ x : Fin n → ℝ, ‖g j (fun l => (x l : ℂ), I)‖ ≤ b j) (hb : Summable b)
    (hT : ∀ x : Fin n → ℝ, HasSum (fun j => g j (fun l => (x l : ℂ), I))
      (T (fun l => (x l : ℂ), I))) (k : Fin n → ℤ) :
    HasSum (fun j => coeff (g j) I k) (coeff T I k) := by
  have _ : s = s := rfl
  have : IsFiniteMeasure (volume.restrict (cube' n)) :=
    ⟨by rw [Measure.restrict_apply_univ, KAM.volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt'
  exact hasSum_integral_of_dominated_convergence (μ := volume.restrict (cube' n))
    (F := fun j x => KAM.character (-k) (fun l => (x l : ℂ)) • g j (fun l => (x l : ℂ), I))
    (f := fun x => KAM.character (-k) (fun l => (x l : ℂ)) • T (fun l => (x l : ℂ), I))
    (fun j _ => b j)
    (fun j => (hchar.smul (hcont j)).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun x => by
      rw [norm_smul, KAM.norm_character_real, one_mul]
      exact hbd j x)
    (Filter.Eventually.of_forall fun _ => hb)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x => (hT x).const_smul _)

/-- The weighted bound from the bounds of all finite partial sums of the coefficient series. -/
private theorem wsummable_of_finset_le {u : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {s B : ℝ}
    {I : Fin N → ℂ} (h : ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff u I k‖ * modeWeight s k ≤ B) :
    WSummable u s I ∧ wsum u s I ≤ B :=
  have hnn : 0 ≤ fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k := fun _ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsum : WSummable u s I := summable_of_sum_le hnn h
  ⟨hsum, hsum.tsum_le_of_sum_le h⟩

end Flat

section OscSeriesAlgebra

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S A B : ℝ}

private theorem osc_cont {u : CHam (n + m)} (hS : 0 < S) (hu : oscClass D r rp rq S u)
    {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D r rp rq) :
    Continuous fun θ : Fin n → ℝ => oscFunction u (fun j => (θ j : ℂ), x) :=
  (oscClass.flat hu).1.continuousOn.comp_continuous
    (continuous_realPt'.prodMk continuous_const)
    fun θ => ⟨KAM.ofReal_mem_complexStrip hS θ, hx⟩

private theorem osc_norm_real {u : CHam (n + m)} {M : ℝ} (hS : 0 < S)
    (hu : oscClass D r rp rq S u) (hb : oscBound D r rp rq S u M)
    {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D r rp rq) (θ : Fin n → ℝ) :
    ‖oscFunction u (fun j => (θ j : ℂ), x)‖ ≤ M := by
  have := oscBound.norm_le hu hb (oscUnpack (fun j => (θ j : ℂ), x))
    (oscUnpack_mem_oscDom.2 ⟨KAM.ofReal_mem_complexStrip hS θ, hx⟩)
  simpa [oscFunction] using this

theorem osc_bound_const_mul (c : ℂ) {u : CHam (n + m)}
    (hu : oscBound D r rp rq S u A) :
    oscBound D r rp rq S (fun z => c * u z) (‖c‖ * A) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hu x hx
  have e : oscFunction (fun z => c * u z) = fun y => c * oscFunction u y := rfl
  have hw : wsum (oscFunction fun z => c * u z) S x = ‖c‖ * wsum (oscFunction u) S x := by
    unfold wsum
    simp_rw [e, coeff_const_mul_flat, norm_mul, mul_assoc]
    exact tsum_mul_left
  refine ⟨?_, ?_⟩
  · unfold WSummable at h1 ⊢
    simp_rw [e, coeff_const_mul_flat, norm_mul, mul_assoc]
    exact h1.mul_left _
  · rw [hw]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem osc_bound_add (hS : 0 < S) {u v : CHam (n + m)}
    (hu : oscClass D r rp rq S u) (hv : oscClass D r rp rq S v)
    (hA : oscBound D r rp rq S u A) (hB : oscBound D r rp rq S v B) :
    oscBound D r rp rq S (fun z => u z + v z) (A + B) := by
  intro x hx
  obtain ⟨hu1, hu2⟩ := hA x hx
  obtain ⟨hv1, hv2⟩ := hB x hx
  have hw : ∀ k : Fin n → ℤ, 0 ≤ modeWeight S k := fun k => (Real.exp_pos _).le
  have e : oscFunction (fun z => u z + v z) = fun y => oscFunction u y + oscFunction v y := rfl
  have hc : ∀ k, coeff (oscFunction fun z => u z + v z) x k =
      coeff (oscFunction u) x k + coeff (oscFunction v) x k := fun k => by
    rw [e]; exact coeff_add_flat (osc_cont hS hu hx) (osc_cont hS hv hx) k
  have hle : ∀ k, ‖coeff (oscFunction fun z => u z + v z) x k‖ * modeWeight S k ≤
      ‖coeff (oscFunction u) x k‖ * modeWeight S k +
        ‖coeff (oscFunction v) x k‖ * modeWeight S k := fun k => by
    rw [hc k, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hw k)
  have hsum : WSummable (oscFunction fun z => u z + v z) S x :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (hw k)) hle (hu1.add hv1)
  refine ⟨hsum, ?_⟩
  calc wsum (oscFunction fun z => u z + v z) S x
      ≤ ∑' k, (‖coeff (oscFunction u) x k‖ * modeWeight S k +
          ‖coeff (oscFunction v) x k‖ * modeWeight S k) :=
        Summable.tsum_le_tsum hle hsum (hu1.add hv1)
    _ = wsum (oscFunction u) S x + wsum (oscFunction v) S x := hu1.tsum_add hv1
    _ ≤ A + B := add_le_add hu2 hv2

private theorem oscBound.mono_E {u : CHam (n + m)} {E E' : ℝ}
    (hb : oscBound D r rp rq S u E) (h : E ≤ E') : oscBound D r rp rq S u E' :=
  fun x hx => ⟨(hb x hx).1, (hb x hx).2.trans h⟩

private theorem osc_tsum_class_bound (hS : 0 < S) {v : ℕ → CHam (n + m)} {b : ℕ → ℝ}
    (hv : ∀ j, oscClass D r rp rq S (v j))
    (hb : ∀ j, oscBound D r rp rq S (v j) (b j)) (hs : Summable b) :
    oscClass D r rp rq S (fun z => ∑' j, v j z) ∧
    oscBound D r rp rq S (fun z => ∑' j, v j z) (∑' j, b j) := by
  have hbd : ∀ j, ∀ z ∈ oscDom (m := m) D r rp rq S, ‖v j z‖ ≤ b j := fun j =>
    oscBound.norm_le (hv j) (hb j)
  have hT : ∀ z ∈ oscDom (m := m) D r rp rq S,
      HasSum (fun j => v j z) (∑' j, v j z) := fun z hz =>
    (Summable.of_norm_bounded hs fun j => hbd j z hz).hasSum
  refine ⟨⟨?_, fun j z hz => ?_⟩, ?_⟩
  · have hK : ∀ N : ℕ, DifferentiableOn ℂ (fun z => ∑ j ∈ Finset.range N, v j z)
        (oscDom (m := m) D r rp rq S) := fun N =>
      DifferentiableOn.fun_sum fun j _ => (hv j).1
    have hconv : TendstoUniformlyOn (fun (N : ℕ) z => ∑ j ∈ Finset.range N, v j z)
        (fun z => ∑' j, v j z) atTop (oscDom (m := m) D r rp rq S) :=
      tendstoUniformlyOn_tsum_nat hs hbd
    exact (uniform_limit_holomorphic (isOpen_oscDom D r rp rq S) hK hconv).1
  · simp only [(hv _).2 _ z hz]
  · intro x hx
    refine wsummable_of_finset_le fun Λ => ?_
    have hw : ∀ k : Fin n → ℤ, 0 < modeWeight S k := fun k => Real.exp_pos _
    have hcont := fun j => osc_cont hS (hv j) hx
    have hsumk : ∀ k, Summable fun j => ‖coeff (oscFunction (v j)) x k‖ := fun k => by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
        (hs.mul_right (modeWeight S k)⁻¹)
      have h1 := (hb j x hx).1.le_tsum k (fun _ _ => mul_nonneg (norm_nonneg _) (hw _).le)
      have h2 := h1.trans (hb j x hx).2
      rw [← div_eq_mul_inv, le_div_iff₀ (hw k)]
      exact h2
    have hnorm : ∀ k, ‖coeff (oscFunction fun z => ∑' j, v j z) x k‖ ≤
        ∑' j, ‖coeff (oscFunction (v j)) x k‖ := fun k => by
      rw [← (hasSum_coeff_flat (s := S) (g := fun j => oscFunction (v j))
        (T := oscFunction fun z => ∑' j, v j z) (b := b) hcont
        (fun j θ => osc_norm_real hS (hv j) (hb j) hx θ) hs
        (fun θ => hT _ (oscUnpack_mem_oscDom.2 ⟨KAM.ofReal_mem_complexStrip hS θ, hx⟩)) k).tsum_eq]
      exact norm_tsum_le_tsum_norm (hsumk k)
    have hterm : ∀ k, Summable fun j => ‖coeff (oscFunction (v j)) x k‖ * modeWeight S k :=
      fun k => (hsumk k).mul_right _
    calc ∑ k ∈ Λ, ‖coeff (oscFunction fun z => ∑' j, v j z) x k‖ * modeWeight S k
        ≤ ∑ k ∈ Λ, (∑' j, ‖coeff (oscFunction (v j)) x k‖) * modeWeight S k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hnorm k) (hw k).le
      _ = ∑ k ∈ Λ, ∑' j, ‖coeff (oscFunction (v j)) x k‖ * modeWeight S k :=
          Finset.sum_congr rfl fun k _ => (tsum_mul_right).symm
      _ = ∑' j, ∑ k ∈ Λ, ‖coeff (oscFunction (v j)) x k‖ * modeWeight S k :=
          (Summable.tsum_finsetSum fun k _ => hterm k).symm
      _ ≤ ∑' j, b j := by
          refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun k _ => hterm k) hs
          exact ((hb j x hx).1.sum_le_tsum Λ
            (fun k _ => mul_nonneg (norm_nonneg _) (hw k).le)).trans (hb j x hx).2

theorem osc_bound_tsum (hS : 0 < S) {v : ℕ → CHam (n + m)} {b : ℕ → ℝ}
    (hv : ∀ j, oscClass D r rp rq S (v j))
    (hb : ∀ j, oscBound D r rp rq S (v j) (b j))
    (hb0 : ∀ j, 0 ≤ b j) (hs : Summable b) :
    oscClass D r rp rq S (fun z => ∑' j, v j z) ∧
    oscBound D r rp rq S (fun z => ∑' j, v j z) (∑' j, b j) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      oscBound D r rp rq S
        (fun z => (∑' j, v j z) - ∑ j ∈ Finset.range N', v j z) ε := by
  obtain ⟨h1, h2⟩ := osc_tsum_class_bound hS hv hb hs
  refine ⟨h1, h2, fun ε hε => ?_⟩
  have htail : Tendsto (fun N' => ∑' j, b (j + N')) atTop (nhds 0) :=
    tendsto_sum_nat_add b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds hε))
  refine ⟨N, fun N' hN' => ?_⟩
  obtain ⟨-, h4⟩ := osc_tsum_class_bound hS (v := fun j => v (j + N')) (b := fun j => b (j + N'))
    (fun j => hv _) (fun j => hb _) ((summable_nat_add_iff N').2 hs)
  refine oscBound.congr hS (fun z hz => ?_) (h4.mono_E (hN N' hN').le)
  have hsm : Summable fun j => v j z :=
    Summable.of_norm_bounded hs fun j => oscBound.norm_le (hv j) (hb j) z hz
  rw [← hsm.sum_add_tsum_nat_add N']
  ring

/-- Truncation uses Weighted.projections/truncation_tail locally on parameter balls. -/
theorem osc_truncation_tail {σ K : ℝ} {f : CHam (n + m)}
    (hf : oscClass D r rp rq S f) (hA : oscBound D r rp rq S f A)
    (hσ : 0 < σ) (hσS : σ < S) (hK : 0 ≤ K) :
    oscClass D r rp rq S (oscTruncate K f) ∧
    oscBound D r rp rq S (oscTruncate K f) A ∧
    oscBound D r rp rq (S - σ) (fun z => f z - oscTruncate K f z)
      (exp (-(2 * π * K * σ)) * A) := by
  have hS : 0 < S := hσ.trans hσS
  have hP := isOpen_oscParams (m := m) D r rp rq
  have hfl := hf.flat
  -- local data at a parameter
  have loc : ∀ x ∈ oscParams (m := m) D r rp rq, ∃ δ : ℝ, 0 < δ ∧
      ball x δ ⊆ oscParams (m := m) D r rp rq ∧
      InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) δ S (oscFunction f) ∧
      WBound ({x} : Set (Fin (n + (m + m)) → ℂ)) δ S (oscFunction f) A := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hP x hx
    refine ⟨δ, hδ, hball, hfl.inClass hball le_rfl, fun I hI => ?_⟩
    rw [polyNbhd_singleton] at hI
    exact hA I (hball hI)
  have hTflat : oscFunction (oscTruncate K f) = truncate K (oscFunction f) := by
    funext y
    simp only [oscFunction, Function.comp, oscTruncate, oscPack_oscUnpack]
  have hTcls : oscClass D r rp rq S (oscTruncate K f) := by
    refine ⟨?_, fun j z hz => ?_⟩
    · have hd : DifferentiableOn ℂ (truncate K (oscFunction f))
          (KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq) := by
        intro y hy
        obtain ⟨δ, hδ, hball, hc, hb⟩ := loc y.2 hy.2
        have hpr := (projections hS hc hb {k | KAM.Fourier.modeSize k ≤ K}).1
        have hmem : y ∈ Dom n ({y.2} : Set (Fin (n + (m + m)) → ℂ)) δ S := by
          refine ⟨hy.1, ?_⟩
          rw [polyNbhd_singleton]; exact mem_ball_self hδ
        have hopen : IsOpen (Dom n ({y.2} : Set (Fin (n + (m + m)) → ℂ)) δ S) := isOpen_Dom _ _ _
        exact (hpr.differentiableOn.differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt
      have h : oscFunction (oscTruncate K f) = truncate K (oscFunction f) := hTflat
      have h2 : oscTruncate K f = (truncate K (oscFunction f)) ∘ oscPackL (m := m) := by
        funext z; rfl
      rw [h2]
      exact hd.comp (oscPackL (m := m)).differentiableOn fun z hz => hz
    · have hz' : oscPack z ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq := hz
      obtain ⟨δ, hδ, hball, hc, hb⟩ := loc (oscPack z).2 hz'.2
      have hpr := (projections hS hc hb {k | KAM.Fourier.modeSize k ≤ K}).1
      have hmem : oscPack z ∈ Dom n ({(oscPack z).2} : Set (Fin (n + (m + m)) → ℂ)) δ S := by
        refine ⟨hz'.1, ?_⟩
        rw [polyNbhd_singleton]; exact mem_ball_self hδ
      have hp := hpr.periodic (j := j) (oscPack z) hmem
      have hshift : oscPack ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) =
          ((oscPack z).1 + Pi.single j 1, (oscPack z).2) := by
        have e : ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) =
            z + (Pi.single (Fin.castAdd m j) 1, 0) := by ext <;> simp
        rw [e]
        have h2 := (oscPackL (m := m)).map_add z (Pi.single (Fin.castAdd m j) 1, 0)
        change oscPack (z + (Pi.single (Fin.castAdd m j) 1, 0)) =
          oscPack z + oscPack (Pi.single (Fin.castAdd m j) 1, 0) at h2
        rw [h2, oscPack_theta]
        ext <;> simp
      show truncate K (oscFunction f)
        (oscPack ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m))) =
          truncate K (oscFunction f) (oscPack z)
      rw [hshift]; exact hp
  refine ⟨hTcls, ?_, ?_⟩
  · intro x hx
    obtain ⟨δ, hδ, hball, hc, hb⟩ := loc x hx
    have hpr := (projections hS hc hb {k | KAM.Fourier.modeSize k ≤ K}).2.2.1
    have hxI : x ∈ polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) δ := by
      rw [polyNbhd_singleton]; exact mem_ball_self hδ
    have hh := hpr x hxI
    rw [hTflat]
    exact hh
  · refine oscBound_of_flat (S := S - σ) (G := fun y => oscFunction f y - truncate K (oscFunction f) y)
      (by linarith) (fun y _ => by simp only [oscFunction, Function.comp, oscTruncate, oscPack_oscUnpack]) ?_
    intro x hx
    obtain ⟨δ, hδ, hball, hc, hb⟩ := loc x hx
    have hxI : x ∈ polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) δ := by
      rw [polyNbhd_singleton]; exact mem_ball_self hδ
    exact (truncation_tail hc hb hσ hσS hK).2 x hxI

end OscSeriesAlgebra

end KAM.Planetary

end
