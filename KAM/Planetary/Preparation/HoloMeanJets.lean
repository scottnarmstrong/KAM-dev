/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloMeanHolo
public import KAM.Planetary.Preparation.HoloMeanSchwarz
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Strip.AnalyticTaylor
public import KAM.Strip.RealRestriction

/-!
# Complex jets from real bounds, in `(J, z)` (P11A-P2e, `stepP:p11:hc-mean`)

`p11_jets_zero_gen`: a holomorphic `G (J, z)` on the product domain `p11MeanDom J₀ r rz` that is
`O(‖z‖ᵏ)` on real points `(ι J, ι₂ z)` for each real `J` has vanishing `z`-jets of order `< k` at
`z = 0` for every complex `J` in the ball and every direction `v` in `B(0, rz)`. Steps: the line
`s ↦ G (ι J, s v)` (`p11_jets_zero_of_real_bound`); the diagonal polynomial `v ↦ D^j G(v, …, v)`
vanishes on real `v` hence on `ℂ`-points (`p11_real_slice_identity`); finally the identity theorem
in `J`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Jets

variable {n : ℕ}

/-- Splitting `ℂ^{n+n} ≅ ℂⁿ × ℂⁿ`. -/
def p11Split (n : ℕ) : P11CVec (n + n) →L[ℂ] P11Phase n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (fun i => w (Fin.castAdd n i), fun i => w (Fin.natAdd n i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem p11Split_apply (w : P11CVec (n + n)) :
    p11Split n w = (fun i => w (Fin.castAdd n i), fun i => w (Fin.natAdd n i)) := rfl

/-- A holomorphic function on `ℂ²ⁿ` vanishing on the real points of a ball vanishes on the ball. -/
theorem p11_phase_real_slice {ρ : ℝ} (hρ : 0 < ρ) {P : P11Phase n → ℂ}
    (hP : Differentiable ℂ P) (hz : ∀ z' : Phase n, ‖z'‖ < ρ → P (KAM.realInclusion₂ n z') = 0) :
    ∀ z : P11Phase n, ‖z‖ < ρ → P z = 0 := by
  have h := p11_real_slice_identity (n := n + n) (x := 0) hρ
    (F := fun w => P (p11Split n w)) (hP.comp (p11Split n).differentiable).differentiableOn
    (fun y hy => by
      have : p11Split n (KAM.realInclusion (n + n) y) = KAM.realInclusion₂ n
          (fun i => y (Fin.castAdd n i), fun i => y (Fin.natAdd n i)) := by
        refine Prod.ext ?_ ?_ <;> funext i <;> simp [p11Split_apply]
      rw [this]
      refine hz _ ?_
      rw [sub_zero] at hy
      rw [Prod.norm_def, max_lt_iff]
      exact ⟨(pi_norm_lt_iff hρ).2 fun i => (norm_le_pi_norm y _).trans_lt hy,
        (pi_norm_lt_iff hρ).2 fun i => (norm_le_pi_norm y _).trans_lt hy⟩)
  intro z hzρ
  have hw : KAM.realInclusion (n + n) 0 = 0 := map_zero _
  have hmem : (Fin.append z.1 z.2 : P11CVec (n + n)) ∈
      Metric.ball (KAM.realInclusion (n + n) (0 : P11Vec (n + n))) ρ := by
    rw [hw, mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at *
    refine (pi_norm_lt_iff hρ).2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using (norm_le_pi_norm z.1 j).trans_lt hzρ.1
    · simpa using (norm_le_pi_norm z.2 j).trans_lt hzρ.2
  have := h _ hmem
  have hs : p11Split n (Fin.append z.1 z.2) = z :=
    Prod.ext (funext fun i => by simp [p11Split_apply]) (funext fun i => by simp [p11Split_apply])
  simpa [hs] using this

/-- The `j`-th jet of `z ↦ G (J, z)` at `0` on a direction `v` is the jet of `G` at `(J, 0)` on
the direction `(0, v)`. -/
theorem p11_jet_slice {G : P11CVec n × P11Phase n → ℂ} {J0 : P11Vec n} {r rz : ℝ}
    (hrz : 0 < rz) (hG : DifferentiableOn ℂ G (p11MeanDom J0 r rz))
    {J : P11CVec n} (hJ : J ∈ Metric.ball (KAM.realInclusion n J0) r) (v : P11Phase n) (j : ℕ) :
    iteratedFDeriv ℂ j (fun z => G (J, z)) 0 (fun _ => v) =
      iteratedFDeriv ℂ j G (J, 0) (fun _ => ((0 : P11CVec n), v)) := by
  have hU := isOpen_p11MeanDom J0 r rz
  have h0 : ((J, (0 : P11Phase n)) : P11CVec n × P11Phase n) ∈ p11MeanDom J0 r rz :=
    ⟨by simpa using mem_ball_iff_norm.1 hJ, by simpa using hrz⟩
  have h1 := iteratedDeriv_line_eq_iteratedFDeriv hU hG h0 ((0 : P11CVec n), v) j
  have hJ' : ∀ z ∈ Metric.ball (0 : P11Phase n) rz, (J, z) ∈ p11MeanDom J0 r rz :=
    fun z hz => ⟨by simpa using mem_ball_iff_norm.1 hJ, by simpa using hz⟩
  have hGJ : DifferentiableOn ℂ (fun z => G (J, z)) (Metric.ball 0 rz) :=
    hG.comp ((differentiable_const J).prodMk differentiable_id).differentiableOn hJ'
  have h2 := iteratedDeriv_line_eq_iteratedFDeriv Metric.isOpen_ball hGJ (mem_ball_self hrz) v j
  rw [← h2, ← h1]
  congr 1
  funext s
  simp

/-- Real points: the jets of `z ↦ G (ι J, z)` vanish on directions in the ball, for real `J`. -/
theorem p11_jets_zero_real {G : P11CVec n × P11Phase n → ℂ} {J0 : P11Vec n} {r rz : ℝ}
    (hrz : 0 < rz) (hG : DifferentiableOn ℂ G (p11MeanDom J0 r rz)) {k : ℕ}
    {J : P11Vec n} (hJ : ‖J - J0‖ < r)
    (hreal : ∃ r0 C0 : ℝ, 0 < r0 ∧ ∀ z' : Phase n, ‖z'‖ < r0 →
      ‖G (KAM.realInclusion n J, KAM.realInclusion₂ n z')‖ ≤ C0 * ‖z'‖ ^ k) :
    ∀ j < k, ∀ v ∈ Metric.ball (0 : P11Phase n) rz,
      iteratedFDeriv ℂ j (fun z => G (KAM.realInclusion n J, z)) 0 (fun _ => v) = 0 := by
  obtain ⟨r0, C0, hr0, hb⟩ := hreal
  have hJb : KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n J0) r := by
    rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion]; exact hJ
  intro j hj
  have hGJ : DifferentiableOn ℂ (fun z => G (KAM.realInclusion n J, z)) (Metric.ball 0 rz) :=
    hG.comp ((differentiable_const _).prodMk differentiable_id).differentiableOn
      fun z hz => ⟨by simpa using mem_ball_iff_norm.1 hJb, by simpa using hz⟩
  have hrealdir : ∀ z' : Phase n,
      iteratedFDeriv ℂ j (fun z => G (KAM.realInclusion n J, z)) 0
        (fun _ => KAM.realInclusion₂ n z') = 0 := by
    intro z'
    set R : ℝ := rz / (‖z'‖ + 1) with hR
    have hz1 : 0 < ‖z'‖ + 1 := by positivity
    have hR0 : 0 < R := div_pos hrz hz1
    have hline : ∀ s ∈ ball (0 : ℂ) R,
        s • KAM.realInclusion₂ n z' ∈ Metric.ball (0 : P11Phase n) rz := by
      intro s hs
      rw [mem_ball_zero_iff, norm_smul, KAM.norm_realInclusion₂]
      have := mem_ball_zero_iff.1 hs
      calc ‖s‖ * ‖z'‖ ≤ ‖s‖ * (‖z'‖ + 1) := by gcongr; linarith
        _ < R * (‖z'‖ + 1) := by gcongr
        _ = rz := by rw [hR]; field_simp
    have hg : DifferentiableOn ℂ (fun s : ℂ => G (KAM.realInclusion n J,
        s • KAM.realInclusion₂ n z')) (ball 0 R) :=
      hGJ.comp ((differentiable_id.smul_const _).differentiableOn) hline
    have hδ : 0 < min R (r0 / (‖z'‖ + 1)) := lt_min hR0 (div_pos hr0 hz1)
    have hbd := p11_jets_zero_of_real_bound (C := C0 * ‖z'‖ ^ k) hR0 hg hδ (k := k) (fun t ht => by
      have hts : |t| < r0 / (‖z'‖ + 1) := ht.trans_le (min_le_right _ _)
      have hsm : ‖t • z'‖ < r0 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖z'‖ ≤ |t| * (‖z'‖ + 1) := by gcongr; linarith
          _ < r0 / (‖z'‖ + 1) * (‖z'‖ + 1) := by gcongr
          _ = r0 := by field_simp
      have heq : ((t : ℂ) • KAM.realInclusion₂ n z') = KAM.realInclusion₂ n (t • z') := by
        refine Prod.ext ?_ ?_ <;> funext i <;> simp
      show ‖G (KAM.realInclusion n J, (t : ℂ) • KAM.realInclusion₂ n z')‖ ≤ _
      rw [heq]
      calc _ ≤ C0 * ‖t • z'‖ ^ k := hb _ hsm
        _ = C0 * ‖z'‖ ^ k * |t| ^ k := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow]; ring)
    have h1 := iteratedDeriv_line_eq_iteratedFDeriv Metric.isOpen_ball hGJ (mem_ball_self hrz)
      (KAM.realInclusion₂ n z') j
    simp only [zero_add] at h1
    rw [← h1]
    exact hbd j hj
  intro v hv
  refine p11_phase_real_slice hrz (P := fun z =>
    iteratedFDeriv ℂ j (fun z => G (KAM.realInclusion n J, z)) 0 (fun _ => z)) ?_
    (fun z' _ => hrealdir z') v (mem_ball_zero_iff.1 hv)
  exact ((iteratedFDeriv ℂ j (fun z => G (KAM.realInclusion n J, z)) 0).contDiff
    (n := 1)).differentiable one_ne_zero |>.comp (differentiable_pi.2 fun _ => differentiable_id)

/-- `hc-mean`: complex jets from real bounds. -/
theorem p11_jets_zero_gen {G : P11CVec n × P11Phase n → ℂ} {J0 : P11Vec n} {r rz : ℝ}
    (hr : 0 < r) (hrz : 0 < rz) (hG : DifferentiableOn ℂ G (p11MeanDom J0 r rz)) {k : ℕ}
    (hreal : ∀ J : P11Vec n, ‖J - J0‖ < r → ∃ r0 C0 : ℝ, 0 < r0 ∧ ∀ z' : Phase n, ‖z'‖ < r0 →
      ‖G (KAM.realInclusion n J, KAM.realInclusion₂ n z')‖ ≤ C0 * ‖z'‖ ^ k) :
    ∀ J ∈ Metric.ball (KAM.realInclusion n J0) r, ∀ j < k, ∀ v ∈ Metric.ball (0 : P11Phase n) rz,
      iteratedFDeriv ℂ j (fun z => G (J, z)) 0 (fun _ => v) = 0 := by
  have hU := isOpen_p11MeanDom J0 r rz
  intro J hJ j hj v hv
  rw [p11_jet_slice hrz hG hJ v j]
  have hmem : ∀ J' ∈ Metric.ball (KAM.realInclusion n J0) r,
      ((J', (0 : P11Phase n)) : P11CVec n × P11Phase n) ∈ p11MeanDom J0 r rz :=
    fun J' hJ' => ⟨by simpa using mem_ball_iff_norm.1 hJ', by simpa using hrz⟩
  have hφ : DifferentiableOn ℂ (fun J' : P11CVec n =>
      iteratedFDeriv ℂ j G (J', 0) (fun _ => ((0 : P11CVec n), v)))
      (Metric.ball (KAM.realInclusion n J0) r) := by
    have hD := differentiableOn_iteratedFDeriv_of_isOpen hU hG j
    have hc : DifferentiableOn ℂ (fun J' : P11CVec n => iteratedFDeriv ℂ j G (J', 0))
        (Metric.ball (KAM.realInclusion n J0) r) :=
      hD.comp ((differentiable_id.prodMk (differentiable_const _)).differentiableOn) hmem
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => P11CVec n × P11Phase n) ℂ
      (fun _ => ((0 : P11CVec n), v))).differentiable.comp_differentiableOn hc
  exact p11_real_slice_identity hr hφ (fun y hy => by
    have hyb : KAM.realInclusion n y ∈ Metric.ball (KAM.realInclusion n J0) r := by
      rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion]; exact hy
    have h0 := p11_jets_zero_real hrz hG hy (hreal y hy) j hj v hv
    rw [← p11_jet_slice hrz hG hyb v j]
    exact h0) J hJ

end Jets

end KAM.Planetary

end
