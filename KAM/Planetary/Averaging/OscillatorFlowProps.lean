/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorFlowMap
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: properties of the oscillator time-one map

Instantiation of `flow_a`–`flow_e` and `symplectic` at the gauge `oscScale` and the domains
`V ⊆ U ⊆ 𝒪` of `osc_iter`. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Props

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ E : ℝ} {φ : CHam (n + m)}

/-- Common hypotheses of the flow package. -/
structure OscFlowHyp (D : Set (Fin n → ℝ)) (r rp rq S ρ ρp ρq σ E : ℝ) (φ : CHam (n + m)) :
    Prop where
  hρ : 0 < ρ
  hρr : ρ < r
  hρp : 0 < ρp
  hρpr : ρp < rp
  hρq : 0 < ρq
  hρqr : ρq < rq
  hσ : 0 < σ
  hσS : σ < S
  cls : oscClass D r rp rq S φ
  bound : oscBound D r rp rq S φ E
  E_nonneg : 0 ≤ E
  small : E / min (ρ * σ) (ρp * ρq) ≤ 1 / 2

/-- The flow domain `𝒪`. -/
abbrev oscO (D : Set (Fin n → ℝ)) (r rp rq S ρ ρp ρq σ : ℝ) : Set (CPhase (n + m)) :=
  oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)

namespace OscFlowHyp

variable (H : OscFlowHyp D r rp rq S ρ ρp ρq σ E φ)

include H

theorem d_pos : 0 < min (ρ * σ) (ρp * ρq) :=
  lt_min (mul_pos H.hρ H.hσ) (mul_pos H.hρp H.hρq)

/-- The gauge. -/
def W : CPhase (n + m) ≃L[ℂ] CPhase (n + m) := oscScale H.hρ H.hρp H.hρq H.hσ

theorem norm_W (x : CPhase (n + m)) : ‖H.W x‖ = oscGauge ρ ρp ρq σ x := norm_oscScale _ _ _ _ x

theorem field_bound : ∀ z ∈ oscO D r rp rq S ρ ρp ρq σ, oscGauge ρ ρp ρq σ (KAM.hamiltonianVectorFieldℂ φ z) ≤
    E / min (ρ * σ) (ρp * ρq) := fun z hz =>
  ob_field H.cls H.bound ⟨H.hρ, H.hρr⟩ ⟨H.hρp, H.hρpr⟩ ⟨H.hρq, H.hρqr⟩ ⟨H.hσ, H.hσS⟩ z hz

theorem smallField : SmallField H.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (KAM.hamiltonianVectorFieldℂ φ)
    (E / min (ρ * σ) (ρp * ρq)) where
  isOpen := isOpen_oscDom _ _ _ _ _
  differentiableOn := differentiableOn_hamField (isOpen_oscDom _ _ _ _ _)
    (H.cls.1.mono (oscDom_mono (by linarith [H.hρ]) (by linarith [H.hρp]) (by linarith [H.hρq])
      (by linarith [H.hσ])))
  eps_nonneg := div_nonneg H.E_nonneg H.d_pos.le
  eps_le := H.small
  bound z hz := by
    rw [H.norm_W]
    exact H.field_bound z hz

theorem half : oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2) (rq - 3 * ρq / 2)
    (S - 3 * σ / 2) ⊆ gaugeInterior H.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2) := by
  intro z hz w hw
  rw [H.norm_W] at hw
  have := oscDom_of_gauge_le H.hρ H.hρp H.hρq H.hσ hz hw
  have e1 : r - 3 * ρ / 2 + ρ * (1 / 2) = r - ρ := by ring
  have e2 : rp - 3 * ρp / 2 + ρp * (1 / 2) = rp - ρp := by ring
  have e3 : rq - 3 * ρq / 2 + ρq * (1 / 2) = rq - ρq := by ring
  have e4 : S - 3 * σ / 2 + σ * (1 / 2) = S - σ := by ring
  rw [e1, e2, e3, e4] at this
  exact this

theorem one : oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) ⊆
    gaugeInterior H.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1 := by
  intro z hz w hw
  rw [H.norm_W] at hw
  have := oscDom_of_gauge_le H.hρ H.hρp H.hρq H.hσ hz hw
  have e1 : r - 2 * ρ + ρ * 1 = r - ρ := by ring
  have e2 : rp - 2 * ρp + ρp * 1 = rp - ρp := by ring
  have e3 : rq - 2 * ρq + ρq * 1 = rq - ρq := by ring
  have e4 : S - 2 * σ + σ * 1 = S - σ := by ring
  rw [e1, e2, e3, e4] at this
  exact this

theorem φ_diff : DifferentiableOn ℂ φ (oscO (m := m) D r rp rq S ρ ρp ρq σ) :=
  H.cls.1.mono (oscDom_mono (by linarith [H.hρ]) (by linarith [H.hρp]) (by linarith [H.hρq])
    (by linarith [H.hσ]))

omit H in
theorem one_mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩

theorem diff_flow : DifferentiableOn ℂ
    (flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1)
    (oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2) (rq - 3 * ρq / 2) (S - 3 * σ / 2)) :=
  ((flow_b H.smallField).2.1 1 one_mem).mono H.half

theorem mapsTo_flow : MapsTo
    (flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1)
    (oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2) (rq - 3 * ρq / 2) (S - 3 * σ / 2))
    (oscO (m := m) D r rp rq S ρ ρp ρq σ) :=
  fun _ hz => (flow_b H.smallField).2.2.1 1 one_mem _ (H.half hz)

theorem inverse_flow : ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
    flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) (-1)
      (flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1 z) = z :=
  fun _ hz => (flow_c H.smallField (H.one hz)).2.1

theorem injOn_flow : InjOn
    (flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1)
    (oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)) := by
  intro z hz z' hz' h
  rw [← H.inverse_flow z hz, ← H.inverse_flow z' hz', h]

theorem lattice_flow : ∀ z ∈ oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
    (rq - 3 * ρq / 2) (S - 3 * σ / 2), ∀ k : Fin n → ℤ,
    flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1
        (z + (Fin.append (fun i => (k i : ℂ)) (0 : Fin m → ℂ), 0)) =
      flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1 z +
        (Fin.append (fun i => (k i : ℂ)) (0 : Fin m → ℂ), 0) := by
  intro z hz k
  have hτΩ := oscDom_shift_image (m := m) (D := D) (r := r - ρ) (rp := rp - ρp) (rq := rq - ρq)
    (S := S - σ) (a := fun i => (k i : ℂ)) (fun i => by simp)
  have hτF : ∀ w ∈ oscO (m := m) D r rp rq S ρ ρp ρq σ,
      KAM.hamiltonianVectorFieldℂ φ (w + fastShift (m := m) (fun i => (k i : ℂ))) =
        KAM.hamiltonianVectorFieldℂ φ w := fun w hw =>
    H.cls.field_periodic (oscDom_mono (by linarith [H.hρ]) (by linarith [H.hρp])
      (by linarith [H.hρq]) (by linarith [H.hσ])) k hw
  exact (flow_d H.smallField hτΩ hτF).2 z (H.half hz) 1 one_mem

theorem gauge_disp : ∀ z ∈ oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
    (rq - 3 * ρq / 2) (S - 3 * σ / 2),
    oscGauge ρ ρp ρq σ (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1 z - z) ≤ E / min (ρ * σ) (ρp * ρq) := by
  intro z hz
  have := (flow_a H.smallField (H.half hz)).2.2.2 1 one_mem
  rwa [H.norm_W, abs_one, one_mul] at this

theorem gauge_fderiv : ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
    ∀ v, oscGauge ρ ρp ρq σ (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1) z v - v) ≤
      2 * (E / min (ρ * σ) (ρp * ρq)) * oscGauge ρ ρp ρq σ v := by
  intro z hz v
  have := (flow_c H.smallField (H.one hz)).2.2.2.2 1 one_mem v
  rwa [H.norm_W, H.norm_W] at this

theorem symplectic_flow : ∀ z ∈ oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
    (rq - 3 * ρq / 2) (S - 3 * σ / 2), ∀ u v,
    symplFormC (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1) z u)
      (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1) z v) = symplFormC u v := by
  intro z hz u v
  exact (symplectic H.φ_diff H.smallField (H.half hz) (t := 1) one_mem _ rfl).1 u v

theorem real_flow (hφr : RealOn (oscDom (m := m) D r rp rq S) φ) :
    ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈
      oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2) (rq - 3 * ρq / 2) (S - 3 * σ / 2) →
      flow (KAM.hamiltonianVectorFieldℂ φ) (oscO (m := m) D r rp rq S ρ ρp ρq σ) 1
        (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m)) := by
  intro x hx
  have hreal : ∀ w ∈ oscO (m := m) D r rp rq S ρ ρp ρq σ, w ∈ range (KAM.realInclusion₂ (n + m)) →
      KAM.hamiltonianVectorFieldℂ φ w ∈ range (KAM.realInclusion₂ (n + m)) := by
    rintro w hw ⟨y, rfl⟩
    obtain ⟨⟨-, h2⟩, -⟩ := KAM.hamiltonian_real (isOpen_oscDom (m := m) D r rp rq S)
      H.cls.1 (fun y hy => hφr y hy) (z := y)
      (oscDom_mono (by linarith [H.hρ]) (by linarith [H.hρp]) (by linarith [H.hρq])
        (by linarith [H.hσ]) hw)
      (H := fun y' => (φ (KAM.realInclusion₂ (n + m) y')).re) (Filter.Eventually.of_forall fun _ => rfl)
    exact ⟨_, h2⟩
  exact flow_e H.smallField hreal _ (H.half hx) ⟨x, rfl⟩ 1 one_mem

end OscFlowHyp

end Props

end KAM.Planetary

end
