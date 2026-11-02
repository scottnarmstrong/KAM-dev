/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Exponential.ComplexTube

/-!
# The complex tube for unequal fast/slow blocks

Source: track LP, non-frozen (amendment N12). Re-types track P's `tube`
(`KAM/Planetary/Exponential/ComplexTube.lean`, `Phase (n + n)`) to `Phase (n + m)`, as needed for
the spatial chart with `n` fast and `m` slow pairs. The generic tools (`fastShift`,
`real_trace_identity`, `exists_glue`, `local_analytic_complexification`) are reused unchanged.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n m : ℕ}

/-- The periodic orbit set of `K` under the fast lattice shifts, on `Phase (n + m)`. -/
def periodicOrbitSetNM (K : Set (Phase (n+m))) : Set (Phase (n+m)) :=
  {w | ∃ k : Fin n → ℤ, ∃ x ∈ K, w = x + fastShift k}
/-- The complex tube of radius `r` around the periodic orbit set of `K`, on `Phase (n + m)`. -/
def complexTubeNM (K : Set (Phase (n+m))) (r : ℝ) :
    Set ((Fin (n+m) → ℂ) × (Fin (n+m) → ℂ)) :=
  {z | ∃ x ∈ periodicOrbitSetNM K, ‖z - KAM.Nekhoroshev.complexifyPhase x‖ < r}

/-- Track P's `mem_ball_shift` is dimension-generic. -/
theorem mem_ball_shiftNM {d : ℕ} {z : (Fin d → ℂ) × (Fin d → ℂ)} {x s : Phase d} {r : ℝ} :
    z ∈ ball (KAM.Nekhoroshev.complexifyPhase (x + s)) r ↔
      z - KAM.Nekhoroshev.complexifyPhase s ∈ ball (KAM.Nekhoroshev.complexifyPhase x) r :=
  mem_ball_shift

/-- (LP:MAIN, amendment N12) Track P's `tube`, re-typed from `Phase (n + n)` to `Phase (n + m)`. -/
theorem tubeNM {W K : Set (Phase (n+m))} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    {f : Phase (n+m) → ℝ} (hf : AnalyticOnNhd ℝ f W)
    (hfp : ∀ k : Fin n → ℤ, ∀ w ∈ W, f (w + fastShift k) = f w) :
    ∃ r : ℝ, 0 < r ∧ ∃ fc : ((Fin (n+m) → ℂ) × (Fin (n+m) → ℂ)) → ℂ,
      DifferentiableOn ℂ fc (complexTubeNM K r) ∧
      (∀ w : Phase (n+m), KAM.Nekhoroshev.complexifyPhase w ∈ complexTubeNM K r →
        w ∈ W ∧ fc (KAM.Nekhoroshev.complexifyPhase w) = (f w : ℂ)) ∧
      ∀ k : Fin n → ℤ, ∀ z ∈ complexTubeNM K r,
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTubeNM K r ∧
        fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z := by
  classical
  have hloc : ∀ x : K, ∃ r : ℝ, 0 < r ∧ ∃ g : ((Fin (n+m) → ℂ) × (Fin (n+m) → ℂ)) → ℂ,
      DifferentiableOn ℂ g (ball (KAM.Nekhoroshev.complexifyPhase (x : Phase (n+m))) r) ∧
      (∀ y : Phase (n+m), ‖y - x‖ < r → g (KAM.Nekhoroshev.complexifyPhase y) = (f y : ℂ)) ∧
      ball (x : Phase (n+m)) r ⊆ W := by
    rintro ⟨x, hx⟩
    obtain ⟨r0, hr0, g, hg, hgr⟩ := local_analytic_complexification (hf x (hKW hx))
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x (hKW hx)
    exact ⟨min r0 ε, lt_min hr0 hε, g, hg.mono (ball_subset_ball (min_le_left _ _)),
      fun y hy => hgr y (hy.trans_le (min_le_left _ _)),
      (ball_subset_ball (min_le_right _ _)).trans hεW⟩
  choose r hr g hg hgr hrW using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => ball x (r ⟨x, hx⟩ / 2))
    (fun x hx => ball_mem_nhds _ (half_pos (hr _)))
  obtain ⟨ρ, hρ, hρt⟩ := exists_pos_le_half r hr t
  set c : Phase (n + m) → (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ) :=
    KAM.Nekhoroshev.complexifyPhase with hc
  have e : ∀ a b : Phase (n + m), c (a + b) = c a + c b := complexifyPhase_add
  -- branches
  let C : K × (Fin n → ℤ) → Phase (n+m) := fun p => (p.1 : Phase (n+m)) + fastShift p.2
  let R : K × (Fin n → ℤ) → ℝ := fun p => r p.1
  let G : K × (Fin n → ℤ) → ((Fin (n+m) → ℂ) × (Fin (n+m) → ℂ)) → ℂ :=
    fun p z => g p.1 (z - c (fastShift p.2))
  have hGd : ∀ p, DifferentiableOn ℂ (G p) (ball (c (C p)) (R p)) := fun p =>
    (hg p.1).comp (differentiableOn_id.sub_const _) fun z hz => mem_ball_shiftNM.1 hz
  have hGval : ∀ p (w : Phase (n+m)), c w ∈ ball (c (C p)) (R p) →
      w ∈ W ∧ G p (c w) = (f w : ℂ) := by
    intro p w hw
    have h1 := mem_ball_shiftNM.1 hw
    rw [← complexifyPhase_sub, mem_ball, dist_eq_norm, ← complexifyPhase_sub,
      norm_complexifyPhase] at h1
    have h2 : w - fastShift p.2 ∈ W := hrW p.1 (by rw [mem_ball, dist_eq_norm]; exact h1)
    have hwW : w ∈ W := by
      have := (hWp p.2 _).1 h2
      rwa [sub_add_cancel] at this
    refine ⟨hwW, ?_⟩
    show g p.1 (c w - c (fastShift p.2)) = _
    rw [← complexifyPhase_sub, hgr p.1 _ h1]
    have := hfp p.2 _ h2
    rw [sub_add_cancel] at this
    rw [this]
  obtain ⟨F, hF⟩ := exists_glue C R G hGd (fun p q w hw =>
    (hGval p w hw.1).2.trans (hGval q w hw.2).2.symm)
  have hcov : ∀ z ∈ complexTubeNM K ρ, ∃ p, z ∈ ball (c (C p)) (R p) := by
    rintro z ⟨x, ⟨k, x0, hx0, rfl⟩, hz⟩
    obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht hx0)
    refine ⟨(i, k), ?_⟩
    rw [mem_ball, dist_eq_norm] at hi ⊢
    have h3 : ‖c (C (i, k)) - c (x0 + fastShift k)‖ = ‖(i : Phase (n+m)) - x0‖ := by
      rw [← complexifyPhase_sub, norm_complexifyPhase]
      congr 1; simp only [C]; abel
    have h4 : ‖(i : Phase (n+m)) - x0‖ = ‖x0 - i‖ := norm_sub_rev _ _
    have h5 : ‖z - c (C (i, k))‖ ≤ ‖z - c (x0 + fastShift k)‖ +
        ‖c (C (i, k)) - c (x0 + fastShift k)‖ := by
      calc _ = ‖(z - c (x0 + fastShift k)) - (c (C (i, k)) - c (x0 + fastShift k))‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have := hρt i hit
    show ‖z - c (C (i, k))‖ < r i
    linarith
  have hFG : ∀ p, EqOn F (G p) (ball (c (C p)) (R p)) := hF
  refine ⟨ρ, hρ, F, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp⟩ := hcov z hz
    exact (((hGd p).congr fun x hx => hFG p hx).differentiableAt
      (isOpen_ball.mem_nhds hp)).differentiableWithinAt
  · intro w hw
    obtain ⟨p, hp⟩ := hcov _ hw
    obtain ⟨hwW, hv⟩ := hGval p w hp
    exact ⟨hwW, (hFG p hp).trans hv⟩
  · intro k z hz
    have hmem : z + c (fastShift k) ∈ complexTubeNM K ρ := by
      obtain ⟨x, ⟨k', x0, hx0, rfl⟩, hzx⟩ := hz
      refine ⟨x0 + fastShift k' + fastShift k, ⟨k' + k, x0, hx0, ?_⟩, ?_⟩
      · rw [fastShift_add]; abel
      · have h1 : z + c (fastShift k) - c (x0 + fastShift k' + fastShift k) =
            z - c (x0 + fastShift k') := by rw [e]; abel
        show ‖z + c (fastShift k) - c (x0 + fastShift k' + fastShift k)‖ < ρ
        rw [h1]; exact hzx
    refine ⟨hmem, ?_⟩
    obtain ⟨p, hp⟩ := hcov z hz
    have hq : z + c (fastShift k) ∈ ball (c (C (p.1, p.2 + k))) (R (p.1, p.2 + k)) := by
      show _ ∈ ball (c ((p.1 : Phase (n+m)) + fastShift (p.2 + k))) (r p.1)
      rw [fastShift_add, ← add_assoc, e, mem_ball, dist_eq_norm,
        show z + c (fastShift k) - (c ((p.1 : Phase (n+m)) + fastShift p.2) + c (fastShift k))
          = z - c (C p) by simp only [C]; abel]
      exact mem_ball_iff_norm.1 hp
    rw [hFG _ hq, hFG p hp]
    show g p.1 (z + c (fastShift k) - c (fastShift (p.2 + k))) =
      g p.1 (z - c (fastShift p.2))
    rw [fastShift_add, e]
    congr 1; abel


theorem isOpen_complexTubeNM (K : Set (Phase (n + m))) (r : ℝ) :
    IsOpen (complexTubeNM K r) := by
  have : complexTubeNM K r = ⋃ x ∈ periodicOrbitSetNM K,
      ball (KAM.Nekhoroshev.complexifyPhase x) r := by
    ext z
    simp [complexTubeNM, mem_ball, dist_eq_norm]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem complexTubeNM_mono (K : Set (Phase (n + m))) {r s : ℝ} (h : r ≤ s) :
    complexTubeNM K r ⊆ complexTubeNM K s := by
  rintro z ⟨x, hx, hz⟩
  exact ⟨x, hx, hz.trans_le h⟩

theorem complexTubeNM_add_fastShift (K : Set (Phase (n + m))) (r : ℝ) (k : Fin n → ℤ)
    (z : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) :
    z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTubeNM K r ↔
      z ∈ complexTubeNM K r := by
  have key : ∀ (k : Fin n → ℤ) (z : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)),
      z ∈ complexTubeNM K r →
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTubeNM K r := by
    rintro k z ⟨x, ⟨k', x0, hx0, rfl⟩, hzx⟩
    refine ⟨x0 + fastShift k' + fastShift k, ⟨k' + k, x0, hx0, ?_⟩, ?_⟩
    · rw [fastShift_add]; abel
    · have h1 : z + KAM.Nekhoroshev.complexifyPhase (fastShift k) -
          KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k' + fastShift k) =
          z - KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k') := by
        rw [complexifyPhase_add]; abel
      rw [h1]; exact hzx
  refine ⟨fun h => ?_, key k z⟩
  have := key (-k) _ h
  have h0 : (fastShift (0 : Fin n → ℤ) : Phase (n + m)) = 0 := by
    refine Prod.ext ?_ rfl
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift]
  have h1 : KAM.Nekhoroshev.complexifyPhase (0 : Phase (n + m)) = 0 := by
    refine Prod.ext ?_ ?_ <;> (ext i; simp [KAM.Nekhoroshev.complexifyPhase])
  rwa [add_assoc, ← complexifyPhase_add, ← fastShift_add, add_neg_cancel, h0, h1,
    add_zero] at this

end KAM.Planetary.Spatial

end
