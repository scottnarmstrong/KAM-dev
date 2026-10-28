/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Planetary.Exponential.LocalComplexification
public import KAM.Planetary.PGAssembly.RealSlice
public import KAM.Planetary.PGAssembly.ExtensionTubeP

/-!
# P14 package E6: the complex tube of a real-analytic periodic function

* `real_trace_identity`: two holomorphic functions on the intersection of two real-centered complex
  balls which agree on the real points of the intersection agree on the intersection (the real-slice
  identity theorem on `ℝ^(d+d)`, transported by the isometric packing `e5Pack`).
* `tube`: a real-analytic function on an open set `W` of `Phase (n+n)` that is periodic under the
  fast lattice shifts has a holomorphic, shift-periodic extension to a thin complex tube around the
  periodic orbit set of a compact `K ⊆ W` (local complexifications, a finite subcover for the
  uniform radius, and gluing by `real_trace_identity`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

theorem e5Pack_unpack (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} (v : Fin (d + d) → 𝕜) :
    e5Pack 𝕜 d (e5Unpack 𝕜 d v) = v := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [e5Unpack, e5Pack_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.append_left,
      Fin.append_right]

theorem norm_realInclusion_sub_le (m : ℕ) (a : Fin m → ℝ) (v : Fin m → ℂ) :
    ‖KAM.realInclusion m (KAM.realPartCLM m v) - KAM.realInclusion m a‖ ≤
      ‖v - KAM.realInclusion m a‖ := by
  rw [← map_sub, KAM.norm_realInclusion]
  have := KAM.norm_realPartCLM_le (v - KAM.realInclusion m a)
  rwa [map_sub, KAM.realPartCLM_realInclusion] at this

/-- Real-centered polydisc intersection instance needed by tube gluing. -/
theorem real_trace_identity {d : ℕ} (x y : Phase d) (r s : ℝ)
    {f g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ}
    (hf : DifferentiableOn ℂ f
      (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s))
    (hg : DifferentiableOn ℂ g
      (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s))
    (heq : ∀ w : Phase d, KAM.Nekhoroshev.complexifyPhase w ∈
      Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
        Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s →
      f (KAM.Nekhoroshev.complexifyPhase w) = g (KAM.Nekhoroshev.complexifyPhase w)) :
    Set.EqOn f g (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
      Metric.ball (KAM.Nekhoroshev.complexifyPhase y) s) := by
  set U := ball (KAM.Nekhoroshev.complexifyPhase x) r ∩
    ball (KAM.Nekhoroshev.complexifyPhase y) s with hU
  set U' := ball (KAM.realInclusion (d + d) (e5Pack ℝ d x)) r ∩
    ball (KAM.realInclusion (d + d) (e5Pack ℝ d y)) s with hU'
  have hmem : ∀ z, e5Pack ℂ d z ∈ U' ↔ z ∈ U := by
    intro z
    simp only [hU, hU', mem_inter_iff, mem_ball, dist_eq_norm, ← e5Pack_complexify, ← map_sub,
      norm_e5Pack]
  have hmem' : ∀ v, v ∈ U' → e5Unpack ℂ d v ∈ U := fun v hv =>
    (hmem _).1 (by rw [e5Pack_unpack]; exact hv)
  have hU'o : IsOpen U' := isOpen_ball.inter isOpen_ball
  have hU'c : IsPreconnected U' := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hf' : DifferentiableOn ℂ (fun v => f (e5Unpack ℂ d v)) U' :=
    hf.comp (e5Unpack ℂ d).differentiableOn fun v hv => hmem' v hv
  have hg' : DifferentiableOn ℂ (fun v => g (e5Unpack ℂ d v)) U' :=
    hg.comp (e5Unpack ℂ d).differentiableOn fun v hv => hmem' v hv
  intro z hz
  have hzU' : e5Pack ℂ d z ∈ U' := (hmem z).2 hz
  have key := real_slice_identity hU'o hU'c hf' hg'
    (V := {u : Fin (d + d) → ℝ | KAM.realInclusion (d + d) u ∈ U'})
    (hU'o.preimage (KAM.realInclusion (d + d)).continuous)
    ⟨KAM.realPartCLM (d + d) (e5Pack ℂ d z), by
      obtain ⟨h1, h2⟩ := hzU'
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm] at h1 ⊢
        exact (norm_realInclusion_sub_le _ _ _).trans_lt h1
      · rw [mem_ball, dist_eq_norm] at h2 ⊢
        exact (norm_realInclusion_sub_le _ _ _).trans_lt h2⟩
    (by rintro _ ⟨u, hu, rfl⟩; exact hu)
    (by
      intro u hu
      have h1 : KAM.realInclusion (d + d) u =
          e5Pack ℂ d (KAM.Nekhoroshev.complexifyPhase (e5Unpack ℝ d u)) := by
        rw [e5Pack_complexify, e5Pack_unpack]
      have h2 : KAM.Nekhoroshev.complexifyPhase (e5Unpack ℝ d u) ∈ U := (hmem _).1 (h1 ▸ hu)
      have := heq _ h2
      simpa only [h1, e5Unpack_pack] using this)
  have := key hzU'
  simpa only [e5Unpack_pack] using this

theorem complexifyPhase_add {d : ℕ} (a b : Phase d) :
    KAM.Nekhoroshev.complexifyPhase (a + b) =
      KAM.Nekhoroshev.complexifyPhase a + KAM.Nekhoroshev.complexifyPhase b := by
  refine Prod.ext ?_ ?_ <;> (ext i; simp [KAM.Nekhoroshev.complexifyPhase])

theorem complexifyPhase_sub {d : ℕ} (a b : Phase d) :
    KAM.Nekhoroshev.complexifyPhase (a - b) =
      KAM.Nekhoroshev.complexifyPhase a - KAM.Nekhoroshev.complexifyPhase b := by
  refine Prod.ext ?_ ?_ <;> (ext i; simp [KAM.Nekhoroshev.complexifyPhase])

theorem norm_complexifyPhase {d : ℕ} (a : Phase d) :
    ‖KAM.Nekhoroshev.complexifyPhase a‖ = ‖a‖ := KAM.norm_realInclusion₂ a

/-- Gluing local holomorphic branches that agree on real points of overlaps. -/
theorem exists_glue {ι : Type*} {d : ℕ} (C : ι → Phase d) (R : ι → ℝ)
    (G : ι → ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i)
      (ball (KAM.Nekhoroshev.complexifyPhase (C i)) (R i)))
    (hag : ∀ i j (w : Phase d), KAM.Nekhoroshev.complexifyPhase w ∈
      ball (KAM.Nekhoroshev.complexifyPhase (C i)) (R i) ∩
        ball (KAM.Nekhoroshev.complexifyPhase (C j)) (R j) →
      G i (KAM.Nekhoroshev.complexifyPhase w) = G j (KAM.Nekhoroshev.complexifyPhase w)) :
    ∃ F : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ, ∀ i,
      EqOn F (G i) (ball (KAM.Nekhoroshev.complexifyPhase (C i)) (R i)) := by
  classical
  refine ⟨fun z => if h : ∃ i, z ∈ ball (KAM.Nekhoroshev.complexifyPhase (C i)) (R i)
    then G h.choose z else 0, fun i z hz => ?_⟩
  have h : ∃ i, z ∈ ball (KAM.Nekhoroshev.complexifyPhase (C i)) (R i) := ⟨i, hz⟩
  dsimp only
  rw [dif_pos h]
  exact real_trace_identity (C h.choose) (C i) (R h.choose) (R i)
    ((hG _).mono inter_subset_left) ((hG i).mono inter_subset_right)
    (fun w hw => hag _ _ w hw) ⟨h.choose_spec, hz⟩

theorem exists_pos_le_half {ι : Type*} (r : ι → ℝ) (hr : ∀ i, 0 < r i) (t : Finset ι) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i ∈ t, ρ ≤ r i / 2 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s has ih =>
    obtain ⟨ρ, h1, h2⟩ := ih
    refine ⟨min ρ (r a / 2), lt_min h1 (half_pos (hr a)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 i hi)

def periodicOrbitSet (K : Set (Phase (n+n))) : Set (Phase (n+n)) :=
  {w | ∃ k : Fin n → ℤ, ∃ x ∈ K, w = x + fastShift k}
def complexTube (K : Set (Phase (n+n))) (r : ℝ) :
    Set ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) :=
  {z | ∃ x ∈ periodicOrbitSet K, ‖z - KAM.Nekhoroshev.complexifyPhase x‖ < r}

theorem mem_ball_shift {d : ℕ} {z : (Fin d → ℂ) × (Fin d → ℂ)} {x s : Phase d} {r : ℝ} :
    z ∈ ball (KAM.Nekhoroshev.complexifyPhase (x + s)) r ↔
      z - KAM.Nekhoroshev.complexifyPhase s ∈ ball (KAM.Nekhoroshev.complexifyPhase x) r := by
  simp only [mem_ball, dist_eq_norm, complexifyPhase_add]
  rw [show z - KAM.Nekhoroshev.complexifyPhase s - KAM.Nekhoroshev.complexifyPhase x =
    z - (KAM.Nekhoroshev.complexifyPhase x + KAM.Nekhoroshev.complexifyPhase s) by abel]

theorem tube {W K : Set (Phase (n+n))} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    {f : Phase (n+n) → ℝ} (hf : AnalyticOnNhd ℝ f W)
    (hfp : ∀ k : Fin n → ℤ, ∀ w ∈ W, f (w + fastShift k) = f w) :
    ∃ r : ℝ, 0 < r ∧ ∃ fc : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ,
      DifferentiableOn ℂ fc (complexTube K r) ∧
      (∀ w : Phase (n+n), KAM.Nekhoroshev.complexifyPhase w ∈ complexTube K r →
        w ∈ W ∧ fc (KAM.Nekhoroshev.complexifyPhase w) = (f w : ℂ)) ∧
      ∀ k : Fin n → ℤ, ∀ z ∈ complexTube K r,
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTube K r ∧
        fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z := by
  classical
  have hloc : ∀ x : K, ∃ r : ℝ, 0 < r ∧ ∃ g : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ,
      DifferentiableOn ℂ g (ball (KAM.Nekhoroshev.complexifyPhase (x : Phase (n+n))) r) ∧
      (∀ y : Phase (n+n), ‖y - x‖ < r → g (KAM.Nekhoroshev.complexifyPhase y) = (f y : ℂ)) ∧
      ball (x : Phase (n+n)) r ⊆ W := by
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
  set c : Phase (n + n) → (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) :=
    KAM.Nekhoroshev.complexifyPhase with hc
  have e : ∀ a b : Phase (n + n), c (a + b) = c a + c b := complexifyPhase_add
  -- branches
  let C : K × (Fin n → ℤ) → Phase (n+n) := fun p => (p.1 : Phase (n+n)) + fastShift p.2
  let R : K × (Fin n → ℤ) → ℝ := fun p => r p.1
  let G : K × (Fin n → ℤ) → ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ :=
    fun p z => g p.1 (z - c (fastShift p.2))
  have hGd : ∀ p, DifferentiableOn ℂ (G p) (ball (c (C p)) (R p)) := fun p =>
    (hg p.1).comp (differentiableOn_id.sub_const _) fun z hz => mem_ball_shift.1 hz
  have hGval : ∀ p (w : Phase (n+n)), c w ∈ ball (c (C p)) (R p) →
      w ∈ W ∧ G p (c w) = (f w : ℂ) := by
    intro p w hw
    have h1 := mem_ball_shift.1 hw
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
  have hcov : ∀ z ∈ complexTube K ρ, ∃ p, z ∈ ball (c (C p)) (R p) := by
    rintro z ⟨x, ⟨k, x0, hx0, rfl⟩, hz⟩
    obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht hx0)
    refine ⟨(i, k), ?_⟩
    rw [mem_ball, dist_eq_norm] at hi ⊢
    have h3 : ‖c (C (i, k)) - c (x0 + fastShift k)‖ = ‖(i : Phase (n+n)) - x0‖ := by
      rw [← complexifyPhase_sub, norm_complexifyPhase]
      congr 1; simp only [C]; abel
    have h4 : ‖(i : Phase (n+n)) - x0‖ = ‖x0 - i‖ := norm_sub_rev _ _
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
    have hmem : z + c (fastShift k) ∈ complexTube K ρ := by
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
      show _ ∈ ball (c ((p.1 : Phase (n+n)) + fastShift (p.2 + k))) (r p.1)
      rw [fastShift_add, ← add_assoc, e, mem_ball, dist_eq_norm,
        show z + c (fastShift k) - (c ((p.1 : Phase (n+n)) + fastShift p.2) + c (fastShift k))
          = z - c (C p) by simp only [C]; abel]
      exact mem_ball_iff_norm.1 hp
    rw [hFG _ hq, hFG p hp]
    show g p.1 (z + c (fastShift k) - c (fastShift (p.2 + k))) =
      g p.1 (z - c (fastShift p.2))
    rw [fastShift_add, e]
    congr 1; abel

end KAM.Planetary

end
