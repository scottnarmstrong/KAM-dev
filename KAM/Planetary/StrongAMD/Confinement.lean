/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness
public import KAM.Planetary.AMD.Closure
public import KAM.Planetary.AMD.ConfinementExit
public import KAM.Planetary.AMD.MovingODE
public import KAM.Planetary.StrongAMD.Continuation
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.StrongAMD.Modulus
public import KAM.Planetary.StrongAMD.Momentum

/-!
# Sharp first exit (conditional confinement helper)

Package LP-CONF, `LP:MAIN L14 (468–500)` with amendments N2 (one shared compact `U`) and N6
(on the Lemma-13 route the stopped radius is `r` and the improvement is to `r / 2`); track LP,
non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`strongFirstExit_of_stopped_drift` is the topological first-exit argument of MAIN Lemma 14 with
the stopped drift as an **explicit hypothesis** `hstop`.  It is NOT the public theorem: it is the
internal conditional helper, and package LP-PS discharges `hstop` from Lemma 13 (LP-NRR) through
the chart lift (LP-LIFT).

The route: the maximal solution of the moving field on the collision-free domain; a forward and a
backward first exit (`amd_exit_forward`, `amd_exit_backward`) for the open tube set
`firstExitTube` and the improved set `firstExitCore`; inside the tube `hstop` improves the drift to
`r / 2` and (17) with the budget improves the AMD margin to `3 δ / 4`; the improved set consists of
barrier states, so `maximal_global_of_barrier` excludes a finite endpoint; uniqueness is the ODE
uniqueness on the open domain in the frozen `MovingUniqueOn` form.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary KAM.ODE Set Filter Topology

variable {n : ℕ}

/-- The open tube set of the first exit: physical states whose action vector is strictly within `r`
of `I₀` and whose AMD margin is strictly above `δ / 2` (the stopped conditions (40), open form). -/
def firstExitTube (ν : Fin n → ℝ) (I₀ : Fin n → ℝ) (δ r : ℝ) : Set (Phase (n * 2)) :=
  {w | IsPhysicalState ν w ∧ ‖actionVector ν w - I₀‖ < r ∧
    strongAMD ν w < strongThreshold ν (actionVector ν w) - δ / 2}

/-- The improved set of the first exit (`LP:MAIN L14 (485)`, N6): action drift at most `r / 2`
and AMD margin at least `3 δ / 4`. -/
def firstExitCore (ν : Fin n → ℝ) (I₀ : Fin n → ℝ) (δ r : ℝ) : Set (Phase (n * 2)) :=
  {w | IsPhysicalState ν w ∧ ‖actionVector ν w - I₀‖ ≤ r / 2 ∧
    strongAMD ν w ≤ strongThreshold ν (actionVector ν w) - 3 * δ / 4}

theorem firstExitCore_subset_tube {ν : Fin n → ℝ} {I₀ : Fin n → ℝ} {δ r : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) : firstExitCore ν I₀ δ r ⊆ firstExitTube ν I₀ δ r :=
  fun _ h => ⟨h.1, lt_of_le_of_lt h.2.1 (by linarith), by linarith [h.2.2]⟩

/-! ### Continuity on physical states -/

theorem movingSolutionOn_mono {ν : Fin n → ℝ} {μ : ℝ} {J J' : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : IsMovingSolutionOn ν μ J z) (h : J' ⊆ J) : IsMovingSolutionOn ν μ J' z :=
  ⟨fun t ht => hz.1 t (h ht), fun t ht => hz.2 t (h ht)⟩

theorem continuousAt_actionVector {ν : Fin n → ℝ} {z : Phase (n * 2)} (hz : IsPhysicalState ν z) :
    ContinuousAt (actionVector ν) z := by
  obtain ⟨hop, hact, -⟩ := element_continuity ν
  exact continuousAt_pi.2 fun i => (hact i).continuousAt (hop.mem_nhds hz)

theorem continuous_totalMomentum' : Continuous (totalMomentum : Phase (n * 2) → ℝ) := by
  unfold totalMomentum planeCross bodyVector
  fun_prop

theorem continuousAt_strongAMD {ν : Fin n → ℝ} {z : Phase (n * 2)} (hz : IsPhysicalState ν z) :
    ContinuousAt (strongAMD ν) z := by
  obtain ⟨hop, hact, -⟩ := element_continuity ν
  have h1 : ContinuousAt (fun w : Phase (n * 2) => ∑ i, keplerAction ν w i) z :=
    (continuousOn_finsetSum _ fun i _ => hact i).continuousAt (hop.mem_nhds hz)
  exact h1.sub continuous_totalMomentum'.abs.continuousAt

theorem continuousAt_keplerEnergy' (ν : Fin n → ℝ) {z : Phase (n * 2)} (i : Fin n)
    (h : 0 < planeLength (bodyVector z.1 i)) :
    ContinuousAt (fun w : Phase (n * 2) => keplerEnergy ν w i) z := by
  have hq : Continuous fun w : Phase (n * 2) => planeLength (bodyVector w.1 i) :=
    continuous_planeLength'.comp ((continuous_bodyVector' i).comp continuous_fst)
  have hp : Continuous fun w : Phase (n * 2) => planeSq (bodyVector w.2 i) :=
    continuous_finsetSum _ fun k _ =>
      (((continuous_apply k).comp ((continuous_bodyVector' i).comp continuous_snd)).pow 2)
  unfold keplerEnergy
  exact (hp.continuousAt.div_const _).sub (continuousAt_const.div hq.continuousAt h.ne')

/-- The margin function `C - B(Λ)` is continuous at a physical state whose action vector lies in
the chamber. -/
theorem continuousAt_strongGap {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {z : Phase (n * 2)} (hz : IsPhysicalState ν z) (hch : actionVector ν z ∈ chamber ν) :
    ContinuousAt (fun w => strongAMD ν w - strongThreshold ν (actionVector ν w)) z := by
  have hB : ContinuousAt (strongThreshold ν) (actionVector ν z) :=
    (continuousOn_strongThreshold hν hn).continuousAt ((isOpen_chamber ν).mem_nhds hch)
  exact (continuousAt_strongAMD hz).sub (hB.comp (continuousAt_actionVector hz))

/-! ### Openness and closedness -/

theorem isOpen_firstExitTube {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUch : U ⊆ chamber ν) {I₀ : Fin n → ℝ} {δ r : ℝ}
    (hball : ∀ I, ‖I - I₀‖ ≤ r → I ∈ U) : IsOpen (firstExitTube ν I₀ δ r) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hp, hr', hg⟩ := hz
  have hΛ := continuousAt_actionVector hp
  have hch : actionVector ν z ∈ chamber ν := hUch (hball _ hr'.le)
  have hgc := continuousAt_strongGap hν hn hp hch
  have e1 : ∀ᶠ w in 𝓝 z, IsPhysicalState ν w := (element_continuity ν).1.mem_nhds hp
  have e2 : ∀ᶠ w in 𝓝 z, ‖actionVector ν w - I₀‖ < r :=
    (hΛ.sub continuousAt_const).norm.eventually (gt_mem_nhds hr')
  have e3 : ∀ᶠ w in 𝓝 z,
      strongAMD ν w - strongThreshold ν (actionVector ν w) < -(δ / 2) :=
    hgc.eventually (gt_mem_nhds (by linarith))
  filter_upwards [e1, e2, e3] with w h1 h2 h3
  exact ⟨h1, h2, by linarith⟩

/-- Closedness of the improved set among limits with positive radii (the physical-state clause is
recovered from the uniform energy bound of the barrier). -/
theorem firstExitCore_closed {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {I₀ : Fin n → ℝ}
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hball : ∀ I, ‖I - I₀‖ ≤ r → I ∈ U)
    (x : ℕ → Phase (n * 2)) (xs : Phase (n * 2)) (hx : ∀ k, x k ∈ firstExitCore ν I₀ δ r)
    (hl : Tendsto x atTop (𝓝 xs)) (hN : ∀ i, 0 < planeLength (bodyVector xs.1 i)) :
    xs ∈ firstExitCore ν I₀ δ r := by
  obtain ⟨dS, dP, R, P, c, -, -, -, -, hc, -, hbar⟩ :=
    strongBarrier_physical hν hn hUc hUch (half_pos hδ)
  have hb : ∀ k, BarrierState ν U (δ / 2) (x k) := fun k =>
    ⟨(hx k).1, hball _ ((hx k).2.1.trans (by linarith)), by linarith [(hx k).2.2]⟩
  have hE : ∀ i, keplerEnergy ν xs i ≤ -c := fun i => by
    have ht := (continuousAt_keplerEnergy' ν i (hN i)).tendsto.comp hl
    refine le_of_tendsto' ht fun k => ?_
    obtain ⟨-, -, -, -, -, -, hE, -⟩ := hbar (x k) (hb k)
    exact hE i
  have hphys : IsPhysicalState ν xs := fun i => ⟨hN i, by linarith [hE i]⟩
  have hΛt : Tendsto (fun k => actionVector ν (x k)) atTop (𝓝 (actionVector ν xs)) :=
    (continuousAt_actionVector hphys).tendsto.comp hl
  have hdr : ‖actionVector ν xs - I₀‖ ≤ r / 2 :=
    le_of_tendsto' (hΛt.sub_const I₀).norm fun k => (hx k).2.1
  have hch : actionVector ν xs ∈ chamber ν := hUch (hball _ (hdr.trans (by linarith)))
  have hgt := (continuousAt_strongGap hν hn hphys hch).tendsto.comp hl
  refine ⟨hphys, hdr, ?_⟩
  have hle : strongAMD ν xs - strongThreshold ν (actionVector ν xs) ≤ -(3 * δ / 4) :=
    le_of_tendsto' hgt fun k => by
      show strongAMD ν (x k) - strongThreshold ν (actionVector ν (x k)) ≤ -(3 * δ / 4)
      linarith [(hx k).2.2]
  linarith

/-! ### The conditional first-exit helper -/

/-- **Conditional confinement helper (not the public theorem)** (`LP:MAIN L14 (468–500)`, N2, N6):
the topological first-exit argument of MAIN Lemma 14, with the stopped drift as the explicit
hypothesis `hstop` (MAIN's stopped conditions (40) in strict, open form, both the action drift
`< r` and the margin `> δ / 2`, improving the drift to `r / 2`).
Package LP-PS discharges `hstop` from Lemma 13 through the chart lift.

Given the budget `n r + Ω_B(r) ≤ δ / 4` and an initial physical state `z₀` whose closed `r`-action
ball lies in the shared compact `U` and whose strong AMD is `≤ B(Λ z₀) - δ`, there is a moving
solution on `[-T, T]`, unique in the frozen `MovingUniqueOn` sense, that stays physical with drift
`≤ r / 2`, with AMD margin `≥ δ / 2` (MAIN (8)), and in barrier states
`BarrierState ν U (δ / 2)`. -/
theorem strongFirstExit_of_stopped_drift {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {μ δ r T : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hT : 0 < T)
    (hbudget : n * r + strongThresholdModulus ν U r ≤ δ / 4)
    {z₀ : Phase (n * 2)} (hphys₀ : IsPhysicalState ν z₀)
    (hball : ∀ I, ‖I - actionVector ν z₀‖ ≤ r → I ∈ U)
    (hC₀ : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ)
    (hstop : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
      IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J, |t| ≤ T →
        (∀ u ∈ Set.uIcc 0 t, IsPhysicalState ν (z u) ∧
          ‖actionVector ν (z u) - actionVector ν z₀‖ < r ∧
          strongAMD ν (z u) < strongThreshold ν (actionVector ν (z u)) - δ / 2) →
        ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ r / 2) :
    ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Icc (-T) T) z ∧
      MovingUniqueOn ν μ (Icc (-T) T) z ∧
      ∀ t ∈ Icc (-T) T, IsPhysicalState ν (z t) ∧
        ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ r / 2 ∧
        strongAMD ν (z t) ≤ strongThreshold ν (actionVector ν (z t)) - δ / 2 ∧
        BarrierState ν U (δ / 2) (z t) := by
  obtain ⟨hW, hF, hiff⟩ := moving_ode ν μ
  have hU0 : actionVector ν z₀ ∈ U := hball _ (by simpa using hr.le)
  obtain ⟨K, -, hKW, hKs⟩ := exists_barrierCompact hν hn hUc hUch (half_pos hδ)
  have hz₀W : z₀ ∈ collisionFreeDomain n := hKW (hKs z₀ ⟨hphys₀, hU0, by linarith⟩)
  obtain ⟨Tm, Tp, z, hz⟩ := (gen_maximal hW hF hz₀W).1
  have hz' : IsMaximalSolution (movingField ν μ) (collisionFreeDomain n) z₀ Tm Tp z := hz
  have hmovAll : IsMovingSolutionOn ν μ (eIoo Tm Tp) z := (hiff _ z).2 hz.isSolution
  set J : Set ℝ := eIoo Tm Tp ∩ Icc (-T) T with hJdef
  have hJ : J.OrdConnected := (ordConnected_eIoo _ _).inter ordConnected_Icc
  have h0 : (0 : ℝ) ∈ J := ⟨zero_mem_eIoo hz, by constructor <;> linarith⟩
  have hmovJ : IsMovingSolutionOn ν μ J z := movingSolutionOn_mono hmovAll inter_subset_left
  have hcont : ContinuousOn z J := fun t ht => (hmovJ.1 t ht).2.2.continuousAt.continuousWithinAt
  have hN : ∀ t ∈ J, z t ∈ {w : Phase (n * 2) | ∀ i, 0 < planeLength (bodyVector w.1 i)} :=
    fun t ht i => (hmovJ.2 t ht).1 i
  have hVopen := isOpen_firstExitTube hν hn hUch hball (δ := δ) (r := r)
  have hCV := firstExitCore_subset_tube (ν := ν) (I₀ := actionVector ν z₀) hδ hr
  have hy0V : z 0 ∈ firstExitTube ν (actionVector ν z₀) δ r := by
    rw [hz.init]
    exact ⟨hphys₀, by simpa using hr, by linarith⟩
  -- the key local step: if the orbit stayed in the tube up to `s`, it is in the improved set at `s`
  have key : ∀ s ∈ J, (∀ u ∈ Set.uIcc (0 : ℝ) s, z u ∈ firstExitTube ν (actionVector ν z₀) δ r) →
      z s ∈ firstExitCore ν (actionVector ν z₀) δ r := by
    intro s hs hV
    have hdrift := hstop J hJ h0 z hmovJ hz.init s hs (abs_le.2 hs.2) fun u hu =>
      hV u hu
    have h17 := strongAMD_le_of_tube hν hn hUc hUch hJ hmovJ h0 hs (δ := δ) (r := r / 2)
      (by rw [hz.init]; exact hC₀) (by rw [hz.init]; exact hdrift) (by rw [hz.init]; exact hU0)
      (hball _ (hdrift.trans (by linarith)))
    have hmono := strongThresholdModulus_mono hν hn hUc hUch (r := r / 2) (s := r) (by linarith)
    have hnr : (n : ℝ) * (r / 2) ≤ n * r := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    exact ⟨(hV s (by simp)).1, hdrift, by linarith⟩
  have hcl := firstExitCore_closed hν hn hUc hUch hδ hr hball
  have hfwd := amd_exit_forward hJ h0 hcont hVopen hCV hcl hN hy0V (fun s hs hs0 hV => by
    refine key s hs fun u hu => ?_
    rw [Set.uIcc_of_le hs0] at hu
    exact hV u hu.1 hu.2)
  have hbwd := amd_exit_backward hJ h0 hcont hVopen hCV hcl hN hy0V (fun s hs hs0 hV => by
    refine key s hs fun u hu => ?_
    rw [Set.uIcc_of_ge hs0] at hu
    exact hV u hu.1 hu.2)
  have hCall : ∀ t ∈ J, z t ∈ firstExitCore ν (actionVector ν z₀) δ r := fun t ht => by
    rcases le_total 0 t with h | h
    · exact hfwd t ht h
    · exact hbwd t ht h
  have hbar : ∀ t ∈ J, BarrierState ν U (δ / 2) (z t) := fun t ht =>
    ⟨(hCall t ht).1, hball _ ((hCall t ht).2.1.trans (by linarith)),
      by linarith [(hCall t ht).2.2]⟩
  have hglob := maximal_global_of_barrier hν hn hUc hUch (half_pos hδ) hz'
  have hTp : ((T : ℝ) : EReal) < Tp := by
    by_contra hle
    rw [not_lt] at hle
    have hTop := hglob.1 ⟨0, le_rfl, hz.pos_lt, fun t ht0 ht => hbar t
      ⟨⟨lt_of_lt_of_le hz.neg_lt (by exact_mod_cast ht0), ht⟩, by
        have : t ≤ T := EReal.coe_le_coe_iff.1 (ht.le.trans hle)
        constructor <;> linarith⟩⟩
    rw [hTop] at hle
    exact absurd hle (by simp)
  have hTm : Tm < ((-T : ℝ) : EReal) := by
    by_contra hle
    rw [not_lt] at hle
    have hBot := hglob.2 ⟨0, le_rfl, hz.neg_lt, fun t ht ht0 => hbar t
      ⟨⟨ht, lt_of_le_of_lt (by exact_mod_cast ht0) hz.pos_lt⟩, by
        have : -T ≤ t := EReal.coe_le_coe_iff.1 (hle.trans ht.le)
        constructor <;> linarith⟩⟩
    rw [hBot] at hle
    exact absurd hle (by simp)
  have hIcc : Icc (-T) T ⊆ eIoo Tm Tp := fun t ht =>
    ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 ht.1),
      lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ht.2) hTp⟩
  have hIJ : ∀ t ∈ Icc (-T) T, t ∈ J := fun t ht => ⟨hIcc ht, ht⟩
  have hmov : IsMovingSolutionOn ν μ (Icc (-T) T) z := movingSolutionOn_mono hmovAll hIcc
  have h0' : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  refine ⟨z, hz.init, hmov, ?_, fun t ht => ?_⟩
  · intro V' w hVo hVc h0V hw0 hwV t ht
    exact gen_uniqueness_inter hW hF (convex_iff_ordConnected.1 hVc) ordConnected_Icc
      (t₀ := 0) ⟨h0V, h0'⟩ ((hiff V' w).1 hwV) ((hiff _ z).1 hmov) hw0 ht
  · have h := hCall t (hIJ t ht)
    exact ⟨h.1, h.2.1, by linarith [h.2.2], hbar t (hIJ t ht)⟩

end KAM.Planetary.StrongAMD
