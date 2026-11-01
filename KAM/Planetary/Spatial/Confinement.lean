/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness
public import KAM.Planetary.AMD.ConfinementExit
public import KAM.Planetary.Spatial.Continuation
public import KAM.Planetary.Spatial.Geometry
public import KAM.Planetary.Spatial.Momentum
public import KAM.Planetary.StrongAMD.Modulus

/-!
# Spatial sharp first exit (conditional confinement helper)

Package LP-SP-CONF, `LP:MAIN L14 (468–500)` for `d = 3` (with `LP:MAIN T19 (599–603)`) and
amendments N2 (one shared compact `U`) and N6 (on the Lemma-13 route the stopped radius is `r` and
the improvement is to `r / 2`); track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`spatialStrongFirstExit_of_stopped_drift` is the topological first-exit argument of MAIN Lemma 14
with the stopped drift as an **explicit hypothesis** `hstop`.  It is NOT the public theorem: it is
the internal conditional helper (the spatial mirror of `strongFirstExit_of_stopped_drift`), and the
spatial analogue of LP-PS discharges `hstop` from Lemma 13 through the chart lift.

The route is that of the planar helper: the maximal solution of the spatial moving field on the
collision-free domain; a forward and a backward first exit (`amd_exit_forward`,
`amd_exit_backward`) for the open tube set `spatialFirstExitTube` and the improved set
`spatialFirstExitCore`; inside the tube `hstop` improves the drift to `r / 2` and (17)
(`spatialStrongAMD_le_of_tube`) with the budget improves the AMD margin to `3 δ / 4`; the improved
set consists of barrier states, so `spatial_maximal_global_of_barrier` excludes a finite endpoint;
uniqueness is the ODE uniqueness on the open domain in the `SpatialMovingUniqueOn` form.

"Physical state" here is `SpatialNegativeEnergy`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.ODE Set Filter Topology

variable {n : ℕ}

/-- The open tube set of the spatial first exit: negative-energy states whose action vector is
strictly within `r` of `I₀` and whose AMD margin is strictly above `δ / 2` (the stopped
conditions (40), open form). -/
def spatialFirstExitTube (ν : Fin n → ℝ) (I₀ : Fin n → ℝ) (δ r : ℝ) : Set (Phase (n * 3)) :=
  {w | SpatialNegativeEnergy ν w ∧ ‖spatialActionVector ν w - I₀‖ < r ∧
    spatialStrongAMD ν w < strongThreshold ν (spatialActionVector ν w) - δ / 2}

/-- The improved set of the spatial first exit (`LP:MAIN L14 (485)`, N6): action drift at most
`r / 2` and AMD margin at least `3 δ / 4`. -/
def spatialFirstExitCore (ν : Fin n → ℝ) (I₀ : Fin n → ℝ) (δ r : ℝ) : Set (Phase (n * 3)) :=
  {w | SpatialNegativeEnergy ν w ∧ ‖spatialActionVector ν w - I₀‖ ≤ r / 2 ∧
    spatialStrongAMD ν w ≤ strongThreshold ν (spatialActionVector ν w) - 3 * δ / 4}

theorem spatialFirstExitCore_subset_tube {ν : Fin n → ℝ} {I₀ : Fin n → ℝ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) :
    spatialFirstExitCore ν I₀ δ r ⊆ spatialFirstExitTube ν I₀ δ r :=
  fun _ h => ⟨h.1, lt_of_le_of_lt h.2.1 (by linarith), by linarith [h.2.2]⟩

/-! ### Continuity on negative-energy states -/

theorem spatialMovingSolutionOn_mono {ν : Fin n → ℝ} {μ : ℝ} {J J' : Set ℝ}
    {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) (h : J' ⊆ J) :
    IsSpatialMovingSolutionOn ν μ J' z :=
  ⟨fun t ht => hz.1 t (h ht), fun t ht => hz.2 t (h ht)⟩

theorem continuous_bodyVector3_snd' (i : Fin n) :
    Continuous (fun z : Phase (n * 3) => bodyVector3 z.2 i) :=
  (continuous_bodyVector3' i).comp continuous_snd

theorem continuous_bodyVector3_fst' (i : Fin n) :
    Continuous (fun z : Phase (n * 3) => bodyVector3 z.1 i) :=
  (continuous_bodyVector3' i).comp continuous_fst

theorem continuous_spaceSq' : Continuous spaceSq := by
  unfold spaceSq; fun_prop

theorem continuous_spaceCross' {α : Type*} [TopologicalSpace α] {u w : α → Fin 3 → ℝ}
    (hu : Continuous u) (hw : Continuous w) : Continuous fun a => spaceCross (u a) (w a) := by
  have hu' : ∀ k, Continuous fun a => u a k := fun k => (continuous_apply k).comp hu
  have hw' : ∀ k, Continuous fun a => w a k := fun k => (continuous_apply k).comp hw
  refine continuous_pi fun k => ?_
  fin_cases k
  · exact (((hu' 1).mul (hw' 2)).sub ((hu' 2).mul (hw' 1))).congr fun a => by
      simp [spaceCross]
  · exact (((hu' 2).mul (hw' 0)).sub ((hu' 0).mul (hw' 2))).congr fun a => by
      simp [spaceCross]
  · exact (((hu' 0).mul (hw' 1)).sub ((hu' 1).mul (hw' 0))).congr fun a => by
      simp [spaceCross]

theorem continuous_angularMomentum3' :
    Continuous (angularMomentum3 : Phase (n * 3) → Fin 3 → ℝ) := by
  unfold angularMomentum3
  exact continuous_finsetSum _ fun i _ =>
    continuous_spaceCross' (continuous_bodyVector3_fst' i) (continuous_bodyVector3_snd' i)

theorem continuousAt_spatialKeplerEnergy' (ν : Fin n → ℝ) {z : Phase (n * 3)} (i : Fin n)
    (h : 0 < spaceLength (bodyVector3 z.1 i)) :
    ContinuousAt (fun w : Phase (n * 3) => spatialKeplerEnergy ν w i) z := by
  have hq : Continuous fun w : Phase (n * 3) => spaceLength (bodyVector3 w.1 i) :=
    continuous_spaceLength.comp (continuous_bodyVector3_fst' i)
  have hp : Continuous fun w : Phase (n * 3) => spaceSq (bodyVector3 w.2 i) :=
    continuous_spaceSq'.comp (continuous_bodyVector3_snd' i)
  unfold spatialKeplerEnergy
  exact (hp.continuousAt.div_const _).sub (continuousAt_const.div hq.continuousAt h.ne')

theorem continuousAt_spatialActionVector {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) : ContinuousAt (spatialActionVector ν) z := by
  refine continuousAt_pi.2 fun i => ?_
  obtain ⟨-, hq, hE⟩ := hz i
  have hE' := continuousAt_spatialKeplerEnergy' ν i hq
  have hax : ContinuousAt (fun w : Phase (n * 3) => spatialKeplerAxis ν w i) z := by
    unfold spatialKeplerAxis
    exact continuousAt_const.div (continuousAt_const.mul hE') (by
      intro h0; linarith)
  unfold spatialActionVector spatialKeplerAction
  exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hax)

theorem continuousAt_spatialStrongAMD {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) : ContinuousAt (spatialStrongAMD ν) z := by
  have h1 : ContinuousAt (fun w : Phase (n * 3) => ∑ i, spatialKeplerAction ν w i) z := by
    have := continuousAt_spatialActionVector hz
    exact tendsto_finsetSum _ fun i _ => continuousAt_pi.1 this i
  exact h1.sub (continuous_spaceLength.comp continuous_angularMomentum3').continuousAt

/-- The margin function `C - B(Λ)` is continuous at a negative-energy state whose action vector
lies in the chamber. -/
theorem continuousAt_spatialStrongGap {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {z : Phase (n * 3)} (hz : SpatialNegativeEnergy ν z)
    (hch : spatialActionVector ν z ∈ chamber ν) :
    ContinuousAt (fun w => spatialStrongAMD ν w - strongThreshold ν (spatialActionVector ν w))
      z := by
  have hB : ContinuousAt (strongThreshold ν) (spatialActionVector ν z) :=
    (continuousOn_strongThreshold hν hn).continuousAt ((isOpen_chamber ν).mem_nhds hch)
  exact (continuousAt_spatialStrongAMD hz).sub
    (hB.comp (continuousAt_spatialActionVector hz))

/-- Negative-energy states form a neighbourhood of each of their points. -/
theorem eventually_spatialNegativeEnergy {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) : ∀ᶠ w in 𝓝 z, SpatialNegativeEnergy ν w := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨hν, hq, hE⟩ := hz i
  have hq' : Continuous fun w : Phase (n * 3) => spaceLength (bodyVector3 w.1 i) :=
    continuous_spaceLength.comp (continuous_bodyVector3_fst' i)
  filter_upwards [hq'.continuousAt.eventually (lt_mem_nhds hq),
    (continuousAt_spatialKeplerEnergy' ν i hq).eventually (gt_mem_nhds hE)] with w h1 h2
  exact ⟨hν, h1, h2⟩

/-! ### Openness and closedness -/

theorem isOpen_spatialFirstExitTube {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUch : U ⊆ chamber ν) {I₀ : Fin n → ℝ} {δ r : ℝ}
    (hball : ∀ I, ‖I - I₀‖ ≤ r → I ∈ U) : IsOpen (spatialFirstExitTube ν I₀ δ r) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hp, hr', hg⟩ := hz
  have hΛ := continuousAt_spatialActionVector hp
  have hch : spatialActionVector ν z ∈ chamber ν := hUch (hball _ hr'.le)
  have hgc := continuousAt_spatialStrongGap hν hn hp hch
  have e1 := eventually_spatialNegativeEnergy hp
  have e2 : ∀ᶠ w in 𝓝 z, ‖spatialActionVector ν w - I₀‖ < r :=
    (hΛ.sub continuousAt_const).norm.eventually (gt_mem_nhds hr')
  have e3 : ∀ᶠ w in 𝓝 z,
      spatialStrongAMD ν w - strongThreshold ν (spatialActionVector ν w) < -(δ / 2) :=
    hgc.eventually (gt_mem_nhds (by linarith))
  filter_upwards [e1, e2, e3] with w h1 h2 h3
  exact ⟨h1, h2, by linarith⟩

/-- Closedness of the improved set among limits with positive radii (the negative-energy clause is
recovered from the uniform energy bound of the barrier). -/
theorem spatialFirstExitCore_closed {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {I₀ : Fin n → ℝ}
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hball : ∀ I, ‖I - I₀‖ ≤ r → I ∈ U)
    (x : ℕ → Phase (n * 3)) (xs : Phase (n * 3))
    (hx : ∀ k, x k ∈ spatialFirstExitCore ν I₀ δ r)
    (hl : Tendsto x atTop (𝓝 xs)) (hN : ∀ i, 0 < spaceLength (bodyVector3 xs.1 i)) :
    xs ∈ spatialFirstExitCore ν I₀ δ r := by
  obtain ⟨dS, dP, R, P, c, -, -, -, -, hc, -, hbar⟩ :=
    spatialStrongBarrier_physical hν hn hUc hUch (half_pos hδ)
  have hb : ∀ k, SpatialBarrierState ν U (δ / 2) (x k) := fun k =>
    ⟨(hx k).1, hball _ ((hx k).2.1.trans (by linarith)), by linarith [(hx k).2.2]⟩
  have hE : ∀ i, spatialKeplerEnergy ν xs i ≤ -c := fun i => by
    have ht := (continuousAt_spatialKeplerEnergy' ν i (hN i)).tendsto.comp hl
    refine le_of_tendsto' ht fun k => ?_
    obtain ⟨-, -, -, -, -, -, hE, -⟩ := hbar (x k) (hb k)
    exact hE i
  have hphys : SpatialNegativeEnergy ν xs := fun i => ⟨hν i, hN i, by linarith [hE i]⟩
  have hΛt : Tendsto (fun k => spatialActionVector ν (x k)) atTop
      (𝓝 (spatialActionVector ν xs)) :=
    (continuousAt_spatialActionVector hphys).tendsto.comp hl
  have hdr : ‖spatialActionVector ν xs - I₀‖ ≤ r / 2 :=
    le_of_tendsto' (hΛt.sub_const I₀).norm fun k => (hx k).2.1
  have hch : spatialActionVector ν xs ∈ chamber ν := hUch (hball _ (hdr.trans (by linarith)))
  have hgt := (continuousAt_spatialStrongGap hν hn hphys hch).tendsto.comp hl
  refine ⟨hphys, hdr, ?_⟩
  have hle : spatialStrongAMD ν xs - strongThreshold ν (spatialActionVector ν xs) ≤
      -(3 * δ / 4) :=
    le_of_tendsto' hgt fun k => by
      show spatialStrongAMD ν (x k) - strongThreshold ν (spatialActionVector ν (x k)) ≤
        -(3 * δ / 4)
      linarith [(hx k).2.2]
  linarith

/-! ### The conditional first-exit helper -/

/-- **Conditional spatial confinement helper (not the public theorem)**
(`LP:MAIN L14 (468–500)`, `d = 3`, N2, N6): the topological first-exit argument of MAIN Lemma 14,
with the stopped drift as the explicit hypothesis `hstop` (MAIN's stopped conditions (40) in
strict, open form, both the action drift `< r` and the margin `> δ / 2`, improving the drift to
`r / 2`).

Given the budget `n r + Ω_B(r) ≤ δ / 4` and an initial negative-energy state `z₀` whose closed
`r`-action ball lies in the shared compact `U` and whose strong AMD is `≤ B(Λ z₀) - δ`, there is a
spatial moving solution on `[-T, T]`, unique in the `SpatialMovingUniqueOn` sense, that stays
negative-energy with drift `≤ r / 2`, with AMD margin `≥ δ / 2` (MAIN (8)), and in barrier states
`SpatialBarrierState ν U (δ / 2)`. -/
theorem spatialStrongFirstExit_of_stopped_drift {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    (hn : 2 ≤ n) {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν)
    {μ δ r T : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hT : 0 < T)
    (hbudget : n * r + strongThresholdModulus ν U r ≤ δ / 4)
    {z₀ : Phase (n * 3)} (hphys₀ : SpatialNegativeEnergy ν z₀)
    (hball : ∀ I, ‖I - spatialActionVector ν z₀‖ ≤ r → I ∈ U)
    (hC₀ : spatialStrongAMD ν z₀ ≤ strongThreshold ν (spatialActionVector ν z₀) - δ)
    (hstop : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 3),
      IsSpatialMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J, |t| ≤ T →
        (∀ u ∈ Set.uIcc 0 t, SpatialNegativeEnergy ν (z u) ∧
          ‖spatialActionVector ν (z u) - spatialActionVector ν z₀‖ < r ∧
          spatialStrongAMD ν (z u) <
            strongThreshold ν (spatialActionVector ν (z u)) - δ / 2) →
        ‖spatialActionVector ν (z t) - spatialActionVector ν z₀‖ ≤ r / 2) :
    ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧ IsSpatialMovingSolutionOn ν μ (Icc (-T) T) z ∧
      SpatialMovingUniqueOn ν μ (Icc (-T) T) z ∧
      ∀ t ∈ Icc (-T) T, SpatialNegativeEnergy ν (z t) ∧
        ‖spatialActionVector ν (z t) - spatialActionVector ν z₀‖ ≤ r / 2 ∧
        spatialStrongAMD ν (z t) ≤ strongThreshold ν (spatialActionVector ν (z t)) - δ / 2 ∧
        SpatialBarrierState ν U (δ / 2) (z t) := by
  obtain ⟨hW, hF, hiff⟩ := spatial_moving_ode ν μ
  have hU0 : spatialActionVector ν z₀ ∈ U := hball _ (by simpa using hr.le)
  obtain ⟨K, -, hKW, hKs⟩ := exists_spatialBarrierCompact hν hn hUc hUch (half_pos hδ)
  have hz₀W : z₀ ∈ spatialCollisionFreeDomain n :=
    hKW (hKs z₀ ⟨hphys₀, hU0, by linarith⟩)
  obtain ⟨Tm, Tp, z, hz⟩ := (gen_maximal hW hF hz₀W).1
  have hz' : IsMaximalSolution (spatialMovingField ν μ) (spatialCollisionFreeDomain n) z₀
      Tm Tp z := hz
  have hmovAll : IsSpatialMovingSolutionOn ν μ (eIoo Tm Tp) z := (hiff _ z).2 hz.isSolution
  set J : Set ℝ := eIoo Tm Tp ∩ Icc (-T) T with hJdef
  have hJ : J.OrdConnected := (ordConnected_eIoo _ _).inter ordConnected_Icc
  have h0 : (0 : ℝ) ∈ J := ⟨zero_mem_eIoo hz, by constructor <;> linarith⟩
  have hmovJ : IsSpatialMovingSolutionOn ν μ J z :=
    spatialMovingSolutionOn_mono hmovAll inter_subset_left
  have hcont : ContinuousOn z J := fun t ht =>
    (hmovJ.1 t ht).2.2.continuousAt.continuousWithinAt
  have hN : ∀ t ∈ J, z t ∈ {w : Phase (n * 3) | ∀ i, 0 < spaceLength (bodyVector3 w.1 i)} :=
    fun t ht i => (hmovJ.2 t ht).1 i
  have hVopen := isOpen_spatialFirstExitTube hν hn hUch hball (δ := δ) (r := r)
  have hCV := spatialFirstExitCore_subset_tube (ν := ν) (I₀ := spatialActionVector ν z₀) hδ hr
  have hy0V : z 0 ∈ spatialFirstExitTube ν (spatialActionVector ν z₀) δ r := by
    rw [hz.init]
    exact ⟨hphys₀, by simpa using hr, by linarith⟩
  -- the key local step: if the orbit stayed in the tube up to `s`, it is in the improved set at `s`
  have key : ∀ s ∈ J,
      (∀ u ∈ Set.uIcc (0 : ℝ) s, z u ∈ spatialFirstExitTube ν (spatialActionVector ν z₀) δ r) →
      z s ∈ spatialFirstExitCore ν (spatialActionVector ν z₀) δ r := by
    intro s hs hV
    have hdrift := hstop J hJ h0 z hmovJ hz.init s hs (abs_le.2 hs.2) fun u hu =>
      hV u hu
    have h17 := spatialStrongAMD_le_of_tube hν hn hUc hUch hJ hmovJ h0 hs (δ := δ) (r := r / 2)
      (by rw [hz.init]; exact hC₀) (by rw [hz.init]; exact hdrift) (by rw [hz.init]; exact hU0)
      (hball _ (hdrift.trans (by linarith)))
    have hmono := strongThresholdModulus_mono hν hn hUc hUch (r := r / 2) (s := r) (by linarith)
    have hnr : (n : ℝ) * (r / 2) ≤ n * r := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    exact ⟨(hV s (by simp)).1, hdrift, by linarith⟩
  have hcl := spatialFirstExitCore_closed hν hn hUc hUch hδ hr hball
  have hfwd := amd_exit_forward hJ h0 hcont hVopen hCV hcl hN hy0V (fun s hs hs0 hV => by
    refine key s hs fun u hu => ?_
    rw [Set.uIcc_of_le hs0] at hu
    exact hV u hu.1 hu.2)
  have hbwd := amd_exit_backward hJ h0 hcont hVopen hCV hcl hN hy0V (fun s hs hs0 hV => by
    refine key s hs fun u hu => ?_
    rw [Set.uIcc_of_ge hs0] at hu
    exact hV u hu.1 hu.2)
  have hCall : ∀ t ∈ J, z t ∈ spatialFirstExitCore ν (spatialActionVector ν z₀) δ r :=
    fun t ht => by
      rcases le_total 0 t with h | h
      · exact hfwd t ht h
      · exact hbwd t ht h
  have hbar : ∀ t ∈ J, SpatialBarrierState ν U (δ / 2) (z t) := fun t ht =>
    ⟨(hCall t ht).1, hball _ ((hCall t ht).2.1.trans (by linarith)),
      by linarith [(hCall t ht).2.2]⟩
  have hglob := spatial_maximal_global_of_barrier hν hn hUc hUch (half_pos hδ) hz'
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
  have hmov : IsSpatialMovingSolutionOn ν μ (Icc (-T) T) z :=
    spatialMovingSolutionOn_mono hmovAll hIcc
  have h0' : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  refine ⟨z, hz.init, hmov, ?_, fun t ht => ?_⟩
  · intro V' w hVo hVc h0V hw0 hwV t ht
    exact gen_uniqueness_inter hW hF (convex_iff_ordConnected.1 hVc) ordConnected_Icc
      (t₀ := 0) ⟨h0V, h0'⟩ ((hiff V' w).1 hwV) ((hiff _ z).1 hmov) hw0 ht
  · have h := hCall t (hIJ t ht)
    exact ⟨h.1, h.2.1, by linarith [h.2.2], hbar t (hIJ t ht)⟩

end KAM.Planetary.Spatial

end
