/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Planetary.AMD.Setting
public import KAM.Planetary.AMD.Elements

/-!
# Closure and continuity on the negative-energy domain (P14, package A3)

Blueprint P, Part 14 (`bpP:p14:closure`).  `element_continuity`: on the open set of phases with
every radius positive and every Kepler energy negative, the Kepler actions and the physical AMD
are continuous.  `amd_closure`: the outer low-AMD region is open, and the collar is sequentially
closed among phases with positive radii (the collar margins force the energies and the angular
momenta away from their degenerate values uniformly).
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

private theorem cl_continuous_planeSq : Continuous planeSq := by
  have : planeSq = fun w : Fin 2 → ℝ => ∑ k, w k ^ 2 := rfl
  rw [this]; fun_prop

private theorem cl_continuous_planeLength : Continuous planeLength :=
  Real.continuous_sqrt.comp cl_continuous_planeSq

private theorem cl_continuous_bodyQ (i : Fin n) :
    Continuous fun z : Phase (n * 2) => bodyVector z.1 i :=
  continuous_pi fun _ => (continuous_apply _).comp continuous_fst

private theorem cl_continuous_bodyP (i : Fin n) :
    Continuous fun z : Phase (n * 2) => bodyVector z.2 i :=
  continuous_pi fun _ => (continuous_apply _).comp continuous_snd

private theorem cl_continuous_len (i : Fin n) :
    Continuous fun z : Phase (n * 2) => planeLength (bodyVector z.1 i) :=
  cl_continuous_planeLength.comp (cl_continuous_bodyQ i)

private theorem cl_continuous_cross (i : Fin n) :
    Continuous fun z : Phase (n * 2) => planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  have hq0 := (continuous_apply (0 : Fin 2)).comp (cl_continuous_bodyQ i)
  have hq1 := (continuous_apply (1 : Fin 2)).comp (cl_continuous_bodyQ i)
  have hp0 := (continuous_apply (0 : Fin 2)).comp (cl_continuous_bodyP i)
  have hp1 := (continuous_apply (1 : Fin 2)).comp (cl_continuous_bodyP i)
  exact (hq0.mul hp1).sub (hq1.mul hp0)

private theorem cl_continuousOn_energy (m : Fin n → ℝ) (i : Fin n) :
    ContinuousOn (fun z : Phase (n * 2) => keplerEnergy m z i)
      {z | 0 < planeLength (bodyVector z.1 i)} := by
  simp only [keplerEnergy]
  refine ContinuousOn.sub ?_ ?_
  · exact ((cl_continuous_planeSq.comp (cl_continuous_bodyP i)).div_const _).continuousOn
  · exact continuousOn_const.div (cl_continuous_len i).continuousOn (fun z hz => hz.ne')

/-- Phases with every radius positive and every Kepler energy negative. -/
def negativeEnergyDomain (m : Fin n → ℝ) : Set (Phase (n*2)) :=
  {z | ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy m z i < 0}

theorem element_continuity (m : Fin n → ℝ) :
    IsOpen (negativeEnergyDomain m) ∧
    (∀ i, ContinuousOn (fun z => keplerAction m z i) (negativeEnergyDomain m)) ∧
    ContinuousOn (physicalAMD m) (negativeEnergyDomain m) := by
  have hopen : IsOpen (negativeEnergyDomain m) := by
    have hset : negativeEnergyDomain m = ⋂ i, ({z : Phase (n * 2) |
        0 < planeLength (bodyVector z.1 i)} ∩
        (fun z : Phase (n * 2) => keplerEnergy m z i) ⁻¹' Iio 0) := by
      ext z
      simp [negativeEnergyDomain]
    rw [hset]
    refine isOpen_iInter_of_finite fun i => ?_
    exact (cl_continuousOn_energy m i).isOpen_inter_preimage
      (isOpen_lt continuous_const (cl_continuous_len i)) isOpen_Iio
  have hact : ∀ i, ContinuousOn (fun z => keplerAction m z i) (negativeEnergyDomain m) := by
    intro i
    have hE : ContinuousOn (fun z : Phase (n * 2) => keplerEnergy m z i)
        (negativeEnergyDomain m) := (cl_continuousOn_energy m i).mono fun z hz => (hz i).1
    have hax : ContinuousOn (fun z : Phase (n * 2) => keplerAxis m z i)
        (negativeEnergyDomain m) := by
      simp only [keplerAxis]
      refine continuousOn_const.div (continuousOn_const.mul hE) fun z hz => ?_
      have h := (hz i).2
      intro h0
      linarith
    simp only [keplerAction]
    exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hax)
  refine ⟨hopen, hact, ?_⟩
  show ContinuousOn (fun z : Phase (n * 2) =>
    (∑ i, keplerAction m z i) - ∑ i, planeCross (bodyVector z.1 i) (bodyVector z.2 i)) _
  exact (continuousOn_finsetSum _ fun i _ => hact i).sub
    (continuous_finsetSum _ fun i _ => cl_continuous_cross i).continuousOn

/-- Elementary facts for one prograde elliptic planet. -/
private theorem cl_pe_facts {m : Fin n → ℝ} {z : Phase (n * 2)} (hp : ProgradeElliptic m z)
    (i : Fin n) :
    0 < keplerAction m z i ∧
    keplerEnergy m z i = -(m i) ^ 3 / (2 * keplerAction m z i ^ 2) ∧
    0 ≤ keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  obtain ⟨-, h2, -, hE, -, -, -, -, -, -, -, -, -, -, -, h16⟩ := elements i (hp i)
  exact ⟨h2, hE, h16⟩

private theorem cl_le_amd {m : Fin n → ℝ} {z : Phase (n * 2)} (hp : ProgradeElliptic m z)
    (i : Fin n) :
    keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤ physicalAMD m z := by
  have h : physicalAMD m z = ∑ j, (keplerAction m z j -
      planeCross (bodyVector z.1 j) (bodyVector z.2 j)) := by
    simp only [physicalAMD, totalMomentum, Finset.sum_sub_distrib]
  rw [h]
  exact Finset.single_le_sum (f := fun j => keplerAction m z j -
    planeCross (bodyVector z.1 j) (bodyVector z.2 j))
    (fun j _ => (cl_pe_facts hp j).2.2) (Finset.mem_univ i)

theorem amd_closure (B : AMDBox n) (hB : B.Admissible) {delta : ℝ} (hd : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD) :
    IsOpen (amdOuter B) ∧
    ∀ (z : ℕ → Phase (n * 2)) (zs : Phase (n * 2)),
      (∀ k, z k ∈ amdCollar B delta) → Filter.Tendsto z Filter.atTop (nhds zs) →
      (∀ i, 0 < planeLength (bodyVector zs.1 i)) → zs ∈ amdCollar B delta := by
  obtain ⟨hlow, -, -, -, -, hOL, -⟩ := hB
  obtain ⟨hNopen, hNact, hNamd⟩ := element_continuity B.mass
  have hmass : ∀ i, 0 < B.mass i := fun i => (hlow i).1
  have hnd : 0 ≤ (n : ℝ) * delta := by positivity
  refine ⟨?_, ?_⟩
  · have hset : amdOuter B = negativeEnergyDomain B.mass ∩
        ((⋂ i, {z : Phase (n * 2) |
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)}) ∩
        ((⋂ i, negativeEnergyDomain B.mass ∩
          (fun z => keplerAction B.mass z i) ⁻¹' Ioo (B.lower i) (B.upper i)) ∩
        (negativeEnergyDomain B.mass ∩ physicalAMD B.mass ⁻¹' Iio B.outerAMD))) := by
      ext z
      simp only [amdOuter, LowAMDRegion, ProgradeElliptic, mem_ofPred_eq, mem_inter_iff,
        mem_iInter, mem_preimage, mem_Ioo, mem_Iio, negativeEnergyDomain]
      constructor
      · rintro ⟨hp, hact, hamd⟩
        have hN : ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy B.mass z i < 0 :=
          fun i => ⟨(hp i).2.1, (hp i).2.2.1⟩
        exact ⟨hN, fun i => (hp i).2.2.2, fun i => ⟨hN, hact i⟩, hN, hamd⟩
      · rintro ⟨hN, hc, hact, -, hamd⟩
        exact ⟨fun i => ⟨hmass i, (hN i).1, (hN i).2, hc i⟩, fun i => (hact i).2, hamd⟩
    rw [hset]
    refine hNopen.inter (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
    · exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (cl_continuous_cross i)
    · exact isOpen_iInter_of_finite fun i =>
        (hNact i).isOpen_inter_preimage hNopen isOpen_Ioo
    · exact hNamd.isOpen_inter_preimage hNopen isOpen_Iio
  · intro z zs hz hlim hlen
    have hO : ∀ k, ProgradeElliptic B.mass (z k) ∧
        (∀ i, B.lower i < keplerAction B.mass (z k) i ∧ keplerAction B.mass (z k) i <
          B.upper i) ∧ physicalAMD B.mass (z k) < B.outerAMD := fun k => (hz k).1
    have hC : ∀ k, (∀ i, B.lower i + delta ≤ keplerAction B.mass (z k) i ∧
        keplerAction B.mass (z k) i ≤ B.upper i - delta) ∧
        physicalAMD B.mass (z k) ≤ B.initialAMD + (n : ℝ) * delta := fun k => (hz k).2
    have hlo : ∀ i, B.lower i - (B.initialAMD + (n : ℝ) * delta) + delta > 0 := by
      intro i
      have := hOL i
      have h1 : 0 ≤ Real.sqrt (1 - B.ecc ^ 2) := Real.sqrt_nonneg _
      have h2 := (hlow i).2.1
      nlinarith
    -- uniform bounds along the sequence
    have hEbd : ∀ k i, keplerEnergy B.mass (z k) i ≤
        -(B.mass i) ^ 3 / (2 * B.upper i ^ 2) := by
      intro k i
      obtain ⟨hΛ, hE, -⟩ := cl_pe_facts (hO k).1 i
      rw [hE]
      have hu := (hC k).1 i
      have hΛu : keplerAction B.mass (z k) i ≤ B.upper i := by linarith [hu.2]
      have hmi := hmass i
      have : (B.mass i) ^ 3 / (2 * B.upper i ^ 2) ≤
          (B.mass i) ^ 3 / (2 * keplerAction B.mass (z k) i ^ 2) := by
        gcongr
      rw [neg_div, neg_div]
      exact neg_le_neg this
    have hCbd : ∀ k i, B.lower i - (B.initialAMD + (n : ℝ) * delta) + delta ≤
        planeCross (bodyVector (z k).1 i) (bodyVector (z k).2 i) := by
      intro k i
      have h1 := cl_le_amd (hO k).1 i
      have h2 := (hC k).1 i
      have h3 := (hC k).2
      linarith [h2.1]
    -- limits
    have hEs : ∀ i, keplerEnergy B.mass zs i ≤ -(B.mass i) ^ 3 / (2 * B.upper i ^ 2) := by
      intro i
      have hcont : ContinuousAt (fun w : Phase (n * 2) => keplerEnergy B.mass w i) zs :=
        (cl_continuousOn_energy B.mass i).continuousAt
          ((isOpen_lt continuous_const (cl_continuous_len i)).mem_nhds (hlen i))
      exact le_of_tendsto' (hcont.tendsto.comp hlim) fun k => hEbd k i
    have hNs : zs ∈ negativeEnergyDomain B.mass := by
      intro i
      refine ⟨hlen i, lt_of_le_of_lt (hEs i) ?_⟩
      have hu : 0 < B.upper i := by linarith [(hlow i).2.1, (hlow i).2.2.1, (hlow i).2.2.2.1,
        (hlow i).2.2.2.2]
      have hmi := hmass i
      rw [neg_div]
      have : 0 < (B.mass i) ^ 3 / (2 * B.upper i ^ 2) := by positivity
      linarith
    have hnhds : negativeEnergyDomain B.mass ∈ nhds zs := hNopen.mem_nhds hNs
    have hactS : ∀ i, B.lower i + delta ≤ keplerAction B.mass zs i ∧
        keplerAction B.mass zs i ≤ B.upper i - delta := by
      intro i
      have hcont := ((hNact i).continuousAt hnhds).tendsto.comp hlim
      exact ⟨ge_of_tendsto' hcont fun k => ((hC k).1 i).1,
        le_of_tendsto' hcont fun k => ((hC k).1 i).2⟩
    have hamdS : physicalAMD B.mass zs ≤ B.initialAMD + (n : ℝ) * delta :=
      le_of_tendsto' ((hNamd.continuousAt hnhds).tendsto.comp hlim) fun k => (hC k).2
    have hcrS : ∀ i, 0 < planeCross (bodyVector zs.1 i) (bodyVector zs.2 i) := by
      intro i
      have hc := ((cl_continuous_cross i).tendsto zs).comp hlim
      have := ge_of_tendsto' hc fun k => hCbd k i
      linarith [hlo i]
    refine ⟨⟨fun i => ⟨hmass i, hlen i, (hNs i).2, hcrS i⟩, fun i => ⟨?_, ?_⟩, ?_⟩,
      hactS, hamdS⟩
    · linarith [(hactS i).1]
    · linarith [(hactS i).2]
    · nlinarith
