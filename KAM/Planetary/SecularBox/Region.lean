/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularBox.Chart
public import KAM.Planetary.SecularBox.Numerics
public import KAM.Frozen.Planetary.Defs.EllipsePhase
public import KAM.Frozen.Planetary.Defs.JupiterSaturnWeights
public import KAM.Frozen.Planetary.Defs.NoCollision

/-!
# The secular region `S`

`sb_sdef` (blueprint `bpP:p14:sb-Sdef`) is the open region of the secular box and `sb_s`
(`bpP:p14:sb-S`) its geometry: eccentricity, longitude Jacobian and collision-freeness. Steps
`sb-S-1`..`sb-S-3` are internal to `sb_s`; the rational comparisons are discharged inline by
`norm_num` (they are the facts N6c, N6d of `sb_numerics`).
-/

@[expose] public noncomputable section

open Set
open KAM.Kepler

namespace KAM.Planetary

def sb_sdef (saturn : ℝ) : Set (Phase (2+2)) :=
  {w | (∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) ∧
    51/10 < secularAxis (jupiterSaturnWeights saturn) w 0 ∧
    secularAxis (jupiterSaturnWeights saturn) w 0 < 53/10 ∧
    47/5 < secularAxis (jupiterSaturnWeights saturn) w 1 ∧
    secularAxis (jupiterSaturnWeights saturn) w 1 < 97/10}

private theorem sbRegion_continuous_fast (i : Fin 2) :
    Continuous fun w : Phase (2+2) => fast w.2 i := by
  unfold fast; fun_prop

private theorem sbRegion_continuous_slow_snd (i : Fin 2) :
    Continuous fun w : Phase (2+2) => slow w.2 i := by
  unfold slow; fun_prop

private theorem sbRegion_continuous_slow_fst (i : Fin 2) :
    Continuous fun w : Phase (2+2) => slow w.1 i := by
  unfold slow; fun_prop

private theorem sbRegion_continuous_gamma (i : Fin 2) :
    Continuous fun w : Phase (2+2) => secularGamma w i := by
  unfold secularGamma oscillatorAction
  have h1 := sbRegion_continuous_slow_snd i
  have h2 := sbRegion_continuous_slow_fst i
  fun_prop

private theorem sbRegion_continuous_axis (m : Fin 2 → ℝ) (i : Fin 2) :
    Continuous fun w : Phase (2+2) => secularAxis m w i := by
  unfold secularAxis
  have := sbRegion_continuous_fast i
  fun_prop

private theorem sbRegion_isOpen (saturn : ℝ) : IsOpen (sb_sdef saturn) := by
  have hset : sb_sdef saturn =
      {w | 0 < fast w.2 0 ∧ 50 * secularGamma w 0 < fast w.2 0} ∩
      {w | 0 < fast w.2 1 ∧ 50 * secularGamma w 1 < fast w.2 1} ∩
      ({w | 51/10 < secularAxis (jupiterSaturnWeights saturn) w 0} ∩
       {w | secularAxis (jupiterSaturnWeights saturn) w 0 < 53/10} ∩
       {w | 47/5 < secularAxis (jupiterSaturnWeights saturn) w 1} ∩
       {w | secularAxis (jupiterSaturnWeights saturn) w 1 < 97/10}) := by
    ext w
    simp only [sb_sdef, mem_ofPred_eq, mem_inter_iff, Fin.forall_fin_two]
    tauto
  have hf := sbRegion_continuous_fast
  have hg := sbRegion_continuous_gamma
  have ha := sbRegion_continuous_axis (jupiterSaturnWeights saturn)
  rw [hset]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  · exact (isOpen_lt continuous_const (hf 0)).inter
      (isOpen_lt (continuous_const.mul (hg 0)) (hf 0))
  · exact (isOpen_lt continuous_const (hf 1)).inter
      (isOpen_lt (continuous_const.mul (hg 1)) (hf 1))
  · exact (((isOpen_lt continuous_const (ha 0)).inter
      (isOpen_lt (ha 0) continuous_const)).inter
      (isOpen_lt continuous_const (ha 1))).inter (isOpen_lt (ha 1) continuous_const)

private theorem sbRegion_bodyVector_ellipsePhase (m : Fin 2 → ℝ) (w : Phase (2+2))
    (F : Fin 2 → ℝ) (i : Fin 2) :
    bodyVector (ellipsePhase m w F).1 i = ellipsePosition m w i (F i) := by
  funext k
  simp [bodyVector, ellipsePhase]

/-- Pointwise geometry of one planet on `S` (steps `sb-S-1`, `sb-S-2`). -/
private theorem sbRegion_planet (m : Fin 2 → ℝ) (hm : ∀ i, 0 < m i) {w : Phase (2+2)}
    (h : ∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) (i : Fin 2) (F : ℝ) :
    (49/50 : ℝ) < secularRoot w i ∧ planeLength (secularEccVector w i) < 1/5 ∧
      (4/5 : ℝ) < longitudeJacobian w i F ∧
      planeLength (ellipsePosition m w i F) = secularAxis m w i * longitudeJacobian w i F ∧
      secularAxis m w i * (1 - planeLength (secularEccVector w i)) ≤
        planeLength (ellipsePosition m w i F) ∧
      planeLength (ellipsePosition m w i F) ≤
        secularAxis m w i * (1 + planeLength (secularEccVector w i)) ∧
      0 < planeLength (ellipsePosition m w i F) := by
  have hG : ∀ j, 0 ≤ secularGamma w j := fun j => by
    unfold secularGamma oscillatorAction; positivity
  obtain ⟨hL, hGL⟩ := h i
  have hch := sb_chart m hm (w := w)
    (fun j => ⟨(h j).1, hG j, by linarith [(h j).2, hG j]⟩) i
  obtain ⟨-, hk0, -, -, he2, he1, -, hF⟩ := hch
  obtain ⟨hJ0, hJ1, hlen, hlo, hhi⟩ := hF F
  have hk : (49/50 : ℝ) < secularRoot w i := by
    have : secularGamma w i / fast w.2 i < 1/50 := by
      rw [div_lt_iff₀ hL]; linarith
    unfold secularRoot; linarith
  have he0 := planeLength_nonneg (secularEccVector w i)
  have he : planeLength (secularEccVector w i) < 1/5 := by
    by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (secularRoot w i - 49/50)]
  have hJ : (4/5 : ℝ) < longitudeJacobian w i F := by linarith
  have haxis : 0 < secularAxis m w i := by
    unfold secularAxis; exact pow_pos (div_pos hL (hm i)) 2
  refine ⟨hk, he, hJ, hlen, hlo, hhi, ?_⟩
  rw [hlen]; exact mul_pos haxis hJ0

theorem sb_s (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    IsOpen (sb_sdef saturn) ∧ ∀ w ∈ sb_sdef saturn, ∀ F : Fin 2 → ℝ,
      (∀ i, (49/50 : ℝ) < secularRoot w i ∧
        planeLength (secularEccVector w i) < 1/5 ∧ (4/5 : ℝ) < longitudeJacobian w i (F i)) ∧
      NoCollision (ellipsePhase (jupiterSaturnWeights saturn) w F).1 := by
  refine ⟨sbRegion_isOpen saturn, ?_⟩
  rintro w ⟨h, ha0, ha0', ha1, ha1'⟩ F
  have hm : ∀ i, 0 < jupiterSaturnWeights saturn i := by
    intro i
    fin_cases i
    · simp [jupiterSaturnWeights]
    · have := hs.1
      simp [jupiterSaturnWeights]; linarith
  have P := sbRegion_planet _ hm h
  refine ⟨fun i => ⟨(P i (F i)).1, (P i (F i)).2.1, (P i (F i)).2.2.1⟩, ?_, ?_⟩
  · intro i
    rw [sbRegion_bodyVector_ellipsePhase]
    exact (P i (F i)).2.2.2.2.2.2
  · -- step `sb-S-3`: radii
    have hq0 : planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) <
        53/10 * (6/5) := by
      obtain ⟨-, he, -, -, -, hhi, -⟩ := P 0 (F 0)
      have hpos : 0 ≤ planeLength (secularEccVector w 0) := planeLength_nonneg _
      calc _ ≤ _ := hhi
        _ < 53/10 * (6/5) := by nlinarith
    have hq1 : 47/5 * (4/5) <
        planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) := by
      obtain ⟨-, he, -, -, hlo, -, -⟩ := P 1 (F 1)
      have hpos : 0 ≤ planeLength (secularEccVector w 1) := planeLength_nonneg _
      calc 47/5 * (4/5 : ℝ) < _ := by nlinarith
        _ ≤ _ := hlo
    have hdiff : 0 < planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1) -
        ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) := by
      have := abs_planeLength_sub_le (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1))
        (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0))
      have := le_abs_self (planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) -
        planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)))
      linarith
    intro i j hij
    rw [sbRegion_bodyVector_ellipsePhase, sbRegion_bodyVector_ellipsePhase]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [planeLength_sub_comm]; exact hdiff
    · exact hdiff
    · exact absurd rfl hij

/-- Radicand margin of step `sb-S-1` of `bpP:p14:sb-S`: on `S`,
`1 - Γ_i / (2 Λ_i) > 99/100` and the radicand of `ρ_i` exceeds `99 / (100 Λ_i)`. -/
theorem sb_s_radicand {w : Phase (2+2)}
    (h : ∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) (i : Fin 2) :
    (99/100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i) ∧
      (99 : ℝ) / (100 * fast w.2 i) <
        (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i := by
  obtain ⟨hL, hGL⟩ := h i
  have hG : 0 ≤ secularGamma w i := by
    unfold secularGamma oscillatorAction; positivity
  have h1 : secularGamma w i / (2 * fast w.2 i) < 1/100 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have h2 : (99/100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i) := by linarith
  refine ⟨h2, ?_⟩
  have : (99 : ℝ) / (100 * fast w.2 i) = (99/100) / fast w.2 i := by
    field_simp
  rw [this]
  exact div_lt_div_of_pos_right h2 hL

/-- Literal conclusion of `bpP:p14:sb-S`: openness; on `S`, ellipticity (`Λ_i > 0`,
`0 ≤ Γ_i < Λ_i`), the radicand margin, `k_i`, `e_i`, `𝒥_i`, the quantitative radii of
`q_0` and `q_1`, their ordering, positivity of `|q_i|` and `|q_0 - q_1|`, and `NoCollision`. -/
theorem sb_s_geometry (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    IsOpen (sb_sdef saturn) ∧ ∀ w ∈ sb_sdef saturn, ∀ F : Fin 2 → ℝ,
      (∀ i, 0 < fast w.2 i ∧ 0 ≤ secularGamma w i ∧ secularGamma w i < fast w.2 i ∧
        (49/50 : ℝ) < secularRoot w i ∧
        (99/100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i) ∧
        (99 : ℝ) / (100 * fast w.2 i) <
          (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i ∧
        planeLength (secularEccVector w i) < 1/5 ∧ (4/5 : ℝ) < longitudeJacobian w i (F i) ∧
        0 < planeLength (ellipsePosition (jupiterSaturnWeights saturn) w i (F i))) ∧
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) < 53/10 * (6/5) ∧
      47/5 * (4/5) <
        planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) ∧
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) <
        planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) ∧
      0 < planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0) -
        ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) ∧
      NoCollision (ellipsePhase (jupiterSaturnWeights saturn) w F).1 := by
  obtain ⟨hopen, hall⟩ := sb_s saturn hs
  refine ⟨hopen, ?_⟩
  intro w hw F
  obtain ⟨h, -⟩ := id hw
  have hm : ∀ i, 0 < jupiterSaturnWeights saturn i := by
    intro i
    fin_cases i
    · simp [jupiterSaturnWeights]
    · have := hs.1
      simp [jupiterSaturnWeights]; linarith
  have P := sbRegion_planet _ hm h
  have hG : ∀ j, 0 ≤ secularGamma w j := fun j => by
    unfold secularGamma oscillatorAction; positivity
  have hq0 : planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) <
      53/10 * (6/5) := by
    obtain ⟨-, he, -, -, -, hhi, -⟩ := P 0 (F 0)
    have hpos : 0 ≤ planeLength (secularEccVector w 0) := planeLength_nonneg _
    have := (hw.2.1)
    have := (hw.2.2.1)
    calc _ ≤ _ := hhi
      _ < 53/10 * (6/5) := by nlinarith
  have hq1 : 47/5 * (4/5) <
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) := by
    obtain ⟨-, he, -, -, hlo, -, -⟩ := P 1 (F 1)
    have hpos : 0 ≤ planeLength (secularEccVector w 1) := planeLength_nonneg _
    have := (hw.2.2.2.1)
    calc 47/5 * (4/5 : ℝ) < _ := by nlinarith
      _ ≤ _ := hlo
  have hlt : planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)) <
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) := by
    linarith
  refine ⟨fun i => ⟨(h i).1, hG i, by linarith [(h i).2, hG i], (P i (F i)).1,
    (sb_s_radicand h i).1, (sb_s_radicand h i).2, (P i (F i)).2.1, (P i (F i)).2.2.1,
    (P i (F i)).2.2.2.2.2.2⟩, hq0, hq1, hlt, ?_, (hall w hw F).2⟩
  have := abs_planeLength_sub_le (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1))
    (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0))
  have := le_abs_self (planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 1 (F 1)) -
    planeLength (ellipsePosition (jupiterSaturnWeights saturn) w 0 (F 0)))
  rw [planeLength_sub_comm]
  linarith

end KAM.Planetary

end
