/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularBox.Numerics
public import KAM.Planetary.SecularBox.Chart
public import KAM.Planetary.SecularBox.Region
public import KAM.Planetary.SecularBox.Smooth
public import KAM.Planetary.SecularBox.GlobalFlow
public import KAM.Planetary.SecularBox.Uniqueness
public import KAM.Planetary.Newtonian.Barycentric
public import KAM.Frozen.Planetary.Defs.SecularInputBox
public import KAM.Frozen.Planetary.Defs.SecularRegular
public import KAM.Frozen.Planetary.Defs.PairBounds

/-!
# Safety of the secular box

`sb_safety` (blueprint `bpP:p14:sb-safety`): the exact frozen type of `secularBoxSafety`, proved by
the ordinary library assembly. Steps `sb-th-1`..`sb-th-11` are internal: actions and axes
(`sbSafety_actions`), initial AMD and membership in `S` (`sbSafety_amd`, `sbSafety_mem`), the global
flow and uniqueness (`sb_global`, `sb_unique`), eccentricities (`sbSafety_ecc`), regularity
(`sb_smooth_prop`), the bridge (`sbSafety_bridge`), radii and gap (`sbSafety_rad`) and the pair
bounds (barycentric differences).
-/

public section

open Set
open KAM.Kepler

namespace KAM.Planetary

private theorem sbSafety_lt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ hb hc 2
  linarith

private theorem sbSafety_hm (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ∀ i, 0 < jupiterSaturnWeights saturn i := by
  intro i
  fin_cases i
  · simp [jupiterSaturnWeights]
  · have := hs.1
    simp [jupiterSaturnWeights]; linarith

/-- Step `sb-th-1`: actions and axes. -/
private theorem sbSafety_actions (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (h : SecularInputBox saturn w0) :
    (87/100 : ℝ) < fast w0.2 0 ∧ fast w0.2 0 < 23/10 ∧
      (87/100 : ℝ) < fast w0.2 1 ∧ fast w0.2 1 < 97/100 := by
  obtain ⟨hG, a0l, a0u, a1l, a1u, -, -⟩ := h
  have hs0 := hs.1
  have hs1 := hs.2
  have hspos : 0 < saturn := by linarith
  have e0 : secularAxis (jupiterSaturnWeights saturn) w0 0 = fast w0.2 0 ^ 2 := by
    simp [secularAxis, jupiterSaturnWeights]
  have e1 : fast w0.2 1 ^ 2 = saturn ^ 2 * secularAxis (jupiterSaturnWeights saturn) w0 1 := by
    simp only [secularAxis, jupiterSaturnWeights]
    field_simp
    simp
  have hL0 := (hG 0).1
  have hL1 := (hG 1).1
  have hs2 : (29/100 : ℝ) ^ 2 ≤ saturn ^ 2 := pow_le_pow_left₀ (by norm_num) hs0 2
  have hs3 : saturn ^ 2 ≤ (31/100 : ℝ) ^ 2 := pow_le_pow_left₀ hspos.le hs1 2
  have lo1 : (29/100 : ℝ) ^ 2 * (189/20) ≤ fast w0.2 1 ^ 2 := by
    rw [e1]; exact mul_le_mul hs2 a1l (by norm_num) (by positivity)
  have hi1 : fast w0.2 1 ^ 2 ≤ (31/100 : ℝ) ^ 2 * (193/20) := by
    rw [e1]; exact mul_le_mul hs3 a1u (by linarith) (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sbSafety_lt_of_sq hL0.le (by rw [← e0] at *; norm_num at a0l ⊢; linarith)
  · exact sbSafety_lt_of_sq (by norm_num) (by rw [← e0] at a0u; norm_num at a0u ⊢; linarith)
  · exact sbSafety_lt_of_sq hL1.le (by norm_num at lo1 ⊢; linarith)
  · exact sbSafety_lt_of_sq (by norm_num) (by norm_num at hi1 ⊢; linarith)

/-- Per-planet bound of step `sb-th-2`: `Γ < c (1 - d)` from `e ≤ ec`, `d² < 1 - ec²`. -/
private theorem sbSafety_gamma_lt {L c Γ k e ec d : ℝ} (hL : 0 < L) (hLc : L < c)
    (hΓ : Γ = L * (1 - k)) (hk0 : 0 < k) (hk1 : k ≤ 1) (he2 : e ^ 2 = 1 - k ^ 2) (he0 : 0 ≤ e)
    (hec : e ≤ ec) (hd : d ^ 2 < 1 - ec ^ 2) : Γ < c * (1 - d) := by
  have he : e ^ 2 ≤ ec ^ 2 := pow_le_pow_left₀ he0 hec 2
  have hkd : d < k := sbSafety_lt_of_sq hk0.le (by linarith)
  have h1 : L * (1 - k) ≤ c * (1 - k) :=
    mul_le_mul_of_nonneg_right hLc.le (by linarith)
  have h2 : c * (1 - k) < c * (1 - d) := mul_lt_mul_of_pos_left (by linarith) (by linarith)
  linarith

/-- Step `sb-th-2`: initial AMD. -/
private theorem sbSafety_amd (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (h : SecularInputBox saturn w0) (hL0 : fast w0.2 0 < 23/10)
    (hL1 : fast w0.2 1 < 97/100) : secularAMD w0 < (16373/2500000 : ℝ) := by
  have hm := sbSafety_hm saturn hs
  have hch := sb_chart _ hm h.1
  obtain ⟨-, hk0, hk1, -, he2, -, hΓ, -⟩ := hch 0
  obtain ⟨-, hk0', hk1', -, he2', -, hΓ', -⟩ := hch 1
  have g0 := sbSafety_gamma_lt (h.1 0).1 hL0 hΓ hk0 hk1 he2 (planeLength_nonneg _) h.2.2.2.2.2.1
    (d := 99819/100000) (by norm_num)
  have g1 := sbSafety_gamma_lt (h.1 1).1 hL1 hΓ' hk0' hk1' he2' (planeLength_nonneg _)
    h.2.2.2.2.2.2 (d := 49877/50000) (by norm_num)
  unfold secularAMD
  rw [Fin.sum_univ_two]
  norm_num at g0 g1 ⊢
  linarith

/-- Step `sb-th-3`: `w₀ ∈ S`. -/
private theorem sbSafety_mem (saturn : ℝ) {w0 : Phase (2+2)} (h : SecularInputBox saturn w0)
    (hL0 : (87/100 : ℝ) < fast w0.2 0) (hL1 : (87/100 : ℝ) < fast w0.2 1)
    (hA : secularAMD w0 < (16373/2500000 : ℝ)) : w0 ∈ sb_sdef saturn := by
  obtain ⟨hG, a0l, a0u, a1l, a1u, -, -⟩ := h
  have hsum : secularGamma w0 0 + secularGamma w0 1 < 16373/2500000 := by
    unfold secularAMD at hA; rwa [Fin.sum_univ_two] at hA
  refine ⟨?_, by linarith, by linarith, by linarith, by linarith⟩
  intro i
  refine ⟨(hG i).1, ?_⟩
  fin_cases i
  · have := (hG 1).2.1; have := (hG 0).2.1
    show 50 * secularGamma w0 0 < fast w0.2 0
    linarith
  · have := (hG 0).2.1; have := (hG 1).2.1
    show 50 * secularGamma w0 1 < fast w0.2 1
    linarith

/-- Step `sb-th-6`: eccentricity bound from conserved actions. -/
private theorem sbSafety_ecc {L Γ k e : ℝ} (hL : 87/100 < L) (hΓ : Γ = L * (1 - k))
    (hA : Γ < 16373/2500000) (he2 : e ^ 2 = 1 - k ^ 2) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    e < 3/20 := by
  have h1 : (2481/2500 : ℝ) < k := by
    by_contra hc
    push Not at hc
    have : 87/100 * (1 - k) ≤ L * (1 - k) :=
      mul_le_mul_of_nonneg_right hL.le (by linarith)
    linarith
  have h2 : (2481/2500 : ℝ) ^ 2 < k ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) two_ne_zero
  exact sbSafety_lt_of_sq (by norm_num) (by norm_num at h2 ⊢; linarith)

/-- Steps `sb-th-9`, `sb-th-10`: radial bounds from the axis range and `e < 3/20`. -/
private theorem sbSafety_rad {a e q alo ahi : ℝ} (ha0 : 0 < alo) (h1 : alo ≤ a) (h2 : a ≤ ahi)
    (he0 : 0 ≤ e) (he : e < 3/20) (hl : a * (1 - e) ≤ q) (hu : q ≤ a * (1 + e)) :
    alo * (17/20) ≤ q ∧ q ≤ ahi * (23/20) := by
  have ha : 0 ≤ a := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (show 17/20 ≤ 1 - e by linarith) ha]
  · nlinarith [mul_le_mul_of_nonneg_left (show 1 + e ≤ 23/20 by linarith) ha]

/-- Step `sb-th-8`: bridge from `z(w;F)₁` to `q_i(w;F_i)`. -/
private theorem sbSafety_bridge (m : Fin 2 → ℝ) (w : Phase (2+2)) (F : Fin 2 → ℝ) (i : Fin 2) :
    bodyVector (ellipsePhase m w F).1 i = ellipsePosition m w i (F i) := by
  funext k
  simp [bodyVector, ellipsePhase]

theorem sb_safety (saturn mu : ℝ)
    (hsaturn : saturn ∈ Set.Icc (29 / 100 : ℝ) (31 / 100)) (hmu : 0 < mu)
    (w0 : Phase (2 + 2)) (hw0 : SecularInputBox saturn w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights saturn) mu (v t)) →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights saturn) mu (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights saturn) mu
              (ellipsePhase (jupiterSaturnWeights saturn) (w t) F).1) := by
  have hm := sbSafety_hm saturn hsaturn
  obtain ⟨hL0, hL0', hL1, hL1'⟩ := sbSafety_actions saturn hsaturn hw0
  have hA := sbSafety_amd saturn hsaturn hw0 hL0' hL1'
  have hS0 := sbSafety_mem saturn hw0 hL0 hL1 hA
  obtain ⟨w, hw00, hwsol, hwall⟩ := sb_global saturn mu hsaturn hS0 hA
    (Fin.forall_fin_two.2 ⟨hL0, hL1⟩)
  refine ⟨w, hw00, hwsol, ?_, ?_⟩
  · intro U v hU hUc h0 hv0 hv _
    exact sb_unique saturn mu hsaturn hwsol (fun t => (hwall t).1) hU hUc h0
      (hv0.trans hw00.symm) hv
  intro t
  obtain ⟨hSt, hfast, hamd⟩ := hwall t
  have hLt : ∀ i, fast (w t).2 i = fast w0.2 i := fun i => by rw [hfast]
  have hLw : ∀ i, (87/100 : ℝ) < fast (w t).2 i := fun i => by
    rw [hLt]; exact Fin.forall_fin_two.2 ⟨hL0, hL1⟩ i
  have hG : ∀ j, 0 ≤ secularGamma (w t) j := fun j => by
    unfold secularGamma oscillatorAction; positivity
  have hsum : secularGamma (w t) 0 + secularGamma (w t) 1 < 16373/2500000 := by
    have := hamd ▸ hA
    unfold secularAMD at this; rwa [Fin.sum_univ_two] at this
  have hΓlt : ∀ j, secularGamma (w t) j < 16373/2500000 := by
    intro j; fin_cases j
    · have := hG 1; show secularGamma (w t) 0 < _; linarith
    · have := hG 0; show secularGamma (w t) 1 < _; linarith
  have hch := sb_chart _ hm (w := w t)
    (fun j => ⟨(hSt.1 j).1, hG j, by linarith [(hSt.1 j).2, hG j]⟩)
  have hecc : ∀ i, planeLength (secularEccVector (w t) i) < 3/20 := fun i => by
    obtain ⟨-, hk0, hk1, -, he2, -, hΓ, -⟩ := hch i
    exact sbSafety_ecc (hLw i) hΓ (hΓlt i) he2 hk0 hk1
  have hax : ∀ i, secularAxis (jupiterSaturnWeights saturn) (w t) i =
      secularAxis (jupiterSaturnWeights saturn) w0 i := fun i => by
    unfold secularAxis; rw [hLt]
  have hrad : ∀ (i : Fin 2) (F : ℝ) (alo ahi : ℝ), 0 < alo →
      alo ≤ secularAxis (jupiterSaturnWeights saturn) w0 i →
      secularAxis (jupiterSaturnWeights saturn) w0 i ≤ ahi →
      alo * (17/20) ≤ planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i F) ∧
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i F) ≤ ahi * (23/20) := by
    intro i F alo ahi ha0 h1 h2
    obtain ⟨-, -, -, -, -, -, -, hF⟩ := hch i
    obtain ⟨-, -, -, hlo, hhi⟩ := hF F
    rw [hax] at hlo hhi
    exact sbSafety_rad ha0 h1 h2 (planeLength_nonneg _) (hecc i) hlo hhi
  obtain ⟨-, a0l, a0u, a1l, a1u, -, -⟩ := hw0
  have hq0 := fun F => hrad 0 F _ _ (by norm_num) a0l a0u
  have hq1 := fun F => hrad 1 F _ _ (by norm_num) a1l a1u
  refine ⟨(sb_smooth_prop saturn mu hsaturn).2.1 (w t) hSt, hfast, hamd, hamd ▸ hA, hecc, ?_⟩
  intro F
  have hr : ∀ i, (1751 / 400 : ℝ) ≤
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ∧
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ≤
        (4439 / 400 : ℝ) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have := hq0 (F 0); constructor <;> linarith [this.1, this.2]
    · have := hq1 (F 1); constructor <;> linarith [this.1, this.2]
  have hgap : (399 / 200 : ℝ) ≤
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 1 (F 1)) -
      planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 0 (F 0)) := by
    linarith [(hq0 (F 0)).2, (hq1 (F 1)).1]
  refine ⟨hr, hgap, ?_⟩
  set b : Fin 2 → (Fin 2 → ℝ) := fun j =>
    ellipsePosition (jupiterSaturnWeights saturn) (w t) j (F j) with hb
  have hpp : ∀ a c : Fin 2, a ≠ c → (399 / 200 : ℝ) ≤ planeLength (b c - b a) ∧
      planeLength (b c - b a) ≤ 4439 / 200 := by
    have key : (399 / 200 : ℝ) ≤ planeLength (b 1 - b 0) ∧ planeLength (b 1 - b 0) ≤ 4439 / 200 := by
      have h1 := abs_planeLength_sub_le (b 1) (b 0)
      have h2 := le_abs_self (planeLength (b 1) - planeLength (b 0))
      have h3 := planeLength_add_le (b 1) (-b 0)
      rw [planeLength_neg, ← sub_eq_add_neg] at h3
      have h4 := hq0 (F 0)
      have h5 := hr 1
      refine ⟨by linarith, ?_⟩
      have : planeLength (b 0) ≤ 4439 / 400 := by
        have := (hq0 (F 0)).2; simp only [hb]; linarith
      have h6 := (hr 1).2
      simp only [hb] at h3 ⊢
      linarith
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => key⟩,
      Fin.forall_fin_two.2 ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
    rw [planeLength_sub_comm]; exact key
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · exact absurd rfl hij
  · rw [barycentricPositions_succ_sub_zero, sbSafety_bridge]
    have := hr j'
    constructor <;> linarith [this.1, this.2]
  · rw [planeLength_sub_comm, barycentricPositions_succ_sub_zero, sbSafety_bridge]
    have := hr i'
    constructor <;> linarith [this.1, this.2]
  · rw [barycentricPositions_succ_sub_succ, sbSafety_bridge, sbSafety_bridge]
    exact hpp i' j' fun h => hij (by rw [h])

end KAM.Planetary

end
