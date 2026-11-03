/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep

/-!
# Physical (original-coordinate) initial box and action drift (track B, B2-ORIG)

* `stepChart_sub_le`, `stepChartInv_sub_le`: coordinatewise displacement `≤ ε δ` of the real
  chart `Ψ` and its inverse on `realInterior W Ω 1`;
* `stepChart_stepChartInv`: `Ψ (Ψinv z) = z` there;
* `oscillatorAction_sub_le`: perturbation of the oscillator actions;
* `oscillatorStep_physical` (in `OscillatorPhysical/Main`): the physical-coordinate version of
  `oscillatorStep_confinement`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

omit [CertNormLe K ℝ] in
/-- Coordinatewise real displacement of the time-`t` real chart map, `|t| ≤ 1`. -/
theorem realFlow_coord_sub_le {χ : CartPolyK K} (hχ : CartFits n χ) {ρ δ ε : ℝ} (hδ : 0 < δ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (ρl : List ℚ)
    (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∀ i, |(realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) t x).1 i -
        x.1 i| ≤ |t| * ε * δ ∧
      |(realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) t x).2 i -
        x.2 i| ≤ |t| * ε * δ := by
  have hS := smallField_of_supBound hχ hδ ρl hρl hε0 hε hq hp
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cpolyOpen ρ →
      (cartEval χ (KAM.realInclusion₂ n x)).im = 0 := fun x _ => cartEval_realInclusion₂_im χ x
  have h := norm_realFlow_sub_le (isOpen_cpolyOpen ρ) (differentiableOn_cartEval (n := n) χ _)
    hS hreal (realInterior_mono (by norm_num) hx) ht
  rw [norm_gaugeScalar_apply, div_le_iff₀ hδ] at h
  intro i
  set y := realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) t x
  have h1 : ‖(KAM.realInclusion₂ n y - KAM.realInclusion₂ n x).1 i‖ ≤ |t| * ε * δ :=
    (norm_le_pi_norm _ i).trans ((le_max_left _ _).trans (by simpa [Prod.norm_def] using h))
  have h2 : ‖(KAM.realInclusion₂ n y - KAM.realInclusion₂ n x).2 i‖ ≤ |t| * ε * δ :=
    (norm_le_pi_norm _ i).trans ((le_max_right _ _).trans (by simpa [Prod.norm_def] using h))
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, KAM.realInclusion₂_apply,
    KAM.realInclusion_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1 h2
  exact ⟨h1, h2⟩

omit [CertNormLe K ℝ] in
/-- Displacement of the chart `Ψ`: `|Ψ x - x| ≤ ε δ` coordinatewise on `realInterior W Ω 1`. -/
theorem stepChart_sub_le {χ : CartPolyK K} (hχ : CartFits n χ) {ρ δ ε : ℝ} (hδ : 0 < δ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (ρl : List ℚ)
    (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1) :
    ∀ i, |(stepChart χ ρ x).1 i - x.1 i| ≤ ε * δ ∧ |(stepChart χ ρ x).2 i - x.2 i| ≤ ε * δ := by
  intro i
  have := realFlow_coord_sub_le hχ hδ hε0 hε ρl hρl hq hp hx
    (t := 1) ⟨by norm_num, le_rfl⟩ i
  simpa [stepChart] using this

omit [CertNormLe K ℝ] in
/-- Displacement of the inverse chart `Ψinv`: `|Ψinv x - x| ≤ ε δ` coordinatewise. -/
theorem stepChartInv_sub_le {χ : CartPolyK K} (hχ : CartFits n χ) {ρ δ ε : ℝ} (hδ : 0 < δ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (ρl : List ℚ)
    (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1) :
    ∀ i, |(stepChartInv χ ρ x).1 i - x.1 i| ≤ ε * δ ∧
      |(stepChartInv χ ρ x).2 i - x.2 i| ≤ ε * δ := by
  intro i
  have := realFlow_coord_sub_le hχ hδ hε0 hε ρl hρl hq hp hx
    (t := -1) ⟨le_rfl, by norm_num⟩ i
  simpa [stepChartInv] using this

omit [CertNormLe K ℝ] in
/-- `Ψ (Ψinv z) = z` for real `z` in `realInterior W Ω 1`. -/
theorem stepChart_stepChartInv {χ : CartPolyK K} (hχ : CartFits n χ) {ρ δ ε : ℝ} (hδ : 0 < δ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (ρl : List ℚ)
    (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : z ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1) :
    stepChart χ ρ (stepChartInv χ ρ z) = z :=
  realFlow_one_realFlow_neg (isOpen_cpolyOpen ρ) (differentiableOn_cartEval (n := n) χ _)
    (smallField_of_supBound hχ hδ ρl hρl hε0 hε hq hp)
    (fun x _ => cartEval_realInclusion₂_im χ x) hz

/-- Perturbation of oscillator actions: coordinates within `e`, and bounded by `s`, `s'`. -/
theorem oscillatorAction_sub_le (x y : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) {e s s' : ℝ}
    (hq : |x.1 j - y.1 j| ≤ e) (hp : |x.2 j - y.2 j| ≤ e)
    (hxq : |x.1 j| ≤ s) (hxp : |x.2 j| ≤ s) (hyq : |y.1 j| ≤ s') (hyp : |y.2 j| ≤ s') :
    |KAM.Planetary.oscillatorAction x.2 x.1 j - KAM.Planetary.oscillatorAction y.2 y.1 j| ≤
      e * (s + s') := by
  have key : ∀ a b : ℝ, |a - b| ≤ e → |a| ≤ s → |b| ≤ s' → |a ^ 2 - b ^ 2| ≤ e * (s + s') := by
    intro a b hab ha hb
    have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [this, abs_mul]
    exact mul_le_mul hab ((abs_add_le a b).trans (add_le_add ha hb)) (abs_nonneg _)
      ((abs_nonneg _).trans hab)
  have h1 := key _ _ hq hxq hyq
  have h2 := key _ _ hp hxp hyp
  have : KAM.Planetary.oscillatorAction x.2 x.1 j - KAM.Planetary.oscillatorAction y.2 y.1 j =
      ((x.2 j ^ 2 - y.2 j ^ 2) + (x.1 j ^ 2 - y.1 j ^ 2)) / 2 := by
    simp only [KAM.Planetary.oscillatorAction]; ring
  rw [this, abs_div, abs_two]
  have := abs_add_le (x.2 j ^ 2 - y.2 j ^ 2) (x.1 j ^ 2 - y.1 j ^ 2)
  linarith

private theorem coord_abs_le_of_action_le (w : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n)
    {c r : ℝ} (hr : 0 ≤ r) (hc : 2 * c ≤ r ^ 2)
    (h : KAM.Planetary.oscillatorAction w.2 w.1 j ≤ c) : |w.1 j| ≤ r ∧ |w.2 j| ≤ r := by
  simp only [KAM.Planetary.oscillatorAction] at h
  exact ⟨abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.2 j)]) hr,
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.1 j)]) hr⟩

/-- **Physical one-step confinement** (track B, B2-ORIG): the premises of
`oscillatorStep_confinement`, plus a physical initial action box `a'` with radii `s` and a
transfer constant `d`. For every physical `z₀` with actions `≤ a'`, the physical flow exists, is
unique, and the PHYSICAL actions drift by at most `2 d + η |t|` on `|t| ≤ T`. -/
theorem oscillatorStep_physical {H χ Nact P : CartPolyK K}
    (hH : CartFits n H) (hχ : CartFits n χ) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    {ρ δ δc ε : ℝ} (hδ : 0 < δ) (hδc : 0 < δc) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom2 : ∀ i, r i + δ < ρ)
    (hdom3 : ∀ i, r i + δc + δ / 2 < ρ)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) /
        ((L.factorial : ℝ) * δc))
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' s d : Fin n → ℝ) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, 2 * a' i ≤ s i ^ 2)
    (hs2 : ∀ i, s i + ε * δ + δ < ρ) (hs3 : ∀ i, (s i + ε * δ) ^ 2 ≤ a i)
    (hd : ∀ j, ε * δ * (2 * r j + ε * δ) ≤ d j)
    (z₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ a' j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j,
        |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
            KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 2 * d j + η j * |t| ∧
          KAM.Planetary.oscillatorAction (z t).2 (z t).1 j ≤ a j + η j * T + d j := by
  have hεδ : 0 ≤ ε * δ := mul_nonneg hε0 hδ.le
  have hb2 : ∀ i, 2 * b i ≤ r i ^ 2 := fun i => by linarith [hdom1 i]
  -- the physical datum lies in the real interior
  have hz₀c : ∀ j, |z₀.1 j| ≤ s j ∧ |z₀.2 j| ≤ s j := fun j =>
    coord_abs_le_of_action_le z₀ j (hs0 j) (hs1 j) (hz₀ j)
  have hz₀I : z₀ ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 :=
    mem_realInterior_cpolyOpen hδ (fun i => by linarith [hs2 i]) hz₀c
  set w₀ := stepChartInv χ ρ z₀ with hw₀def
  have hdisp0 := stepChartInv_sub_le hχ hδ hε0 hε ρl hρl hq hp hz₀I
  have hΨw₀ : stepChart χ ρ w₀ = z₀ := stepChart_stepChartInv hχ hδ hε0 hε ρl hρl hq hp hz₀I
  have hw₀c : ∀ j, |w₀.1 j| ≤ s j + ε * δ ∧ |w₀.2 j| ≤ s j + ε * δ := fun j => by
    have h1 := hdisp0 j
    have h2 := hz₀c j
    have e1 : |w₀.1 j| ≤ |z₀.1 j| + |w₀.1 j - z₀.1 j| := by
      simpa using abs_add_le (z₀.1 j) (w₀.1 j - z₀.1 j)
    have e2 : |w₀.2 j| ≤ |z₀.2 j| + |w₀.2 j - z₀.2 j| := by
      simpa using abs_add_le (z₀.2 j) (w₀.2 j - z₀.2 j)
    constructor <;> linarith [h1.1, h1.2]
  have hw₀a : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j := fun j => by
    have h1 := hw₀c j
    have h3 := hs3 j
    have q1 : w₀.1 j ^ 2 ≤ (s j + ε * δ) ^ 2 :=
      sq_le_sq' (by linarith [abs_le.1 h1.1]) (by linarith [abs_le.1 h1.1])
    have q2 : w₀.2 j ^ 2 ≤ (s j + ε * δ) ^ 2 :=
      sq_le_sq' (by linarith [abs_le.1 h1.2]) (by linarith [abs_le.1 h1.2])
    simp only [KAM.Planetary.oscillatorAction]
    linarith
  obtain ⟨T₁, hT₁, z, hz0, hode, huniq, hb⟩ := oscillatorStep_confinement hH hχ hN hP hA hL hid
    hδ hδc hε0 hε ρl hρl hq hp a b η εb T hεb hT rl r hrl hr0 hdom1 hdom2 hdom3 hη hdrift hmargin
    w₀ hw₀a
  rw [hΨw₀] at hz0
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := mul_nonneg hT (hη j)
    linarith [hmargin j]
  refine ⟨T₁, hT₁, z, hz0, hode, fun I y hI h0 hy0 hyd t htI htT => huniq I y hI h0
    (by rw [hΨw₀]; exact hy0) hyd t htI htT, fun t ht j => ?_⟩
  obtain ⟨hinv, hbd⟩ := hb t ht
  set u := stepChartInv χ ρ (z t) with hu
  have hbj : ∀ k, KAM.Planetary.oscillatorAction u.2 u.1 k ≤ b k := fun k => by
    have := (hbd k).2
    have h2 := mul_le_mul_of_nonneg_left ht (hη k)
    have h3 := hmargin k
    nlinarith [mul_comm T (η k)]
  have huI : u ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 :=
    oscClosed_subset_realInterior hδ hb2 hr0 hdom2 hbj
  have hdispu := stepChart_sub_le hχ hδ hε0 hε ρl hρl hq hp huI
  rw [show stepChart χ ρ u = z t from hinv] at hdispu
  have huc := coord_abs_le_of_action_le u j (hr0 j) (hb2 j) (hbj j)
  have hztc : |(z t).1 j| ≤ r j + ε * δ ∧ |(z t).2 j| ≤ r j + ε * δ := by
    have h1 := hdispu j
    have e1 : |(z t).1 j| ≤ |u.1 j| + |(z t).1 j - u.1 j| := by
      simpa using abs_add_le (u.1 j) ((z t).1 j - u.1 j)
    have e2 : |(z t).2 j| ≤ |u.2 j| + |(z t).2 j - u.2 j| := by
      simpa using abs_add_le (u.2 j) ((z t).2 j - u.2 j)
    constructor <;> linarith [h1.1, h1.2, huc.1, huc.2]
  have hw₀r := coord_abs_le_of_action_le w₀ j (hr0 j) (hb2 j)
    ((hw₀a j).trans (hab j))
  have hz₀r : |z₀.1 j| ≤ r j + ε * δ ∧ |z₀.2 j| ≤ r j + ε * δ := by
    have h1 := hdisp0 j
    have e1 : |z₀.1 j| ≤ |w₀.1 j| + |w₀.1 j - z₀.1 j| := by
      have := abs_add_le (w₀.1 j) (z₀.1 j - w₀.1 j)
      rw [abs_sub_comm (z₀.1 j) (w₀.1 j)] at this; simpa using this
    have e2 : |z₀.2 j| ≤ |w₀.2 j| + |w₀.2 j - z₀.2 j| := by
      have := abs_add_le (w₀.2 j) (z₀.2 j - w₀.2 j)
      rw [abs_sub_comm (z₀.2 j) (w₀.2 j)] at this; simpa using this
    constructor <;> linarith [h1.1, h1.2, hw₀r.1, hw₀r.2]
  have hdj := hd j
  have p1 := oscillatorAction_sub_le (e := ε * δ) (z t) u j (hdispu j).1 (hdispu j).2
    hztc.1 hztc.2 huc.1 huc.2
  have p2 := oscillatorAction_sub_le (e := ε * δ) z₀ w₀ j (by rw [abs_sub_comm]; exact (hdisp0 j).1)
    (by rw [abs_sub_comm]; exact (hdisp0 j).2) hz₀r.1 hz₀r.2 hw₀r.1 hw₀r.2
  have hc := hbd j
  have e3 : ε * δ * (r j + ε * δ + r j) = ε * δ * (2 * r j + ε * δ) := by ring
  rw [e3] at p1 p2
  have p1' := abs_le.1 (p1.trans hdj)
  have p2' := abs_le.1 (p2.trans hdj)
  have c1 := abs_le.1 hc.1
  constructor
  · rw [abs_le]; constructor <;> nlinarith [c1.1, c1.2, p1'.1, p1'.2, p2'.1, p2'.2]
  · nlinarith [hc.2, p1'.2]

end KAM.EffectiveStability

end
