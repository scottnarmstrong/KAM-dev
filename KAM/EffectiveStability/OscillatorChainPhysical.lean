/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain
public import KAM.EffectiveStability.OscillatorPhysical

/-!
# Physical initial box and physical action drift for `m`-generator charts (track B, B2-ORIGCHAIN)

Combines `OscillatorPhysical` (B2-ORIG) with `OscillatorChain` (B2-MULTI).

* `oscChainMap_sub_le`, `oscChainInv_sub_le`: coordinatewise displacement `≤ oscTail l` of the
  chain chart and its inverse; `oscChainMap_oscChainInv`: `Ψ (Ψinv z) = z` on the physical box
  (domain recorded by `OscPhysDom`);
* `oscillatorChain_physical`: physical-coordinate version of `oscillatorChain_confinement`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- Radius budget of the inverse chain started on `|z_i| ≤ s i + c`: before step `k` the
coordinates are at most `s i + (∑_{j<k} ε_j δ_j)`, which must fit the real chart domain. -/
def OscPhysDom (n : ℕ) (s : Fin n → ℝ) : List (OscStepK K) → ℝ → Prop
  | [], _ => True
  | st :: l, c => (∀ i, s i + c + (st.δ : ℝ) < (st.ρ : ℝ)) ∧
      OscPhysDom n s l (c + (st.ε : ℝ) * (st.δ : ℝ))

section Step

variable {st : OscStepK K}

omit [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ]
  [CertNormLe K ℂ] in
private theorem oscStep_cast :
    ∀ i : Fin n, (((List.replicate n st.ρ).getD i 0 : ℚ) : ℝ) = (st.ρ : ℝ) := fun i => by
  rw [replicate_getD_oscRad]

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
private theorem oscStep_epsHalf (hs : OscStepOK n st) : (st.ε : ℝ) ≤ 1 / 2 := by
  have h : ((st.ε : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 hs.ε_le
  simpa using h

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
private theorem oscStep_eps0 (hs : OscStepOK n st) : (0 : ℝ) ≤ (st.ε : ℝ) := by
  exact_mod_cast hs.ε_nonneg

omit [CertNormLe K ℝ] in
/-- Displacement of one step chart. -/
theorem oscStep_chart_sub_le (hs : OscStepOK n st) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar (st.δ : ℝ) hs.delta_posℝ) (cpolyOpen (st.ρ : ℝ)) 1) :
    ∀ i, |(stepChart st.gen (st.ρ : ℝ) x).1 i - x.1 i| ≤ (st.ε : ℝ) * (st.δ : ℝ) ∧
      |(stepChart st.gen (st.ρ : ℝ) x).2 i - x.2 i| ≤ (st.ε : ℝ) * (st.δ : ℝ) :=
  stepChart_sub_le hs.fits_gen hs.delta_posℝ (oscStep_eps0 hs) (oscStep_epsHalf hs)
    (List.replicate n st.ρ) oscStep_cast (fun i => by exact_mod_cast hs.bound_q i)
    (fun i => by exact_mod_cast hs.bound_p i) hx

omit [CertNormLe K ℝ] in
/-- Displacement of one inverse step chart. -/
theorem oscStep_inv_sub_le (hs : OscStepOK n st) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar (st.δ : ℝ) hs.delta_posℝ) (cpolyOpen (st.ρ : ℝ)) 1) :
    ∀ i, |(stepChartInv st.gen (st.ρ : ℝ) x).1 i - x.1 i| ≤ (st.ε : ℝ) * (st.δ : ℝ) ∧
      |(stepChartInv st.gen (st.ρ : ℝ) x).2 i - x.2 i| ≤ (st.ε : ℝ) * (st.δ : ℝ) :=
  stepChartInv_sub_le hs.fits_gen hs.delta_posℝ (oscStep_eps0 hs) (oscStep_epsHalf hs)
    (List.replicate n st.ρ) oscStep_cast (fun i => by exact_mod_cast hs.bound_q i)
    (fun i => by exact_mod_cast hs.bound_p i) hx

omit [CertNormLe K ℝ] in
theorem oscStep_chart_chartInv (hs : OscStepOK n st) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar (st.δ : ℝ) hs.delta_posℝ) (cpolyOpen (st.ρ : ℝ)) 1) :
    stepChart st.gen (st.ρ : ℝ) (stepChartInv st.gen (st.ρ : ℝ) x) = x :=
  stepChart_stepChartInv hs.fits_gen hs.delta_posℝ (oscStep_eps0 hs) (oscStep_epsHalf hs)
    (List.replicate n st.ρ) oscStep_cast (fun i => by exact_mod_cast hs.bound_q i)
    (fun i => by exact_mod_cast hs.bound_p i) hx

end Step

private theorem abs_sub_add_le {a b c e f : ℝ} (h1 : |a - b| ≤ e) (h2 : |b - c| ≤ f) :
    |a - c| ≤ e + f := by
  have := abs_add_le (a - b) (b - c)
  simp only [sub_add_sub_cancel] at this
  linarith

variable {r : Fin n → ℝ} {δc : ℝ}

omit [CertNormLe K ℝ] in
/-- Displacement of the chain chart: `|Ψ x - x| ≤ ∑ ε_k δ_k` coordinatewise on `oscBox r 0`. -/
theorem oscChainMap_sub_le : ∀ {l : List (OscStepK K)}, (∀ st ∈ l, OscStepOK n st) →
    OscDomOK n r δc l → ∀ {x : (Fin n → ℝ) × (Fin n → ℝ)}, x ∈ oscBox r 0 →
    ∀ i, |(oscChainMap l x).1 i - x.1 i| ≤ (oscTail l : ℝ) ∧
      |(oscChainMap l x).2 i - x.2 i| ≤ (oscTail l : ℝ)
  | [], _, _, x, _ => fun i => by simp [oscChainMap, oscTail]
  | st :: l, hl, hdom, x, hx => fun i => by
    obtain ⟨h1, -, h3⟩ := hdom
    have hl' : ∀ t ∈ l, OscStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl st (by simp)
    have hy : oscChainMap l x ∈ oscBox r (oscTail l : ℝ) :=
      (oscChain_isCanonical hl' h3).chart_maps hx
    have hyI := oscBox_subset_realInterior hs h1 hy
    have hA := oscStep_chart_sub_le hs hyI i
    have hB := oscChainMap_sub_le hl' h3 hx i
    have e : (oscTail (st :: l) : ℝ) = (st.ε : ℝ) * (st.δ : ℝ) + (oscTail l : ℝ) := by
      simp only [oscTail]; push_cast; ring
    rw [e]
    exact ⟨abs_sub_add_le hA.1 hB.1, abs_sub_add_le hA.2 hB.2⟩

omit [CertNormLe K ℝ] in
/-- Displacement of the inverse chain chart and the inverse property, on coordinates
`|z_i| ≤ s i + c` within the budget `OscPhysDom`. -/
theorem oscChainInv_sub_le {s : Fin n → ℝ} : ∀ {l : List (OscStepK K)}, (∀ st ∈ l, OscStepOK n st) →
    ∀ {c : ℝ} {z : (Fin n → ℝ) × (Fin n → ℝ)}, OscPhysDom n s l c →
    (∀ i, |z.1 i| ≤ s i + c ∧ |z.2 i| ≤ s i + c) →
    (∀ i, |(oscChainInv l z).1 i - z.1 i| ≤ (oscTail l : ℝ) ∧
      |(oscChainInv l z).2 i - z.2 i| ≤ (oscTail l : ℝ)) ∧
    oscChainMap l (oscChainInv l z) = z
  | [], _, c, z, _, _ => by simp [oscChainInv, oscChainMap, oscTail]
  | st :: l, hl, c, z, hdom, hz => by
    obtain ⟨h1, h2⟩ := hdom
    have hl' : ∀ t ∈ l, OscStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl st (by simp)
    have hzI : z ∈ realInterior (gaugeScalar (st.δ : ℝ) hs.delta_posℝ) (cpolyOpen (st.ρ : ℝ))
        1 := mem_realInterior_cpolyOpen hs.delta_posℝ (r := fun i => s i + c) h1 hz
    set z' := stepChartInv st.gen (st.ρ : ℝ) z with hz'
    have hA := oscStep_inv_sub_le hs hzI
    have hz'c : ∀ i, |z'.1 i| ≤ s i + (c + (st.ε : ℝ) * (st.δ : ℝ)) ∧
        |z'.2 i| ≤ s i + (c + (st.ε : ℝ) * (st.δ : ℝ)) := fun i => by
      have a1 : |z'.1 i| ≤ |z.1 i| + |z'.1 i - z.1 i| := by
        simpa using abs_add_le (z.1 i) (z'.1 i - z.1 i)
      have a2 : |z'.2 i| ≤ |z.2 i| + |z'.2 i - z.2 i| := by
        simpa using abs_add_le (z.2 i) (z'.2 i - z.2 i)
      constructor <;> linarith [(hA i).1, (hA i).2, (hz i).1, (hz i).2]
    obtain ⟨hB, hC⟩ := oscChainInv_sub_le hl' h2 hz'c
    have e : (oscTail (st :: l) : ℝ) = (st.ε : ℝ) * (st.δ : ℝ) + (oscTail l : ℝ) := by
      simp only [oscTail]; push_cast; ring
    refine ⟨fun i => ?_, ?_⟩
    · rw [e]
      have c1 := abs_sub_add_le (hB i).1 (hA i).1
      have c2 := abs_sub_add_le (hB i).2 (hA i).2
      change |(oscChainInv l z').1 i - z.1 i| ≤ _ ∧ |(oscChainInv l z').2 i - z.2 i| ≤ _
      constructor <;> linarith
    · show stepChart st.gen (st.ρ : ℝ) (oscChainMap l (oscChainInv l z')) = z
      rw [hC]
      exact oscStep_chart_chartInv hs hzI

private theorem chainCoord_abs_le (w : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n)
    {c r : ℝ} (hr : 0 ≤ r) (hc : 2 * c ≤ r ^ 2)
    (h : KAM.Planetary.oscillatorAction w.2 w.1 j ≤ c) : |w.1 j| ≤ r ∧ |w.2 j| ≤ r := by
  simp only [KAM.Planetary.oscillatorAction] at h
  exact ⟨abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.2 j)]) hr,
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.1 j)]) hr⟩

private theorem chain_coord_add {x y : ℝ} {e R : ℝ} (h : |x - y| ≤ e) (hy : |y| ≤ R) :
    |x| ≤ R + e := by
  have : |x| ≤ |y| + |x - y| := by simpa using abs_add_le y (x - y)
  linarith

/-- **Shared tail of the physical theorems** (track B, B3-CHAINK): the proof of
`oscillatorChain_physical` with the bound on the chart action of `w₀ = Ψinv z₀` taken as the
hypothesis `hchart` (every point within `oscTail l` coordinatewise of `z₀` has actions `≤ a`)
instead of the inequality `hs3`. -/
theorem oscillatorChain_physical_core {H Nact P : CartPolyK K}
    (hH : CartFits n H) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {l : List (OscStepK K)} (hok : OscChainOK n Nact P l H)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom : OscDomOK n r δc l)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' s d : Fin n → ℝ) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, 2 * a' i ≤ s i ^ 2)
    (hs2 : OscPhysDom n s l 0)
    (hd : ∀ j, (oscTail l : ℝ) * (2 * r j + (oscTail l : ℝ)) ≤ d j)
    (z₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ a' j)
    (hchart : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ i, |w.1 i - z₀.1 i| ≤ (oscTail l : ℝ) ∧ |w.2 i - z₀.2 i| ≤ (oscTail l : ℝ)) →
      ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j ≤ a j) :
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
  have hl := hok.stepsOK
  set e : ℝ := (oscTail l : ℝ) with he
  have hb2 : ∀ i, 2 * b i ≤ r i ^ 2 := fun i => by linarith [hdom1 i, hεb]
  have hz₀c : ∀ j, |z₀.1 j| ≤ s j + 0 ∧ |z₀.2 j| ≤ s j + 0 := fun j => by
    have := chainCoord_abs_le z₀ j (hs0 j) (hs1 j) (hz₀ j)
    simpa using this
  obtain ⟨hdisp0, hΨw₀⟩ := oscChainInv_sub_le hl hs2 hz₀c
  set w₀ := oscChainInv l z₀ with hw₀def
  have hw₀a : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j := hchart w₀ hdisp0
  obtain ⟨T₁, hT₁, z, hz0, hode, huniq, hb⟩ := oscillatorChain_confinement hH hN hP hA hok hδc
    a b η εb T hεb hT rl r hrl hr0 hdom1 hdom hη hdrift hmargin w₀ hw₀a
  rw [hΨw₀] at hz0
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := mul_nonneg hT (hη j)
    linarith [hmargin j]
  refine ⟨T₁, hT₁, z, hz0, hode, fun I y hI h0 hy0 hyd t htI htT => huniq I y hI h0
    (by rw [hΨw₀]; exact hy0) hyd t htI htT, fun t ht j => ?_⟩
  obtain ⟨hinv, hbd⟩ := hb t ht
  set u := oscChainInv l (z t) with hu
  have hbj : ∀ k, KAM.Planetary.oscillatorAction u.2 u.1 k ≤ b k := fun k => by
    have := (hbd k).2
    have h2 := mul_le_mul_of_nonneg_left ht (hη k)
    have h3 := hmargin k
    nlinarith [mul_comm T (η k)]
  have huI : u ∈ oscBox r 0 := osc_subset_oscBox hdom1 hr0 (fun k => by
    have := hbj k
    linarith)
  have hdispu := oscChainMap_sub_le hl hdom huI
  rw [show oscChainMap l u = z t from hinv] at hdispu
  have huc := chainCoord_abs_le u j (hr0 j) (hb2 j) (hbj j)
  have hztc : |(z t).1 j| ≤ r j + e ∧ |(z t).2 j| ≤ r j + e :=
    ⟨chain_coord_add (hdispu j).1 huc.1, chain_coord_add (hdispu j).2 huc.2⟩
  have hw₀r := chainCoord_abs_le w₀ j (hr0 j) (hb2 j) ((hw₀a j).trans (hab j))
  have hz₀r : |z₀.1 j| ≤ r j + e ∧ |z₀.2 j| ≤ r j + e :=
    ⟨chain_coord_add (by rw [abs_sub_comm]; exact (hdisp0 j).1) hw₀r.1,
      chain_coord_add (by rw [abs_sub_comm]; exact (hdisp0 j).2) hw₀r.2⟩
  have hdj := hd j
  have p1 := oscillatorAction_sub_le (e := e) (z t) u j (hdispu j).1 (hdispu j).2
    hztc.1 hztc.2 huc.1 huc.2
  have p2 := oscillatorAction_sub_le (e := e) z₀ w₀ j (by rw [abs_sub_comm]; exact (hdisp0 j).1)
    (by rw [abs_sub_comm]; exact (hdisp0 j).2) hz₀r.1 hz₀r.2 hw₀r.1 hw₀r.2
  have hc := hbd j
  have e3 : e * (r j + e + r j) = e * (2 * r j + e) := by ring
  rw [e3] at p1 p2
  have p1' := abs_le.1 (p1.trans hdj)
  have p2' := abs_le.1 (p2.trans hdj)
  have c1 := abs_le.1 hc.1
  constructor
  · rw [abs_le]; constructor <;> nlinarith [c1.1, c1.2, p1'.1, p1'.2, p2'.1, p2'.2]
  · nlinarith [hc.2, p1'.2]

/-- **Physical `m`-generator confinement** (track B, B2-ORIGCHAIN): the premises of
`oscillatorChain_confinement`, plus a physical action box `a'` with radii `s`, the inverse-chain
domain budget `OscPhysDom n s l 0`, and a transfer constant `d`. For every physical `z₀` with
actions `≤ a'`, the physical flow exists, is unique, and the PHYSICAL actions drift by at most
`2 d + η |t|` on `|t| ≤ T`. -/
theorem oscillatorChain_physical {H Nact P : CartPolyK K}
    (hH : CartFits n H) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {l : List (OscStepK K)} (hok : OscChainOK n Nact P l H)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom : OscDomOK n r δc l)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' s d : Fin n → ℝ) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, 2 * a' i ≤ s i ^ 2)
    (hs2 : OscPhysDom n s l 0) (hs3 : ∀ i, (s i + (oscTail l : ℝ)) ^ 2 ≤ a i)
    (hd : ∀ j, (oscTail l : ℝ) * (2 * r j + (oscTail l : ℝ)) ≤ d j)
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
  refine oscillatorChain_physical_core hH hN hP hA hok hδc a b η εb T hεb hT rl r hrl hr0 hdom1
    hdom hη hdrift hmargin a' s d hs0 hs1 hs2 hd z₀ hz₀ ?_
  intro w hdisp j
  have hz₀c : ∀ j, |z₀.1 j| ≤ s j + 0 ∧ |z₀.2 j| ≤ s j + 0 := fun j => by
    have := chainCoord_abs_le z₀ j (hs0 j) (hs1 j) (hz₀ j)
    simpa using this
  have h1 : |w.1 j| ≤ s j + (oscTail l : ℝ) ∧ |w.2 j| ≤ s j + (oscTail l : ℝ) :=
    ⟨chain_coord_add (hdisp j).1 (by simpa using (hz₀c j).1),
      chain_coord_add (hdisp j).2 (by simpa using (hz₀c j).2)⟩
  have h3 := hs3 j
  have q1 : w.1 j ^ 2 ≤ (s j + (oscTail l : ℝ)) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.1 h1.1]) (by linarith [abs_le.1 h1.1])
  have q2 : w.2 j ^ 2 ≤ (s j + (oscTail l : ℝ)) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.1 h1.2]) (by linarith [abs_le.1 h1.2])
  simp only [KAM.Planetary.oscillatorAction]
  linarith

end KAM.EffectiveStability

end
