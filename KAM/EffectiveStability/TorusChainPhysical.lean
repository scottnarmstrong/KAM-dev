/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain
public import KAM.EffectiveStability.TorusPhysical

/-!
# Physical action box and physical action drift for `m`-generator torus charts (track B,
B4-TORIGCHAIN)

Combines `TorusPhysical` (B4-TORIG) with `TorusChain` (B4-TMULTI), mirroring
`OscillatorChainPhysical` (B2-ORIGCHAIN).

* `tchChainMap_sub_le`, `tchChainInv_sub_le`: coordinatewise displacement (angles `≤ tchTailA l`,
  actions `≤ tchTailJ l`) of the chain chart and its inverse; `tchChainMap_tchChainInv`:
  `Ψ (Ψinv z) = z` on the physical box (domain recorded by `TChPhysDom`);
* `torusChain_physical`: physical-coordinate version of `torusChain_confinement`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set KAM.Canonical

variable {n : ℕ}

/-- Radius budget of the inverse chain started on `|z.2 i| ≤ q i + c`: before step `k` the actions
are at most `q i + (∑_{j<k} ε_j ρ'_j)`, which must fit the real chart domain of that step. -/
def TChPhysDom (n : ℕ) (q : Fin n → ℝ) : List TChStep → ℝ → Prop
  | [], _ => True
  | st :: l, c => (∀ i, q i + c + (st.ρ' : ℝ) < (st.ρ : ℝ)) ∧
      TChPhysDom n q l (c + (st.ε : ℝ) * (st.ρ' : ℝ))

private theorem tchPhys_abs_sub_add_le {a b c e f : ℝ} (h1 : |a - b| ≤ e) (h2 : |b - c| ≤ f) :
    |a - c| ≤ e + f := by
  have := abs_add_le (a - b) (b - c)
  simp only [sub_add_sub_cancel] at this
  linarith

private theorem tchPhys_tailA (st : TChStep) (l : List TChStep) :
    (tchTailA (st :: l) : ℝ) = (st.ε : ℝ) * (st.σ' : ℝ) + (tchTailA l : ℝ) := by
  simp only [tchTailA]; push_cast; ring

private theorem tchPhys_tailJ (st : TChStep) (l : List TChStep) :
    (tchTailJ (st :: l) : ℝ) = (st.ε : ℝ) * (st.ρ' : ℝ) + (tchTailJ l : ℝ) := by
  simp only [tchTailJ]; push_cast; ring

variable {b r : Fin n → ℝ} {εb δc : ℝ}

/-- Displacement of the chain chart on `cyl (b + εb)`: angles `≤ ∑ ε σ'`, actions `≤ ∑ ε ρ'`. -/
theorem tchChainMap_sub_le {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hdom : TChDomOK n b r εb δc l) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ cyl (fun j => b j + εb)) (i : Fin n) :
    |(tchChainMap l x).1 i - x.1 i| ≤ (tchTailA l : ℝ) ∧
      |(tchChainMap l x).2 i - x.2 i| ≤ (tchTailJ l : ℝ) := by
  induction l with
  | nil => simp [tchChainMap, tchTailA, tchTailJ]
  | cons st l ih =>
    obtain ⟨h1, -, -, h4⟩ := hdom
    have hl' : ∀ t ∈ l, TChStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl st (by simp)
    have hy : tchChainMap l x ∈ cyl (fun j => b j + εb + (tchTailJ l : ℝ)) :=
      (tchChain_isCanonical hl' h4).chart_maps hx
    have hy2 := realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num)
      (cyl_subset_realInterior_tch hs (fun i => by simpa using h1 i) hy)
    have hA := torusChart_sub_le hs.σ'_posℝ hs.ρ'_posℝ hs.tchSmallField hy2 i
    obtain ⟨hB1, hB2⟩ := ih hl' h4
    rw [tchPhys_tailA, tchPhys_tailJ]
    exact ⟨tchPhys_abs_sub_add_le hA.1 hB1, tchPhys_abs_sub_add_le hA.2 hB2⟩

/-- Displacement of the inverse chain chart and the inverse property, on points with actions
`|z.2 i| ≤ q i + c` within the budget `TChPhysDom`. -/
theorem tchChainInv_sub_le {q : Fin n → ℝ} {l : List TChStep}
    (hl : ∀ s ∈ l, TChStepOK n s) {c : ℝ} {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (hdom : TChPhysDom n q l c) (hz : ∀ i, |z.2 i| ≤ q i + c) :
    (∀ i, |(tchChainInv l z).1 i - z.1 i| ≤ (tchTailA l : ℝ) ∧
      |(tchChainInv l z).2 i - z.2 i| ≤ (tchTailJ l : ℝ)) ∧
    tchChainMap l (tchChainInv l z) = z := by
  induction l generalizing c z with
  | nil => simp [tchChainInv, tchChainMap, tchTailA, tchTailJ]
  | cons st l ih =>
    obtain ⟨h1, h2⟩ := hdom
    have hl' : ∀ t ∈ l, TChStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl st (by simp)
    have hS := hs.tchSmallField
    have hzI : z ∈ realInterior (scaleCLE (st.ρ' : ℝ) (st.σ' : ℝ) hs.ρ'_posℝ hs.σ'_posℝ)
        (cstripOpen (st.σ : ℝ) (st.ρ : ℝ)) 1 :=
      cylClosed_subset_realInterior_cstrip hs.ρ'_posℝ hs.σ'_posℝ hs.σ'_ltℝ
        (c := fun i => q i + c) h1 hz
    have hzI2 := realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num) hzI
    set z' := torusChartInv st.gen (st.σ : ℝ) (st.ρ : ℝ) z with hz'
    have hA := torusChartInv_sub_le hs.σ'_posℝ hs.ρ'_posℝ hS hzI2
    have hz'c : ∀ i, |z'.2 i| ≤ q i + (c + (st.ε : ℝ) * (st.ρ' : ℝ)) := fun i => by
      have a2 : |z'.2 i| ≤ |z.2 i| + |z'.2 i - z.2 i| := by
        simpa using abs_add_le (z.2 i) (z'.2 i - z.2 i)
      linarith [(hA i).2, hz i]
    obtain ⟨hB, hC⟩ := ih hl' h2 hz'c
    refine ⟨fun i => ?_, ?_⟩
    · rw [tchPhys_tailA, tchPhys_tailJ]
      change |(tchChainInv l z').1 i - z.1 i| ≤ _ ∧ |(tchChainInv l z').2 i - z.2 i| ≤ _
      have c1 := tchPhys_abs_sub_add_le (hB i).1 (hA i).1
      have c2 := tchPhys_abs_sub_add_le (hB i).2 (hA i).2
      constructor <;> linarith
    · show torusChart st.gen (st.σ : ℝ) (st.ρ : ℝ) (tchChainMap l (tchChainInv l z')) = z
      rw [hC]
      exact torusChart_torusChartInv hs.σ'_posℝ hs.ρ'_posℝ hS hzI

/-- **Physical `m`-generator torus confinement** (track B, B4-TORIGCHAIN): the premises of
`torusChain_confinement`, plus a physical action box `a'` with `a' i + ∑ ε ρ' ≤ a i` and the
inverse-chain domain budget `TChPhysDom n a' l 0`. For every physical `z₀` with
`|z₀.2 j| ≤ a' j`, the physical flow exists, is unique, and the PHYSICAL actions drift by at most
`2 D + η |t|` on `|t| ≤ T`, where `D = ∑ ε ρ'` (`tchTailJ l`). -/
theorem torusChain_physical {H Nact P : FTPoly}
    (hH : FTFits n H) (hP : FTFits n P) (hA : ftActOnly Nact = true) {l : List TChStep}
    (hok : TChChainOK n Nact P l H) {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ)
    (hεb : 0 < εb) (hT : 0 ≤ T) (bl : List ℚ)
    (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i) (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hdom : TChDomOK n b r εb δc l) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j ftPiUB bl : ℚ) : ℝ) +
      (tchChainBound n l H : ℝ) / δc ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (a' : Fin n → ℝ) (hpa : ∀ i, a' i + (tchTailJ l : ℝ) ≤ a i) (hpd : TChPhysDom n a' l 0)
    (z₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hz₀ : ∀ j, |z₀.2 j| ≤ a' j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j,
        |(z t).2 j - z₀.2 j| ≤ 2 * (tchTailJ l : ℝ) + η j * |t| ∧
          |(z t).2 j| ≤ a j + η j * T + (tchTailJ l : ℝ) := by
  have hl := hok.tchStepsOK
  set D : ℝ := (tchTailJ l : ℝ) with hD
  have hz₀c : ∀ j, |z₀.2 j| ≤ a' j + 0 := fun j => by simpa using hz₀ j
  obtain ⟨hdisp0, hΨw₀⟩ := tchChainInv_sub_le hl hpd hz₀c
  set w₀ := tchChainInv l z₀ with hw₀def
  have hw₀a : ∀ j, |w₀.2 j| ≤ a j := fun j => by
    have h1 := (hdisp0 j).2
    have e : |w₀.2 j| ≤ |z₀.2 j| + |w₀.2 j - z₀.2 j| := by
      simpa using abs_add_le (z₀.2 j) (w₀.2 j - z₀.2 j)
    linarith [hz₀ j, hpa j]
  obtain ⟨T₁, hT₁, z, hz0, hode, huniq, hb⟩ := torusChain_confinement hH hP hA hok hδc a b η
    εb T hεb hT bl hbl r hbr hdom hη hdrift hmargin w₀ hw₀a
  rw [hΨw₀] at hz0
  refine ⟨T₁, hT₁, z, hz0, hode, fun I y hI h0 hy0 hyd t htI htT => huniq I y hI h0
    (by rw [hΨw₀]; exact hy0) hyd t htI htT, fun t ht j => ?_⟩
  obtain ⟨hinv, hbd⟩ := hb t ht
  set u := tchChainInv l (z t) with hu
  have hbj : ∀ k, |u.2 k| ≤ b k := fun k => by
    have h2 := mul_le_mul_of_nonneg_left ht (hη k)
    have h3 := hmargin k
    have := (hbd k).2
    nlinarith [mul_comm T (η k)]
  have huI : u ∈ cyl (fun j => b j + εb) := fun k => by
    have := hbj k
    linarith
  have hdispu := (tchChainMap_sub_le hl hdom huI j).2
  rw [show tchChainMap l u = z t from hinv] at hdispu
  have c1 := abs_le.1 (hbd j).1
  have c2 := (hbd j).2
  have q1 := abs_le.1 hdispu
  have q2 := abs_le.1 (hdisp0 j).2
  have ub : |(z t).2 j| ≤ |u.2 j| + |(z t).2 j - u.2 j| := by
    simpa using abs_add_le (u.2 j) ((z t).2 j - u.2 j)
  constructor
  · rw [abs_le]; constructor <;> nlinarith [c1.1, c1.2, q1.1, q1.2, q2.1, q2.2]
  · linarith

end KAM.EffectiveStability

end
