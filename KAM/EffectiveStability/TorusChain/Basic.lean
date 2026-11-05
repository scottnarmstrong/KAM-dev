/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep.Drift

/-!
# Chains of torus normalization steps: data and complex-side analysis (track B, B4-TMULTI)

A *chain* is a `List TChStep` (outermost generator first): the chart is `Ψ = Φ₁ ∘ ⋯ ∘ Φ_m`.
All data are `ℚ`-valued Fourier–Taylor polynomials and radii. The predicates `TChStepOK`,
`TChChainOK`, `TChDomOK` are finite exact checks (`ftEqCheck`, `ftSupBound` majorants,
rational/real inequalities between data); the constant `π` is bounded by the fixed `ftPiUB`.

On the complex side: `tchTheta l` is the composition of the complex time-one flows of `l`,
`tchRem l Q` the sum of the pushed-forward Lie remainders, `tchDom l` an open domain on which both
are holomorphic, and `tchChainBound` the rational majorant of `‖tchRem‖` on the Cauchy discs.
`tchTheta_bound` tracks the displacement budget: an inner flow moves angles by at most `ε σ'` and
actions by at most `ε ρ'`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- One torus normalization step: generator `gen`, output polynomial `out`, Lie order, strip
half-width `σ`, polydisc radius `ρ`, gauge `(σ', ρ')`, small-field constant `ε` and strip constant
`lam` (finite data only). -/
structure TChStep where
  gen : FTPoly
  out : FTPoly
  order : ℕ
  σ : ℚ
  ρ : ℚ
  σ' : ℚ
  ρ' : ℚ
  ε : ℚ
  lam : ℚ

/-- The complex time-one flow of the step generator on `cstripOpen σ ρ`. -/
def tchStepFlow (s : TChStep) : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC s.gen w))
    (cstripOpen (s.σ : ℝ) (s.ρ : ℝ)) 1

/-- The composite of the complex flows `X₁ ∘ ⋯ ∘ X_m` of a chain. -/
def tchTheta : List TChStep → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)
  | [] => id
  | s :: l => tchStepFlow s ∘ tchTheta l

/-- The pushed-forward remainders `∑_k E_k ∘ (X_{k+1} ∘ ⋯ ∘ X_m)`, started at the polynomial `Q`. -/
def tchRem : List TChStep → FTPoly → (Fin n → ℂ) × (Fin n → ℂ) → ℂ
  | [], _ => fun _ => 0
  | s :: l, Q => fun z => torusRem s.gen Q (s.σ : ℝ) (s.ρ : ℝ) s.order (tchTheta l z) +
      tchRem l s.out z

/-- Total angle displacement budget `∑ ε σ'` of a chain. -/
def tchTailA : List TChStep → ℚ
  | [] => 0
  | s :: l => s.ε * s.σ' + tchTailA l

/-- Total action displacement budget `∑ ε ρ'` of a chain. -/
def tchTailJ : List TChStep → ℚ
  | [] => 0
  | s :: l => s.ε * s.ρ' + tchTailJ l

/-- The rational majorant `∑_k B_k / L_k!` of the remainders,
`B_k = ftSupBound (ad^{L_k} Q_{k-1}) πub λ_k ρ_k`. -/
def tchChainBound (n : ℕ) : List TChStep → FTPoly → ℚ
  | [], _ => 0
  | s :: l, Q => ftSupBound (ftAdPow s.gen s.order Q) ftPiUB s.lam (List.replicate n s.ρ) /
      (s.order.factorial : ℚ) + tchChainBound n l s.out

/-- Per-step checks: positivity, strip check, small field majorants, polynomial typing. -/
structure TChStepOK (n : ℕ) (s : TChStep) : Prop where
  σ'_pos : 0 < s.σ'
  ρ'_pos : 0 < s.ρ'
  σ'_lt : s.σ' < s.σ
  ε_nonneg : 0 ≤ s.ε
  ε_le : s.ε ≤ 1 / 2
  order_pos : 1 ≤ s.order
  fits_gen : FTFits n s.gen
  fits_out : FTFits n s.out
  strip_lt : 2 * ftPiUB * s.σ < 1
  lam_ge : 1 / (1 - 2 * ftPiUB * s.σ) ≤ s.lam
  bound_J : ∀ i : Fin n, ftSupBound (ftDJ i s.gen) ftPiUB s.lam (List.replicate n s.ρ) ≤
    s.ε * s.σ'
  bound_φ : ∀ i : Fin n, ftSupBound (ftDφ i s.gen) ftPiUB s.lam (List.replicate n s.ρ) ≤
    s.ε * s.ρ'

/-- The exact identity checks of a chain started at the polynomial `Q`: step identities
`Q_k = ∑_{j<L_k} (j!)⁻¹ ad_{χ_k}^j Q_{k-1}` and the final `Q_m = Nact(J) + P`. -/
def TChChainOK (n : ℕ) (Nact P : FTPoly) : List TChStep → FTPoly → Prop
  | [], Q => ftEqCheck Q (ftAdd Nact P) = true
  | s :: l, Q => TChStepOK n s ∧ ftEqCheck (ftLieSum s.gen Q s.order) s.out = true ∧
      TChChainOK n Nact P l s.out

/-- The radius budget of a chain: for every step, the real chart domain
(`b + εb + (inner action displacement) + ρ'_k ≤ ρ_k`) and the Cauchy discs
(`δc + (inner angle displacement) + σ'_k / 2 < σ_k`,
`r + δc + (inner action displacement) + ρ'_k / 2 < ρ_k`). -/
def TChDomOK (n : ℕ) (b r : Fin n → ℝ) (εb δc : ℝ) : List TChStep → Prop
  | [] => True
  | s :: l => (∀ i, b i + εb + (tchTailJ l : ℝ) + (s.ρ' : ℝ) ≤ (s.ρ : ℝ)) ∧
      δc + (tchTailA l : ℝ) + (s.σ' : ℝ) / 2 < (s.σ : ℝ) ∧
      (∀ i, r i + δc + (tchTailJ l : ℝ) + (s.ρ' : ℝ) / 2 < (s.ρ : ℝ)) ∧
      TChDomOK n b r εb δc l

/-- Imaginary parts of the angles lie within `d`, actions within `r i + c`. -/
def TChBound (r : Fin n → ℝ) (d c : ℝ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : Prop :=
  ∀ i, |(z.1 i).im| ≤ d ∧ ‖z.2 i‖ ≤ r i + c

theorem replicate_getD_tchRad (ρ : ℚ) (i : Fin n) :
    ((List.replicate n ρ).getD i 0 : ℚ) = ρ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [i.2]

theorem TChStepOK.σ'_posℝ {s : TChStep} (hs : TChStepOK n s) : (0 : ℝ) < (s.σ' : ℝ) := by
  exact_mod_cast hs.σ'_pos

theorem TChStepOK.ρ'_posℝ {s : TChStep} (hs : TChStepOK n s) : (0 : ℝ) < (s.ρ' : ℝ) := by
  exact_mod_cast hs.ρ'_pos

theorem TChStepOK.σ'_ltℝ {s : TChStep} (hs : TChStepOK n s) : (s.σ' : ℝ) < (s.σ : ℝ) := by
  exact_mod_cast hs.σ'_lt

theorem TChStepOK.strip_ltℝ {s : TChStep} (hs : TChStepOK n s) :
    2 * ((ftPiUB : ℚ) : ℝ) * (s.σ : ℝ) < 1 := by
  exact_mod_cast hs.strip_lt

theorem TChStepOK.lam_geℝ {s : TChStep} (hs : TChStepOK n s) :
    1 / (1 - 2 * ((ftPiUB : ℚ) : ℝ) * (s.σ : ℝ)) ≤ ((s.lam : ℚ) : ℝ) := by
  have := (Rat.cast_le (K := ℝ)).2 hs.lam_ge
  simpa using this

theorem TChStepOK.σ_nonneg {s : TChStep} (hs : TChStepOK n s) : (0 : ℝ) ≤ (s.σ : ℝ) :=
  (hs.σ'_posℝ.trans hs.σ'_ltℝ).le

theorem TChStepOK.tchLam_pos {s : TChStep} (hs : TChStepOK n s) : 0 < s.lam := by
  have h1 : 0 < 1 - 2 * ((ftPiUB : ℚ) : ℝ) * (s.σ : ℝ) := by linarith [hs.strip_ltℝ]
  have : (0 : ℝ) < ((s.lam : ℚ) : ℝ) := lt_of_lt_of_le (by positivity) hs.lam_geℝ
  exact_mod_cast this

theorem TChStepOK.stripLog {s : TChStep} (hs : TChStepOK n s) :
    (s.σ : ℝ) ≤ Real.log ((s.lam : ℚ) : ℝ) / (2 * Real.pi) :=
  strip_le_log_lam pi_le_ftPiUB hs.σ_nonneg hs.strip_ltℝ hs.lam_geℝ

/-- The coordinate bounds of a step give the small-field hypothesis. -/
theorem TChStepOK.tchSmallField {s : TChStep} (hs : TChStepOK n s) :
    SmallField (scaleCLE (s.ρ' : ℝ) (s.σ' : ℝ) hs.ρ'_posℝ hs.σ'_posℝ)
      (cstripOpen (s.σ : ℝ) (s.ρ : ℝ))
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC s.gen w))
      (s.ε : ℝ) :=
  smallField_of_ftBounds hs.fits_gen hs.σ'_posℝ hs.ρ'_posℝ pi_le_ftPiUB
    (by exact_mod_cast hs.tchLam_pos) hs.stripLog (List.replicate n s.ρ)
    (fun i => by rw [replicate_getD_tchRad]) (by exact_mod_cast hs.ε_nonneg)
    (by
      have h : ((s.ε : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 hs.ε_le
      simpa using h)
    (fun i => by exact_mod_cast hs.bound_J i) (fun i => by exact_mod_cast hs.bound_φ i)

theorem tchTailA_nonneg_of {l : List TChStep} (h : ∀ s ∈ l, TChStepOK n s) :
    0 ≤ tchTailA l := by
  induction l with
  | nil => simp [tchTailA]
  | cons s l ih =>
    have hs := h s (by simp)
    have := ih (fun t ht => h t (by simp [ht]))
    simp only [tchTailA]
    have := mul_nonneg hs.ε_nonneg hs.σ'_pos.le
    positivity

theorem tchTailJ_nonneg_of {l : List TChStep} (h : ∀ s ∈ l, TChStepOK n s) :
    0 ≤ tchTailJ l := by
  induction l with
  | nil => simp [tchTailJ]
  | cons s l ih =>
    have hs := h s (by simp)
    have := ih (fun t ht => h t (by simp [ht]))
    simp only [tchTailJ]
    have := mul_nonneg hs.ε_nonneg hs.ρ'_pos.le
    positivity

theorem TChChainOK.tchStepsOK {Nact P : FTPoly} :
    ∀ {l : List TChStep} {Q : FTPoly}, TChChainOK n Nact P l Q → ∀ s ∈ l, TChStepOK n s
  | [], _, _ => fun s hs => by simp at hs
  | t :: l, Q, h => fun s hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h.1
    · exact TChChainOK.tchStepsOK h.2.2 s hs

/-! ### The open domain of the composite complex flow -/

/-- The open domain on which the composite flow `Θ_l` is defined with every intermediate point in
the half interior of the next strip × polydisc. -/
def tchDom : List TChStep → Set ((Fin n → ℂ) × (Fin n → ℂ))
  | [] => univ
  | s :: l => tchDom l ∩
      tchTheta l ⁻¹' cstripOpen ((s.σ : ℝ) - (s.σ' : ℝ) / 2) ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2)

theorem cstripSub_subset_gaugeInterior {s : TChStep} (hs : TChStepOK n s) :
    cstripOpen (n := n) ((s.σ : ℝ) - (s.σ' : ℝ) / 2) ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2) ⊆
      gaugeInterior (scaleCLE (s.ρ' : ℝ) (s.σ' : ℝ) hs.ρ'_posℝ hs.σ'_posℝ)
        (cstripOpen (s.σ : ℝ) (s.ρ : ℝ)) (1 / 2) := by
  intro z hz
  refine mem_gaugeInterior_cstripOpen hs.ρ'_posℝ hs.σ'_posℝ fun i => ?_
  have h1 := (hz i).1
  have h2 := (hz i).2
  constructor <;> linarith

theorem tchNorm_coord_le (v : (Fin n → ℂ) × (Fin n → ℂ)) (i : Fin n) :
    ‖v.1 i‖ ≤ ‖v‖ ∧ ‖v.2 i‖ ≤ ‖v‖ :=
  ⟨(norm_le_pi_norm v.1 i).trans (le_max_left _ _),
    (norm_le_pi_norm v.2 i).trans (le_max_right _ _)⟩

/-- A step flow moves each angle by at most `ε σ'` and each action by at most `ε ρ'`. -/
theorem tchStepFlow_disp {s : TChStep} (hs : TChStepOK n s) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ cstripOpen (n := n) ((s.σ : ℝ) - (s.σ' : ℝ) / 2) ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2))
    (i : Fin n) :
    ‖(tchStepFlow s z - z).1 i‖ ≤ (s.ε : ℝ) * (s.σ' : ℝ) ∧
      ‖(tchStepFlow s z - z).2 i‖ ≤ (s.ε : ℝ) * (s.ρ' : ℝ) := by
  have hS := hs.tchSmallField
  obtain ⟨-, -, -, hd⟩ := flow_a hS (cstripSub_subset_gaugeInterior hs hz)
  have h1 := hd 1 ⟨by norm_num, le_rfl⟩
  rw [norm_scaleCLE, scaledNorm, abs_one, one_mul, max_le_iff, div_le_iff₀ hs.σ'_posℝ,
    div_le_iff₀ hs.ρ'_posℝ] at h1
  exact ⟨(norm_le_pi_norm (tchStepFlow s z - z).1 i).trans h1.1,
    (norm_le_pi_norm (tchStepFlow s z - z).2 i).trans h1.2⟩

/-- One step flow enlarges the angle and action budgets by `ε σ'` and `ε ρ'`. -/
theorem tchStepFlow_bound {s : TChStep} (hs : TChStepOK n s) {r : Fin n → ℝ} {d c : ℝ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ cstripOpen (n := n) ((s.σ : ℝ) - (s.σ' : ℝ) / 2) ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2))
    (hb : TChBound r d c z) :
    TChBound r (d + (s.ε : ℝ) * (s.σ' : ℝ)) (c + (s.ε : ℝ) * (s.ρ' : ℝ)) (tchStepFlow s z) := by
  intro i
  obtain ⟨h1, h2⟩ := tchStepFlow_disp hs hz i
  have e1 : |((tchStepFlow s z).1 i).im| ≤ |(z.1 i).im| + ‖(tchStepFlow s z - z).1 i‖ := by
    have : ((tchStepFlow s z).1 i).im = (z.1 i).im + ((tchStepFlow s z - z).1 i).im := by simp
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add_right (Complex.abs_im_le_norm _) _)
  have e2 : ‖(tchStepFlow s z).2 i‖ ≤ ‖z.2 i‖ + ‖(tchStepFlow s z - z).2 i‖ := by
    simpa using norm_add_le (z.2 i) ((tchStepFlow s z - z).2 i)
  have := hb i
  constructor <;> linarith [this.1, this.2]

theorem tchDom_isOpen_and_differentiableOn {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s) :
    IsOpen (tchDom (n := n) l) ∧ DifferentiableOn ℂ (tchTheta (n := n) l) (tchDom l) := by
  induction l with
  | nil => exact ⟨isOpen_univ, differentiableOn_id⟩
  | cons s l ih =>
    obtain ⟨ho, hd⟩ := ih (fun t ht => hl t (by simp [ht]))
    have hs := hl s (by simp)
    have hS := hs.tchSmallField
    have hfl : DifferentiableOn ℂ (tchStepFlow (n := n) s)
        (gaugeInterior (scaleCLE (s.ρ' : ℝ) (s.σ' : ℝ) hs.ρ'_posℝ hs.σ'_posℝ)
          (cstripOpen (s.σ : ℝ) (s.ρ : ℝ)) (1 / 2)) :=
      (flow_b hS).2.1 1 ⟨by norm_num, le_rfl⟩
    refine ⟨ContinuousOn.isOpen_inter_preimage hd.continuousOn ho (isOpen_cstripOpen _ _), ?_⟩
    show DifferentiableOn ℂ (tchStepFlow s ∘ tchTheta l) (tchDom l ∩
      tchTheta l ⁻¹' cstripOpen ((s.σ : ℝ) - (s.σ' : ℝ) / 2) ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2))
    exact hfl.comp (hd.mono inter_subset_left) (fun z hz =>
      cstripSub_subset_gaugeInterior hs hz.2)

section Chain

variable {r : Fin n → ℝ} {b : Fin n → ℝ} {εb δc : ℝ}

/-- A point of the Cauchy disc budget lies in the domain and its image stays within the budget
enlarged by the inner displacements. -/
theorem tchTheta_bound {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hD : TChDomOK n b r εb δc l) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : TChBound r δc δc z) :
    z ∈ tchDom l ∧ TChBound r (δc + (tchTailA l : ℝ)) (δc + (tchTailJ l : ℝ)) (tchTheta l z) := by
  induction l with
  | nil => exact ⟨mem_univ _, by simpa [tchTailA, tchTailJ, tchTheta] using hz⟩
  | cons s l ih =>
    obtain ⟨-, h2, h3, h4⟩ := hD
    obtain ⟨hzd, hzb⟩ := ih (fun t ht => hl t (by simp [ht])) h4
    have hs := hl s (by simp)
    have hmem : tchTheta l z ∈ cstripOpen (n := n) ((s.σ : ℝ) - (s.σ' : ℝ) / 2)
        ((s.ρ : ℝ) - (s.ρ' : ℝ) / 2) := by
      intro i
      constructor <;> linarith [(hzb i).1, (hzb i).2, h2, h3 i]
    refine ⟨⟨hzd, hmem⟩, ?_⟩
    have := tchStepFlow_bound hs hmem hzb
    have e1 : δc + (tchTailA (s :: l) : ℝ) = δc + (tchTailA l : ℝ) + (s.ε : ℝ) * (s.σ' : ℝ) := by
      simp only [tchTailA]; push_cast; ring
    have e2 : δc + (tchTailJ (s :: l) : ℝ) = δc + (tchTailJ l : ℝ) + (s.ε : ℝ) * (s.ρ' : ℝ) := by
      simp only [tchTailJ]; push_cast; ring
    rw [e1, e2]
    exact this

end Chain

end KAM.EffectiveStability
