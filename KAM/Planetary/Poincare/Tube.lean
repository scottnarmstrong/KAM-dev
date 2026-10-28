/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.CircularTube

/-!
# The circular torus and its tube in chart coordinates

Blueprint P, Part 7 (`bpP:p7:tube`): the circular torus `{circularPoint φ}` is the image of
`Λ_i = m_i √(κ a_i)`, `Γ_i = 0` under the product chart, and every sufficiently thin tube
`circularTube η` lies in `regionProd` with chart coordinates within `δ` of the torus
(`Λ_i` close to `m_i √(κ a_i)`, `Γ_i < δ`).  The tube statement is the neighbourhood form
`IsCompact.exists_cthickening_subset_open` applied to the compact torus and the open set
`tubeNbhd` of physical points whose elements `(Λ_i, Γ_i)` are `δ`-close to the torus.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM KAM.Kepler

section Tube

variable {n : ℕ}

/-! ### The torus in chart coordinates -/

private theorem tube_planetBlock_assemble (I phi : Fin n → ℝ) (j : Fin n) :
    planetBlock (assemble I phi (0 : Fin n → ℝ) (0 : Fin n → ℝ) : Phase (n + n)) j =
      (![phi j, 0], ![I j, 0]) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, assemble, fast, slow, Fin.append_left]

private theorem tube_fast_assemble (I phi : Fin n → ℝ) (i : Fin n) :
    fast (assemble I phi (0 : Fin n → ℝ) (0 : Fin n → ℝ) : Phase (n + n)).2 i = I i := by
  simp [assemble, fast, Fin.append_left]

/-- `bpP:p7:tube`: the circular torus in chart coordinates. -/
theorem circularPoint_eq_poincareProd {G m0 : ℝ} {m a : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) (φ : Fin n → ℝ) :
    circularPoint G m0 m a φ =
      poincareProd m (G * m0)
        (assemble (fun i => m i * √(G * m0 * a i)) (fun i => 2 * π * φ i) (0 : Fin n → ℝ)
          (0 : Fin n → ℝ)) := by
  have hκ : 0 < G * m0 := mul_pos hG hm0
  have hblk : ∀ i, (bodyVector (circularPoint G m0 m a φ).1 i,
      bodyVector (circularPoint G m0 m a φ).2 i) =
      poincare (m i) (G * m0) (planetBlock (assemble (fun i => m i * √(G * m0 * a i))
        (fun i => 2 * π * φ i) (0 : Fin n → ℝ) (0 : Fin n → ℝ) : Phase (n + n)) i) := by
    intro i
    have hai := ha i
    have hmi := hm i
    rw [tube_planetBlock_assemble]
    have hΛ : 0 < m i * √(G * m0 * a i) := by positivity
    rw [poincare_circular hmi hκ hΛ]
    have hax : (m i * √(G * m0 * a i)) ^ 2 / (m i ^ 2 * (G * m0)) = a i := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [hax]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp only [bodyVector, circularPoint, Equiv.symm_apply_apply] <;> simp
  conv_lhs => rw [← ofPlanets_bodyVector (circularPoint G m0 m a φ)]
  rw [poincareProd_eq_ofPlanets]
  congr 1
  funext i
  exact hblk i

/-! ### The neighbourhood `V_δ` of the torus -/

/-- Physical points whose per-body elements `(Λ_i, Γ_i)` are `δ`-close to the torus. -/
def tubeNbhd (m : Fin n → ℝ) (κ : ℝ) (Λ₀ : Fin n → ℝ) (δ : ℝ) : Set (Phase (n * 2)) :=
  {z | ∀ i, (bodyVector z.1 i, bodyVector z.2 i) ∈ regionMK (m i) κ ∧
    |actionMK (m i) κ (bodyVector z.1 i, bodyVector z.2 i) - Λ₀ i| < δ ∧
    actionMK (m i) κ (bodyVector z.1 i, bodyVector z.2 i) -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) < δ}

theorem tubeNbhd_subset_regionProd (m : Fin n → ℝ) (κ : ℝ) (Λ₀ : Fin n → ℝ) (δ : ℝ) :
    tubeNbhd m κ Λ₀ δ ⊆ regionProd m κ := fun _ hz i => (hz i).1

theorem mem_tubeNbhd_poincareProd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {Λ₀ : Fin n → ℝ} {δ : ℝ} {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    poincareProd m κ w ∈ tubeNbhd m κ Λ₀ δ ↔
      ∀ i, |fast w.2 i - Λ₀ i| < δ ∧ poincareGamma (planetBlock w i) < δ := by
  refine forall_congr' fun i => ?_
  have hb1 : bodyVector (poincareProd m κ w).1 i = (poincare (m i) κ (planetBlock w i)).1 :=
    congrArg Prod.fst (poincareProd_block m κ w i)
  have hb2 : bodyVector (poincareProd m κ w).2 i = (poincare (m i) κ (planetBlock w i)).2 :=
    congrArg Prod.snd (poincareProd_block m κ w i)
  simp only [hb1, hb2]
  obtain ⟨hreg, -, -, hact, hcr, -⟩ := poincare_elements (hm i) hκ (hw i)
  have hf : (planetBlock w i).2 0 = fast w.2 i := rfl
  rw [hact, hcr, hf]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hreg, h1, by linarith⟩

private theorem continuous_tube_planeSq : Continuous planeSq := by
  have : planeSq = fun w : Fin 2 → ℝ => ∑ k, w k ^ 2 := rfl
  rw [this]; fun_prop

private theorem continuous_tube_planeLength : Continuous planeLength :=
  Real.continuous_sqrt.comp continuous_tube_planeSq

private theorem continuous_tube_planeCross :
    Continuous (fun z : Phase 2 => planeCross z.1 z.2) := by
  unfold planeCross; fun_prop

private theorem continuousOn_actionMK {m κ : ℝ} :
    ContinuousOn (actionMK m κ) (regionMK m κ) := by
  have hE : ContinuousOn (fun z : Phase 2 => energyMK m κ z)
      {z : Phase 2 | 0 < planeLength z.1} := by
    unfold energyMK
    refine ContinuousOn.sub ?_ ?_
    · exact ((continuous_tube_planeSq.comp continuous_snd).div_const _).continuousOn
    · refine ContinuousOn.div continuousOn_const
        (continuous_tube_planeLength.comp continuous_fst).continuousOn ?_
      intro z hz; exact hz.ne'
  have hE' : ContinuousOn (fun z : Phase 2 => energyMK m κ z) (regionMK m κ) :=
    hE.mono fun z hz => hz.1
  unfold actionMK axisMK
  refine continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn ?_)
  refine continuousOn_const.mul ?_
  refine ContinuousOn.div continuousOn_const (continuousOn_const.mul hE') ?_
  intro z hz
  have := hz.2.1
  intro h
  have : energyMK m κ z = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · norm_num at h
    · exact h
  linarith [hz.2.1]

private theorem isOpen_tubeNbhd_block {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (Λ₀ δ : ℝ) :
    IsOpen {b : Phase 2 | b ∈ regionMK m κ ∧ |actionMK m κ b - Λ₀| < δ ∧
      actionMK m κ b - planeCross b.1 b.2 < δ} := by
  have hF : ContinuousOn (fun b : Phase 2 => (actionMK m κ b, planeCross b.1 b.2)) (regionMK m κ) :=
    continuousOn_actionMK.prodMk continuous_tube_planeCross.continuousOn
  have hT : IsOpen {p : ℝ × ℝ | |p.1 - Λ₀| < δ ∧ p.1 - p.2 < δ} :=
    IsOpen.and
      (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const)
      (isOpen_lt (continuous_fst.sub continuous_snd) continuous_const)
  exact hF.isOpen_inter_preimage (isOpen_regionMK hm hκ) hT

private theorem isOpen_tubeNbhd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    (Λ₀ : Fin n → ℝ) (δ : ℝ) : IsOpen (tubeNbhd m κ Λ₀ δ) := by
  have hblk : ∀ i : Fin n, Continuous fun z : Phase (n * 2) =>
      (bodyVector z.1 i, bodyVector z.2 i) := fun i => by
    refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun k => ?_)
    · exact (continuous_apply _).comp continuous_fst
    · exact (continuous_apply _).comp continuous_snd
  have : tubeNbhd m κ Λ₀ δ = ⋂ i,
      (fun z : Phase (n * 2) => (bodyVector z.1 i, bodyVector z.2 i)) ⁻¹'
      {b : Phase 2 | b ∈ regionMK (m i) κ ∧ |actionMK (m i) κ b - Λ₀ i| < δ ∧
        actionMK (m i) κ b - planeCross b.1 b.2 < δ} := by
    ext z; simp only [tubeNbhd, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_tubeNbhd_block (hm i) hκ _ _).preimage (hblk i)

/-! ### The compact torus -/

private theorem tube_cos_fract (x : ℝ) : Real.cos (2 * π * Int.fract x) = Real.cos (2 * π * x) := by
  conv_rhs => rw [← Int.fract_add_floor x]
  rw [mul_add, show 2 * π * ((⌊x⌋ : ℤ) : ℝ) = (⌊x⌋ : ℤ) * (2 * π) by ring]
  exact (Real.cos_add_int_mul_two_pi _ _).symm

private theorem tube_sin_fract (x : ℝ) : Real.sin (2 * π * Int.fract x) = Real.sin (2 * π * x) := by
  conv_rhs => rw [← Int.fract_add_floor x]
  rw [mul_add, show 2 * π * ((⌊x⌋ : ℤ) : ℝ) = (⌊x⌋ : ℤ) * (2 * π) by ring]
  exact (Real.sin_add_int_mul_two_pi _ _).symm

private theorem circularPoint_fract (G m0 : ℝ) (m a : Fin n → ℝ) (φ : Fin n → ℝ) :
    circularPoint G m0 m a (fun i => Int.fract (φ i)) = circularPoint G m0 m a φ := by
  simp only [circularPoint, tube_cos_fract, tube_sin_fract]

private theorem continuous_circularPoint (G m0 : ℝ) (m a : Fin n → ℝ) :
    Continuous (circularPoint G m0 m a) := by
  have h1 : ∀ (j : Fin n) (l : Fin 2), Continuous fun φ : Fin n → ℝ =>
      a j * (![Real.cos (2 * π * φ j), Real.sin (2 * π * φ j)] : Fin 2 → ℝ) l := fun j l => by
    fin_cases l <;> simp <;> fun_prop
  have h2 : ∀ (j : Fin n) (l : Fin 2), Continuous fun φ : Fin n → ℝ =>
      m j * √(G * m0 / a j) *
        (![-Real.sin (2 * π * φ j), Real.cos (2 * π * φ j)] : Fin 2 → ℝ) l := fun j l => by
    fin_cases l <;> simp <;> fun_prop
  exact Continuous.prodMk (continuous_pi fun k => h1 _ _) (continuous_pi fun k => h2 _ _)

/-- `bpP:p7:tube`: thin tubes lie in the chart region, with chart coordinates `δ`-close to the
torus. -/
theorem tube_in_chart {G m0 : ℝ} {m a : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η, 0 < η → η ≤ η₀ →
      circularTube G m0 m a η ⊆ regionProd m (G * m0) ∧
      ∀ w ∈ poincareProdDom n, poincareProd m (G * m0) w ∈ circularTube G m0 m a η →
        ∀ i, |fast w.2 i - m i * √(G * m0 * a i)| < δ ∧ poincareGamma (planetBlock w i) < δ := by
  have hκ : 0 < G * m0 := mul_pos hG hm0
  let Λ₀ : Fin n → ℝ := fun i => m i * √(G * m0 * a i)
  have hΛ₀ : ∀ i, 0 < Λ₀ i := fun i => by
    have := ha i; have := hm i; positivity
  let K : Set (Phase (n * 2)) :=
    circularPoint G m0 m a '' Set.pi univ fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_circularPoint G m0 m a)
  have hKV : K ⊆ tubeNbhd m (G * m0) Λ₀ δ := by
    rintro _ ⟨φ, -, rfl⟩
    have hw : (assemble (fun i => Λ₀ i) (fun i => 2 * π * φ i) (0 : Fin n → ℝ) (0 : Fin n → ℝ) :
        Phase (n + n)) ∈ poincareProdDom n := by
      intro i
      rw [tube_planetBlock_assemble]
      refine ⟨hΛ₀ i, ?_⟩
      simpa [poincareGamma] using hΛ₀ i
    rw [circularPoint_eq_poincareProd hG hm0 hm ha φ, mem_tubeNbhd_poincareProd hm hκ hw]
    intro i
    rw [tube_fast_assemble]
    refine ⟨by simpa using hδ, ?_⟩
    simpa [poincareGamma, tube_planetBlock_assemble] using hδ
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_tubeNbhd hm hκ Λ₀ δ) hKV
  refine ⟨r, hr, fun η hη hηr => ?_⟩
  have hT : circularTube G m0 m a η ⊆ tubeNbhd m (G * m0) Λ₀ δ := by
    rintro z ⟨φ, hφ⟩
    apply hsub
    refine mem_cthickening_of_dist_le z (circularPoint G m0 m a (fun i => Int.fract (φ i))) r K
      ⟨_, fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩ ?_
    rw [circularPoint_fract, dist_eq_norm]
    exact (hφ.trans_le hηr).le
  refine ⟨hT.trans (tubeNbhd_subset_regionProd _ _ _ _), fun w hw hz i => ?_⟩
  exact (mem_tubeNbhd_poincareProd hm hκ hw).1 (hT hz) i

end Tube

end KAM.Planetary

end
