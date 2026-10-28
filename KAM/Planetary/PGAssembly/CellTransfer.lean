/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Family
public import KAM.Planetary.PGAssembly.Chart
public import KAM.Planetary.PGAssembly.CellTransferTile
public import KAM.Planetary.Hamiltonian.Liouville
public import KAM.Planetary.Hamiltonian.TorusUnion

/-!
# P Part 5: cell transfer (`bpP:p5:cell-transfer`)

`outputRepresentative` is the part of the raw union with input angles in the unit cell. Its
σ-compactness comes from the Lipschitz parametrisation, lattice saturation and the F-sigma cell
(`stepP:p5:ct-cell`). The union `kset` is the `phi`-image of the scaled raw union, hence Borel
(P1 Liouville), and cut by the fast cell it is the disjoint union of the fast translates of the
`phi`-image of the scaled representative (`stepP:p5:ct-dec`, `ct-disj`, `ct-count`); `phi` is
injective there and P1 `chart_measure_image` with `volume_angleScale_image` gives the exact
factor `(2π)^(a+b)` (`stepP:p5:ct-liou`). Declarations are copied verbatim from
`P45Signatures.lean`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CT.
-/

@[expose] public noncomputable section

open Set MeasureTheory KAM.ODE

namespace KAM.Planetary

variable {a b : ℕ}

def outputRepresentative (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  rawUnion d r mu h B ∩ {z | z.1 ∈ unitCube (a+b)}

theorem ct_spec (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    PGFamilySpec d r mu h (pgFamily d r mu h) :=
  (torus_conv d r mu h).choose_spec

/-- The raw family as a map on phase space. -/
def ctCellMap (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    Phase (a+b) → Phase (a+b) :=
  fun z => (pgFamily d r mu h).raw z.1 z.2

theorem ct_rawUnion_period (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) (k : Fin (a+b) → ℤ) :
    (fun z => z + angleShift k) '' rawUnion d r mu h B = rawUnion d r mu h B := by
  obtain ⟨-, -, hper, -⟩ := ct_spec d r mu h
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨J, hJ, hy'⟩ := mem_iUnion₂.1 hy
    obtain ⟨θ, rfl⟩ := hy'
    exact mem_iUnion₂.2 ⟨J, hJ, θ + fun i => (k i : ℝ), hper J (hsub hJ) θ k⟩
  · intro hz
    obtain ⟨J, hJ, hz'⟩ := mem_iUnion₂.1 hz
    obtain ⟨θ, rfl⟩ := hz'
    refine ⟨(pgFamily d r mu h).raw J (θ - fun i => (k i : ℝ)),
      mem_iUnion₂.2 ⟨J, hJ, _, rfl⟩, ?_⟩
    have := hper J (hsub hJ) (θ - fun i => (k i : ℝ)) k
    rw [sub_add_cancel] at this
    exact this.symm

theorem ct_rawUnion_eq (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) :
    rawUnion d r mu h B = ⋃ k : Fin (a+b) → ℤ, (fun z => z + angleShift k) ''
      (ctCellMap d r mu h '' (B ×ˢ torusCube (a+b))) := by
  obtain ⟨-, -, hper, -⟩ := ct_spec d r mu h
  exact torus_union_saturation (E := B) (F := ctCellMap d r mu h)
    (fun ω hω ϑ k => hper ω (hsub hω) ϑ k)

theorem ct_rawUnion_sigmaCompact (d : PGData a b) (r mu : ℝ)
    (h : admissible d (pgRstar d) r mu) {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B)
    (hsub : B ⊆ pgD0 d r mu) : IsSigmaCompact (rawUnion d r mu h B) := by
  obtain ⟨-, ⟨L, -, hL⟩, -⟩ := ct_spec d r mu h
  have hF : ∀ x ∈ B ×ˢ torusCube (a+b), ∀ y ∈ B ×ˢ torusCube (a+b),
      ‖ctCellMap d r mu h x - ctCellMap d r mu h y‖ ≤ L * ‖x - y‖ :=
    fun x hx y hy => hL x ⟨hsub hx.1, hx.2⟩ y ⟨hsub hy.1, hy.2⟩
  rw [ct_rawUnion_eq d r mu h hsub]
  exact isSigmaCompact_iUnion _ fun k =>
    ((torus_union_measurableSet_of_sigmaCompact hB hF).1).image (continuous_id.add continuous_const)

theorem ct_sigmaCompact_inter_cell {n : ℕ} {R : Set (Phase n)} (hR : IsSigmaCompact R) :
    IsSigmaCompact (R ∩ {z : Phase n | z.1 ∈ unitCube n}) := by
  obtain ⟨K, hK, rfl⟩ := hR
  obtain ⟨C, hC, hCU⟩ := (isSigmaCompact_torusCube (d := n))
  have key : (⋃ i, K i) ∩ {z : Phase n | z.1 ∈ unitCube n} =
      ⋃ p : ℕ × ℕ, K p.1 ∩ Prod.fst ⁻¹' C p.2 := by
    ext z
    have hz : z.1 ∈ unitCube n ↔ ∃ m, z.1 ∈ C m := by
      have h0 : z.1 ∈ torusCube n ↔ ∃ m, z.1 ∈ C m := by rw [← hCU]; simp
      exact h0
    simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, mem_preimage, Prod.exists, hz]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨m, hm⟩⟩
      exact ⟨i, m, hi, hm⟩
    · rintro ⟨i, m, hi, hm⟩
      exact ⟨⟨i, hi⟩, ⟨m, hm⟩⟩
  rw [key]
  exact isSigmaCompact_iUnion_of_isCompact _ fun p =>
    (hK p.1).inter_right ((hC p.2).isClosed.preimage continuous_fst)

theorem ct_continuous_angleScale {n : ℕ} (c : ℝ) : Continuous (angleScale c : Phase n → Phase n) :=
  (angleScaleCLM c).continuous

theorem ct_scaled_subset (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) :
    angleScale (2*Real.pi) '' rawUnion d r mu h B ⊆ phiDomain d r mu := by
  obtain ⟨-, -, -, -, hout, -⟩ := ct_spec d r mu h
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨J, hJ, hy'⟩ := mem_iUnion₂.1 hy
  obtain ⟨θ, rfl⟩ := hy'
  exact (location d r mu h _ (hout J (hsub hJ) θ)).1

theorem ct_kset_eq (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) :
    kset d r mu h B = phi d r mu h '' (angleScale (2*Real.pi) '' rawUnion d r mu h B) := by
  ext z
  constructor
  · intro hz
    obtain ⟨J, hJ, hz'⟩ := mem_iUnion₂.1 hz
    obtain ⟨θ, rfl⟩ := hz'
    exact ⟨_, ⟨_, mem_iUnion₂.2 ⟨J, hJ, mem_range_self θ⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨J, hJ, hy'⟩ := mem_iUnion₂.1 hy
    obtain ⟨θ, rfl⟩ := hy'
    exact mem_iUnion₂.2 ⟨J, hJ, mem_range_self θ⟩

theorem ct_kset_subset_cylinder (d : PGData a b) (r mu : ℝ)
    (h : admissible d (pgRstar d) r mu) {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) :
    kset d r mu h B ⊆ cylinder d.V r := by
  obtain ⟨-, -, -, -, hout, -⟩ := ct_spec d r mu h
  rw [ct_kset_eq]
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨J, hJ, hy'⟩ := mem_iUnion₂.1 hy
  obtain ⟨θ, rfl⟩ := hy'
  exact (location d r mu h _ (hout J (hsub hJ) θ)).2

theorem ct_kset_measurable (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B) (hsub : B ⊆ pgD0 d r mu) :
    MeasurableSet (kset d r mu h B) := by
  obtain ⟨hO, hΨ, -, -⟩ := phi_chart d r mu h
  rw [ct_kset_eq]
  exact measurableSet_chart_image one_pos hO hΨ (ct_scaled_subset d r mu h hsub)
    (measurableSet_of_isSigmaCompact
      ((ct_rawUnion_sigmaCompact d r mu h hB hsub).image (ct_continuous_angleScale _)))

theorem ct_angleShift_add {n : ℕ} (k m : Fin n → ℤ) :
    (angleShift (k + m) : Phase n) = angleShift k + angleShift m := by
  refine Prod.ext (funext fun i => ?_) (by simp [angleShift])
  simp [angleShift]

/-- Two points of the unit cell that differ by an integer shift coincide (`stepP:p5:ct-disj`). -/
theorem ct_cell_shift_unique {n : ℕ} {y y' : Phase n} (hy : y.1 ∈ unitCube n)
    (hy' : y'.1 ∈ unitCube n) {p q : Fin n → ℤ} (h : y' + angleShift p = y + angleShift q) :
    y' = y ∧ p = q := by
  have hp : p = q := by
    funext i
    have h1 := congrArg (fun w : Phase n => w.1 i) h
    simp only [Prod.fst_add, Pi.add_apply, angleShift] at h1
    have a1 := Set.mem_pi.1 hy i (mem_univ i)
    have b1 := Set.mem_pi.1 hy' i (mem_univ i)
    have h3 : ((p i : ℤ) : ℝ) < q i + 1 := by linarith [a1.1, a1.2, b1.1, b1.2]
    have h4 : ((q i : ℤ) : ℝ) < p i + 1 := by linarith [a1.1, a1.2, b1.1, b1.2]
    have h5 : p i < q i + 1 := by exact_mod_cast h3
    have h6 : q i < p i + 1 := by exact_mod_cast h4
    omega
  subst hp
  exact ⟨add_right_cancel h, rfl⟩

theorem ct_fastShift_zero : (fastShift (0 : Fin a → ℤ) : Phase (a+b)) = 0 := by
  refine Prod.ext (funext fun i => ?_) rfl
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [fastShift, Fin.append_left, Fin.append_right]

theorem ct_blockFast_append (k : Fin a → ℤ) :
    blockFast (Fin.append k (0 : Fin b → ℤ)) = k := by
  funext i; simp [blockFast, Fin.append_left]

theorem ct_phi_shift (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) {y : Phase (a+b)}
    (hy : y ∈ rawUnion d r mu h B) (M : Fin (a+b) → ℤ) :
    phi d r mu h (angleScale (2*Real.pi) (y + angleShift M)) =
      phi d r mu h (angleScale (2*Real.pi) y) + fastShift (blockFast M) := by
  obtain ⟨-, -, hshift, -⟩ := phi_chart d r mu h
  have hz := ct_scaled_subset d r mu h hsub ⟨y, hy, rfl⟩
  rw [angleScale_add_angleShift]
  exact (hshift _ hz M).2

/-- Fast translates of points of the scaled representative are distinct (`stepP:p5:ct-disj`). -/
theorem ct_translate_inj (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) {y y' : Phase (a+b)}
    (hy : y ∈ outputRepresentative d r mu h B) (hy' : y' ∈ outputRepresentative d r mu h B)
    {k k' : Fin a → ℤ}
    (heq : phi d r mu h (angleScale (2*Real.pi) y) + fastShift k =
      phi d r mu h (angleScale (2*Real.pi) y') + fastShift k') : y = y' ∧ k = k' := by
  obtain ⟨-, -, -, hQ2⟩ := phi_chart d r mu h
  set M : Fin (a+b) → ℤ := Fin.append k (0 : Fin b → ℤ) with hM
  set M' : Fin (a+b) → ℤ := Fin.append k' (0 : Fin b → ℤ) with hM'
  have e1 := ct_phi_shift d r mu h hsub hy.1 M
  have e2 := ct_phi_shift d r mu h hsub hy'.1 M'
  rw [hM, ct_blockFast_append] at e1
  rw [hM', ct_blockFast_append] at e2
  have hper := ct_rawUnion_period d r mu h hsub
  have m1 : y + angleShift M ∈ rawUnion d r mu h B := by
    rw [← hper M]; exact mem_image_of_mem _ hy.1
  have m2 : y' + angleShift M' ∈ rawUnion d r mu h B := by
    rw [← hper M']; exact mem_image_of_mem _ hy'.1
  obtain ⟨m, hm⟩ := hQ2 _ (ct_scaled_subset d r mu h hsub ⟨_, m1, rfl⟩) _
    (ct_scaled_subset d r mu h hsub ⟨_, m2, rfl⟩) 0
    (by rw [ct_fastShift_zero, add_zero, e1, e2, heq])
  have hm' : angleScale (2*Real.pi) (y' + angleShift M') =
      angleScale (2*Real.pi) (y + angleShift M + angleShift m) := by
    rw [angleScale_add_angleShift (2*Real.pi) (y + angleShift M) m]; exact hm
  have hm'' := fam_angleScale_injective (by positivity) hm'
  rw [add_assoc, ← ct_angleShift_add] at hm''
  obtain ⟨hyy, -⟩ := ct_cell_shift_unique hy.2 hy'.2 hm''
  subst hyy
  refine ⟨rfl, ?_⟩
  have h3 := add_left_cancel heq
  funext i
  have := congrArg (fun w : Phase (a+b) => w.1 (Fin.castAdd b i)) h3
  simp only [fastShift_fst_castAdd] at this
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast mul_left_cancel₀ hp this

theorem ct_kset_cover (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hsub : B ⊆ pgD0 d r mu) :
    kset d r mu h B = ⋃ k : Fin a → ℤ, (fun z : Phase (a+b) => z + fastShift k) ''
      (phi d r mu h '' (angleScale (2*Real.pi) '' outputRepresentative d r mu h B)) := by
  have hper := ct_rawUnion_period d r mu h hsub
  rw [ct_kset_eq]
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ := exists_shift_mem_unitCell (A := rawUnion d r mu h B) hper hy
    have e := ct_phi_shift d r mu h hsub hy m
    refine mem_iUnion.2 ⟨-(blockFast m), ?_⟩
    refine ⟨_, ⟨_, ⟨_, ⟨hm.1, ?_⟩, rfl⟩, rfl⟩, ?_⟩
    · exact Set.mem_pi.2 fun i _ => hm.2 i
    · simp only [e, add_assoc, ← fastShift_add, add_neg_cancel, ct_fastShift_zero, add_zero]
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := hk
    have m1 : y + angleShift (Fin.append k (0 : Fin b → ℤ)) ∈ rawUnion d r mu h B := by
      rw [← hper (Fin.append k (0 : Fin b → ℤ))]; exact mem_image_of_mem _ hy.1
    refine ⟨_, ⟨_, m1, rfl⟩, ?_⟩
    rw [ct_phi_shift d r mu h hsub hy.1, ct_blockFast_append]

theorem cell_transfer (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B) (hsub : B ⊆ pgD0 d r mu) :
    IsSigmaCompact (outputRepresentative d r mu h B) ∧ MeasurableSet (kset d r mu h B) ∧
    kset d r mu h B ⊆ cylinder d.V r ∧
    volume (kset d r mu h B ∩ cylinderCell d.V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b))*volume (outputRepresentative d r mu h B) := by
  have hR0 : IsSigmaCompact (outputRepresentative d r mu h B) :=
    ct_sigmaCompact_inter_cell (ct_rawUnion_sigmaCompact d r mu h hB hsub)
  have hcyl := ct_kset_subset_cylinder d r mu h hsub
  refine ⟨hR0, ct_kset_measurable d r mu h hB hsub, hcyl, ?_⟩
  obtain ⟨hO, hΨ, -, -⟩ := phi_chart d r mu h
  have hA0sub : angleScale (2*Real.pi) '' outputRepresentative d r mu h B ⊆ phiDomain d r mu :=
    (image_mono inter_subset_left).trans (ct_scaled_subset d r mu h hsub)
  have hA0meas : MeasurableSet (angleScale (2*Real.pi) '' outputRepresentative d r mu h B) :=
    measurableSet_of_isSigmaCompact (hR0.image (ct_continuous_angleScale _))
  have hEmeas : MeasurableSet
      (phi d r mu h '' (angleScale (2*Real.pi) '' outputRepresentative d r mu h B)) :=
    measurableSet_chart_image one_pos hO hΨ hA0sub hA0meas
  have hinj : InjOn (phi d r mu h)
      (angleScale (2*Real.pi) '' outputRepresentative d r mu h B) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ heq
    have := (ct_translate_inj d r mu h hsub hy hy' (k := 0) (k' := 0)
      (by simp only [ct_fastShift_zero, add_zero]; exact heq)).1
    rw [this]
  have hcell : kset d r mu h B ∩ cylinderCell d.V r = kset d r mu h B ∩ ctFastCell a b := by
    ext z
    exact ⟨fun hz => ⟨hz.1, hz.2.2⟩, fun hz => ⟨hz.1, hcyl hz.1, hz.2⟩⟩
  rw [hcell, ct_kset_cover d r mu h hsub]
  rw [volume_fastTranslates_inter_fastCell hEmeas]
  · rw [(chart_measure_image one_pos hO hΨ hA0sub hA0meas.nullMeasurableSet).2.2 hinj,
      volume_angleScale_image (by positivity)]
    simp
  · intro k k' x hx hx'
    obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨_, ⟨y', hy', rfl⟩, rfl⟩, he⟩ := hx'
    exact (ct_translate_inj d r mu h hsub hy hy' he.symm).2

end KAM.Planetary

end
