/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Iso.Confinement.PatchConst
public import KAM.Iso.Confinement.RealHam
public import KAM.Iso.Confinement.Graph
public import KAM.Iso.Confinement.EnergyCoordinate
public import KAM.Iso.Confinement.Position
public import KAM.Iso.Confinement.Invariance

/-!
# Part 5: separation

Blueprint `bpI:p5:separation`, steps `sp-open`, `sp-init`, `sp-closure`, `sp-window`, `sp-bdry`,
`sp-barrier`. The data are those
of `§sec-sep` (`SepSetting`): one chart patch `p`, its constants, the smallness, and the two
torus graphs `Y₊, Y₋` at the energy `E`; the region is
`𝒱 = sepRegion p Y₊ Y₋ = {(φ, I) : I ∈ Ω, μ₋(φ) < m(I) < μ₊(φ)}`, `μ_± = m ∘ Y_±`.

* (a) `separation_isOpen`: `𝒱` is open. `separation_init`: an initial point with
  `‖I₀ - c‖ < ρc` lies in `𝒱` and off both tori.
* (b) `separation_closure`: `closure 𝒱 ⊆ ℝ² × 𝒦`. `separation_window`: on the energy level of
  such a point, `I ∈ 𝒦` forces `|h(I) - E_c| < δE`. `separation_boundary`: `∂𝒱 ∩ G ⊆ 𝒯₊ ∪ 𝒯₋`
  (through `energy_coordinate`).
* (c) `separation_confined_of_invariant` (conditional helper, takes the invariance of
  `𝒯₊ ∪ 𝒯₋` as a premise) and the source-facing `separation_confined` (takes the named Part 3
  output for both tori and derives the invariance by `torus_invariant`): a solution of `X_ℝ` in
  `W_B` through `z₀` stays in `𝒱` (`gen_barrier`).
-/

public section

open Set Metric

namespace KAM.Iso.Confinement

open KAM KAM.ODE

section Separation

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε η₁ F₁ C_K : ℝ} {p : EnergyPatch (realPart h) B η₁}
  {r Lm LΦ κ E : ℝ} {Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Ip Im : Fin 2 → ℝ}

/-! ## Helpers: slopes of the two graphs and continuity -/

/-- The three slopes `(μ₋(φ), m(I), μ₊(φ))` of a point `(φ, I)`. -/
private theorem continuousOn_slopes
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {A : Set P2} (hA : ∀ z ∈ A, z.2 ∈ p.W) :
    ContinuousOn (fun z : P2 => (p.m (Ym z.1), p.m z.2, p.m (Yp z.1))) A := by
  have hm : ContinuousOn p.m p.W := p.m_contDiffOn.continuousOn
  have hμm : Continuous fun z : P2 => p.m (Ym z.1) :=
    (slope_continuous p S.pconst S.minus S.small.lt_r.le).comp continuous_fst
  have hμp : Continuous fun z : P2 => p.m (Yp z.1) :=
    (slope_continuous p S.pconst S.plus S.small.lt_r.le).comp continuous_fst
  exact hμm.continuousOn.prodMk ((hm.comp continuous_snd.continuousOn hA).prodMk
    hμp.continuousOn)

/-- `|m (Y_+ φ)| < δm`. -/
private theorem abs_slope_plus_lt (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    (φ : Fin 2 → ℝ) : |p.m (Yp φ)| < p.δm := by
  obtain ⟨h1, h2⟩ := slope_window_plus p S.pconst S.small S.plus φ
  exact abs_lt.2 ⟨by linarith [p.δm_pos], h2⟩

/-- `|m (Y_- φ)| < δm`. -/
private theorem abs_slope_minus_lt
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    (φ : Fin 2 → ℝ) : |p.m (Ym φ)| < p.δm := by
  obtain ⟨h1, h2⟩ := slope_window_minus p S.pconst S.small S.minus φ
  exact abs_lt.2 ⟨h1, by linarith [p.δm_pos]⟩

/-! ## (a) openness and the initial point -/

/-- (a), openness (step `sp-open`). -/
theorem separation_isOpen (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im) :
    IsOpen (sepRegion p Yp Ym) := by
  have hU : IsOpen ((univ : Set (Fin 2 → ℝ)) ×ˢ p.Omega) := isOpen_univ.prod p.isOpen_Omega
  have hcont := continuousOn_slopes S (A := (univ : Set (Fin 2 → ℝ)) ×ˢ p.Omega)
    (fun z hz => hz.2.1)
  have ht : IsOpen {x : ℝ × ℝ × ℝ | x.1 < x.2.1 ∧ x.2.1 < x.2.2} :=
    (isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))
  convert hcont.isOpen_inter_preimage hU ht using 1
  ext z
  exact ⟨fun hz => ⟨⟨mem_univ _, hz.1⟩, hz.2⟩, fun hz => ⟨hz.1.2, hz.2⟩⟩

/-- (a), the initial point (step `sp-init`): `‖I₀ - c‖ < ρc ⇒ z₀ ∈ 𝒱 ∖ (𝒯₊ ∪ 𝒯₋)`. -/
theorem separation_init (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) :
    z₀ ∈ sepRegion p Yp Ym ∧ z₀ ∉ graphSet Yp ∪ graphSet Ym := by
  have hball : z₀.2 ∈ ball p.c p.ρc := by rwa [mem_ball, dist_eq_norm]
  have hW : z₀.2 ∈ p.W := p.ball_subset hball
  obtain ⟨h1l, h1r⟩ := abs_lt.1 (p.ball_h _ hball)
  obtain ⟨h2l, h2r⟩ := abs_lt.1 (p.ball_m _ hball)
  have hδE := p.δE_pos
  have hδm := p.δm_pos
  obtain ⟨hp1, hp2⟩ := slope_window_plus p S.pconst S.small S.plus z₀.1
  obtain ⟨hm1, hm2⟩ := slope_window_minus p S.pconst S.small S.minus z₀.1
  refine ⟨⟨⟨hW, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rintro (hz | hz)
    · have hz' : z₀.2 = Yp z₀.1 := hz
      have := congrArg p.m hz'
      linarith
    · have hz' : z₀.2 = Ym z₀.1 := hz
      have := congrArg p.m hz'
      linarith

/-! ## (b) closure, energy window, boundary -/

/-- (b), closure (step `sp-closure`): `closure 𝒱 ⊆ ℝ² × 𝒦`. -/
theorem separation_closure (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im) :
    closure (sepRegion p Yp Ym) ⊆ univ ×ˢ p.K := by
  have _hS := S
  refine closure_minimal ?_ (isClosed_univ.prod p.isCompact_K.isClosed)
  intro z hz
  exact ⟨mem_univ _, p.Omega_subset_K hz.1⟩

/-- The energy `E = H_ℝ(z₀)` of an initial point near the centre is within `3 δE / 4` of the
centre energy. -/
private theorem abs_energy_sub_lt (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀) :
    |E - realPart h p.c| < 3 * p.δE / 4 := by
  have hball : z₀.2 ∈ ball p.c p.ρc := by rwa [mem_ball, dist_eq_norm]
  have hB : z₀.2 ∈ B := p.W_subset_B (p.ball_subset hball)
  have h1 := realHam_sub_le S.base S.perturb (z := z₀) (subset_realAct S.base.hr hB)
  have h2 := p.ball_h _ hball
  have h3 := abs_sub_le E (realPart h z₀.2) (realPart h p.c)
  rw [← hE] at h1
  have h4 := S.small.lt_dE
  linarith

/-- Any point of the energy level `{H_ℝ = E}` over `B` has chart energy within `δE` of the
centre energy. -/
private theorem abs_chart_energy_lt
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀) {z : P2}
    (hzE : realHamiltonian h f z = E) (hzB : z.2 ∈ B) :
    |realPart h z.2 - realPart h p.c| < p.δE := by
  have h1 := realHam_sub_le S.base S.perturb (z := z) (subset_realAct S.base.hr hzB)
  rw [hzE, abs_sub_comm] at h1
  have h2 := abs_sub_le (realPart h z.2) E (realPart h p.c)
  have h3 := abs_energy_sub_lt S hz₀ hE
  have h4 := S.small.lt_dE
  linarith

/-- (b), energy window (step `sp-window`): `E = H_ℝ(z₀)`, `‖I₀ - c‖ < ρc`; on the level set,
`I ∈ 𝒦 ⇒ |h(I) - E_c| < δE`. -/
theorem separation_window (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀) :
    ∀ z ∈ levelSet (realHamiltonian h f) E, z.2 ∈ p.K →
      |realPart h z.2 - realPart h p.c| < p.δE := fun _ hz hzK =>
  abs_chart_energy_lt S hz₀ hE hz (p.W_subset_B hzK.1)

/-- Points of the closure of `𝒱` satisfy `μ₋ ≤ m ≤ μ₊` (closed condition on `ℝ² × 𝒦`). -/
private theorem slope_le_of_mem_closure
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im) {z : P2}
    (hz : z ∈ closure (sepRegion p Yp Ym)) :
    p.m (Ym z.1) ≤ p.m z.2 ∧ p.m z.2 ≤ p.m (Yp z.1) := by
  have hcont := continuousOn_slopes S (A := (univ : Set (Fin 2 → ℝ)) ×ˢ p.K) (fun z hz => hz.2.1)
  have ht : IsClosed {x : ℝ × ℝ × ℝ | x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2} :=
    (isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
      (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))
  have hclosed := hcont.preimage_isClosed_of_isClosed
    (isClosed_univ.prod p.isCompact_K.isClosed) ht
  have hsub : sepRegion p Yp Ym ⊆ ((univ : Set (Fin 2 → ℝ)) ×ˢ p.K) ∩
      (fun z : P2 => (p.m (Ym z.1), p.m z.2, p.m (Yp z.1))) ⁻¹'
        {x : ℝ × ℝ × ℝ | x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2} :=
    fun z hz => ⟨⟨mem_univ _, p.Omega_subset_K hz.1⟩, hz.2.1.le, hz.2.2.le⟩
  exact (closure_minimal hsub hclosed hz).2

/-- Step `sp-bdry`, `boundary_slope_eq`/`boundary_mem_Q`: a point of the energy level over `𝒦`
whose slope equals that of the torus graph `Y` has the same position as the graph point, by
injectivity of the energy coordinate (`energy_coordinate`). -/
private theorem eq_graph_of_slope_eq
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ} {mσ : ℝ}
    (G : GraphData p (realHamiltonian h f) E (C_K * ε) Y I mσ)
    (hwin : ∀ φ, |p.m (Y φ)| < p.δm) {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc)
    (hE : E = realHamiltonian h f z₀) {z : P2} (hzE : realHamiltonian h f z = E)
    (hzK : z.2 ∈ p.K) (hzm : p.m z.2 = p.m (Y z.1)) : z.2 = Y z.1 := by
  obtain ⟨-, hYW, hYB⟩ := torus_graph_mem p S.pconst G.near G.base_mem S.small.lt_r.le z.1
  have hwY := abs_chart_energy_lt S hz₀ hE (G.energy z.1) hYB
  obtain ⟨hwl, hwr⟩ := abs_lt.1 hwY
  obtain ⟨hml, hmr⟩ := abs_lt.1 (hwin z.1)
  have hQz : (realPart h z.2, p.m z.2) ∈ p.Q := hzK.2
  have hQY : (realPart h (Y z.1), p.m z.2) ∈ p.Q := by
    rw [hzm]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have e1 : p.Ψ (realPart h z.2, p.m z.2) = z.2 := p.Ψ_left z.2 hzK.1
  have e2 : p.Ψ (realPart h (Y z.1), p.m z.2) = Y z.1 := by
    rw [hzm]
    exact p.Ψ_left _ hYW
  have heq : realHamiltonian h f (z.1, p.Ψ (realPart h z.2, p.m z.2)) =
      realHamiltonian h f (z.1, p.Ψ (realPart h (Y z.1), p.m z.2)) := by
    rw [e1, e2]
    exact hzE.trans (G.energy z.1).symm
  have := energy_coordinate S.base S.perturb p S.pconst S.small S.dbound z.1 hQz hQY heq
  rwa [e1, e2] at this

/-- (b), boundary on the level (step `sp-bdry`): `∂𝒱 ∩ G ⊆ 𝒯₊ ∪ 𝒯₋`. -/
theorem separation_boundary (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀) :
    frontier (sepRegion p Yp Ym) ∩ levelSet (realHamiltonian h f) E ⊆
      graphSet Yp ∪ graphSet Ym := by
  rintro z ⟨hfr, hG⟩
  rw [(separation_isOpen S).frontier_eq] at hfr
  obtain ⟨hcl, hnV⟩ := hfr
  have hzK : z.2 ∈ p.K := (separation_closure S hcl).2
  obtain ⟨hle1, hle2⟩ := slope_le_of_mem_closure S hcl
  obtain ⟨hp1, hp2⟩ := slope_window_plus p S.pconst S.small S.plus z.1
  obtain ⟨hm1, hm2⟩ := slope_window_minus p S.pconst S.small S.minus z.1
  obtain ⟨hwl, hwr⟩ := abs_lt.1 (separation_window S hz₀ hE z hG hzK)
  by_cases h1 : p.m (Ym z.1) < p.m z.2
  · by_cases h2 : p.m z.2 < p.m (Yp z.1)
    · exact (hnV ⟨⟨hzK.1, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩, h1, h2⟩).elim
    · exact Or.inl (eq_graph_of_slope_eq S S.plus (abs_slope_plus_lt S) hz₀ hE hG hzK
        (le_antisymm hle2 (not_lt.1 h2)))
  · exact Or.inr (eq_graph_of_slope_eq S S.minus (abs_slope_minus_lt S) hz₀ hE hG hzK
      (le_antisymm (not_lt.1 h1) hle1))

/-! ## (c) the barrier -/

/-- (c), the barrier, CONDITIONAL HELPER (distinct name): `hinv` is a produced fact.
The source-facing `separation_confined` below derives it. The barrier (step `sp-barrier`): a
solution of `X_ℝ` in `W_B` on an interval `J ∋ 0` through `z₀` stays in `𝒱`. `hinv` is Lemma
`invariance` for `𝒯₊ ∪ 𝒯₋` (`range k_± = graphSet Y_±`, `isInvariantSet_union`). -/
theorem separation_confined_of_invariant
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀)
    (hinv : IsInvariantSet (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B)
      (graphSet Yp ∪ graphSet Ym))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → P2}
    (hz : IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) J z)
    (hz0 : z 0 = z₀) : ∀ t ∈ J, z t ∈ sepRegion p Yp Ym := by
  obtain ⟨hinit, hnotS⟩ := separation_init S hz₀
  have hzE : ∀ t ∈ J, realHamiltonian h f (z t) = E := fun t ht => by
    rw [hE, ← hz0]
    exact realHam_energy_const S.base S.perturb hJ hz t ht 0 h0
  refine gen_barrier hJ h0 hz (separation_isOpen S) (by rwa [hz0])
    (G := levelSet (realHamiltonian h f) E) ?_ hinv (separation_boundary S hz₀ hE)
    (by rwa [hz0])
  rintro _ ⟨t, ht, rfl⟩
  exact hzE t ht

/-- The real torus `k(ℝ²) = graph Y` over a graph with the data `GraphData` has actions in `B`
(`torus_graph_mem`). -/
private theorem torus_mem_B (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ} {mσ : ℝ}
    (G : GraphData p (realHamiltonian h f) E (C_K * ε) Y I mσ)
    {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hg : range (realRestriction K) = graphSet Y)
    (θ : Fin 2 → ℝ) : (realRestriction K θ).2 ∈ B := by
  have h1 : realRestriction K θ ∈ graphSet Y := hg ▸ mem_range_self θ
  have h2 : (realRestriction K θ).2 = Y (realRestriction K θ).1 := h1
  rw [h2]
  exact (torus_graph_mem p S.pconst G.near G.base_mem S.small.lt_r.le _).2.2

/-- (c), SOURCE-FACING (`bpI:p5:separation` (c)): premises are the named output of Part 3
(`TorusOutput` for both tori) and the graph identifications `𝒯_± = graph Y_±` of `§sec-graph`;
`𝒯₊ ∪ 𝒯₋` invariance is derived inside (`torus_invariant` twice, `isInvariantSet_union`), with
`(k θ).2 ∈ B` recovered from `GraphData.near`, `base_mem`, `PatchConst.thick_subset`,
`Smallness.lt_r`. -/
theorem separation_confined (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {ωp ωm : Fin 2 → ℝ}
    (Tp : TorusOutput h f ε C_K s₀ E Kp Ip ωp) (Tm : TorusOutput h f ε C_K s₀ E Km Im ωm)
    (hgp : Set.range (realRestriction Kp) = graphSet Yp)
    (hgm : Set.range (realRestriction Km) = graphSet Ym)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → P2}
    (hz : IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) J z)
    (hz0 : z 0 = z₀) : ∀ t ∈ J, z t ∈ sepRegion p Yp Ym := by
  have hip := (torus_invariant S.base S.perturb Tp (torus_mem_B S S.plus hgp)).2
  have him := (torus_invariant S.base S.perturb Tm (torus_mem_B S S.minus hgm)).2
  rw [hgp] at hip
  rw [hgm] at him
  exact separation_confined_of_invariant S hz₀ hE (isInvariantSet_union hip him) hJ h0 hz hz0

end Separation

end KAM.Iso.Confinement
