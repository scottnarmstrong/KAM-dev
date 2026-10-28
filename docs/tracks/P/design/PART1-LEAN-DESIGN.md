# Lean design for blueprint-P Part 1 (Hamiltonian tools: charts, period conversion, Diophantine conversion, Liouville)

Design v1, 2026-10-28, branch `inp-design-p1` (brief `.drafts/briefs/offload-main/DESIGN-P1.md`). Planning evidence,
not approved Lean; no proofs. Scope: every node of `docs/graph/P/DEPGRAPH.md` whose statement source is
`blueprint-P/parts/p1-hamiltonian-tools.tex` (46 nodes: 5 externals, 1 data node, 22 statement nodes, 18 steps).
No frozen declaration is in scope (Part 1 has no root); the frozen objects consumed are definitions only
(`symplecticForm`, `hamiltonianVectorField`, `IsDiophantine`, `Phase`, `fastShift`, `IsCylinderTorus`,
`IsPhysicalTorus`). Modeled on `docs/tracks/P/design/KEPLER-LEAN-DESIGN.md` and
`docs/tracks/N/design/PART145-LEAN-DESIGN.md`.

**The signatures.** Every result node has its exact Lean statement in the untracked
`/root/code/KAM-inp/.drafts/design/PPart1Signatures.lean` (568 lines, 76 `def`/`theorem`, sha256
`78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7`; copied verbatim in Appendix A).
- Check: copied to `.drafts/scratch/PPart1Signatures.lean` in this worktree and run with
  `LEAN_NUM_THREADS=1 nice -n 5 lake env lean`: **exit 0, 64 diagnostics, all `declaration uses 'sorry'`**
  (plus the `#check`/`#synth` probe output). No `set_option`, no `maxHeartbeats`, no `axiom/admit/unsafe/opaque`.
- Imports: `Mathlib`, frozen DEFINITIONS, and delivered implementation modules (`KAM.Kepler.Basic`, `KAM.ODE.Basic`,
  `KAM.ODE.Uniqueness`, `KAM.Canonical.Setting`, `KAM.Measure.Lipschitz`, `KAM.Measure.McShane`). No provider, no
  frozen theorem anchor, no DRAFT_SORRY anchor.

## 0. Decisions in brief

1. **Location and namespace.** New directory `KAM/Planetary/Hamiltonian/` (namespace `KAM.Planetary`, the
   namespace in which the Kepler design already expects `angleScale`, `fullShift`, `measure_chart_image`). Eight
   modules, one per section of the signatures file (Section 6).
2. **`IsChart` unfolds to the Kepler predicate.** `IsChart c Ψ O := AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O`
   with the delivered `KAM.Kepler.IsSymplecticOn` (no second symplecticity predicate). It is homogeneous
   (`Phase d → Phase d`): the blueprint chart is, and the field identity needs invertibility. Heterogeneous charts
   (`poincareProd : Phase (n+n) → Phase (n*2)`) enter through the delivered `poincareProdCast`
   (`isChart_iff.2 ⟨analyticOnNhd_poincareProdCast hm hκ, poincareProdCast_symplectic hm hκ⟩`). `0 < c` and
   `IsOpen O` are hypotheses at use sites, as in the delivered Kepler/Poincare code and the Kepler signature of
   `measure_chart_image`.
3. **Part 1 owns `angleScale` (`S_c`) and `fullShift`, with the Kepler bodies.** `angleScale {d} (c) (z) :=
   (c • z.1, z.2)` is character-for-character the Kepler signature; `fullShift` keeps the Kepler body
   `(fun i => 2 * π * (k i : ℝ), 0)` but is generalised from `Fin (n + n) → ℤ` to any `Fin d → ℤ` (every Kepler
   call site `fullShift k` with `k : Fin (n + n) → ℤ` elaborates unchanged). They live in `Hamiltonian/Chart`,
   which `Poincare/Lattice` (P7-6) imports; P7-6 must NOT declare them (Kepler design risk 8: "only those
   declarations move").
4. **`measure_chart_image` adopted verbatim.** The Kepler consumer form (P6-5 (b)) is declared by Part 1 with the
   exact Kepler signature (separate `AnalyticOnNhd`/`IsSymplecticOn` hypotheses, inline `((fun i => (k i : ℝ)), 0)`,
   Borel `MeasurableSet`), proved as a corollary of `liouville_lattice` + `liouville_lattice_measurableSet`
   (`angleShift k` is `rfl`-equal to the inline vector). The F6 caveat is kept: it is a FULL-position-lattice
   theorem and not the interface for P12's Cartesian cylinder measure.
5. **The integer lattice `ι_k` is the delivered `KAM.ODE.angleShift`** (`KAM/ODE/Basic.lean`,
   `(fun i => (k i : ℝ), 0)`), not a new definition.
6. **Lattice tori are parametrised by the lattice family.** `IsLatticeTorus L G O w K` has the six clauses
   (L1)-(L6) with `K(θ+k) = K θ + L k`; the blueprint `LT(G,O,w,K)` is `IsLatticeTorus angleShift G O w K`, and
   the `2π` lattice of `phys-pipeline` is `L = fullShift`. The transport theorem is stated for arbitrary `L`
   (its proof never uses the form of `ι_k`), which is exactly the blueprint's "the argument ... applies verbatim
   with `τ_k` in place of `ι_k`" (phys-pipeline proof) made a statement. This is a generalisation, not a change:
   the blueprint instance is `L := angleShift`.
7. **The `2π` convention is a predicate, the period conversion an `iff`.** `IsTwoPiLatticeTorus G O ω κ` is CP09's
   torus in the `2π` convention (lattice `fullShift`, flow with `ω̃`); `periodOne κ θ := κ ((2π) • θ)` and
   `isLatticeTorus_periodOne_iff : IsLatticeTorus fullShift G O ((2π)⁻¹ • ω) (periodOne κ) ↔ IsTwoPiLatticeTorus G O ω κ`
   packages `period-convert` (c). The frozen frequency `w = ω̃/2π` is written `(2 * π)⁻¹ • ω`.
8. **Linear algebra is coordinate-free.** Matrices `M₀`, `J₀` are not introduced: `Ω` is the frozen
   `symplecticForm`, `X_ℓ` is `linearField ℓ` for `ℓ : Phase d →L[ℝ] ℝ` (`hamiltonianVectorField H z =
   linearField (fderiv ℝ H z)` by `rfl`), `det` is `LinearMap.det`, and `X_{ℓ∘A} = c A⁻¹ X_ℓ` is stated
   inverse-free as `A (X_{ℓ∘A}) = c • X_ℓ`.
9. **Totality is part of the statements.** `chart_field` is unconditional (both sides are `0` when `H` is not
   differentiable at `Ψ z`), and `chart_field_differentiableAt_iff` transports differentiability.
10. **Haar instance.** Instance search does NOT find `(volume : Measure (Phase d)).IsAddHaarMeasure` (probe:
   `#synth` fails on the product measure; the term `Measure.prod.instIsAddHaarMeasure _ _` works). Part 1 provides
   the theorem `isAddHaarMeasure_volume_phase` and provers use `haveI` locally; no global instance on a Mathlib
   type.
11. **Reuse, not re-proof.** Lipschitz images: `KAM.lip_image_prod`, `KAM.lip_preimage_null_prod`
   (`KAM/Measure/Lipschitz`, `bp:p1:lip-image`); McShane: `KAM.mcshane_prod` (`KAM/Measure/McShane`);
   holomorphic ⇒ analytic: `KAM.holomorphic_analytic` (`KAM/Strip/Analytic`); real slice: the pattern of
   `KAM.real_restriction` (`KAM/Strip/RealRestriction`); ODE: `KAM.ODE.IsSolutionIn`, `gen_uniqueness`,
   `ham_smooth_c1`, `ham_energy`; complexification `KAM.Kepler.phaseToC`; complex form `KAM.Canonical.symplFormC`;
   nondegeneracy (first slot) `KAM.Planetary.eq_zero_of_symplecticForm` (`Poincare/Product`, but see Section 6:
   Part 1 re-proves the 6-line fact in `Algebra` rather than import the Poincare chart).

## 1. Carriers

| object | Lean | source |
|---|---|---|
| phase space `Ph_d` | frozen `Phase d = (Fin d → ℝ) × (Fin d → ℝ)`, positions first, max norm | frozen |
| `Ω` | frozen `KAM.symplecticForm` | frozen |
| `X_H` | frozen `KAM.hamiltonianVectorField` | frozen |
| `X_ℓ` | `linearField ℓ`, `ℓ : Phase d →L[ℝ] ℝ` | new (A) |
| `ι_k` | `KAM.ODE.angleShift k` | delivered (ODE/Basic) |
| `S_c` | `angleScale c`, `angleScaleCLM c` | new (B); Kepler name |
| `(2πk, 0)` | `fullShift k` | new (B); Kepler name/body |
| `c`-chart | `IsChart c Ψ O` | new (B) = `AnalyticOnNhd ∧ KAM.Kepler.IsSymplecticOn` |
| `H^Ψ` | `chartPullback c H Ψ z = c⁻¹ * H (Ψ z)` | new (B) |
| `ℂ^{2d}`, real embedding | `(Fin d → ℂ) × (Fin d → ℂ)`, `KAM.Kepler.phaseToC` | delivered |
| complex `Ω` | `KAM.Canonical.symplFormC` | delivered (Canonical/Setting) |
| `LT(G,O,w,K)` | `IsLatticeTorus angleShift G O w K` | new (D) |
| CP09 `2π` torus | `IsTwoPiLatticeTorus G O ω κ` | new (D) |
| `K(θ) = κ̃(2πθ)` | `periodOne κ` | new (D) |
| `𝒟_{γ₁,γ₂,τ}` | `twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ : Set (Fin (n₁+n₂) → ℝ)` | new (E) |
| `Q` | `unitCell d = {z | ∀ i, z.1 i ∈ Ico 0 1}` | new (F) |
| `[0,1)^d`, `A = E × [0,1)^d` | `unitCube d`, `E ×ˢ unitCube d` | new (G) |
| Lebesgue measure | `MeasureTheory.volume` (product of Pi volumes); Lebesgue measurable = `NullMeasurableSet`, Borel = `MeasurableSet` | Mathlib |
| solutions | `KAM.ODE.IsSolutionIn` | delivered |

### 1.1 Standing structures
None. `IsChart`, `IsLatticeTorus`, `IsTwoPiLatticeTorus` are `Prop`-valued definitions (conjunctions, `@[expose]`),
typing data for consumers; no theorem of Part 1 produces one from a conclusion-shaped premise.

## 2. Node table

All declarations in namespace `KAM.Planetary`. Module = `KAM/Planetary/Hamiltonian/<M>.lean`.

| node | kind | Lean | M |
|---|---|---|---|
| `bpP:p1:conv#data` | data | `linearField`, `angleShift` (reuse), `angleScale`, `angleScaleCLM`, `fullShift`; `hamiltonianVectorField_eq_linearField` | Algebra, Chart |
| `bpP:p1:ext-comp` | external | Mathlib `fderiv_comp`, `HasFDerivAt.comp_hasDerivAt`, `AnalyticAt.comp`, `AnalyticOnNhd.comp`; delivered `IsSymplecticOn.comp` | – |
| `bpP:p1:ext-ift` | external | `HasStrictFDerivAt.toOpenPartialHomeomorph`, `HasStrictFDerivAt.to_localInverse`, `ContDiffAt.to_localInverse`, `AnalyticAt.hasStrictFDerivAt` | – |
| `bpP:p1:ext-area` | external | `addHaar_image_le_lintegral_abs_det_fderiv`, `lintegral_abs_det_fderiv_eq_addHaar_image(₀)`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (all `#check`ed) | – |
| `bpP:p1:ext-borel` | external | `MeasurableSet.image_of_continuousOn_injOn`, `NullMeasurableSet.exists_measurable_subset_ae_eq`, `IsSigmaCompact.image_of_continuousOn` | – |
| `bpP:p1:ext-det` | external | `LinearMap.det_comp`, `LinearMap.det_conj`, `LinearMap.det_smul`, `LinearMap.det_prodMap` | – |
| `bpP:p1:omega-algebra` (a) | lemma | `symplecticForm_antisymm`, `eq_zero_of_symplecticForm_right`, `symplecticForm_linearField`, `eq_linearField_iff`, `symplecticForm_hamiltonianVectorField` | Algebra |
| `bpP:p1:omega-algebra` (b) | lemma | `bijective_of_symplectic`, `abs_det_of_symplectic`, `apply_linearField_comp_of_symplectic` | Algebra |
| `bpP:p1:omega-algebra` (c) | lemma | `symplectic_neg_iff` (the matrix form is not introduced; Decision 8) | Algebra |
| `stepP:p1:oa-mat`, `oa-b` | steps | inside the (a), (b) proofs | Algebra |
| `bpP:p1:order` | claim | convention only (no declaration): the frozen order is `(angle, action)` and Part 3 is read after `Prod.swap`; `hamiltonianVectorField` already is `(∂_I H, -∂_θ H)` | – |
| `bpP:p1:chart` | def | `IsChart`, `isChart_iff`, `IsChart.analyticOnNhd/.symplectic/.mono`, `chartPullback`, `IsChart.bijective_fderiv`, `IsChart.abs_det_fderiv` | Chart |
| `bpP:p1:chart-field` | lemma | `chart_field_differentiableAt_iff` (`cf-diff`), `chart_field` (`cf-field`) | Chart |
| `bpP:p1:chart-orbit` | corollary | `chart_orbit` | Chart |
| `bpP:p1:typical` | claim | (2) `isChart_angleScale`; (3) `IsChart.comp`, `chartPullback_comp`; (1) is the Kepler design's `polarMap_symplectic` + `analyticOnNhd_polarMap` (P7-6, owner Kepler) via `isChart_iff`; helper `isChart_continuousLinearEquiv` | Chart |
| `bpP:p1:hol-chart` | lemma | `hol_chart` | HolChart |
| `stepP:p1:hc-real-derivative` | step | `fderiv_real_slice` | HolChart |
| `bpP:p1:lattice-torus` | def | `IsLatticeTorus angleShift` | Transport |
| `bpP:p1:torus-transport` | theorem | (a) `torus_transport_cyl`, (b) `torus_transport_phys`, last sentence `fderiv_chart_comp_torus` (+ Mathlib `Set.range_comp`) | Transport |
| `stepP:p1:tt-an` … `tt-dio` | steps | inside the two proofs (shared private helpers for (i), (iv), (v)) | Transport |
| `bpP:p1:period-convert` (a) | lemma | `isChart_angleScale`, `angleScale_add_angleShift`, `abs_det_fderiv_angleScale`, `volume_angleScale_image` | Chart |
| `bpP:p1:period-convert` (b) | lemma | `chartPullback_angleScale`, `angleScale_hamiltonianVectorField` | Chart |
| `bpP:p1:period-convert` (c) | lemma | `periodOne`, `analyticOnNhd_periodOne_iff`, `fderiv_periodOne`, `periodOne_lattice_iff`, `periodOne_injMod_iff`, `periodOne_hasDerivAt_iff`, `isLatticeTorus_periodOne_iff` | Transport |
| `bpP:p1:period-convert` (d) | lemma | `fastShift_eq_angleScale`, `fullShift_eq_angleScale` | Chart |
| `stepP:p1:pc-a/b/c` | steps | inside the above | Chart, Transport |
| `bpP:p1:cyl-pipeline` | corollary | `cyl_pipeline` | Transport |
| `bpP:p1:phys-pipeline` | corollary | `phys_pipeline` | Transport |
| `bpP:p1:two-scale` | def | `twoScaleDiophantine` | Diophantine |
| `bpP:p1:dio-basic` | lemma | (a) `IsDiophantine.mono`, (b) `isDiophantine_of_le_l1`, (c) `isDiophantine_smul_iff`, (d) `isDiophantine_min_of_mem_twoScale` | Diophantine |
| `bpP:p1:dio-sources` (= `diophantine-convert`) | lemma | (a) `cp10_isDiophantine`, `smul_mem_twoScale`; (b) `cp09_isDiophantine` | Diophantine |
| `bpP:p1:liouville` (= `measure-symplectic`) | lemma | `chart_measure_image` (Lebesgue), `measurableSet_chart_image` (Borel); helper `isAddHaarMeasure_volume_phase` | Liouville |
| `stepP:p1:li-det` | step | `IsChart.abs_det_fderiv` (Chart) | Chart |
| `stepP:p1:li-meas`, `li-borel`, `li-vol` | steps | inside the two proofs | Liouville |
| `bpP:p1:liouville-lattice` | lemma | `liouville_lattice` (Lebesgue), `liouville_lattice_measurableSet` (Borel), consumer form `measure_chart_image` (Kepler signature verbatim) | Liouville |
| `bpP:p1:torus-union` | lemma | `torus_union`, `torus_union_measurableSet_of_sigmaCompact` (B1), `torus_union_measurableSet_of_injOn` (B2), `torus_union_lower`, `torus_union_saturation`, `nullMeasurableSet_torus_union_saturation` | TorusUnion |
| `stepP:p1:tu-ext/meas/borel/bounds` | steps | inside the above | TorusUnion |
| (`bpP:p1:torus-orbit`) | lemma, NOT a graph node | `torus_orbit` (issue B1) | TorusOrbit |

Remarks `vs-N`, `cyl-scope`, `dio-d`, `measure-use`, `newton-transfer` and the `ode` table are not graph nodes and get
no declaration; `measure-use`'s factor bookkeeping is `volume_angleScale_image`.

## 3. Conventions binding for all modules

1. Every file is a Lean module (copyright, `module`, `public import`, docstring, `@[expose] public noncomputable section`).
2. Phase points `Phase d`, frozen `symplecticForm`/`hamiltonianVectorField`; never `EuclideanSpace` (CP09's Euclidean
   norm is written `√(∑ i, (k i : ℝ)^2)`). Integer vectors `Fin d → ℤ`, coerced by `fun i => (k i : ℝ)`.
3. `0 < c` (`hc`) and `IsOpen O` (`hO`) are explicit hypotheses, only where used (Section 4).
4. Lattice hypotheses use the membership form `∀ z ∈ O, ∀ k, z + L k ∈ O ∧ …` (equivalent to `O + ι_k = O` for all
   `k`) and the image form `(fun z => z + angleShift k) '' A = A` for sets, as in the Kepler signature.
5. Scalars on vectors by `•`; frequency conversion `(2 * π)⁻¹ • ω`; parameter scaling `(2 * π) • θ`.
6. Diophantine bounds in the frozen form `γ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|` (also in `𝒟`).
7. `IsAddHaarMeasure` of `volume` on `Phase d` only via `haveI := isAddHaarMeasure_volume_phase d`.
8. `open scoped` only locally; no new global instance.

## 4. Departures from the literal blueprint text

1. Unused hypotheses dropped: `IsOpen O` in `chart-field`, `chart-orbit`, `torus-transport`, pipelines (analyticity
   at each point of `O` suffices; the IFT is applied at a point); interval-ness of `J` in `chart-orbit` (the claim
   is pointwise); `γ, τ > 0` and `γ' > 0` in `dio-basic` (a) (true without them, both cases checked); "real at real
   points" in `hol-chart` is implied by the agreement hypothesis `hagree` and is not separate.
2. Kept although unused by the cheapest proof: `0 < c` everywhere (consumers have it; `c ≠ 0` is what the algebra
   uses), `1 ≤ μ` in `cp09_isDiophantine` (source data; `τ > n μ ≥ n`).
3. Matrix statements of `omega-algebra` (a) (`M₀ᵀ = -M₀`, `M₀² = -1`) and (c) are replaced by bilinear-form
   statements (Decision 8); `M₀² = -1` is internal to the uniqueness proof. `hol-chart`'s complex matrix identity
   `DΨᵀ M₀ DΨ = c M₀` is the equivalent bilinear identity for `symplFormC` on all complex `u, v`.
4. `X_{ℓ∘A} = c A⁻¹ X_ℓ` is stated as `A (X_{ℓ∘A}) = c • X_ℓ` (equivalent given `bijective_of_symplectic`).
5. Generalisation by the lattice family `L` in `IsLatticeTorus`/`torus_transport_*` (Decision 6).
6. `two-scale`: `γ |k|₁^{-τ}` written `γ / |k|₁^τ` (equal on `k ≠ 0`, where `|k|₁ ≥ 1`).
7. `torus-transport`: "`𝒦(R^d) = Ψ(K(R^d))`" is Mathlib's `Set.range_comp` (no declaration); "`D𝒦 = DΨ DK`" is
   `fderiv_chart_comp_torus`.
8. `phys-pipeline` additionally returns `range (Φ ∘ periodOne κ) = Φ '' range κ` (the blueprint's last clause).
9. `liouville` proof route (not statement): Lebesgue measurability via `NullMeasurableSet.exists_measurable_subset_ae_eq`
   (`A = B ∪ N`, `B ⊆ A` Borel) + the Borel part + `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
   for `Ψ(N)`; this avoids the blueprint's `F_σ` + Lindelöf + `lip-image` route for the null part. The Borel part
   follows the blueprint (countable cover by IFT neighbourhoods, `TopologicalSpace.isOpen_iUnion_countable`).

## 5. Blueprint / graph issues (for the orchestrator; none blocks the design)

- **B1 (graph coverage).** `bpP:p1:torus-orbit` (L237-L242) is a labelled lemma of the part but is NOT a node of
  `DEPGRAPH.md` (no consumer edge either). Designed as package P1-8 (optional); the graph should either add it or
  record that it is unused.
- **B2 (Kepler interface, no mismatch).** `fullShift` is generalised from `Phase (n+n)` to `Phase d` with the same
  body; `angleScale` and `measure_chart_image` are verbatim; `IsChart` unfolds to `AnalyticOnNhd ∧ IsSymplecticOn`.
  No delivered declaration changes signature. The undelivered Kepler P7-6 signatures elaborate unchanged once
  `Poincare/Lattice` imports `Hamiltonian/Chart` and drops its own `angleScale`/`fullShift` lines.
- **B3 (`torus-union`, sign of `Λ`).** The blueprint does not say `Λ ≥ 0`; McShane needs it. Harmless (for `Λ < 0`
  the Lipschitz hypothesis forces `A` to be a subsingleton, image measure `0`); the statement keeps no sign
  hypothesis and the proof splits cases.
- **B4 (`liouville`, Lean totality).** The blueprint's "`Ψ(A)` Borel because `Ψ` is a local homeomorphism" holds for
  `A ⊆ O` only; the signature requires `A ⊆ O` (as the blueprint's "`A ⊂ O`").
- **B5 (`dio-basic` (a)).** The positivity hypotheses are unnecessary (Section 4.1); not an error.
- **B6 (Haar instance).** Not a blueprint error; recorded because every measure proof hits it (Decision 10).
No suspected errata in the pinned source.

## 6. Modules and import DAG

| module | content (signature section) | imports (besides Mathlib + frozen defs) | est. lines |
|---|---|---|---|
| `Hamiltonian/Algebra` | A | — | 200 |
| `Hamiltonian/Chart` | B | Algebra, `KAM.Kepler.Basic`, `KAM.ODE.Basic` | 450 |
| `Hamiltonian/HolChart` | C | Chart, `KAM.Canonical.Setting`, `KAM.Strip.Analytic` | 300 |
| `Hamiltonian/Transport` | D | Chart | 500 |
| `Hamiltonian/Diophantine` | E | — | 250 |
| `Hamiltonian/Liouville` | F (+ `measure_chart_image`) | Chart | 600 (split `LiouvilleLattice` if > 1,000) |
| `Hamiltonian/TorusUnion` | G | `KAM.ODE.Basic`, `KAM.Measure.Lipschitz`, `KAM.Measure.McShane` | 400 |
| `Hamiltonian/TorusOrbit` | H | `KAM.ODE.Uniqueness`, `KAM.ODE.Hamiltonian` | 80 |

DAG: Algebra → Chart → {HolChart, Transport, Liouville}; Diophantine, TorusUnion, TorusOrbit independent. No module
imports a provider, a frozen theorem anchor, or `Poincare/*`. Consumers: `Poincare/Lattice` (P7-6) imports `Chart`
(and `Transport` for `phys-pipeline`); `Newtonian/Assembly` (P6-5 (b)) imports `Liouville`; Parts 3, 5, 12, 13
import `Chart`/`Transport`/`Diophantine`/`Liouville`/`TorusUnion`.

## 7. Prover packages and waves

| package | nodes | module | est. | needs | wave |
|---|---|---|---|---|---|
| P1-1 Algebra | conv#data (X_ℓ), omega-algebra | Algebra | 200 | – | 1 |
| P1-2 Diophantine | two-scale, dio-basic, dio-sources | Diophantine | 250 | – | 1 |
| P1-3 TorusUnion | torus-union | TorusUnion | 400 | – | 1 |
| P1-4 Chart | chart, chart-field, chart-orbit, typical (2)(3), period-convert (a)(b)(d), li-det | Chart | 450 | P1-1 | 2 |
| P1-5 HolChart | hol-chart, hc-real-derivative | HolChart | 300 | P1-4 | 3 |
| P1-6 Transport | lattice-torus, torus-transport, period-convert (c), cyl-/phys-pipeline | Transport | 500 | P1-4 | 3 |
| P1-7 Liouville | liouville, liouville-lattice, `measure_chart_image` | Liouville | 600 | P1-4 | 3 |
| P1-8 TorusOrbit (optional, B1) | torus-orbit | TorusOrbit | 80 | – | 1 |

Gates on the Kepler side: P7-6 (Tube and lattice) needs P1-4 (and P1-6 if it states `phys-pipeline` instances);
P6-5 (b) needs P1-7. Three waves; the critical path is P1-1 → P1-4 → P1-7.

### 7.1 Proof plans
- **P1-1.** `linearField` and the frozen field unfold to sums over `Pi.single`; `symplecticForm_linearField`:
  expand `ℓ w = ∑ i, ℓ(w.1 i • (e_i,0)) + ℓ(w.2 i • (0,e_i))` (`ContinuousLinearMap` on `Prod`/`Pi`: `ℓ.map_sum`,
  `Finset.univ_sum_single`). Uniqueness from nondegeneracy (`eq_zero_of_symplecticForm_right`, the 6-line proof of
  the delivered first-slot lemma). (b): injectivity from nondegeneracy, bijectivity from finite dimension
  (`LinearMap.injective_iff_surjective`); det: write `Ω(u,v) = ⟪u, M v⟫` with `M = (u,v) ↦ (-v, u)`-type CLE, so
  `Aᵀ M A = c M` as linear maps and `det(A)² det M = c^{2d} det M`, `det M = 1` (`LinearMap.det_prodMap` on the
  block form). Alternative avoiding transposes: `LinearMap.BilinForm` and `LinearMap.BilinForm.toMatrix`; choose
  whichever elaborates fast. The field identity: uniqueness + `hA`.
- **P1-4.** `IsChart.bijective_fderiv` from P1-1 (b) at `A = fderiv ℝ Ψ z`; analyticity gives `HasStrictFDerivAt`
  (`AnalyticAt.hasStrictFDerivAt`). `cf-diff` (⇒): `HasStrictFDerivAt.to_localInverse` with the CLE
  `ContinuousLinearEquiv.ofBijective`; `H = c • H^Ψ ∘ Ψ⁻¹_loc` near `Ψ z` (`HasStrictFDerivAt.eventually_left_inverse`/
  `eventually_right_inverse`, `Filter.EventuallyEq.differentiableAt_iff`). `cf-field`: differentiable branch by
  `fderiv_comp` + P1-1 (b) field identity with `ℓ = fderiv H (Ψ z)`, scalar `c⁻¹`; other branch both sides `0`
  (`fderiv_zero_of_not_differentiableAt`, `map_zero`). `chart_orbit`: `HasFDerivAt.comp_hasDerivAt` + `chart_field`.
  `IsChart.comp`: delivered `IsSymplecticOn.comp` (it gives `c₂ * c₁`; `mul_comm`). `angleScale`: it is
  `angleScaleCLM`, so `fderiv` is constant (`ContinuousLinearMap.fderiv`), analytic (`ContinuousLinearMap.analyticAt`),
  symplectic by `simp [symplecticForm, Finset.mul_sum]; ring`. `volume_angleScale_image`:
  `MeasureTheory.Measure.addHaar_image_continuousLinearMap` + det (with `haveI` of Decision 10).
- **P1-5.** Reduce to `KAM.holomorphic_analytic` through the measurable/linear equivalence
  `(Fin d → ℂ) × (Fin d → ℂ) ≃L[ℂ] (Fin (d+d) → ℂ)` (`ContinuousLinearEquiv.finTwoArrow`-style or
  `Fin.appendIsometry`; `KAM.appendMeasurableEquiv` is the real analogue); real derivative: `HasFDerivAt` of
  `phaseToC ∘ Ψr = Ψ ∘ phaseToC` near `z` (`hV` open, `phaseToC` continuous) and injectivity of `phaseToC`
  (`Complex.ofReal_injective`). Copy the structure of `KAM.Strip.RealRestriction.realRestriction_fderiv`.
  Symplectic: `symplFormC (phaseToC u) (phaseToC v) = symplecticForm u v` (cast lemma, new private).
- **P1-6.** One private lemma per step (i), (ii), (iii), (iv), (v), used by both `torus_transport_cyl/_phys`.
  (iii) cylinder: apply `hQ2` with `k' := Fin.append k 0` (`Fin.append_left`), then (L2) and (L3).
  `periodOne`: `periodOne κ = κ ∘ ((2π) • ·)` with the CLE `(2π) • id` (`ContinuousLinearEquiv.smulLeft`/
  `unitsEquiv`); `fderiv` via `ContinuousLinearEquiv.comp_right_fderiv`, analyticity both ways via the inverse CLE.
  Flow: `θ + s • (2π)⁻¹ • ω` maps to `(2π) • θ + s • ω` exactly (`smul_add`, `smul_smul`, `mul_inv_cancel₀`) —
  `HasDerivAt` of literally the same function after `funext`. Pipelines: `IsChart.comp` (`c = 1 * 2π`),
  `chartPullback_comp`, `angleScale_add_angleShift` + `fullShift_eq_angleScale`; `phys_pipeline`:
  `chartPullback 1 H Φ = H ∘ Φ` (`inv_one, one_mul`), `isLatticeTorus_periodOne_iff`, `isDiophantine_smul_iff`.
- **P1-7.** `isAddHaarMeasure_volume_phase := Measure.prod.instIsAddHaarMeasure _ _`. Borel part: for each `z ∈ O`
  the IFT `OpenPartialHomeomorph` `e_z` with source `⊆ O`; countable subcover of `O`
  (`TopologicalSpace.isOpen_iUnion_countable`); `Ψ '' (A ∩ e.source) = e.symm ⁻¹' (A ∩ e.source) ∩ e.target`,
  Borel by `ContinuousOn.measurableSet_preimage`-type lemma on the open target (`ContinuousOn.isOpen_inter_preimage`
  does not suffice for Borel `A`; use `MeasurableSet.image_of_continuousOn_injOn` on `A ∩ e.source` — `e` is injective
  on its source: this is the cleanest). Measure: `addHaar_image_le_lintegral_abs_det_fderiv` with `f' = fderiv ℝ Ψ`,
  `HasFDerivWithinAt` from analyticity, `|det| = c^d` constant on `A` (`setLIntegral_const`); equality with
  `lintegral_abs_det_fderiv_eq_addHaar_image₀`. Lebesgue part: Section 4.9. Lattice: `A = ⋃ m, (A ∩ Q) + ι_m`
  (`Int.fract`/`Int.floor` per coordinate: `z = (z - ι_{⌊z₁⌋}) + ι_{⌊z₁⌋}`), `Ψ` injective on `A ∩ Q` by `hQ2`
  (two points of `Q` differing by `ι_m` have `m = 0`, `Int.floor_eq_iff`); measure positivity via
  `measure_iUnion_null_iff` and translation invariance (`measure_preimage_add`); finiteness: bounded ⇒
  `IsBounded.measure_lt_top`. `measure_chart_image`: `rfl` unfolding of `angleShift` + `liouville_lattice(_measurableSet)`.
- **P1-2.** `Real.rpow_le_rpow_of_exponent_le` (base `≥ 1`), `div_le_div_of_nonneg_left`, case split on `γ' ≤ 0`;
  (b) `Real.rpow_le_rpow`; (c) `abs_smul`-free: `∑ k i * (s⁻¹ * ω i) = s⁻¹ * ∑ …`, `abs_mul`, `div_div`;
  CP09: `√(∑ k_i²) ≤ ∑ |k_i|` (`Real.sqrt_le_left`-type: `∑ k_i² ≤ (∑ |k_i|)²` for nonnegative terms,
  `Finset.sum_sq_le_sq_sum_of_nonneg`), positivity for `k ≠ 0`.
- **P1-3.** McShane `KAM.mcshane_prod` (case `Λ ≥ 0`; `Λ < 0` ⇒ subsingleton) → `F̂`; `A` null measurable
  (`NullMeasurableSet.prod`, `volume_prod`/`Measure.prod_prod`, `volume (unitCube d) = 1` via `Real.volume_pi_Ico`);
  measurability: `A = B ∪ N` with `B ⊆ A` an `F_σ` set (inner regularity, `MeasurableSet.exists_isClosed_lt_add` /
  `Measure.InnerRegular`) and `N` null; closed sets of `ℝ^N` are σ-compact (`IsClosed.isSigmaCompact`), so `F̂(B)` is
  σ-compact hence Borel;
  `F̂(N)` null by `KAM.lip_image_prod`. Upper bound `lip_image_prod`; lower bound `lip_image_prod` applied to the
  inverse on `F(A)` (`Function.invFunOn`). Saturation: `ϑ = (ϑ - ⌊ϑ⌋) + ⌊ϑ⌋`.
- **P1-8.** `ham_smooth_c1` for `C¹` field and differentiability, `gen_uniqueness` with `J = univ`
  (`Set.ordConnected_univ`), `ham_energy`.

### 7.2 Consumers
P3 (`period-dictionary`: `chartPullback_angleScale`, `angleScale_hamiltonianVectorField`); P4/P5 (`twoScaleDiophantine`,
`cyl_pipeline`, `torus_union*`, `volume_angleScale_image`); P6-5 (`measure_chart_image`); P7-6 (`angleScale`,
`fullShift`, `IsChart` via `isChart_iff`, `phys_pipeline`); P9, P10, P11 (`torus_transport_*`, `hol_chart`,
`IsChart.comp`); P12/P13 (`phys_pipeline`, `liouville_lattice_measurableSet`, `chart_measure_image` with injectivity,
`cp09_isDiophantine`, `torus_union_measurableSet_of_sigmaCompact`).

## 8. Risks

1. **Determinant of a conformally symplectic map (P1-1).** The only genuinely new linear algebra. If the
   `LinearMap.det`-of-block-form route is slow, use `LinearMap.toMatrix` with the basis `Pi.basisFun` on each factor
   (`Basis.prod`) and `Matrix.det_fromBlocks_zero₂₂`-style lemmas; a default-heartbeat failure is a design signal
   (split per identity), never a budget override.
2. **Haar instance on `Phase d`** (Decision 10): every measure proof needs the `haveI`; forgetting it gives
   confusing synthesis failures.
3. **Borel images under local diffeomorphisms (P1-7).** Mathlib has no "local homeomorphism maps Borel to Borel";
   the route via `image_of_continuousOn_injOn` on the IFT sources is designed above. Fallback: state Borel
   consumption only for `InjOn` (all consumers in Part 12 have injectivity on `A ∩ Q`, blueprint li-borel remark).
4. **Real slice of a holomorphic map on `ℂ^d × ℂ^d` (P1-5).** `KAM.holomorphic_analytic` is stated on `Fin m → ℂ`;
   the transfer through the product/append equivalence is bookkeeping but may be long (budget +150 lines).
5. **`Fin.castAdd`/`Fin.append` in `fastShift` (P1-6, cylinder (iii)).** Reuse the simp lemmas delivered by
   P7-5 (`Poincare/Product`) only if Part 1 does not import `Poincare` — re-derive locally (`Fin.append_left`).
6. **Generalised lattice `L`.** If a reviewer objects to the generalisation, add `abbrev`-free instances
   `torus_transport_cyl_angleShift`/`_phys_angleShift` with `L := angleShift` (pure `@`-applications).
7. **Statement drift.** `measure_chart_image` must stay byte-identical to the Kepler signature; the Kepler P7-6
   package must delete (not duplicate) `angleScale`/`fullShift`.
8. **File size.** All modules well under 1,500 lines; Liouville splits into `Liouville` + `LiouvilleLattice` (facade
   kept) if it passes 1,000.

## 9. Mathlib / KAM checks (by `#check`/`#synth`/`grep` at the pinned snapshot)

`#check`ed in the signatures file: `addHaar_image_le_lintegral_abs_det_fderiv`, `lintegral_abs_det_fderiv_eq_addHaar_image`,
`MeasurableSet.image_of_continuousOn_injOn`, `HasStrictFDerivAt.to_localInverse`, `KAM.lip_image_prod`, `KAM.mcshane_prod`,
`KAM.ODE.gen_uniqueness`; `#synth BorelSpace (Phase 3)` succeeds (`Prod.borelSpace`). Grepped: `lintegral_abs_det_fderiv_eq_addHaar_image₀`
(`Jacobian.lean:1105`), `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (`:556`),
`HasStrictFDerivAt.toOpenPartialHomeomorph` (`InverseFunctionTheorem/FDeriv.lean:118`), `IsSigmaCompact.image_of_continuousOn`
(`SigmaCompact.lean:97`), `Measure.prod.instIsAddHaarMeasure` (`Group/Measure.lean:928`, additive via `to_additive`;
applicability probe: the explicit term type-checks for `Phase 3`, instance search does not). Delivered KAM:
`KAM.Kepler.IsSymplecticOn`, `IsSymplecticOn.comp`, `phaseToC`, `phaseCast*` (`KAM/Kepler/Basic.lean`); `KAM.ODE.angleShift`,
`IsSolutionIn` (`KAM/ODE/Basic.lean`); `KAM.Canonical.symplFormC` (`KAM/Canonical/Setting.lean`); `KAM.holomorphic_analytic`
(`KAM/Strip/Analytic.lean`); `poincareProdCast`, `poincareProdCast_symplectic`, `analyticOnNhd_poincareProdCast`
(`KAM/Planetary/Poincare/Product.lean`).

## Appendix A. `/root/code/KAM-inp/.drafts/design/PPart1Signatures.lean` (verbatim)

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.IsCylinderTorus
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus
public import KAM.Kepler.Basic
public import KAM.ODE.Basic
public import KAM.Canonical.Setting
public import KAM.ODE.Uniqueness
public import KAM.Measure.Lipschitz
public import KAM.Measure.McShane

/-!
# Signatures of blueprint-P Part 1 (Hamiltonian tools) — design draft

Design `docs/tracks/P/design/PART1-LEAN-DESIGN.md`. Every body is `sorry`; no `set_option`.
Imports: Mathlib, frozen DEFINITIONS, and the delivered implementation modules `KAM.Kepler.Basic`
(`IsSymplecticOn`, `phaseToC`), `KAM.ODE.Basic` (`angleShift`, `IsSolutionIn`), `KAM.Canonical.Setting`
(`symplFormC`). No provider, no frozen theorem anchor.

Sections (one per planned module, `KAM/Planetary/Hamiltonian/<Name>.lean`):
A `Algebra`, B `Chart`, C `HolChart`, D `Transport`, E `Diophantine`, F `Liouville`, G `TorusUnion`,
H `TorusOrbit`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-! ## A. `Hamiltonian/Algebra` — `bpP:p1:conv#data`, `bpP:p1:omega-algebra` -/

section Algebra

variable {d : ℕ}

/-- `bpP:p1:conv#data`: `X_ℓ = ((ℓ(0, eᵢ))ᵢ, (-ℓ(eᵢ, 0))ᵢ)` for a linear form `ℓ`. -/
def linearField (ℓ : Phase d →L[ℝ] ℝ) : Phase d :=
  (fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0))

/-- `X_H(z) = X_{DH(z)}` (definitional; with Lean totality `X_H z = 0` off differentiability). -/
theorem hamiltonianVectorField_eq_linearField (H : Phase d → ℝ) (z : Phase d) :
    hamiltonianVectorField H z = linearField (fderiv ℝ H z) := sorry

/-- (a) `M₀ᵀ = -M₀` in bilinear form. -/
theorem symplecticForm_antisymm (v w : Phase d) : symplecticForm v w = -symplecticForm w v := sorry

/-- (a) nondegeneracy (in the second slot; the first-slot form is `eq_zero_of_symplecticForm`). -/
theorem eq_zero_of_symplecticForm_right {v : Phase d} (h : ∀ w, symplecticForm w v = 0) :
    v = 0 := sorry

/-- (a) `Ω(w, X_ℓ) = ℓ w`. -/
theorem symplecticForm_linearField (ℓ : Phase d →L[ℝ] ℝ) (w : Phase d) :
    symplecticForm w (linearField ℓ) = ℓ w := sorry

/-- (a) uniqueness of `X_ℓ`. -/
theorem eq_linearField_iff (ℓ : Phase d →L[ℝ] ℝ) (v : Phase d) :
    (∀ w, symplecticForm w v = ℓ w) ↔ v = linearField ℓ := sorry

/-- (a) last clause: `Ω(w, X_H z) = DH(z) w` for every `z` (both sides `0` off differentiability). -/
theorem symplecticForm_hamiltonianVectorField (H : Phase d → ℝ) (z w : Phase d) :
    symplecticForm w (hamiltonianVectorField H z) = fderiv ℝ H z w := sorry

/-- (b) a conformally symplectic matrix (`c ≠ 0`) is invertible. -/
theorem bijective_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) : Bijective A := sorry

/-- (b) `|det A| = |c|^d`. -/
theorem abs_det_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) :
    |LinearMap.det (A : Phase d →ₗ[ℝ] Phase d)| = |c| ^ d := sorry

/-- (b) `X_{ℓ∘A} = c A⁻¹ X_ℓ`, stated inverse-free: `A X_{ℓ∘A} = c X_ℓ`. -/
theorem apply_linearField_comp_of_symplectic {c : ℝ} (hc : c ≠ 0) {A : Phase d →L[ℝ] Phase d}
    (hA : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) (ℓ : Phase d →L[ℝ] ℝ) :
    A (linearField (ℓ.comp A)) = c • linearField ℓ := sorry

/-- (c) the chart condition does not depend on the sign of the form (CP09 prints `-Ω`). -/
theorem symplectic_neg_iff {c : ℝ} {A : Phase d →L[ℝ] Phase d} :
    (∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) ↔
      ∀ u v, -symplecticForm (A u) (A v) = c * -symplecticForm u v := sorry

end Algebra

/-! ## B. `Hamiltonian/Chart` — `bpP:p1:chart`, `chart-field`, `chart-orbit`, `typical` (2),(3),
`period-convert` (a),(b),(d); owns `angleScale` (= `S_c`) and `fullShift` -/

section Chart

variable {d : ℕ}

/-- `bpP:p1:chart`: `Ψ` is a `c`-chart on `O` (openness of `O` and `0 < c` are separate hypotheses
at use sites). Unfolds to `AnalyticOnNhd` + the Kepler design's `IsSymplecticOn`. -/
def IsChart (c : ℝ) (Ψ : Phase d → Phase d) (O : Set (Phase d)) : Prop :=
  AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O

theorem isChart_iff {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)} :
    IsChart c Ψ O ↔ AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O := sorry

theorem IsChart.analyticOnNhd {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) : AnalyticOnNhd ℝ Ψ O := sorry

theorem IsChart.symplectic {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) : IsSymplecticOn c Ψ O := sorry

theorem IsChart.mono {c : ℝ} {Ψ : Phase d → Phase d} {O O' : Set (Phase d)}
    (h : IsChart c Ψ O) (hO : O' ⊆ O) : IsChart c Ψ O' := sorry

/-- `bpP:p1:chart`: the pulled-back Hamiltonian `H^Ψ = c⁻¹ (H ∘ Ψ)`. -/
def chartPullback (c : ℝ) (H : Phase d → ℝ) (Ψ : Phase d → Phase d) : Phase d → ℝ :=
  fun z => c⁻¹ * H (Ψ z)

/-- Remark after `bpP:p1:chart`: `DΨ(z)` is invertible on `O`. -/
theorem IsChart.bijective_fderiv {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {z : Phase d} (hz : z ∈ O) : Bijective (fderiv ℝ Ψ z) := sorry

/-- `stepP:p1:li-det`: `|det DΨ| = c^d` on `O`. -/
theorem IsChart.abs_det_fderiv {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {z : Phase d} (hz : z ∈ O) :
    |LinearMap.det (fderiv ℝ Ψ z : Phase d →ₗ[ℝ] Phase d)| = c ^ d := sorry

/-- `bpP:p1:chart-field`, `stepP:p1:cf-diff`. -/
theorem chart_field_differentiableAt_iff {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d}
    {O : Set (Phase d)} (h : IsChart c Ψ O) (H : Phase d → ℝ) {z : Phase d} (hz : z ∈ O) :
    DifferentiableAt ℝ (chartPullback c H Ψ) z ↔ DifferentiableAt ℝ H (Ψ z) := sorry

/-- `bpP:p1:chart-field`, `stepP:p1:cf-field`: `DΨ(z) X_{H^Ψ}(z) = X_H(Ψ z)` (unconditionally). -/
theorem chart_field {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) (H : Phase d → ℝ) {z : Phase d} (hz : z ∈ O) :
    fderiv ℝ Ψ z (hamiltonianVectorField (chartPullback c H Ψ) z) =
      hamiltonianVectorField H (Ψ z) := sorry

/-- `bpP:p1:chart-orbit` (pointwise in `t`; `J` any set). -/
theorem chart_orbit {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {H : Phase d → ℝ} {J : Set ℝ} {y : ℝ → Phase d}
    (hyO : ∀ t ∈ J, y t ∈ O)
    (hy : ∀ t ∈ J, DifferentiableAt ℝ (chartPullback c H Ψ) (y t) ∧
      HasDerivAt y (hamiltonianVectorField (chartPullback c H Ψ) (y t)) t) :
    ∀ t ∈ J, DifferentiableAt ℝ H (Ψ (y t)) ∧
      HasDerivAt (Ψ ∘ y) (hamiltonianVectorField H (Ψ (y t))) t := sorry

/-- `bpP:p1:typical` (3): composition of charts. -/
theorem IsChart.comp {c₁ c₂ : ℝ} {Ψ₁ Ψ₂ : Phase d → Phase d} {O₁ O₂ : Set (Phase d)}
    (h₁ : IsChart c₁ Ψ₁ O₁) (h₂ : IsChart c₂ Ψ₂ O₂) (hmaps : MapsTo Ψ₁ O₁ O₂) :
    IsChart (c₁ * c₂) (Ψ₂ ∘ Ψ₁) O₁ := sorry

/-- `bpP:p1:typical` (3): `(H^{Ψ₂})^{Ψ₁} = H^{Ψ₂ ∘ Ψ₁}`. -/
theorem chartPullback_comp (c₁ c₂ : ℝ) (H : Phase d → ℝ) (Ψ₁ Ψ₂ : Phase d → Phase d) :
    chartPullback c₁ (chartPullback c₂ H Ψ₂) Ψ₁ = chartPullback (c₁ * c₂) H (Ψ₂ ∘ Ψ₁) := sorry

/-- A continuous linear equivalence that is conformally symplectic is a chart on every set
(used for `phaseCast`, `angleScale`). -/
theorem isChart_continuousLinearEquiv {c : ℝ} (L : Phase d ≃L[ℝ] Phase d)
    (hL : ∀ u v, symplecticForm (L u) (L v) = c * symplecticForm u v) (O : Set (Phase d)) :
    IsChart c L O := sorry

/-- `bpP:p1:conv#data`: `S_c(z₁, z₂) = (c z₁, z₂)` (Kepler design: `angleScale`, P7-6). -/
def angleScale (c : ℝ) (z : Phase d) : Phase d := (c • z.1, z.2)

/-- `S_c` as a continuous linear map. -/
def angleScaleCLM (c : ℝ) : Phase d →L[ℝ] Phase d :=
  ((c • ContinuousLinearMap.id ℝ (Fin d → ℝ)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.snd ℝ _ _)

theorem angleScaleCLM_apply (c : ℝ) (z : Phase d) : angleScaleCLM c z = angleScale c z := sorry

/-- The full `2π`-lattice `(2π k, 0)` (Kepler design: `fullShift`, P7-6; here for every `d`). -/
def fullShift (k : Fin d → ℤ) : Phase d := (fun i => 2 * π * (k i : ℝ), 0)

theorem fullShift_eq_angleScale (k : Fin d → ℤ) : fullShift k = angleScale (2 * π) (angleShift k) :=
  sorry

/-- `bpP:p1:period-convert` (a): `S_c` is a `c`-chart on all of phase space. -/
theorem isChart_angleScale {c : ℝ} (hc : 0 < c) : IsChart c (angleScale c) (univ : Set (Phase d)) :=
  sorry

/-- (a) the lattice formula `S_c(z + ι_k) = S_c z + (c k, 0)`. -/
theorem angleScale_add_angleShift (c : ℝ) (z : Phase d) (k : Fin d → ℤ) :
    angleScale c (z + angleShift k) = angleScale c z + (fun i => c * (k i : ℝ), 0) := sorry

/-- (a) `|det DS_c| = c^d`. -/
theorem abs_det_fderiv_angleScale {c : ℝ} (hc : 0 < c) (z : Phase d) :
    |LinearMap.det (fderiv ℝ (angleScale c) z : Phase d →ₗ[ℝ] Phase d)| = c ^ d := sorry

/-- (a) consequence used by `bpP:p1:measure-use`: `S_c` multiplies Lebesgue measure by `c^d`. -/
theorem volume_angleScale_image {c : ℝ} (hc : 0 < c) (A : Set (Phase d)) :
    volume (angleScale c '' A) = ENNReal.ofReal (c ^ d) * volume A := sorry

/-- (b) the Hamiltonian dictionary: `H̃^{S_c}(z₁, z₂) = c⁻¹ H̃(c z₁, z₂)`. -/
theorem chartPullback_angleScale (c : ℝ) (H : Phase d → ℝ) (z : Phase d) :
    chartPullback c H (angleScale c) z = c⁻¹ * H (c • z.1, z.2) := sorry

/-- (b) `S_c X_{H̃^{S_c}}(z) = X_{H̃}(S_c z)` for every `z`. -/
theorem angleScale_hamiltonianVectorField {c : ℝ} (hc : 0 < c) (H : Phase d → ℝ) (z : Phase d) :
    angleScale c (hamiltonianVectorField (chartPullback c H (angleScale c)) z) =
      hamiltonianVectorField H (angleScale c z) := sorry

/-- (d) the frozen fast shift is `S_{2π}` applied to `((k_f, 0_b), 0)`. -/
theorem fastShift_eq_angleScale {a b : ℕ} (k : Fin a → ℤ) :
    fastShift (b := b) k =
      angleScale (2 * π) (Fin.append (fun i => (k i : ℝ)) (0 : Fin b → ℝ), 0) := sorry

end Chart

/-! ## C. `Hamiltonian/HolChart` — `bpP:p1:hol-chart`, `stepP:p1:hc-real-derivative` -/

section HolChart

variable {d : ℕ}

/-- `stepP:p1:hc-real-derivative`: on the real slice of an arbitrary open `V`, the real derivative
of a real-at-real-points holomorphic map is the restriction of the complex derivative. -/
theorem fderiv_real_slice {V : Set ((Fin d → ℂ) × (Fin d → ℂ))} (hV : IsOpen V)
    {Ψ : (Fin d → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) × (Fin d → ℂ)} (hΨ : DifferentiableOn ℂ Ψ V)
    {Ψr : Phase d → Phase d} (hagree : ∀ z, phaseToC z ∈ V → phaseToC (Ψr z) = Ψ (phaseToC z))
    {z : Phase d} (hz : phaseToC z ∈ V) :
    AnalyticAt ℝ Ψr z ∧
      ∀ u, phaseToC (fderiv ℝ Ψr z u) = fderiv ℂ Ψ (phaseToC z) (phaseToC u) := sorry

/-- `bpP:p1:hol-chart`: a holomorphic, conformally symplectic map, real at real points, restricts
to a `c`-chart on `O = V ∩ ℝ^{2d}` (any total extension `Ψr` off `O`). -/
theorem hol_chart {c : ℝ} (hc : 0 < c) {V : Set ((Fin d → ℂ) × (Fin d → ℂ))} (hV : IsOpen V)
    {Ψ : (Fin d → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) × (Fin d → ℂ)} (hΨ : DifferentiableOn ℂ Ψ V)
    (hsympl : ∀ z : Phase d, phaseToC z ∈ V → ∀ u v,
      KAM.Canonical.symplFormC (fderiv ℂ Ψ (phaseToC z) u) (fderiv ℂ Ψ (phaseToC z) v) =
        (c : ℂ) * KAM.Canonical.symplFormC u v)
    {Ψr : Phase d → Phase d} (hagree : ∀ z, phaseToC z ∈ V → phaseToC (Ψr z) = Ψ (phaseToC z)) :
    IsOpen (phaseToC ⁻¹' V) ∧ IsChart c Ψr (phaseToC ⁻¹' V) ∧
      ∀ z, phaseToC z ∈ V → ∀ u,
        phaseToC (fderiv ℝ Ψr z u) = fderiv ℂ Ψ (phaseToC z) (phaseToC u) := sorry

end HolChart

/-! ## D. `Hamiltonian/Transport` — `bpP:p1:lattice-torus`, `torus-transport`,
`period-convert` (c), `cyl-pipeline`, `phys-pipeline` -/

section Transport

variable {d : ℕ}

/-- `bpP:p1:lattice-torus` with the lattice vectors `L k` as a parameter: the blueprint's
`LT(G, O, w, K)` is `IsLatticeTorus angleShift G O w K`; `L = fullShift` is the `2π` lattice
used by `phys-pipeline`. Clauses (L1)-(L6) in order. -/
def IsLatticeTorus (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ) (O : Set (Phase d))
    (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (hamiltonianVectorField G (K (θ + t • w))) t)

/-- `bpP:p1:torus-transport` (a), cylinder case (`σ_k = fastShift k_f`). -/
theorem torus_transport_cyl {a b : ℕ} {c : ℝ} (hc : 0 < c) {O : Set (Phase (a + b))}
    {Ψ : Phase (a + b) → Phase (a + b)} (hΨ : IsChart c Ψ O) {H : Phase (a + b) → ℝ}
    {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    {L : (Fin (a + b) → ℤ) → Phase (a + b)} (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin (a + b) → ℤ, z + L k ∈ O ∧
      Ψ (z + L k) = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)))
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, ∀ k : Fin (a + b) → ℤ,
      Ψ z' = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)) →
        ∃ m : Fin (a + b) → ℤ, z' = z + L m)
    {U : Set (Phase (a + b))} (hU : Ψ '' range K ⊆ U) :
    IsCylinderTorus H U w (Ψ ∘ K) := sorry

/-- `bpP:p1:torus-transport` (b), physical case (`σ_k = 0`, `w` Diophantine). -/
theorem torus_transport_phys {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hΨ : IsChart c Ψ O) {H : Phase d → ℝ} {w : Fin d → ℝ} {K : (Fin d → ℝ) → Phase d}
    {L : (Fin d → ℤ) → Phase d} (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + L k ∈ O ∧ Ψ (z + L k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + L m)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hw : IsDiophantine γ τ w) :
    IsPhysicalTorus H w (Ψ ∘ K) := sorry

/-- `bpP:p1:torus-transport`, closing sentence: derivative of the transported torus. -/
theorem fderiv_chart_comp_torus {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hΨ : IsChart c Ψ O) {K : (Fin d → ℝ) → Phase d} (hKan : AnalyticOnNhd ℝ K univ)
    (hKO : ∀ θ, K θ ∈ O) (θ : Fin d → ℝ) :
    fderiv ℝ (Ψ ∘ K) θ = (fderiv ℝ Ψ (K θ)).comp (fderiv ℝ K θ) := sorry

/-- `bpP:p1:period-convert` (c): the period-one parameter `K(θ) = κ̃(2πθ)`. -/
def periodOne (κ : (Fin d → ℝ) → Phase d) : (Fin d → ℝ) → Phase d := fun θ => κ ((2 * π) • θ)

/-- The `2π`-convention torus of CP09 Thm. 3 (`bpP:p1:phys-pipeline`): (L1)-(L5) with period
`2π` (`τ_k = fullShift k`) and the flow clause with the angular frequency `ω̃`. -/
def IsTwoPiLatticeTorus (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ κ univ ∧ ∀ ϑ, κ ϑ ∈ O ∧ DifferentiableAt ℝ G (κ ϑ)) ∧
  (∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * π * (k i : ℝ)) = κ ϑ + fullShift k) ∧
  (∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * π * (k i : ℝ)) ∧
  (∀ ϑ, Injective (fderiv ℝ κ ϑ)) ∧
  (∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0) ∧
  (∀ ϑ t, HasDerivAt (fun s : ℝ => κ (ϑ + s • ω))
    (hamiltonianVectorField G (κ (ϑ + t • ω))) t)

/-- (c) analyticity. -/
theorem analyticOnNhd_periodOne_iff (κ : (Fin d → ℝ) → Phase d) :
    AnalyticOnNhd ℝ (periodOne κ) univ ↔ AnalyticOnNhd ℝ κ univ := sorry

/-- (c) `DK(θ) = 2π Dκ̃(2πθ)` (unconditionally). -/
theorem fderiv_periodOne (κ : (Fin d → ℝ) → Phase d) (θ : Fin d → ℝ) :
    fderiv ℝ (periodOne κ) θ = (2 * π) • fderiv ℝ κ ((2 * π) • θ) := sorry

/-- (c) the lattice clause, for any family `τ_k`. -/
theorem periodOne_lattice_iff (κ : (Fin d → ℝ) → Phase d) (T : (Fin d → ℤ) → Phase d) :
    (∀ θ (k : Fin d → ℤ), periodOne κ (θ + fun i => (k i : ℝ)) = periodOne κ θ + T k) ↔
      ∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * π * (k i : ℝ)) = κ ϑ + T k := sorry

/-- (c) injectivity modulo the lattice. -/
theorem periodOne_injMod_iff (κ : (Fin d → ℝ) → Phase d) :
    (∀ θ θ', periodOne κ θ = periodOne κ θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ↔
      ∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * π * (k i : ℝ) := sorry

/-- (c) the flow clause: frozen frequency `w = ω̃ / 2π`, same time. -/
theorem periodOne_hasDerivAt_iff (κ : (Fin d → ℝ) → Phase d) (ω : Fin d → ℝ) (θ : Fin d → ℝ)
    (v : Phase d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => periodOne κ (θ + s • (2 * π)⁻¹ • ω)) v t ↔
      HasDerivAt (fun s : ℝ => κ ((2 * π) • θ + s • ω)) v t := sorry

/-- (c) packaged: the `2π` torus is a `fullShift`-lattice torus of period one with `w = ω̃/2π`. -/
theorem isLatticeTorus_periodOne_iff (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) :
    IsLatticeTorus fullShift G O ((2 * π)⁻¹ • ω) (periodOne κ) ↔ IsTwoPiLatticeTorus G O ω κ :=
  sorry

/-- `bpP:p1:cyl-pipeline` (consumed by Part 5). -/
theorem cyl_pipeline {a b : ℕ} {H : Phase (a + b) → ℝ} {Φ : Phase (a + b) → Phase (a + b)}
    {O₀ : Set (Phase (a + b))} (hΦ : IsChart 1 Φ O₀)
    (hQ1 : ∀ z ∈ O₀, ∀ k : Fin (a + b) → ℤ, z + fullShift k ∈ O₀ ∧
      Φ (z + fullShift k) = Φ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)))
    (hQ2 : ∀ z ∈ O₀, ∀ z' ∈ O₀, ∀ k : Fin (a + b) → ℤ,
      Φ z' = Φ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)) →
        ∃ m : Fin (a + b) → ℤ, z' = z + fullShift m)
    {w : Fin (a + b) → ℝ} {K₃ : (Fin (a + b) → ℝ) → Phase (a + b)}
    (hK : IsLatticeTorus angleShift (chartPullback (2 * π) H (Φ ∘ angleScale (2 * π)))
      (angleScale (2 * π) ⁻¹' O₀) w K₃)
    {U : Set (Phase (a + b))} (hU : (Φ ∘ angleScale (2 * π)) '' range K₃ ⊆ U) :
    IsCylinderTorus H U w (Φ ∘ angleScale (2 * π) ∘ K₃) := sorry

/-- `bpP:p1:phys-pipeline` (consumed by Parts 12, 13). -/
theorem phys_pipeline {H : Phase d → ℝ} {Φ : Phase d → Phase d} {O₀ : Set (Phase d)}
    (hΦ : IsChart 1 Φ O₀)
    (hQ1 : ∀ z ∈ O₀, ∀ k : Fin d → ℤ, z + fullShift k ∈ O₀ ∧ Φ (z + fullShift k) = Φ z)
    (hQ2 : ∀ z ∈ O₀, ∀ z' ∈ O₀, Φ z' = Φ z → ∃ m : Fin d → ℤ, z' = z + fullShift m)
    {κ : (Fin d → ℝ) → Phase d} {ω : Fin d → ℝ} (hκ : IsTwoPiLatticeTorus (H ∘ Φ) O₀ ω κ)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hω : IsDiophantine γ τ ω) :
    IsPhysicalTorus H ((2 * π)⁻¹ • ω) (Φ ∘ periodOne κ) ∧
      range (Φ ∘ periodOne κ) = Φ '' range κ := sorry

end Transport

/-! ## E. `Hamiltonian/Diophantine` — `bpP:p1:two-scale`, `dio-basic`, `dio-sources` -/

section Diophantine

/-- `bpP:p1:two-scale`: `𝒟_{γ₁,γ₂,τ}` on `ℝ^{n₁} × ℝ^{n₂}` (first `n₁` coordinates via
`Fin.castAdd`), with the frozen `γ / |k|₁^τ` form of the bound. -/
def twoScaleDiophantine (n₁ n₂ : ℕ) (γ₁ γ₂ τ : ℝ) : Set (Fin (n₁ + n₂) → ℝ) :=
  {ω | (∀ k : Fin (n₁ + n₂) → ℤ, (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) ≠ 0 →
        γ₁ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) ∧
    (∀ k : Fin (n₁ + n₂) → ℤ, k ≠ 0 → (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) = 0 →
        γ₂ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|)}

variable {d : ℕ}

/-- `bpP:p1:dio-basic` (a) monotonicity. -/
theorem IsDiophantine.mono {γ τ γ' τ' : ℝ} {ω : Fin d → ℝ} (h : IsDiophantine γ τ ω)
    (hγ : γ' ≤ γ) (hτ : τ ≤ τ') : IsDiophantine γ' τ' ω := sorry

/-- `bpP:p1:dio-basic` (b) other norms `0 < ν k ≤ |k|₁`. -/
theorem isDiophantine_of_le_l1 {γ τ : ℝ} (hτ : 0 < τ) {ω : Fin d → ℝ} {ν : (Fin d → ℤ) → ℝ}
    (hν : ∀ k, k ≠ 0 → 0 < ν k ∧ ν k ≤ ∑ i, |(k i : ℝ)|)
    (h : ∀ k : Fin d → ℤ, k ≠ 0 → γ / ν k ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) :
    IsDiophantine γ τ ω := sorry

/-- `bpP:p1:dio-basic` (c) scaling. -/
theorem isDiophantine_smul_iff {γ τ s : ℝ} (hs : 0 < s) (ω : Fin d → ℝ) :
    IsDiophantine γ τ ω ↔ IsDiophantine (γ / s) τ (s⁻¹ • ω) := sorry

/-- `bpP:p1:dio-basic` (d) two scales. -/
theorem isDiophantine_min_of_mem_twoScale {n₁ n₂ : ℕ} {γ₁ γ₂ τ : ℝ} {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) : IsDiophantine (min γ₁ γ₂) τ ω := sorry

/-- `bpP:p1:dio-sources` (a) scaling of `𝒟`. -/
theorem smul_mem_twoScale {n₁ n₂ : ℕ} {γ₁ γ₂ τ s : ℝ} (hs : 0 < s) {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) :
    s⁻¹ • ω ∈ twoScaleDiophantine n₁ n₂ (γ₁ / s) (γ₂ / s) τ := sorry

/-- `bpP:p1:dio-sources` (a) CP10: the clause of `IsCylinderKolmogorovSet`. -/
theorem cp10_isDiophantine {n₁ n₂ : ℕ} {γ₁ γ₂ τ : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hτ : ((n₁ + n₂ : ℕ) : ℝ) < τ) {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) :
    IsDiophantine (min γ₁ γ₂) τ ω ∧
      ∃ γ τ' : ℝ, 0 < γ ∧ ((n₁ + n₂ : ℕ) : ℝ) < τ' ∧ IsDiophantine γ τ' ω := sorry

/-- `bpP:p1:dio-sources` (b) CP09 (6) with the Euclidean norm `√(∑ kᵢ²)` (no `EuclideanSpace`). -/
theorem cp09_isDiophantine {γ τ : ℝ} (hγ : 0 < γ) {μ : ℕ} (hμ : 1 ≤ μ)
    (hτ : (d : ℝ) * μ < τ) {ω : Fin d → ℝ}
    (h : ∀ k : Fin d → ℤ, k ≠ 0 →
      γ / (√(∑ i, (k i : ℝ) ^ 2)) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) :
    IsDiophantine γ τ ω ∧ IsDiophantine (γ / (2 * π)) τ ((2 * π)⁻¹ • ω) ∧ (d : ℝ) - 1 < τ :=
  sorry

end Diophantine

/-! ## F. `Hamiltonian/Liouville` — `bpP:p1:liouville` (= `measure-symplectic`),
`liouville-lattice`, and the Kepler consumer form `measure_chart_image` -/

section Liouville

variable {d : ℕ}

/-- Lebesgue measure on `Phase d` is an additive Haar measure. Instance search does NOT find this
(probe: `#synth` fails on the product `volume`); provers use `haveI := isAddHaarMeasure_volume_phase d`
locally (never a global instance on the Mathlib product type). -/
theorem isAddHaarMeasure_volume_phase (d : ℕ) : (volume : Measure (Phase d)).IsAddHaarMeasure :=
  sorry

/-- `Q = {z : z₁ ∈ [0,1)^d}`. -/
def unitCell (d : ℕ) : Set (Phase d) := {z | ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}

/-- `bpP:p1:liouville`, Lebesgue part (`stepP:p1:li-meas`, `li-vol`). -/
theorem chart_measure_image {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O) {A : Set (Phase d)} (hAO : A ⊆ O)
    (hA : NullMeasurableSet A) :
    NullMeasurableSet (Ψ '' A) ∧ volume (Ψ '' A) ≤ ENNReal.ofReal (c ^ d) * volume A ∧
      (InjOn Ψ A → volume (Ψ '' A) = ENNReal.ofReal (c ^ d) * volume A) := sorry

/-- `bpP:p1:liouville`, Borel part (`stepP:p1:li-borel`). -/
theorem measurableSet_chart_image {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O) {A : Set (Phase d)} (hAO : A ⊆ O)
    (hA : MeasurableSet A) : MeasurableSet (Ψ '' A) := sorry

/-- `bpP:p1:liouville-lattice` (Lebesgue version). -/
theorem liouville_lattice {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + angleShift m)
    {A : Set (Phase d)} (hA : NullMeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + angleShift k) '' A = A) :
    NullMeasurableSet (Ψ '' A) ∧ Ψ '' A = Ψ '' (A ∩ unitCell d) ∧
      volume (Ψ '' A) = ENNReal.ofReal (c ^ d) * volume (A ∩ unitCell d) ∧
      (0 < volume (Ψ '' A) ↔ 0 < volume A) ∧
      (Bornology.IsBounded (A ∩ unitCell d) → volume (Ψ '' A) < ⊤) := sorry

/-- `bpP:p1:liouville-lattice` (Borel version; `MeasurableSet.image_of_continuousOn_injOn`). -/
theorem liouville_lattice_measurableSet {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + angleShift m)
    {A : Set (Phase d)} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + angleShift k) '' A = A) :
    MeasurableSet (Ψ '' A) := sorry

/-- The Kepler design's consumer form of `bpP:p1:liouville-lattice` (P6-5 (b)), adopted VERBATIM
(signature of `KeplerSignaturesP.lean`); FULL position lattice only (audit F6 caveat). -/
theorem measure_chart_image {d : ℕ} {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : AnalyticOnNhd ℝ Ψ O) (hs : IsSymplecticOn c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + ((fun i => (k i : ℝ)), 0) ∈ O ∧ Ψ (z + ((fun i => (k i : ℝ)), 0)) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin d → ℤ, z' = z + ((fun i => (k i : ℝ)), 0))
    {A : Set (Phase d)} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + ((fun i => (k i : ℝ)), 0)) '' A = A) :
    MeasurableSet (Ψ '' A) ∧
      MeasureTheory.volume (Ψ '' A) =
        ENNReal.ofReal (c ^ d) * MeasureTheory.volume (A ∩ {z | ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}) ∧
      (0 < MeasureTheory.volume (Ψ '' A) ↔ 0 < MeasureTheory.volume A) := sorry

end Liouville

/-! ## G. `Hamiltonian/TorusUnion` — `bpP:p1:torus-union` -/

section TorusUnion

variable {d : ℕ}

/-- `[0,1)^d`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ico (0 : ℝ) 1

/-- `bpP:p1:torus-union`: measurability and the upper bound (`tu-ext`, `tu-meas`, `tu-bounds`). -/
theorem torus_union {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E) {F : Phase d → Phase d}
    {Λ : ℝ} (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖) :
    NullMeasurableSet (F '' (E ×ˢ unitCube d)) ∧
      volume (F '' (E ×ˢ unitCube d)) ≤ ENNReal.ofReal (Λ ^ (2 * d)) * volume E := sorry

/-- (B1): `E` σ-compact gives a σ-compact, hence Borel, image (no injectivity). -/
theorem torus_union_measurableSet_of_sigmaCompact {E : Set (Fin d → ℝ)} (hE : IsSigmaCompact E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖) :
    IsSigmaCompact (F '' (E ×ˢ unitCube d)) ∧ MeasurableSet (F '' (E ×ˢ unitCube d)) := sorry

/-- (B2): `E` Borel and `F` injective on `A` give a Borel image. -/
theorem torus_union_measurableSet_of_injOn {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hinj : InjOn F (E ×ˢ unitCube d)) : MeasurableSet (F '' (E ×ˢ unitCube d)) := sorry

/-- Lower bound under a lower Lipschitz bound. -/
theorem torus_union_lower {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E) {F : Phase d → Phase d}
    {Λ lam : ℝ} (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hlam : 0 < lam)
    (hlow : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, lam * ‖x - y‖ ≤ ‖F x - F y‖) :
    ENNReal.ofReal (lam ^ (2 * d)) * volume E ≤ volume (F '' (E ×ˢ unitCube d)) ∧
      (0 < volume (F '' (E ×ˢ unitCube d)) ↔ 0 < volume E) ∧
      (volume (F '' (E ×ˢ unitCube d)) < ⊤ ↔ volume E < ⊤) := sorry

/-- Saturation: the union of whole tori is the lattice saturation of the cell image. -/
theorem torus_union_saturation {E : Set (Fin d → ℝ)} {F : Phase d → Phase d}
    (hper : ∀ ω ∈ E, ∀ ϑ (k : Fin d → ℤ),
      F (ω, ϑ + fun i => (k i : ℝ)) = F (ω, ϑ) + angleShift k) :
    (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ)) =
      ⋃ k : Fin d → ℤ, (fun z => z + angleShift k) '' (F '' (E ×ˢ unitCube d)) := sorry

/-- Saturation is measurable (Lebesgue; Borel if the cell image is). -/
theorem nullMeasurableSet_torus_union_saturation {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hper : ∀ ω ∈ E, ∀ ϑ (k : Fin d → ℤ),
      F (ω, ϑ + fun i => (k i : ℝ)) = F (ω, ϑ) + angleShift k) :
    NullMeasurableSet (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ)) ∧
      (MeasurableSet (F '' (E ×ˢ unitCube d)) →
        MeasurableSet (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ))) := sorry

end TorusUnion

/-! ## H. `Hamiltonian/TorusOrbit` — `bpP:p1:torus-orbit` (NOT a node of the graph; issue B1) -/

section TorusOrbit

variable {d : ℕ}

/-- `bpP:p1:torus-orbit`. -/
theorem torus_orbit {H : Phase d → ℝ} {W : Set (Phase d)} (hW : IsOpen W)
    (hH : ContDiffOn ℝ 2 H W) {K : (Fin d → ℝ) → Phase d} {w : Fin d → ℝ} (hKW : range K ⊆ W)
    (hflow : ∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
      (hamiltonianVectorField H (K (θ + t • w))) t) (θ : Fin d → ℝ) :
    IsSolutionIn (hamiltonianVectorField H) W univ (fun t : ℝ => K (θ + t • w)) ∧
      (∀ y : ℝ → Phase d, IsSolutionIn (hamiltonianVectorField H) W univ y → y 0 = K θ →
        y = fun t : ℝ => K (θ + t • w)) ∧
      ∀ t : ℝ, H (K (θ + t • w)) = H (K θ) := sorry

end TorusOrbit

/-! ## Applicability probes (no proofs; instance synthesis only) -/

#synth BorelSpace (Phase 3)
#check @MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
#check @MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
#check @MeasurableSet.image_of_continuousOn_injOn
#check @HasStrictFDerivAt.to_localInverse
#check @KAM.lip_image_prod
#check @KAM.mcshane_prod
#check @KAM.ODE.gen_uniqueness

end KAM.Planetary
```
