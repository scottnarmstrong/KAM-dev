# The application contract: from a model to a physical theorem

Date: 1 November 2026. Branch `v2-adapt` (worker V2-ADAPT, improvement #7 of
[CERTIFIER-V2-IMPROVEMENTS](CERTIFIER-V2-IMPROVEMENTS.md#7-package-the-model-to-physical-conclusion-interface)).
Status: the core adapters below are proved in Lean (`KAM/Application/`, default limits, standard
axioms only); the SO-2/SO-3/LG00 instances are described as recipes with exact Lean names and are
**not** re-proved here (their files are read-only in this wave, and the SO lock coordinates and
LG00 modules are not built in this worktree). No application certificate is claimed by this note.
Revised by V2-ADAPT-FIX after AUDIT-V2-ADAPT-1: torus invariance (`Invariance`), the real-torus
checks (`checkAngleGraphReal`, `checkActionRangeReal`), `IsFieldTransport.const_mul` (SO-3 clock),
dot-notation names, and the probes (`Tests/Probes`).
Extended by V2-CLOCKGRAPH (branch `v2-clockgraph`): the qualitative graph notion
`IsAnalyticAngleGraph` (`AngleGraph`) and the **clock-triangular graph adapter** of the Moon's
spin–orbit tori (`ClockGraph`, `ClockGraphCert`, `ClockGraphCheck`, `Tests/ClockGraph`; §2.4), with
the adoption recipe for SO-2/SO-3 (§3.1, §3.2).
Extended by V2-GRAPHBRIDGE (branch `v2-graphbridge`, after AUDIT-V2-CLOCKGRAPH-1): the bridge from
both graph adapters to the core confinement's `GraphTorus` (`GraphBridge`, `Tests/GraphBridge`;
§2.5), and the audit nits N1–N3 (§2.4, §3.1).

## 1. What a certified application must supply

A certificate application turns a passing numerical certificate into a theorem about a physical
system. Each row names what must be written down and the Lean object that carries it.

| Component | Required information | Lean carrier (core) |
|---|---|---|
| **Model** | Exact equations, parameters, units and normalization | the physical vector field `F : E → E` on a real normed space `E` (any variable order), and, when it is Hamiltonian, `H_phys : E → ℝ` |
| **Coordinates** | Chart, valid domain, symplectic identity or justified time change | the chart `Ψ : ℝⁿ × ℝⁿ → E`, its open model domain `O`, and the transport identity `IsFieldTransport Ψ Hc F κ O` (`DΨ X_{Hc} = κ F ∘ Ψ` on `O`; `κ` the clock); from a conformally symplectic chart by `isFieldTransport_of_isChart` |
| **Approximation** | Fourier/model truncation and rigorous remainder budgets | the certificate's exact Hamiltonian expression `c.ham` (`c.H = c.ham.eval`) and the identity `Hc = Re c.H` on `O` (`hHc`); a truncated or approximate model is a *different* exact model, and its relation to the physical one is a separate theorem |
| **Frequency** | Exact target, enclosure and infinite Diophantine witness | `ωstar : Fin n → ℝ` exact; `FreqEncloses n c.freqBox ωstar`; `IsDiophantine γ τ ωstar` (proved, e.g. quadratic/cubic constructions); the torus frequency is `s∞ ωstar`, `CertifiedTorusAt.isDiophantine`, `abs_sub_mul_norm_le` |
| **Certificate** | Candidate, route, witness, checked margins and replay receipts | `c : TorusCertificate n α`, a certifier (landed `checkTorusCertificate`, v2 `checkTorusCertificateV2 E`, hybrid …) whose soundness gives `CertifiedTorus c ωstar`; the adapter checks `checkStatic`, `checkHamBounds`, `checkAngleGraphReal c δ` (or the conservative strip `checkAngleGraph c δ`), `checkActionRangeReal c i ctr r` (or `checkActionRange`); with a clock: `checkClock c i a` and `checkClockGraphReal c i mono` (or the SOS `checkClockGraph c i mono mono₀ sos`) |
| **Physical output** | Observable bounds, initial set, quantifiers, time interval | `IsPhysicalFlowTorus F ν (Ψ ∘ k)` (every torus line `τ ↦ L(θ + τν)` solves `ż = F z` for all real `τ`) and its invariance (`IsPhysicalFlowTorus.mem_range_of_solution`, `isInvariantSet`: every solution meeting the torus stays on it, `F` of class `C¹` near the torus), energy level `H_phys = E₀/a`, `IsAngleGraph` or, with a clock, `IsClockAngleGraph` (graph over the angles; both give `IsAnalyticAngleGraph`, and for `n = 2` a confinement `GraphTorus` by `GraphBridge`), observable enclosures (`observable_bounds`, `abs_action_sub_ctr_le_real`, `IsPhysicalFlowTorus.forall_solution`) |

The hub is **`CertifiedTorusAt c ω* K∞ s∞`** (`KAM/Application/Certified.lean`): the body of
`CertifiedTorus` with the exact torus `K∞` and the scalar `s∞` named
(`certifiedTorus_iff : CertifiedTorus c ω* ↔ ∃ K∞ s∞, CertifiedTorusAt c ω* K∞ s∞`, `Iff.rfl`).
Every adapter is stated on it, so the graph, the transport and the observables attach to the same
torus: `obtain ⟨K∞, s∞, hT⟩ := (certifiedTorus_iff c ω*).1 h`, then use `hT.isRealModelTorus`,
`hT.isAngleGraph`, `hT.physical`, `hT.observable_bounds`, … (LG00's `lg00TorusWith` is the `n = 2`
case, verbatim.)

## 2. The adapters (`KAM/Application/`)

Module map (all core, additive, under 350 lines each; the last four rows and `AngleGraph` are
V2-CLOCKGRAPH's):

| Module | Content |
|---|---|
| `Graph` | pure: `DerivNearId f L` (`‖Df - 1‖ ≤ L`), bi-Lipschitz, bijective (contraction), `toHomeomorph`, analytic inverse; `torusAngle`, `torusGraph`, `IsAngleGraph` (with `angleHomeomorph`, `continuous_graph`, `apply_invFun`, …), `isAngleGraph_of_derivNearId` |
| `RealTorus` | pure: `realHam h = Re h ∘ ι`, `IsRealHolo D h`, `IsRealModelTorus H ω E k`, `isRealModelTorus_realRestriction`, `IsRealModelTorus.congr`, `isDiophantine_mul_smul` |
| `Certified` | `CertifiedTorusAt`, `certifiedTorus_iff`, `isRealHolo_of_{differentiableOn,nonvanishing,checkHamBounds}`, `CertifiedTorusAt.isRealModelTorus`, `norm_realRestriction_sub_le`, `isDiophantine`, `abs_sub_mul_norm_le` |
| `GraphCert` | `norm_fderiv_sub_le_of_real` (Cauchy at real points), `derivNearId_torusAngle_realRestriction`, `AngleNearId c δ`, `CertifiedTorusAt.isAngleGraph`, `KAM.Certificate.CertifiedTorus.exists_realGraph` (`hT.exists_realGraph`; alias `KAM.Application.CertifiedTorus.exists_realGraph`) |
| `GraphCheck` | real torus: `angleDerivModel`, `angleRowUpReal`, `checkAngleGraphReal`, `checkAngleGraphReal_sound`; strip: `angleRowUp`, `checkAngleGraph`, `checkAngleGraph_sound`; `KAM.Certificate.CertifiedTorus.exists_realGraph_of_checks` (either check; alias in `KAM.Application`) |
| `Transport` | pure: `IsFieldTransport`, `IsPhysicalFlowTorus`, `hasDerivAt_comp` (orbits), `IsRealModelTorus.isPhysicalFlowTorus` (tori), `analyticOnNhd_comp`, `comp_add_int`, `injective_mod_comp`, `injective_fderiv_comp`, `level_comp`, `energy_comp`, `hamiltonianVectorField_const_mul`, `IsFieldTransport.const_mul` (clock rescaling), `IsRealModelTorus.isPhysicalFlowTorus_self` |
| `Invariance` | `IsPhysicalFlowTorus.eqOn_line`, `mem_range_of_solution`, `isInvariantSet`, `forall_solution` (ODE uniqueness, `KAM.ODE.gen_uniqueness`, `F` of class `C¹` on an open set containing the torus) |
| `TransportChart` | `isFieldTransport_of_isChart`, `KAM.Planetary.IsChart.injective_fderiv` (from `KAM.Planetary.IsChart`; imports all of Mathlib, hence separate) |
| `Physical` | `CertifiedTorusAt.physical`, `CertifiedTorusAt.physical_energy` (the generic `lg00_physical_orbits`) |
| `Observables` | `abs_sub_le_of_convex`, `forall_orbit` (along torus lines only), `CertifiedTorusAt.observable_bounds`, `abs_angle_sub_le`, `abs_action_sub_le`, `norm_fderiv_realRestriction_sub_le`, `norm_physFreq_sub_le`, `checkActionRangeReal`/`checkActionRange` with `abs_action_sub_ctr_le_real`/`abs_action_sub_ctr_le`, `realInclusion₂_realRestriction_K_mem_D` |
| `Tests/Toy2` | the whole chain on the toy T2 through the `2π` chart (`toyCert2_physical`, via `CertifiedTorusAt.physical`) |
| `Tests/Probes` | negative cases of every check, nonzero angle data (real vs strip), `physical`/`physical_energy`/`const_mul`/`observable_bounds` on T2 (no chart layer) |
| `AngleGraph` | pure: `IsAnalyticAngleGraph k` (the graph property without a near-identity constant), `isAnalyticAngleGraph_of_bijective` (bijective angle map with invertible derivative; inverse function theorem), `homeomorphOfAnalytic`, `analyticOnNhd_invFun_of_bijective`, accessors (`angleHomeomorph`, `k_invFun`, `continuous_angleInv`, `continuous_graph`, `mem_range_iff`), `IsAngleGraph.isAnalyticAngleGraph` |
| `ClockGraph` | pure: `IsClockTriangular A i c m` (clock rows `A θ l = θ l + c l`, `l ≠ i`; `∂_i A_i ≥ m > 0`), `abs_slice_le`, `injective`, `surjective`, `fderiv_injective`, `invFun_clock`; `IsClockAngleGraph k i c m`, `isClockAngleGraph_of_clock` |
| `ClockGraphCert` | `invarianceError_ofReal_mul`, `ClockMono c i m`, `CertifiedTorusAt.clock` (clock lemma with slope `a`), `CertifiedTorusAt.le_fderiv_torusAngle` (Cauchy transfer of the diagonal), `CertifiedTorusAt.isClockAngleGraph`, `KAM.Certificate.CertifiedTorus.exists_clockGraph` (certified hypotheses satisfiable only for `n = 2`, see §2.4 *Scope*) |
| `ClockGraphCheck` | `actionSlope`, `eval_add_action`, `checkClock`, `checkClock_sound`; `clockDiagModel`, `checkClockGraph` (SOS, the SO form), `checkClockGraphReal` (real torus), their soundness; `KAM.Certificate.CertifiedTorus.exists_clockGraph_of_checks` (only for `n = 2`, as above) |
| `Tests/ClockGraph` | clock check on T2 and fail-closed shapes; diagonal checks on probe data (off-diagonal mode: near-identity check fails, clock checks pass); the full chain on the certified T2 (`toyCert2_clockGraph`, `s∞ = 2`) |
| `GraphBridge` | `IsAnalyticAngleGraph.toGraphTorus`, `.toGraphTorusOfModel`, `IsAngleGraph.toGraphTorus`, `.toGraphTorusOfModel`, `IsClockAngleGraph.toGraphTorusOfModel`: either graph adapter gives a `Confinement.GraphTorus` (`n = 2`) for `twoTorus_confinement` |
| `Tests/GraphBridge` | a near-identity torus and a sheared clock torus (`∂₀A₁` up to `6π`, `shear_not_derivNearId`) feed one `twoTorus_confinement` (`bridge_confined`); the certified T2 as a `GraphTorus` through both adapters |

### 2.1 Graph/embedding adapter — the checkable condition

For `K_θ(θ) = θ + U(θ)` (angle block of the certificate's own embedding `c.K`), the numerical
condition is exactly

* **`AngleNearId c δ`**: `0 ≤ δ` and `‖(DK(ι x)(ι v))_θ - ι v‖ ≤ δ ‖v‖` for real `x, v`, i.e. for
  every row `i`: `Σ_j |∂_j U_i(x)| ≤ δ` on the real torus (max-norm operator norm);
* **the margin** `δ + disp/ρ∞ < 1`.

Two `Bool` checks, both `decide (0 ≤ δ)`, `decide (δ ρ∞ + disp < ρ∞)` (exact rationals) and, for
each `i < n`, `ble (row bound)↑ (δ)↓` (`δ : ℚ`):

* **`checkAngleGraphReal c δ` (use this one)**: the row bound is `Σ_j sup_{x ∈ ℝⁿ} |∂_j U_i(x)|`
  from the derivative models before their conversion to degree `0` (`angleDerivModel`, i.e.
  `CertModel.ofDeriv`), summed with the weight `w = 1` (`CertModel.norm_le_supBound_real`): for
  `U_i = (2π)^d Σ_k c_k e^{2πi k·θ}` it is `(2π)^{d+1} Σ_j Σ_k |k_j| |c_k|` (upper rational bound of
  `2π`; radius from coefficient rounding only, `0` on `ℚ`). Sound by `checkAngleGraphReal_sound`.
* `checkAngleGraph c δ` (strip, kept for compatibility): the row bound is the sup over the strip
  `T_ρ` of the degree-`0` models used by `checkEmbedding`; each mode carries about `e^{2π|k|ρ}`, and
  the degree conversion adds a radius measured in that weight. On T2 (`ρ = 9`) a single mode of
  amplitude `10⁻²⁰` fails it at `δ = 0.99` while the real check passes at `2 · 10⁻¹⁹`
  (`Tests/Probes`). Sound (`checkAngleGraph_sound`) but **very** conservative for large `ρ`.

Why the margin: `‖K∞ - K‖ ≤ disp` on `T_{ρ∞}` gives, by Cauchy on the polydiscs of radius `< ρ∞`
around real points, `‖DK∞(ι x) - DK(ι x)‖ ≤ disp/ρ∞` (`norm_fderiv_sub_le_of_real`), so the angle
map `A` of `k = Re K∞ ∘ ι` has `‖DA - 1‖ ≤ δ + disp/ρ∞ < 1` (`derivNearId_torusAngle_realRestriction`).
Then `A` is a bi-Lipschitz bijection of `ℝⁿ` commuting with `ℤⁿ` (a lift of a homeomorphism of
`𝕋ⁿ`), its inverse is analytic, and (`IsAngleGraph k L`):

* `eq_graph`: `k θ = (A θ, G (A θ))`, `G = torusGraph k` analytic and `ℤⁿ`-periodic;
* `range_eq`: `range k = {z | z.2 = G z.1}`; `apply_invFun`: `k (A⁻¹ φ) = (φ, G φ)`;
* `injective_mod`: `A θ' = A θ + m → θ' = θ + m` (the torus embeds `𝕋ⁿ`);
* `immersion`, `fderiv_lower`: `(1 - L) ‖v‖ ≤ ‖Dk(θ) v‖`; `angle_lower`, bijectivity,
  `angleHomeomorph`, continuity and analyticity of `G` and `A⁻¹`.

The fully checked form:

```lean
theorem KAM.Certificate.CertifiedTorus.exists_realGraph_of_checks {c : TorusCertificate n α}
    {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar) (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) {δ : ℚ}
    (hg : checkAngleGraphReal c δ = true ∨ checkAngleGraph c δ = true) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf) ((δ : ℝ) + (c.params.disp : ℝ) / c.params.rhoInf)
```

`IsRealModelTorus H ω E k`: `k` analytic, `k(θ + m) = k θ + (m, 0)`, `H` differentiable along `k`,
every line `s ↦ k(θ + s ω)` solves Hamilton's equations of `H` (frozen `X_H = (∂_I H, -∂_θ H)`),
and `H ∘ k = E`. It moves to any real Hamiltonian agreeing with `H` on an open set containing the
torus (`IsRealModelTorus.congr`), e.g. a closed-form physical expression.

### 2.2 Chart transport adapter

`IsFieldTransport Ψ Hc F κ O`: for `p ∈ O`, `Ψ` is differentiable at `p` and
`DΨ(p) X_{Hc}(p) = κ F(Ψ p)`. Consequences (all in `Transport`):

* orbits: a model solution `y` gives the physical solution `τ ↦ Ψ (y (τ/κ))`;
* tori: `IsRealModelTorus Hc ω E k` inside `O` gives `IsPhysicalFlowTorus F (κ⁻¹ ω) (Ψ ∘ k)`;
* energy levels: `Hc = a · H_phys ∘ Ψ` on `O` gives `H_phys ∘ Ψ ∘ k = E/a`;
* lattice: `Ψ(p + (m, 0)) = Ψ p + T m` gives `(Ψ ∘ k)(θ + m) = (Ψ ∘ k) θ + T m` (`T = 0`: periodic);
* injectivity modulo `ℤⁿ` (chart injective modulo the angle lattice on `O`) and immersion
  (`DΨ` injective on `O`); analyticity (analytic chart);
* clock rescaling: `IsFieldTransport.const_mul`: `IsFieldTransport Ψ Hc F κ O` gives
  `IsFieldTransport Ψ (r · Hc) F (r κ) O` for `r ≠ 0` (a certificate Hamiltonian `κ · H`).

**Invariance** (`Invariance`). `IsPhysicalFlowTorus F ν L` only says that the torus lines are
solutions. If `F` is `C¹` on an open `W ⊇ range L` (hence locally Lipschitz there), a solution `y`
of `ż = F z` in `W` on an interval `J` with `y t₀ = L θ₀` satisfies `y t = L(θ₀ + (t - t₀) ν)` for
all `t ∈ J` (`eqOn_line`, by `KAM.ODE.gen_uniqueness`); so `range L` is invariant
(`mem_range_of_solution`, `isInvariantSet`) and every bound valid on the torus holds along every
solution that meets it (`forall_solution`). In model coordinates use
`IsRealModelTorus.isPhysicalFlowTorus_self` (`F = X_H`, `C¹` where `H` is `C²`).

From geometry: `isFieldTransport_of_isChart`: a core `c`-chart (`KAM.Planetary.IsChart c Ψ O`:
analytic, `Ω(DΨ u, DΨ v) = c Ω(u, v)`) and `Hc = a · H ∘ Ψ` on the open `O` give
`IsFieldTransport Ψ Hc (hamiltonianVectorField H) (a c) O`.

Assembly (`Physical`): with `hDO : ∀ p, ι₂ p ∈ c.D → p ∈ O` (the real points of the certificate
domain lie in the chart domain) and `hHc : ∀ p ∈ O, Hc p = realHam c.H p`,

```lean
theorem CertifiedTorusAt.physical (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H)
    {O : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hO : IsOpen O)
    (hDO : ∀ p, realInclusion₂ n p ∈ c.D → p ∈ O) {Hc : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hHc : ∀ p ∈ O, Hc p = realHam c.H p) {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → E} {F : E → E}
    {κ : ℝ} (hκ : κ ≠ 0) (hΨ : IsFieldTransport Ψ Hc F κ O) :
    (∀ θ, realRestriction Kinf θ ∈ O) ∧
      IsRealModelTorus Hc (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsPhysicalFlowTorus F (κ⁻¹ • (sinf • ωstar)) (Ψ ∘ realRestriction Kinf)
```

and `CertifiedTorusAt.physical_energy` adds `H_phys (Ψ (k θ)) = E₀ / a`.

### 2.3 Observables

From an enclosure of the certificate's own real torus `Re K ∘ ι` (numerical data):

* `observable_bounds`: `‖Df‖ ≤ Λ` on a convex `S` containing the real points of `c.D` and of
  `Re K ∘ ι` (the latter from `checkEmbedding`, `realInclusion₂_realRestriction_K_mem_D`), and
  `f ∘ Re K ∘ ι ∈ [lo, hi]`, give `f ∘ k ∈ [lo - Λ disp, hi + Λ disp]`. For a physical observable
  `g` take `f = g ∘ Ψ`;
* coordinates: `abs_angle_sub_le`, `abs_action_sub_le` (shift `≤ disp`); derivatives:
  `norm_fderiv_realRestriction_sub_le` (shift `≤ disp/ρ∞`);
* checked action range: `checkActionRangeReal c i ctr r` (the model of `A_i - ctr` of
  `checkEmbedding`, summed at the real points with weight `1`) gives `|k_I(θ)_i - ctr| ≤ r + disp`
  (`abs_action_sub_ctr_le_real`); the strip version `checkActionRange` (weight `W`) is conservative
  (`abs_action_sub_ctr_le`);
* frequency: `‖κ⁻¹ s∞ ω* - κ⁻¹ s ω*‖ ≤ disp/|κ|` (`norm_physFreq_sub_le`);
* time: a bound at every torus point holds along every torus line for all `τ ∈ ℝ` (`forall_orbit`,
  a restatement), and along every solution that meets the torus, at every time of its interval,
  when `F` is `C¹` near the torus (`IsPhysicalFlowTorus.forall_solution`).

These bound observables **on the torus**. In dimension `n ≥ 3` one torus does not enclose a region of
its energy surface: bounds for uncertain initial conditions need families of tori, extra geometry
or finite-time stability (programs B–D). For `n = 2` (two degrees of freedom), two tori on one energy
level bound a region of it; that confinement argument is the core's
`KAM.Application.Confinement.twoTorus_confinement` (landed from LG00-CONF), which takes its tori as
`Confinement.GraphTorus`; both graph adapters produce one through `GraphBridge` (§2.5).

### 2.4 Clock-triangular graph adapter (`AngleGraph`, `ClockGraph*`)

`AngleNearId` bounds whole rows of `DU`. In an extended phase space with a **clock** (an action
`I_l` with `∂_{I_l} H ≡ a` constant: periodically forced systems, e.g. the Moon's spin–orbit
problem), the clock lemma `KAM.Certificate.clock_frequency` makes the clock angle of the exact
torus exact, `A_l(θ) = θ_l + c_l`; then `DA` is triangular and only the diagonal entry
`∂_i A_i` of the free row matters. No bound on the off-diagonal entries `∂_l U_i` is needed.

**The graph notion** (`AngleGraph`). `IsAnalyticAngleGraph k` is the qualitative content of
`IsAngleGraph` without the constant `L`: `k` analytic; `A = torusAngle k` bijective, commuting
with `ℤⁿ`, with analytic inverse and `DA(θ)` injective for every `θ`; `eq_graph`, `range_eq`,
`graph_add_int`, `analytic_graph` (`G = torusGraph k`); `injective_mod`; `immersion`. The general
constructor `isAnalyticAngleGraph_of_bijective` needs an analytic `k` with
`k(θ + m) = k θ + (m, 0)`, a bijective `A` and `DA` injective everywhere (the inverse is
continuous because `A` is an open map, `isOpenMap_of_hasStrictFDerivAt_equiv`, and analytic by
`Homeomorph.contDiff_symm` at order `ω`). `IsAngleGraph.isAnalyticAngleGraph` (given analytic `k`)
shows that the near-identity adapter lands in the same notion, so a consumer can take
`IsAnalyticAngleGraph` and accept either adapter. Not included: bi-Lipschitz constants (the
clock criterion gives only the slice bound below).

**The pure criterion** (`ClockGraph`). `IsClockTriangular A i c m`: `A : ℝⁿ → ℝⁿ`
differentiable, `A(θ + m) = A θ + m` (`m ∈ ℤⁿ`), `A θ l = θ l + c l` for every `l ≠ i`, and
`m ≤ ∂_i A_i(θ)` with `0 < m`. Then `A` is bijective (injective by the slice bound
`m |s' - s| ≤ |A_i(θ + s' eᵢ) - A_i(θ + s eᵢ)|` (`abs_slice_le`) once the clock components agree;
surjective by intermediate values on the line with `A_i(θ + eᵢ) = A_i(θ) + 1`), `DA(θ)` is
injective (triangular, diagonal `≥ m` and `1`), and `A⁻¹(φ)_l = φ_l - c_l` (`invFun_clock`).
`IsClockAngleGraph k i c m` is `IsAnalyticAngleGraph k` plus `IsClockTriangular (torusAngle k) i
c m`; `isClockAngleGraph_of_clock` builds it from an analytic `k` with `k(θ + m) = k θ + (m, 0)`,
the clock rows and the diagonal bound.

**Certificate level** (`ClockGraphCert`). The checkable diagonal condition is

* **`ClockMono c i m`**: `m ≤ Re (DK(ι x) eᵢ)_{θ,i}` for every real `x` (the certificate's own
  `K`), and **the margin** `disp < m ρ∞`.

`CertifiedTorusAt.clock`: if `∂_{I_l} c.H = a > 0` on `c.D` and `ω*` is `(γ, τ)`-Diophantine
(`γ > 0`; an input of every certifier's soundness theorem), then `s∞ ω*_l = a` and
`A_l(θ) = θ_l + c_l` (the clock lemma applied to `a⁻¹ c.H` at `a⁻¹ s∞ ω*`, via
`invarianceError_ofReal_mul`). `CertifiedTorusAt.le_fderiv_torusAngle`: Cauchy on `T_{ρ∞}` moves
`ClockMono c i m` to `∂_i A_i ≥ m - disp/ρ∞` (the single-entry case of
`norm_fderiv_sub_le_of_real`). Together (`CertifiedTorusAt.isClockAngleGraph`,
`CertifiedTorus.exists_clockGraph`), with every `l ≠ i` a clock:
`IsClockAngleGraph (realRestriction K∞) i c' (m - disp/ρ∞)`, `m - disp/ρ∞ > 0`.

**Checks** (`ClockGraphCheck`):

* **`checkClock c i a`**: `0 < a` and `actionSlope l c.ham = some a` for every `l ≠ i`.
  `actionSlope l` is syntactic: `.action j` has slope `1` if `j = l` else `0`; constants, `π` and
  modes `0`; sums add; `.mul (.const q) e` has `q ·` the slope of `e`; every other constructor
  (products, quotients, powers, `exp`, `sin`, `cos`, `sqrt`) needs operands of slope `0`.
  Sound: `eval_add_action` (`H(z + t e_{I_l}) = H(z) + a t` for complex `t`), hence
  `∂_{I_l} H = a` wherever `H` is holomorphic (`checkClock_sound`, from `IsRealHolo c.D c.H`).
  It recognises `soHamExpr` (slope `1`), `soRotHamExprScaled c` (slope `c`) and
  `κ · lockHamExpr Ω cs` (slope `κ`; checked on concrete `Ω, cs`); a constant *right* factor or
  a product of actions fails closed.
* **`checkClockGraphReal c i mono`** (use this one when `ρ` is large): the margin
  `disp < mono ρ∞` and `sup_{x ∈ ℝⁿ} |∂_i U_i(x)| ≤ 1 - mono`, the bound being the unconverted
  derivative model `angleDerivModel n c.emb c.weight i i` at weight `1`, i.e.
  `(2π)^{d+1} Σ_k |k_i| |c_k|` (rounded up). Sound: `checkClockGraphReal_sound`.
* **`checkClockGraph c i mono mono₀ sos`** (the spin–orbit form): the margin and
  `checkRealLowerBound c.weight c.cfgLow (clockDiagModel n c.emb c.weight c.piEnc i) mono₀ mono
  sos`, a paid SOS lower bound of `Re ∂_i K_{θ,i}` on the real torus; its residual is measured in
  the strip weight, so it is conservative for large `ρ` (on T2, `ρ = 9`, it fails with an empty
  witness where the real check passes). Sound: `checkClockGraph_sound`.

The fully checked form:

```lean
theorem KAM.Certificate.CertifiedTorus.exists_clockGraph_of_checks
    {c : TorusCertificate n α} {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar)
    (hs : checkStatic c = true) (hh : checkHamBounds c = true) {i : Fin n} {a : ℚ}
    (hclk : checkClock c i a = true) {γ τ : ℝ} (hγ : 0 < γ) (hdio : IsDiophantine γ τ ωstar)
    {mono : ℚ}
    (hg : checkClockGraphReal c i mono = true ∨
      ∃ (mono₀ : ℚ) (sos : CertPoly α), checkClockGraph c i mono mono₀ sos = true) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      (∀ l, l ≠ i → sinf * ωstar l = a) ∧ ∃ cc : Fin n → ℝ,
      IsClockAngleGraph (realRestriction Kinf) i cc
        ((mono : ℝ) - (c.params.disp : ℝ) / c.params.rhoInf)
```

(`CertifiedTorus.exists_clockGraph` is the same with `IsRealHolo c.D c.H`, the clock hypotheses
`∂_{I_l} c.H = a` on `c.D` and `ClockMono c i m` as `Prop`s, e.g. for an entire `H` without
`checkHamBounds`.)

Scope: for `n ≥ 3`, two clocks have the same frequency `a`, so `s∞ ω*` is resonant
(`k = e_l - e_{l'}`) and the Diophantine hypothesis fails: the certified adapter is of use for
`n = 2` (one clock, one free angle). The pure layer holds for every `n`. This applies to each
certified statement: `CertifiedTorusAt.clock` is fine for any `n` (one clock), but
`CertifiedTorusAt.isClockAngleGraph`, `KAM.Certificate.CertifiedTorus.exists_clockGraph` and
`KAM.Certificate.CertifiedTorus.exists_clockGraph_of_checks` (every `l ≠ i` a clock) have
satisfiable hypotheses only for `n ≤ 2`. (AUDIT-V2-CLOCKGRAPH-1 N2: the landed docstrings of
`ClockGraphCert.lean` and `ClockGraphCheck.lean` do not repeat this, and landed `.lean` files are
not edited; the caveat lives here and in the module docstring of `GraphBridge.lean`.)

Beyond near-identity (N3): `Tests/GraphBridge` proves `IsClockAngleGraph (shearK c) 1 0 1` for the
sheared parametrization `A(θ) = (θ₀, θ₁ + 3 sin 2πθ₀)` of a flat torus, whose off-diagonal entry
`∂₀A₁ = 6π cos 2πθ₀` reaches `6π`, and `shear_not_derivNearId`: no `DerivNearId` bound with
`L < 1` holds for it. A *certified* torus with a large off-diagonal `∂_l U_i` is not available
cheaply (for an integrable toy the exact torus at a Diophantine frequency has constant `U`), so
this case is tested at the pure level.

Tests (`Tests/ClockGraph`, `decide +kernel`, 2.4 s, 1.8 GB): `checkClock toyCert2 0 1` (T2:
`H = I₁ + I₀²/2`) and its fail-closed variants; on T2's data with one mode added to `U₀`:
the off-diagonal mode `k = (0, 1)`, `a = 1/10` (`sup |∂₁ U₀| = 4π/10 > 1`) fails
`checkAngleGraphReal` at `δ = 0.99` and passes both clock checks at `mono = 0.99`; the diagonal
mode `k = (1, 0)`, `a = 1/100` passes the real check at `mono = 4/5`, fails it at `9/10`, and fails
the SOS check at `4/5`; `mono = 0` fails the margin. Full chain: `toyCert2_clockGraph` (exact
torus of T2 at `s∞ = 2`, clock-triangular graph with free angle `0`, diagonal
`≥ 99/100 - disp/ρ∞`), through either diagonal check.

### 2.5 Bridge to the confinement (`GraphBridge`)

The core confinement (`KAM.Application.Confinement.twoTorus_confinement`, two degrees of freedom,
`Phase = ℝ² × ℝ²`) takes its tori as `GraphTorus V H E lo hi`: `k`, a continuous two-sided inverse
`Θ` of the angle map, the linear flow `s ↦ k(θ + s ν)` of `V`, the level `H ∘ k = E`, the action
box `(k θ).2 ∈ [lo, hi]`. `GraphBridge` produces it from either graph adapter, with
`Θ = A⁻¹ = invFun (torusAngle k)`:

```lean
def IsAnalyticAngleGraph.toGraphTorus (hG : IsAnalyticAngleGraph k) (ν : Fin 2 → ℝ)
    (hflow : ∀ θ t, HasDerivAt (fun s : ℝ => k (θ + s • ν)) (V (k (θ + t • ν))) t)
    (henergy : ∀ θ, H (k θ) = E) (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) : GraphTorus V H E lo hi
def IsAnalyticAngleGraph.toGraphTorusOfModel (hG : IsAnalyticAngleGraph k)
    (hT : IsRealModelTorus H ω E k) (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) :
    GraphTorus (hamiltonianVectorField H) H E lo hi
def IsAngleGraph.toGraphTorus (h : IsAngleGraph k L) (hk : AnalyticOnNhd ℝ k univ) ...
def IsAngleGraph.toGraphTorusOfModel (h : IsAngleGraph k L) (hT : IsRealModelTorus H ω E k) ...
def IsClockAngleGraph.toGraphTorusOfModel (h : IsClockAngleGraph k i c m)
    (hT : IsRealModelTorus H ω E k) ...
```

(simp lemmas `toGraphTorus_k`, `toGraphTorus_Θ`, `toGraphTorus_ν`, `toGraphTorus_graph₁`: the
first action over `φ` is `torusGraph k φ 0`). For a certified torus: the graph and the real model
torus from `CertifiedTorus.exists_realGraph_of_checks` or `CertifiedTorus.exists_clockGraph_of_checks`,
the action box from `CertifiedTorusAt.abs_action_sub_ctr_le_real` (`checkActionRangeReal`), then
the bridge. The model torus solves `X_{realHam c.H}`; for the confinement's chart Hamiltonian move
it with `IsRealModelTorus.congr` (equal on an open set containing the torus).

Tests (`Tests/GraphBridge`, 3.2 s, 1.87 GB): `bridge_confined` runs `twoTorus_confinement` on the
toy `H = −a₂` with the torus `a = (−1/2, 0)` from the near-identity adapter
(`IsAngleGraph.toGraphTorus`, `L = 0`) and the torus `a = (1/2, 0)` in the sheared parametrization
from the clock adapter; `toyCert2_graphTorus_clock` and `toyCert2_graphTorus_nearId` make the
certified T2 a `GraphTorus` of `X_{realHam c.H}` on the level `E₀` with the box
`[ctr ± (r + disp)]` from two `checkActionRangeReal` checks. (T2 has one certified torus and
`∂H/∂I₁ = 1 > 0`, so it is not itself run through the confinement.)

## 3. Instances

### 3.1 SO-2 (the Moon's spin band; landed pipeline, read-only here)

| Component | SO-2 |
|---|---|
| Model | `KAM.SpinOrbit.soField` on `ℝ³ = (q, p, φ)` (frozen), `soV`, `soEps`, `soModes`, `soA` |
| Coordinates | extended phase space with the clock action; rotating frame `Q₀ = q - φ` and time scale `c` (`soRotHamExprScaled c`); shear `(x, y) ↦ (x - y, y)` (`SoGraph.torus_of_rot`) |
| Approximation | exact: the certificate's `HamExpr` evaluates to the model (`soHamExpr_eval`, `soRotHamExpr_eval`) |
| Frequency | `lunarRotFreq ν κ = (κ(ν - 1), κ)`, `ν = ν∓` quadratic, `lunarRotFreq{Minus,Plus}N_isDiophantine_65` |
| Certificate | `SoGraphCert` over `CertFixed 96`, route `routeAV2`, `lunar_barriers_of_R2V2` (`LunarAssemblyV2`), data `KAMLunarBand` |
| Physical output | frozen `SoBarrier`, `lunar_barriers`, `lunar_spin_confinement` (`|p(t) - 1| ≤ 2755/100000` for all `t`) via `so_confinement` |

Relation to the adapters: SO's graph check `checkSoGraph` (`mono > disp/ρ∞`, one SOS lower bound of
`∂_{θ₀} K_{q}`, the action range `[pLo, pHi]`) is the clock-triangular criterion of §2.4 at
`n = 2`, free angle `i = 0`, clock `1` (`clock_frequency`: `φ = θ₁ + c₀`):

* `soGraphMonoModel g` **is** `clockDiagModel 2 g.base.emb g.base.weight g.base.piEnc 0`
  (`rfl`), and the first two conjuncts of `checkSoGraph g` are exactly
  `checkClockGraph g.base 0 g.mono g.mono₀ g.sosMono`;
* `soGraph_deriv_transfer` is the single-entry case of `norm_fderiv_sub_le_of_real`
  (`CertifiedTorusAt.le_fderiv_torusAngle`); `SoGraph.graphAbs_sub_le` corresponds to
  `abs_slice_le`, and `SoGraph.Torus.soGraphInv` (and SO-3's `LockAngle.lockInv`) corresponds to
  `invFun (torusAngle k)` of `IsClockAngleGraph` (`invFun_clock`: the clock component of the
  inverse is `φ - c₀`); these are analogues on different carriers (`ℝ → ℝ → ℝ` versus
  `Fin n → ℝ`), not proved identifications;
* the clock slope of `soHamExpr` is `1`, of `soRotHamExprScaled c` is `c`
  (`checkClock g.base 0 c`);
* the action range is `observable_bounds` for the action coordinate; the rotated-frame map is a
  field transport (complex form `hamiltonianVectorFieldℂ_soRotHC`).

**Adoption recipe (SO-2).** Compiled on `v2-clockgraph` in a scratch module importing
`KAM.SpinOrbit.Graph.Cert` and `KAM.SpinOrbit.Rotated` (not committed: the core does not import
the SO track; the text is in `docs/campaign/handoffs/V2-CLOCKGRAPH.md`):

```lean
theorem checkClockGraph_of_checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α)
    (h : checkSoGraph g = true) : checkClockGraph g.base 0 g.mono g.mono₀ g.sosMono = true := by
  simp only [checkSoGraph, Bool.and_eq_true] at h
  simp only [checkClockGraph, Bool.and_eq_true]
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem checkClock_soRot {α : Type} [CertArith α] (g : SoGraphCert α) {c : ℚ} (hc0 : 0 < c)
    (hham : g.base.ham = soRotHamExprScaled c) : checkClock g.base 0 c = true := by
  have h1 : actionSlope 1 (soRotHamExprScaled c) = some c := by
    simp [soRotHamExprScaled, actionSlope, hamConstVal?, soRot_slope]  -- soRot_slope: decide
  simp [checkClock, hham, h1, hc0, List.all_cons, List.finRange_succ]

-- a rotated-frame SO-2 certificate through the clock adapter
example ... (hham : g.base.ham = soRotHamExprScaled c) (hs : checkStatic g.base = true)
    (hh : checkHamBounds g.base = true) (hg : checkSoGraph g = true)
    (hT : CertifiedTorus g.base ωstar) (hdio : IsDiophantine γ τ ωstar) :
    ∃ Kinf sinf, CertifiedTorusAt g.base ωstar Kinf sinf ∧ sinf * ωstar 1 = c ∧
      ∃ cc, IsClockAngleGraph (realRestriction Kinf) 0 cc (g.mono - disp/ρ∞) := by
  obtain ⟨Kinf, sinf, hT', -, hf, hG⟩ := hT.exists_clockGraph_of_checks hs hh
    (checkClock_soRot g hc0 hham) (by exact_mod_cast (checkStatic_sound hs).hγ) hdio
    (.inr ⟨_, _, checkClockGraph_of_checkSoGraph g hg⟩)
  exact ⟨Kinf, sinf, hT', hf 1 (by decide), hG⟩
```

What adoption would change: nothing in the data or in the frozen statements (`checkSoGraph`
implies `checkClockGraph`, whose model is SO's own, definitionally); a new proof module of the SO track could derive
`SoBarrier` from `IsClockAngleGraph` (continuous, doubly periodic graph `p = (torusGraph k)(q, φ)`
with the shear `(x, y) ↦ (x - y, y)` in the rotated frame) and the invariance of §2.2
(`IsRealModelTorus.isPhysicalFlowTorus_self` or a field transport to `soField`), replacing the
hand-made inversion `SoGraph.Torus`. If `checkHamBounds` is not at hand, `exists_clockGraph` with
`isRealHolo_of_nonvanishing` (or `isRealHolo_of_differentiableOn` for the entire `soRotHC`) does
the same.

### 3.2 SO-3 (the Moon's synchronous lock; in progress)

| Component | SO-3 |
|---|---|
| Model | `soField` (as SO-2); `lunarSyncOrbit`, `libAction` (frozen) |
| Coordinates | lock chart `lockToPhysicalR Ω c : ℝ² × ℝ² → ℝ³` around the centre `c = lockCentre cs`, Hamiltonian `lockHamiltonianR Ω c`, domain `{z | 0 < z.2 0}`, time scale `κ` |
| Approximation | exact model expression `lockHamExpr Ω cs` (`.mul (.const κ) …`) |
| Frequency | as SO-2, at the lock frequencies |
| Certificate | `LockGraphCert` (graph cert + `Ω`, `κ`, `cs`), `lockBarrier_of_certV2`, data `KAMLunarLock` |
| Physical output | `LockBarrier`, frozen `lunar_sync_lock` (draft) |

The transport identity of the unscaled lock Hamiltonian is exactly `lock_conjugacy`
(`KAM/SpinOrbit/Lock/Coords/Conjugacy.lean`), at clock `1`. The certificate Hamiltonian is the
time-scaled `κ · lockHamExpr Ω cs` (`KAM/SpinOrbit/Lock/Graph.lean`), so the model Hamiltonian of
the contract (`hHc : Hc = realHam c.H` on `O`) is `Hc = κ · lockHamiltonianR Ω c` and the clock is
**`κ`**, by `IsFieldTransport.const_mul`:

```lean
-- recipe (not compiled here: KAM.SpinOrbit.Lock.* is not built in this worktree)
theorem lock_isFieldTransport {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (hc : ContDiff ℝ 3 c) :
    IsFieldTransport (lockToPhysicalR Ω c) (lockHamiltonianR Ω c) soField 1
      {z | 0 < z.2 0} :=
  fun z hz => ⟨differentiableAt_lockToPhysicalR hΩ hd0 hd1 z hz, by
    rw [one_smul]; exact lock_conjugacy hΩ c hc z hz⟩
  -- hd0, hd1 from `contDiff_succ_iff_deriv` as in `lock_conjugacy`

-- the certificate's clock: `Hc = κ · lockHamiltonianR Ω c`, physical frequency `(κ · 1)⁻¹ s∞ ω*`
theorem lock_isFieldTransport_scaled {Ω κ : ℝ} (hΩ : 0 < Ω) (hκ : κ ≠ 0) (c : ℝ → ℝ)
    (hc : ContDiff ℝ 3 c) :
    IsFieldTransport (lockToPhysicalR Ω c) (fun z => κ * lockHamiltonianR Ω c z) soField
      (κ * 1) {z | 0 < z.2 0} :=
  (lock_isFieldTransport hΩ c hc).const_mul hκ
```

`hHc` (`κ · lockHamiltonianR Ω (lockCentre cs) = realHam c.H` on `{z | 0 < z.2 0}`) is the real
form of the lock package's evaluation identity for `lockHamExpr` (the one behind
`hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt`).

The lock's angle inversion (`LockAngle`, monotone `α` in `θ₀`) is again the clock-triangular graph
condition (§2.4), with clock slope `κ`: `LockGraphCert.graph` is a `SoGraphCert`, so
`checkClockGraph_of_checkSoGraph g.graph` applies, and
`actionSlope 1 (.mul (.const κ) (lockHamExpr Ω cs)) = some κ` (by `decide` on the concrete
`Ω, cs`; a sample `Ω = 1/3`, `cs = [1/2, 1/5]`, `κ = 5/4` was checked). `CertifiedTorusAt.clock`
then gives `s∞ ω*₁ = κ`, i.e. SO-3's unscaled `(s∞/κ) ω*₁ = 1`. Recipe (compiled in the same
scratch module with `KAM.SpinOrbit.Lock.Graph`):

```lean
example (g : LockGraphCert α) (hκ : 0 < g.κ)
    (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hslope : actionSlope 1 (lockHamExpr g.Ω g.cs) = some 1)   -- `decide` on concrete data
    (hs : checkStatic g.graph.base = true)
    (hnv : g.graph.base.ham.NonvanishingOn g.graph.base.D)
    (hg : checkSoGraph g.graph = true) (hT : CertifiedTorus g.graph.base ωstar)
    (hdio : IsDiophantine γ τ ωstar) :
    ∃ Kinf sinf, CertifiedTorusAt g.graph.base ωstar Kinf sinf ∧ sinf * ωstar 1 = g.κ ∧
      ∃ cc, IsClockAngleGraph (realRestriction Kinf) 0 cc (g.graph.mono - disp/ρ∞) := by
  have hH := isRealHolo_of_nonvanishing g.graph.base hnv
  have hclk : checkClock g.graph.base 0 g.κ = true := by
    have h1 : actionSlope 1 g.graph.base.ham = some g.κ := by
      simp [hham, actionSlope, hamConstVal?, hslope]
    simp [checkClock, h1, hκ, List.finRange_succ]
  obtain ⟨ha, hclock⟩ := checkClock_sound hH hclk
  obtain ⟨hmono, hm⟩ := checkClockGraph_sound hs (checkClockGraph_of_checkSoGraph g.graph hg)
  obtain ⟨Kinf, sinf, hT', -, hf, hG⟩ := hT.exists_clockGraph hs hH ha hclock
    (by exact_mod_cast (checkStatic_sound hs).hγ) hdio hmono hm
  exact ⟨Kinf, sinf, hT', hf 1 (by decide), hG⟩
```

### 3.3 LG00 (secular Sun–Jupiter–Saturn; branch `lg00-cert`, application package to come)

| Component | LG00 |
|---|---|
| Model | `lg00H11` (LG00 eq. (11)), field `lg00H11Field` in LG00's `(ξ, η)` order, time in years |
| Coordinates | `lg00Psi : (θ, a) ↦ (ξ, η)` on `lg00PositivePhase`; `Ψ*(Σ dξ∧dη) = 2πℓ Σ da∧dθ`, `Hc = lg00Hc = (κ/ℓ) H₁₁ ∘ Ψ`, clock `2πκ` (`lg00_transport`) |
| Approximation | exact polynomial (11) and the square-root chart (`lg00_ham_identity`) |
| Frequency | `lg00OmegaStar` on LG00's direction `Γ′` (eq. (51) window) |
| Certificate | `lg00Cert`, `lg00_kamTorus` (and T′, T″ on the exact level, LG00-T2) |
| Physical output | `lg00_physical_torus`; confinement (LG00-CONF) |

Recipe for `lg00_physical_orbits` from the adapters (in the LG00 package):

* `hDO`: from `lg00Cert_D_act_pos` (real points of `lg00Cert.D` have positive actions);
* `hHc : ∀ p ∈ lg00PositivePhase, lg00Hc p = realHam lg00Cert.H p`: real part of
  `lg00_ham_identity`;
* `hΨ : IsFieldTransport lg00Psi lg00Hc lg00H11Field (2 * π * lg00Kappa) lg00PositivePhase`:
  `analyticAt_lg00Psi` and `lg00_transport`;
* `hH : IsRealHolo lg00Cert.D lg00Cert.H`: `isRealHolo_of_differentiableOn` with
  `differentiableOn_lg00Cert_H` restricted to `lg00Cert.D` (or `isRealHolo_of_checkHamBounds`);
* then `hT.physical` gives the flow clause at `(2πκ)⁻¹ s∞ ω*`, `hT.physical_energy` with
  `a = κ/ℓ` the level `(ℓ/κ) E₀`, `analyticOnNhd_comp` and `comp_add_int` (`lg00Psi_add_int`,
  `T = 0`) the rest.

For the confinement (LG00-CONF), the certificate-side facts of the graph adapter for each of T′, T″
are `checkAngleGraphReal c δ = true` (choose `δ ≥ max_i (2π)^{d+1} Σ_j Σ_k |k_j||c_k|`, the real
row sums of the emitted `U`, with `δ ρ∞ + disp < ρ∞`) and, for explicit action bounds,
`checkActionRangeReal c i ctr r = true`; both are small kernel computations on the emitted
certificate data. The strip versions (`checkAngleGraph`, `checkActionRange`) weight each mode by
about `e^{2π|k|ρ}` and may fail where the real criterion holds.

## 4. Gaps and next steps

* **Weaker graph criteria.** `AngleNearId` asks `‖DU‖ < 1`. The clock-triangular criterion of
  SO-2/SO-3 is now in the core (§2.4, V2-CLOCKGRAPH). Still open: invertibility of `DA` everywhere
  as the only input (Hadamard's global inverse theorem, since `A - id` is periodic hence `A`
  proper; not in Mathlib — `isAnalyticAngleGraph_of_bijective` takes bijectivity as an input),
  a general-`n` triangular criterion (one clock, the free block near the identity), and clocks
  with a constant *right* factor in `actionSlope`.
* **Real-point sup bounds (done).** `checkAngleGraphReal` and `checkActionRangeReal` bound at the
  real points with weight `1`. What remains conservative: the row bound is `Σ_j sup_x |∂_j U_i|`
  (not `sup_x Σ_j`), and on fixed-point backends the coefficient-rounding radius is still measured
  in the strip weight (ulp-sized).
* **Invariance needs `C¹`.** `IsPhysicalFlowTorus.mem_range_of_solution` assumes `F` of class `C¹`
  on an open set containing the torus (the core uniqueness lemma); a merely locally Lipschitz `F`
  would need a Lipschitz variant of `KAM.ODE.gen_uniqueness`.
* **Isotropy.** The frozen planetary `IsPhysicalTorus` also asks the torus to be Lagrangian; the
  adapters do not prove isotropy of the certified torus (true for Diophantine invariant tori; not
  needed by the current applications).
* **Lift of LG00-CONF (done).** The two-degree-of-freedom confinement is in the core
  (`KAM.Application.Confinement`); `GraphBridge` (§2.5) connects both graph adapters to it.
* Parameter families and non-Hamiltonian effects are outside this interface (§7 of the
  improvements note).
