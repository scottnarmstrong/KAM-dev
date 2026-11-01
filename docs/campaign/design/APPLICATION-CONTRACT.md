# The application contract: from a model to a physical theorem

Date: 1 November 2026. Branch `v2-adapt` (worker V2-ADAPT, improvement #7 of
[CERTIFIER-V2-IMPROVEMENTS](CERTIFIER-V2-IMPROVEMENTS.md#7-package-the-model-to-physical-conclusion-interface)).
Status: the core adapters below are proved in Lean (`KAM/Application/`, default limits, standard
axioms only); the SO-2/SO-3/LG00 instances are described as recipes with exact Lean names and are
**not** re-proved here (their files are read-only in this wave, and the SO lock coordinates and
LG00 modules are not built in this worktree). No application certificate is claimed by this note.

## 1. What a certified application must supply

A certificate application turns a passing numerical certificate into a theorem about a physical
system. Each row names what must be written down and the Lean object that carries it.

| Component | Required information | Lean carrier (core) |
|---|---|---|
| **Model** | Exact equations, parameters, units and normalization | the physical vector field `F : E → E` on a real normed space `E` (any variable order), and, when it is Hamiltonian, `H_phys : E → ℝ` |
| **Coordinates** | Chart, valid domain, symplectic identity or justified time change | the chart `Ψ : ℝⁿ × ℝⁿ → E`, its open model domain `O`, and the transport identity `IsFieldTransport Ψ Hc F κ O` (`DΨ X_{Hc} = κ F ∘ Ψ` on `O`; `κ` the clock); from a conformally symplectic chart by `isFieldTransport_of_isChart` |
| **Approximation** | Fourier/model truncation and rigorous remainder budgets | the certificate's exact Hamiltonian expression `c.ham` (`c.H = c.ham.eval`) and the identity `Hc = Re c.H` on `O` (`hHc`); a truncated or approximate model is a *different* exact model, and its relation to the physical one is a separate theorem |
| **Frequency** | Exact target, enclosure and infinite Diophantine witness | `ωstar : Fin n → ℝ` exact; `FreqEncloses n c.freqBox ωstar`; `IsDiophantine γ τ ωstar` (proved, e.g. quadratic/cubic constructions); the torus frequency is `s∞ ωstar`, `CertifiedTorusAt.isDiophantine`, `abs_sub_mul_norm_le` |
| **Certificate** | Candidate, route, witness, checked margins and replay receipts | `c : TorusCertificate n α`, a certifier (landed `checkTorusCertificate`, v2 `checkTorusCertificateV2 E`, hybrid …) whose soundness gives `CertifiedTorus c ωstar`; the adapter checks `checkStatic`, `checkHamBounds`, `checkAngleGraph c δ`, `checkActionRange c i ctr r` |
| **Physical output** | Observable bounds, initial set, quantifiers, time interval | `IsPhysicalFlowTorus F ν (Ψ ∘ k)` (every orbit on the torus, all real times), energy level `H_phys = E₀/a`, `IsAngleGraph` (graph over the angles), observable enclosures (`observable_bounds`, `abs_action_sub_ctr_le`, `forall_orbit`) |

The hub is **`CertifiedTorusAt c ω* K∞ s∞`** (`KAM/Application/Certified.lean`): the body of
`CertifiedTorus` with the exact torus `K∞` and the scalar `s∞` named
(`certifiedTorus_iff : CertifiedTorus c ω* ↔ ∃ K∞ s∞, CertifiedTorusAt c ω* K∞ s∞`, `Iff.rfl`).
Every adapter is stated on it, so the graph, the transport and the observables attach to the same
torus: `obtain ⟨K∞, s∞, hT⟩ := (certifiedTorus_iff c ω*).1 h`, then use `hT.isRealModelTorus`,
`hT.isAngleGraph`, `hT.physical`, `hT.observable_bounds`, … (LG00's `lg00TorusWith` is the `n = 2`
case, verbatim.)

## 2. The adapters (`KAM/Application/`)

Module map (all core, additive, under 350 lines each):

| Module | Content |
|---|---|
| `Graph` | pure: `DerivNearId f L` (`‖Df - 1‖ ≤ L`), bi-Lipschitz, bijective (contraction), `toHomeomorph`, analytic inverse; `torusAngle`, `torusGraph`, `IsAngleGraph`, `isAngleGraph_of_derivNearId` |
| `RealTorus` | pure: `realHam h = Re h ∘ ι`, `IsRealHolo D h`, `IsRealModelTorus H ω E k`, `isRealModelTorus_realRestriction`, `IsRealModelTorus.congr`, `isDiophantine_mul_smul` |
| `Certified` | `CertifiedTorusAt`, `certifiedTorus_iff`, `isRealHolo_of_{differentiableOn,nonvanishing,checkHamBounds}`, `CertifiedTorusAt.isRealModelTorus`, `norm_realRestriction_sub_le`, `isDiophantine`, `abs_sub_mul_norm_le` |
| `GraphCert` | `norm_fderiv_sub_le_of_real` (Cauchy at real points), `derivNearId_torusAngle_realRestriction`, `AngleNearId c δ`, `CertifiedTorusAt.isAngleGraph`, `CertifiedTorus.exists_realGraph` |
| `GraphCheck` | `angleRowUp`, `checkAngleGraph`, `checkAngleGraph_sound`, `CertifiedTorus.exists_realGraph_of_checks` |
| `Transport` | pure: `IsFieldTransport`, `IsPhysicalFlowTorus`, `hasDerivAt_comp` (orbits), `IsRealModelTorus.isPhysicalFlowTorus` (tori), `analyticOnNhd_comp`, `comp_add_int`, `injective_mod_comp`, `injective_fderiv_comp`, `level_comp`, `energy_comp`, `hamiltonianVectorField_const_mul` |
| `TransportChart` | `isFieldTransport_of_isChart` (from `KAM.Planetary.IsChart`; imports all of Mathlib, hence separate) |
| `Physical` | `CertifiedTorusAt.physical`, `CertifiedTorusAt.physical_energy` (the generic `lg00_physical_orbits`) |
| `Observables` | `abs_sub_le_of_convex`, `forall_orbit`, `CertifiedTorusAt.observable_bounds`, `abs_angle_sub_le`, `abs_action_sub_le`, `norm_fderiv_realRestriction_sub_le`, `norm_physFreq_sub_le`, `checkActionRange`, `abs_action_sub_ctr_le`, `realInclusion₂_realRestriction_K_mem_D` |
| `Tests/Toy2` | the whole chain on the toy T2 (`toyCert2_physical`) |

### 2.1 Graph/embedding adapter — the checkable condition

For `K_θ(θ) = θ + U(θ)` (angle block of the certificate's own embedding `c.K`), the numerical
condition is exactly

* **`AngleNearId c δ`**: `0 ≤ δ` and `‖(DK(ι x)(ι v))_θ - ι v‖ ≤ δ ‖v‖` for real `x, v`, i.e. for
  every row `i`: `Σ_j |∂_j U_i(x)| ≤ δ` on the real torus (max-norm operator norm);
* **the margin** `δ + disp/ρ∞ < 1`.

`checkAngleGraph c δ` (`δ : ℚ`) checks both with the strip models already used by
`checkEmbedding`: `decide (0 ≤ δ)`, `decide (δ ρ∞ + disp < ρ∞)` (exact rationals), and for each
`i < n`, `ble (Σ_j sup_{T_ρ} |∂_j U_i|)↑ (δ)↓`. The sup over `T_ρ` dominates the real torus, so the
check is sound (`checkAngleGraph_sound`) and slightly conservative.

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
theorem CertifiedTorus.exists_realGraph_of_checks {c : TorusCertificate n α}
    {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar) (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) {δ : ℚ} (hg : checkAngleGraph c δ = true) :
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
  (`DΨ` injective on `O`); analyticity (analytic chart).

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
* checked action range: `checkActionRange c i ctr r` (strip model of `A_i - ctr`, as in
  `checkEmbedding`) gives `|k_I(θ)_i - ctr| ≤ r + disp` (`abs_action_sub_ctr_le`);
* frequency: `‖κ⁻¹ s∞ ω* - κ⁻¹ s ω*‖ ≤ disp/|κ|` (`norm_physFreq_sub_le`);
* time: orbits on the torus stay on it, so each bound holds along them for all `τ ∈ ℝ`
  (`forall_orbit`).

These bound observables **on the torus**. In dimension `n ≥ 3` one torus does not enclose a region of
its energy surface: bounds for uncertain initial conditions need families of tori, extra geometry
or finite-time stability (programs B–D). For `n = 2` (two degrees of freedom), two tori on one energy
level bound a region of it; that confinement argument is LG00-CONF's (`LG00.Confinement.*`), which
consumes `IsAngleGraph` and `IsRealModelTorus`.

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
`∂_{θ₀} K_{q}`, the action range `[pLo, pHi]`) is the **clock-triangular** special case of the
graph condition: the second angle is the clock (`clock_frequency`: `φ = θ₁ + c₀`), so only the
first row needs `∂_{θ₀} Q ≥ m > 0`, which is weaker than `AngleNearId` (no near-identity bound on
`∂_{θ₁} Q`). Its transfer `soGraph_deriv_transfer` is the single-entry case of
`norm_fderiv_sub_le_of_real`; its action range is `observable_bounds` for the action coordinate;
the rotated-frame map is a field transport (complex form `hamiltonianVectorFieldℂ_soRotHC`). An
integration branch could restate the SO-2 chain through `CertifiedTorusAt` and `IsFieldTransport`;
nothing in SO-2 needs to change for the adapters to exist.

### 3.2 SO-3 (the Moon's synchronous lock; in progress)

| Component | SO-3 |
|---|---|
| Model | `soField` (as SO-2); `lunarSyncOrbit`, `libAction` (frozen) |
| Coordinates | lock chart `lockToPhysicalR Ω c : ℝ² × ℝ² → ℝ³` around the centre `c = lockCentre cs`, Hamiltonian `lockHamiltonianR Ω c`, domain `{z | 0 < z.2 0}`, time scale `κ` |
| Approximation | exact model expression `lockHamExpr Ω cs` (`.mul (.const κ) …`) |
| Frequency | as SO-2, at the lock frequencies |
| Certificate | `LockGraphCert` (graph cert + `Ω`, `κ`, `cs`), `lockBarrier_of_certV2`, data `KAMLunarLock` |
| Physical output | `LockBarrier`, frozen `lunar_sync_lock` (draft) |

The transport identity is exactly `lock_conjugacy` (`KAM/SpinOrbit/Lock/Coords/Conjugacy.lean`):

```lean
-- recipe (not compiled here: KAM.SpinOrbit.Lock.* is not built in this worktree)
theorem lock_isFieldTransport {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (hc : ContDiff ℝ 3 c) :
    IsFieldTransport (lockToPhysicalR Ω c) (lockHamiltonianR Ω c) soField 1
      {z | 0 < z.2 0} :=
  fun z hz => ⟨differentiableAt_lockToPhysicalR hΩ hd0 hd1 z hz, by
    rw [one_smul]; exact lock_conjugacy hΩ c hc z hz⟩
  -- hd0, hd1 from `contDiff_succ_iff_deriv` as in `lock_conjugacy`
```

The lock's angle inversion (`LockAngle`, monotone `α` in `θ₀`) is again the clock-triangular graph
condition.

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
are `checkAngleGraph c δ = true` (choose `δ ≥ max_i Σ_j sup |∂_j U_i|` with `δ ρ∞ + disp < ρ∞`) and,
for explicit action bounds, `checkActionRange c i ctr r = true`; both are small kernel computations
on the emitted certificate data.

## 4. Gaps and next steps

* **Weaker graph criteria.** `AngleNearId` asks `‖DU‖ < 1`. The clock-triangular criterion of
  SO-2/SO-3 (and, in general, invertibility of `DA` everywhere: Hadamard's global inverse theorem,
  since `A - id` is periodic hence `A` proper) would cover more certificates; neither is in Mathlib
  in the needed form.
* **Real-point sup bounds.** `checkAngleGraph` bounds `|∂_j U_i|` on the whole strip `T_ρ`; a check
  on the real torus only (`CertModel.norm_le_supBound_real` exists in the hybrid layer) would be
  sharper.
* **Isotropy.** The frozen planetary `IsPhysicalTorus` also asks the torus to be Lagrangian; the
  adapters do not prove isotropy of the certified torus (true for Diophantine invariant tori; not
  needed by the current applications).
* **Lift of LG00-CONF.** After `LG00-CONF DONE`, its general two-degree-of-freedom confinement
  lemma can move to `KAM/Application/` on top of `IsAngleGraph` and `IsRealModelTorus`.
* Parameter families and non-Hamiltonian effects are outside this interface (§7 of the
  improvements note).
