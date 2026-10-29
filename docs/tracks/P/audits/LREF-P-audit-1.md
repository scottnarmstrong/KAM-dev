# LREF-P independent reference audit 1

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-lrefaud`.
Baseline and HEAD: `4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a` (`inp` = `HEAD`).

**Result: 2 CLOSABLE; 7 NEEDS BUNDLE; 0 NOT CLOSABLE.** Existing Lean content passes validation, with packaging notes. A blanket nine-node LEAN_REF relabel is not justified under the handoff's one-declaration rule. No new provider or frozen anchor is being sealed; per-anchor seal readiness is not applicable. This is PASS WITH NOTES for the existing infrastructure, not a proof or seal of any planetary headline.

Authority: the supplied package-audit brief, overridden by the user's exact report destination and the LREF-P handoff's specialized AUDIT FOCUS. Read AGENTS.md, PLAN.md, DECISIONS.md, the nine complete graph records, the cited Part 1/6 blueprint clauses and their parent statements, Track P statement, relevant frozen definitions/theorem context, and the survey's p0-p10 leftovers. The handoff was already untracked on entry; it was not edited. `git diff inp...HEAD` is empty. There are no new public declarations or definitions to audit as branch additions.

## Rule applied

A node can close only by one landed named declaration, or a conjunct of one, expressing its complete SOURCE_CONCLUSION under SOURCE_HYPOTHESES. Multiple correct references do not collectively satisfy that rule. All-time specialization, conversion from analyticity to smoothness, extraction of a local proof fact, or combining moving/fixed cases are proof work unless already exported together. Omitted source assumptions and broader parameter ranges are acceptable strengthenings; added proof-output premises are not.

## Node verdicts

Names below are fully qualified by `KAM.Planetary` except the planar geometry names, which are under `KAM.Kepler`. Locators refer to this exact checkout.

| Node / source record | Candidate declarations | Verdict | Exact reason / usable reference |
|---|---|---|---|
| `stepP:p1:pc-c`; graph 2561; blueprint p1:131-139 | Transport:174 `analyticOnNhd_periodOne_iff`; :188 `fderiv_periodOne`; :212 `periodOne_lattice_iff`; :224 `periodOne_injMod_iff`; :239 `periodOne_hasDerivAt_iff`; :252 `isLatticeTorus_periodOne_iff`; Chart:236 `fastShift_eq_angleScale` | **NEEDS BUNDLE** | The complete (c), plus (d), is split. The packaged torus iff only equates conjunctions specialized to `fullShift`; it does not state the derivative identity, arbitrary shift-family `T` equivalence, or separate injectivity/Lagrangian equivalences. Its `hinj` and `hsym` are local `have`s, not exports. (d) is separately in Chart:236. No extra analyticity or torus premise belongs in the requested wrapper. Proposed `lref_pc_c` below. |
| `stepP:p6:pl-a`; graph 11168; blueprint p6:39-47 | Plane:45 `planeSq_eq_planeDot`; :51 `planeLength_sq`; :54 `planeLength_nonneg`; :65 `planeLength_eq_zero_iff`; :72 `planeLength_neg`; :78 `planeLength_smul`; :89 `abs_planeDot_le`; :95 `planeLength_add_le` | **NEEDS BUNDLE** | Each algebraic clause is proved, with no premises beyond `v,w,c`, but no one theorem states their conjunction. `abs_planeDot_le` is stronger than the signed Cauchy-Schwarz inequality used in the proof. Bundle the seven literal clauses; Cauchy-Schwarz is a proof dependency, not an assumption. |
| `stepP:p6:pl-b`; graph 11196; blueprint p6:41,48 | Plane:117 `norm_le_planeLength`; :125 `planeLength_le_sqrt_two_mul_norm` | **NEEDS BUNDLE** | Correct Pi max norm and sharp sqrt(2) constant; lower and upper inequalities are separate declarations. Proposed conjunction has only `v`. |
| `stepP:p6:pl-c`; graph 11223; blueprint p6:42,49 | Plane:240 `analyticAt_planeLength`; :252 `analyticAt_inv_planeLength`; :262 `hasFDerivAt_planeLength`; :286 `hasFDerivAt_inv_planeLength` | **NEEDS BUNDLE** | All four pieces are proved under exactly `v ≠ 0`; derivative continuous linear maps evaluate to the literal dot/length formulas. Analyticity is stronger regularity, but no single named theorem gives both regularities and both derivatives. Scratch-proved `lref_pl_c` states C-infinity and both scalar evaluations explicitly. |
| `stepP:p6:dom-open`; graph 11285; blueprint p6:54-58 | Models:258 `isOpen_collisionFreeDomain` | **CLOSABLE** | `LEAN_REF: KAM.Planetary.isOpen_collisionFreeDomain`. Type: `(n : ℕ) → IsOpen (collisionFreeDomain n)`. `collisionFreeDomain n` unfolds to exactly `{z : Phase (n*2) | NoCollision z.1}`. It holds for every n, strengthening n≥1, and does not need physical parameters. The graph's q is a dummy domain coordinate, not a missing theorem premise. |
| `stepP:p6:dom-smooth`; graph 11315; blueprint p6:54-59 | Models:319 `analyticOnNhd_movingHamiltonian`; :327 `analyticOnNhd_fixedHamiltonian`; :335/:339 differentiability corollaries | **NEEDS BUNDLE** | Moving and fixed results are separate. Analyticity is an accepted stronger regularity under the package brief's stronger-statement rule, but is not syntactically the graph's C-infinity conclusion. Neither individual analytic theorem states both models. A bundled analytic conjunction could be accepted as stronger content; the supplied, scratch-proved `ContDiffOn ℝ ∞` conjunction removes that representational question. No new regularity hypothesis or uniqueness-of-derivatives assumption is needed. |
| `stepP:p6:he-fix`; graph 11562; blueprint p6:81-99 | Models:556 `hamiltonianVectorField_fixed`; HamiltonNodes:54 `fixedField_blocks`; :130 `hamilton_eqs_fixed`; :167 `fderiv_fixedHamiltonian_partials` | **CLOSABLE** | `LEAN_REF: KAM.Planetary.hamilton_eqs_fixed`, conjunct `.1`. It is `∀ z, NoCollision z.1 → ∀ i,` the conjunction of exactly the position and momentum block formulas. This preserves source order (point z, collision guard, components). `fixedField_blocks` is also a single direct componentwise reference. All real G,m0,m,ε and n are allowed, stronger than the positive/nonnegative source data. No directional-derivative output is taken as a premise. |
| `stepP:p6:rc-pack`; graph 11977; blueprint p6:155-177 | Reconstruction:233 `reconstruction`; :246 `reconstruction_all_time` | **NEEDS BUNDLE** | Arbitrary-J conclusion alone is CLOSABLE by `KAM.Planetary.reconstruction`; all-time conclusion alone is CLOSABLE by `KAM.Planetary.reconstruction_all_time`. The record explicitly asks for both. Neither one statement contains both named predicates. At J=univ, the interval predicate includes membership arguments and is not definitionally the all-time predicate; :246 explicitly repackages these conjuncts. Proposed bundle retains arbitrary J first and `J=univ →` the all-time clause second. μ=0 is already included by `0 ≤ μ`. |
| `stepP:p6:ot-apply`; graph 12175; blueprint p6:194-205 | Reconstruction:304 `orbit_transfer_moving`; :315 `orbit_transfer_fixed` | **NEEDS BUNDLE** | Moving alternative alone is CLOSABLE by `KAM.Planetary.orbit_transfer_moving`; fixed alternative alone by `KAM.Planetary.orbit_transfer_fixed`. The full node asks for (a) and (b); no one named declaration states both. Bundle the two implications, each under its own torus and NoCollision hypotheses, with `∀ φ` after those inputs. Requiring both torus hypotheses simultaneously would weaken the source and is not the proposed bundle. |

The rc-pack and ot-apply verdicts are deliberately for the complete recorded nodes. They are not failures of either existing reconstruction/transfer theorem. Splitting those graph records would be an orchestrator decision; this audit does not silently narrow them.

## Literal hypotheses, quantifiers, units and applicability

For pl-a/b the theorem parameters are arbitrary planar vectors and real c. For pl-c the sole analytic domain guard is `v ≠ 0`; h is an arbitrary direction after that guard. The dot/length formulas use the frozen Euclidean planar length, never the Pi norm. The latter appears only in pl-b, exactly as in the source.

For dom-open/smooth, n≥1, positive masses and G, and nonnegative couplings may all be omitted: these total-function regularity statements hold for all parameter values on W. No constants or existential choices gain wider dependence. For he-fix, both field blocks are asserted under NoCollision at the same z, with the source signs, factor G*m0*m_i, and ε*G*m_i. The block extraction is the frozen `bodyVector` via `finProdFinEquiv`, matching index 2i+c.

For rc-pack, `reconstruction` and `reconstruction_all_time` take G>0, m0>0, every m_i>0, μ≥0, then the curve/collision conditions; arbitrary J need not be open, connected, nonempty, or an interval. The hypothesized curve derivative is (R2), a source premise, not a dependency output. Source order of t∈J and the body indices is preserved inside the frozen predicates. The interval predicate has mass array `fun k => G * actualMasses m0 m μ k`; the all-time predicate instead receives G separately. No hidden positivity of the planet actual masses is imposed at μ=0.

For ot-apply, the supplied torus and the separate global NoCollision condition are both SOURCE_HYPOTHESES. NoCollision is not smuggled in as a reconstruction result. Each declaration fixes its relevant data and source hypotheses before arbitrary φ and its all-real-time orbit. The fixed theorem allows arbitrary G and ε and omits G>0/ε≥0; this strengthens the source. Using a conjunction of implications preserves the two alternatives without assuming the output of ot-curve.

For pc-c, the parameter conversion is exactly `periodOne κ θ = κ ((2*pi) • θ)`; the frequency is `(2*pi)⁻¹ • omega`, time is unchanged, and the flow derivative equivalence is pointwise in θ,v,t without analyticity assumptions. An arbitrary lattice shift family T is essential: `isLatticeTorus_periodOne_iff` only packages `fullShift`. The factor in the symplectic derivative expression is `(2*pi)*(2*pi)`, nonzero, giving the zero-pullback equivalence. The proposed wrapper also explicitly states that equivalence and (d).

## Exact one-line bundle statements

These are proposed exports, not landed references and not repository edits. Each code block contains one complete declaration signature, with namespace assumptions `open KAM KAM.Planetary KAM.Kepler Set Real Function` and `open scoped ContDiff`. `∞` is the smooth order; `⊤` in the current differentiability-order type denotes the stronger analytic order and is intentionally not substituted.

Six bundles (all except pc-c) were actually proved in disposable scratch using only the existing declarations. The pc-c signature was typechecked only; its proof still needs the local injectivity/Lagrangian arguments exported or repeated, together with the other existing conversion results and Chart:236. No scratch proof is being represented as a landed LEAN_REF.

`pc-c`:

```lean
theorem lref_pc_c {d a b : ℕ} (κ : (Fin d → ℝ) → Phase d) (omega : Fin d → ℝ) (T : (Fin d → ℤ) → Phase d) : (AnalyticOnNhd ℝ (periodOne κ) Set.univ ↔ AnalyticOnNhd ℝ κ Set.univ) ∧ (∀ θ, fderiv ℝ (periodOne κ) θ = (2 * Real.pi) • fderiv ℝ κ ((2 * Real.pi) • θ)) ∧ (∀ θ, Function.Injective (fderiv ℝ (periodOne κ) θ) ↔ Function.Injective (fderiv ℝ κ ((2 * Real.pi) • θ))) ∧ (∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v) = (2 * Real.pi) * (2 * Real.pi) * symplecticForm (fderiv ℝ κ ((2 * Real.pi) • θ) u) (fderiv ℝ κ ((2 * Real.pi) • θ) v)) ∧ ((∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v) = 0) ↔ ∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0) ∧ ((∀ θ (k : Fin d → ℤ), periodOne κ (θ + fun i => (k i : ℝ)) = periodOne κ θ + T k) ↔ ∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * Real.pi * (k i : ℝ)) = κ ϑ + T k) ∧ ((∀ θ θ', periodOne κ θ = periodOne κ θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ↔ ∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * Real.pi * (k i : ℝ)) ∧ (∀ θ (v : Phase d) (t : ℝ), HasDerivAt (fun s : ℝ => periodOne κ (θ + s • (2 * Real.pi)⁻¹ • omega)) v t ↔ HasDerivAt (fun s : ℝ => κ ((2 * Real.pi) • θ + s • omega)) v t) ∧ (∀ k : Fin a → ℤ, fastShift (b := b) k = angleScale (2 * Real.pi) (Fin.append (fun i => (k i : ℝ)) (0 : Fin b → ℝ), 0))
```

`pl-a`:

```lean
theorem lref_pl_a (v w : Fin 2 → ℝ) (c : ℝ) : 0 ≤ planeLength v ∧ planeLength v ^ 2 = planeSq v ∧ planeSq v = planeDot v v ∧ (planeLength v = 0 ↔ v = 0) ∧ planeLength (-v) = planeLength v ∧ planeLength (c • v) = |c| * planeLength v ∧ planeLength (v + w) ≤ planeLength v + planeLength w
```

`pl-b`:

```lean
theorem lref_pl_b (v : Fin 2 → ℝ) : ‖v‖ ≤ planeLength v ∧ planeLength v ≤ Real.sqrt 2 * ‖v‖
```

`pl-c`:

```lean
theorem lref_pl_c (v : Fin 2 → ℝ) (hv : v ≠ 0) (h : Fin 2 → ℝ) : ContDiffAt ℝ ∞ planeLength v ∧ ContDiffAt ℝ ∞ (fun x => (planeLength x)⁻¹) v ∧ fderiv ℝ planeLength v h = planeDot v h / planeLength v ∧ fderiv ℝ (fun x => (planeLength x)⁻¹) v h = -(planeDot v h) / planeLength v ^ 3
```

`dom-smooth`:

```lean
theorem lref_dom_smooth {n : ℕ} (G m0 : ℝ) (m : Fin n → ℝ) (μ ε : ℝ) : ContDiffOn ℝ ∞ (movingHamiltonian G m0 m μ) (collisionFreeDomain n) ∧ ContDiffOn ℝ ∞ (fixedHamiltonian G m0 m ε) (collisionFreeDomain n)
```

`rc-pack`:

```lean
theorem lref_rc_pack {n : ℕ} {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) (J : Set ℝ) (z : ℝ → Phase (n * 2)) (hz : ∀ t ∈ J, NoCollision (z t).1 ∧ HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) : IsNewtonSolutionOn (fun k => G * actualMasses m0 m μ k) J (fun t => barycentricPositions m0 m μ (z t).1) (fun t => barycentricVelocities m0 m μ (z t).2) ∧ (J = Set.univ → IsNewtonSolution G (actualMasses m0 m μ) (fun t => barycentricPositions m0 m μ (z t).1) (fun t => barycentricVelocities m0 m μ (z t).2))
```

`ot-apply`:

```lean
theorem lref_ot_apply {n : ℕ} {G m0 μ ε : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) (w : Fin (n * 2) → ℝ) (K : (Fin (n * 2) → ℝ) → Phase (n * 2)) : (IsPhysicalTorus (movingHamiltonian G m0 m μ) w K → (∀ φ, NoCollision (K φ).1) → ∀ φ, IsNewtonSolution G (actualMasses m0 m μ) (fun t => barycentricPositions m0 m μ (K (φ + t • w)).1) (fun t => barycentricVelocities m0 m μ (K (φ + t • w)).2)) ∧ (IsPhysicalTorus (fixedHamiltonian G m0 m ε) w K → (∀ φ, NoCollision (K φ).1) → ∀ φ, IsFixedSolution G m0 m ε (fun t i => bodyVector (K (φ + t • w)).1 i) (fun t i => (1 / m i) • bodyVector (K (φ + t • w)).2 i))
```

## Definition classification

There are no new branch definitions. The existing bodies used by these candidates were checked as follows.

| Definition(s) / location | Classification and whole-carrier behavior |
|---|---|
| Transport:44 `IsLatticeTorus`, :136 `IsTwoPiLatticeTorus` | Explicit six-clause predicates, with the analytic/range/differentiability data bundled in clause one. Parameter shifts are respectively integers and 2*pi integers. They do not define a fallback torus. Their field/range clauses explain why the packaged iff is narrower than all individual conversion identities. |
| Transport:132 `periodOne` | Literal linear precomposition for every κ and every θ, including nonanalytic κ. The unconditional fderiv identity handles nondifferentiability via Lean's standard total fderiv, with invertible precomposition proving both sides' nondifferentiability together; no junk-dependent proof. |
| Models:39 `collisionFreeDomain` | Exactly the preimage of frozen NoCollision under the phase position projection, on the whole phase space. |
| Models:42 `ofBodies` | Literal inverse coordinate reindexing by `finProdFinEquiv`; both inverse identities are proved at :44/:48 for the entire carrier. |
| Models:55 `keplerPart`, :57 `pairPotential`, :60 `fMov`, :62 `fFix` | Literal finite sums and split terms. Same direct pair potential, with moving total-momentum kinetic correction. Standard Lean total division at zero, no conditional branch. Physical uses are collision guarded and, for reconstruction, masses positive. Off-domain total values are explicitly irrelevant in blueprint p6:55. |
| Models:65 `gKernel`, :66 `fKernel` | Literal central and mutual-force formulas. `fKernel` excludes j=i and uses q_j-q_i. Total division is guarded by NoCollision where force laws are claimed. |
| Models private :72 `posCLM`, :79 `momCLM`, :90 `dotCLM`; HamiltonNodes private :251 `hnPos`, :258 `hnMom`, :269 `hnDot` | Coordinate projections and the finite dot-product continuous linear functional, defined correctly for all vectors. No bundled conclusions or hidden mathematical premise. |
| Models private :348 `modelH`, :471 `pairW` | Common literal split Hamiltonian and position-derivative pair kernel. Exact moving/fixed specialization identities precede their use; `pairW` is antisymmetric, with no special-case fallback. |
| Frozen `Phase`, `bodyVector`, `planeSq`, `planeLength`, `planeDot`, `NoCollision` | Fin-function phase product, canonical coordinate extraction, sum of squares, its real square root, finite dot product, and explicit positive Sun/planet distances. Length is Euclidean even though the ambient norm is Pi max. |
| Frozen moving/fixed Hamiltonians; actualMasses; barycentricPositions/Velocities | Exactly the two physical models and reconstruction maps in the source. Barycentric position denominator is m0+μ*Σm_i, positive under the reconstruction hypotheses including μ=0. Velocity division by m_i is guarded by positive base masses. |
| Frozen IsNewtonSolutionOn / IsNewtonSolution / IsFixedSolution / IsPhysicalTorus / fastShift | Explicit source clauses, with interval/all-time and G/mass placement as detailed above; physical torus has the genuine all-time flow clause. fastShift is the 2*pi fast-angle shift, not a period-one physical-angle shift. |

No new structures/abbrevs occur in these five modules. Plane and Reconstruction introduce no object definitions. All physical singular expressions rely only on the stated source guards; no invalid off-carrier value was used to obtain a conclusion.

## Independent validation

All audit-owned Lean/Lake invocations were serialized, inherited `LEAN_NUM_THREADS=1`, and ran under `nice -n 5`. No library-wide rebuild, clean, update, cache download, or package-directory change was performed. The build used the mandated gate. Tools elsewhere on this shared host were not started or controlled by this audit.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lrefaud KAM.Planetary.Hamiltonian.Transport KAM.Kepler.Plane KAM.Planetary.Newtonian.Models KAM.Planetary.Newtonian.HamiltonNodes KAM.Planetary.Newtonian.Reconstruction
```

Exit 0; terminal output `Build completed successfully (9105 jobs).` Gate: slot 2 acquired. Replayed unused-variable warnings only: Algebra:146 hc; Chart:193 hc; Diophantine:124 hγ; Transport:55 hc; Energy:106 hm and hκ. No heartbeat/design failure.

Kernel replay command (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Transport KAM.Kepler.Plane KAM.Planetary.Newtonian.Models KAM.Planetary.Newtonian.HamiltonNodes KAM.Planetary.Newtonian.Reconstruction
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.Newtonian.Reconstruction
replaying KAM.Planetary.Newtonian.HamiltonNodes
replaying KAM.Planetary.Newtonian.Models
replaying KAM.Kepler.Plane
replaying KAM.Planetary.Hamiltonian.Transport
```

Probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/lref-probe.lean
```

Final exit 0, zero errors. Imports were the five modules above. An explicit fresh `example` checked the dom-open signature, and another checked exactly `(hamilton_eqs_fixed G m0 m ε).1` at its full source block-form type. The probe also elaborated proofs of the six proposed bundles and ran `#check @name` / `#print axioms name` for all 80 public theorems in the five modules. Initial scratch-only wrapper drafts had algebraic-distribution, smoothness-API and notation errors, corrected before this successful run; they did not reveal a package proof failure or require resource overrides.

pc-c extended signature typecheck:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/lref-pc-type.lean
```

Exit 0, zero errors. The entire proposed signature, including the explicit Lagrangian iff and frozen shift conjunct, elaborated as a proposition. No proof of this wrapper was claimed.

Exact axiom output (every one of the 80 checked names):

```text
'KAM.Planetary.fderiv_chart_comp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torus_transport_cyl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torus_transport_phys' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_periodOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_periodOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.periodOne_lattice_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.periodOne_injMod_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.periodOne_hasDerivAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isLatticeTorus_periodOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cyl_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phys_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeSq_eq_planeDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_sub_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeSq_mul_planeSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.abs_planeDot_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.abs_planeLength_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.norm_le_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_le_sqrt_two_mul_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.eq_of_planeDot_planeCross_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeLength_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeDot_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeCross_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.rot_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.rot_two_pi_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.rot_quarterTurn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.rot_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.exists_rot_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.analyticAt_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.analyticAt_inv_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.analyticAt_inv_cube_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.hasFDerivAt_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.hasFDerivAt_inv_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.radius_eq_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.radiusSq_eq_planeSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bodyVector_ofBodies' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ofBodies_bodyVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerPart_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.movingHamiltonian_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedHamiltonian_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.moving_sub_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_mass_smul_fKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_collisionFreeDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_fMov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_fFix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_movingHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_fixedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableAt_movingHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableAt_fixedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonianVectorField_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonianVectorField_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_bodyVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.movingField_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_iff_bodyVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_movingField_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_fixedField_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamilton_eqs_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamilton_eqs_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_movingHamiltonian_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_fixedHamiltonian_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_coords_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_equations' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_rf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_movingHamiltonian_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_fixedHamiltonian_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sp_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.reconstruction_all_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isNewtonSolutionOn_of_isMovingSolutionOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.reconstruction_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.reconstruction_fixed_all_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.orbit_transfer_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.orbit_transfer_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every set is exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx or other axiom occurs. Provider/frozen seal type-equality and seal-body probes are not applicable: there is no LREF-P provider/anchor change. This audit does not import the physical headlines to obtain these helper results.

A recursive inspection of local KAM imports from the five modules found 59 KAM modules, zero provider modules, and zero frozen theorem-anchor modules. Thus no imported DRAFT_SORRY theorem or provider supplies these results. Frozen definition imports were inspected as definitions; there is no theorem-anchor manifest-state exemption to invoke.

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 0. Exact output:

```text
check_lean_modules: PASS (1218 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This checkout has no stale-generated-root exception: lint passed outright. That includes forbidden-token/resource-override checks, module headers/import layout, exposed definitions, ambient types, line lengths/file caps, generated-root/errata consistency, frozen guard, and 144 ABI hashes. Candidate line counts: Transport 373, Plane 308, Models 579, HamiltonNodes 544, Reconstruction 329; all below 1500.

Protected-path checks:

```sh
git diff inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

All exit 0 with empty output. No state-changing git command was used. Scratch probes/logs are removed after incorporating their evidence here. The sole audit-authored repository artifact is this exact report path, not a report in `/root/code/KAM-inp`.

## Blueprint/source defects, deviations and limits

No suspected mathematical defect in the inspected blueprint/frozen definitions was found. No pinned-source erratum is asserted: this task audits the literal local graph/blueprint contracts against landed Lean, not a fresh PDF transcription. Existing references to external papers were not independently re-audited.

The survey's suggested blanket `LEAN_REF + audit` classification (GAP-PLAN-P2.md:155,160-167) is too coarse under this handoff's explicit rule. For example, graph pl-b says “¦v¦_inf <= l(v) <= sqrt2 ¦v¦_inf”, while its two named Lean inequalities remain separate. The survey's “analytic ⇒ C^∞” observation is mathematically correct, but does not combine both models or both planar derivative results into one named declaration. Likewise its rc-pack and ot-apply lists cite multiple exports. These are reference-packaging deficiencies, not counterexamples to the source mathematics.

`isLatticeTorus_periodOne_iff` at Transport:252 has local `hinj` and `hsym`; quoting that iff as though it separately exported those propositions would overstate its type. Global equivalence of two conjunctions does not by itself give equivalence of each constituent. Its body proves the required constituents; a wrapper can reproduce them without assuming a lattice-torus conclusion.

No source, graph, frozen file, manifest, Lean module, README or generated root was edited. Proposed bundle statements in this report are reviewable recommendations only. No constant dependence, carrier, physical law, quantifier order, or consumer application was silently repaired. The remaining uncertainty is administrative: if the orchestrator elects to split multi-case graph records, the individual rc-pack/ot-apply cases can use the exact existing references listed above. Until then the seven full nodes remain NEEDS BUNDLE.
