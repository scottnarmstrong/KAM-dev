# Lean design for N Parts 8–9: resonance geometry and Pöschel Theorem 1

Design draft, 2026-10-28, branch `inp-design-n89`. No statements are approved or frozen by this document.
Scope: every graph node whose source is `blueprint-N/parts/p8-resonance-geometry.tex` or
`p9-poschel-theorem1.tex`, including the four additional claim nodes. The design closes no frozen
anchor. `thm1` is an internal theorem for Part 10, not a replacement for N-HEAD-C.

Snapshot: worktree base `081967912d5200ad4711d6d16abde6a8cfafea71`.
Source SHA-256: p8 `8c7b5239312aaa1bb68e282b36accc8731812c60e07b983c205059399ce23094`;
p9 `5306ce090f13d1bad7822ee8f0c8486418f75e3ff06273d76085b4903a908f92`;
graph `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2`;
upstream NPart67Signatures `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`.
Format reference: PART145 design (including Appendix A), with both design-audit reports; its
warnings about specialized carriers, empty-domain norm bounds, and actual module dependencies apply.

## 1. Decisions

1. Use `AddSubgroup (Fin n → ℤ)` for lattices. `lattice` is the existing
   `KAM.Stability.resSpan` applied to its underlying set; `resonance` is the existing
   `KAM.Stability.resSpace`. No new lattice structure or norm instance.
2. Euclidean length is exactly `KAM.Nekhoroshev.euclid`; the ambient function norm remains max norm.
   All projections use the dot product, and all geometric balls are explicitly `eBall`, not metric balls
   in the ambient max norm. Matrix entries live in `ℤ` for bases/change of basis and in `ℝ` for Gram matrices.
3. Take the canonical projector onto a subspace from its **unique** characterization, proved first in
   `projection_exists_unique`. Reuse `KAM.Stability.IsOrthProj` and `exists_orthProj`; expose
   range/fixed-point/uniqueness, matrix formula, distance attainment and nested projection laws together.
   Never install an inner-product structure on a bare function type.
4. `volume_def` is the square root of the Gram determinant of an integer basis, including rank zero:
   the empty determinant is 1. The basis choice is auxiliary and nonunique; the **value** is independent
   of it. Land `lattice_basis`, the basis-independent Gram identity in `lattice_volume`, positivity and
   `volume_def` as one semantic unit, after their proofs. A chosen arbitrary basis alone certifies no volume.
5. Part 8 is Hamiltonian-free in all its premises and accepts arbitrary maps from any action carrier.
   Positivity assumptions of `CoverParams.Valid` are exactly the Covering Lemma's assumptions. Keep
   weaker K-lattice maximality, not saturation. Neither unimodular saturation nor basis vectors of length
   ≤ K may be assumed. The latter is why the upper volume bound uses a short independent generating
   sublattice and volume monotonicity, rather than a purported short integer basis.
6. Keep the exact period-one Part 6/7 normalization: geometric cutoff `K`, analytic cutoff `K/√n`,
   `κ=2π(K/√n)s`, `p=9/8`, `q=9`, `b=1/8`. Reuse `HeadParams.expo n` for `1/(2n)`.
7. `Theorem1Setting` contains only the listed S1–S4 and positive standing parameters, including
   `m≤M` and `r0≤ell/(2M)`. Its alias `setting` follows the graph naming convention. The independent
   `m_le_M` lemma does **not** assume `m≤M`. No block conclusion or orbit containment enters the setting.
8. Maxima are actual attained maxima: `FrequencyBall` guards the center, nonnegative radius, and radius
   `<r0`; its `maximum` is the supremum on precisely that closed Euclidean ball. `frequency_maximum`
   proves compactness, attainment, the upper-bound property, and the Lipschitz bound. There is no
   fabricated maximizing point, fallback value, global frequency lower bound or compactness premise.
9. Infinite time is encoded by the exact multiplication inequalities in `blockAdm`, as in the upstream
   stability API. Full rank makes every time admissible. For intermediate rank and Ω=0, the inequality
   is automatic. Main `thm1` retains the joint two-branch statement and shared constants.
10. Signatures are quarantined design evidence: real bodies for definitions, only `sorry` for proofs,
    verbatim upstream definition excerpts to elaborate against the present shared build. Replace those
    excerpts by the owning imports on implementation; do not copy them into new production files.

## 2. Carriers, standing structures and conventions

| Source object | Exact Lean representation |
|---|---|
| integer lattice, Θ, full lattice | `Lattice n := AddSubgroup (Fin n → ℤ)`, `⊥`, `⊤` |
| WΛ, dimension | `lattice Λ := KAM.Stability.resSpan (Λ : Set _)`, `latticeDim Λ` |
| real inclusion of integer vector | `integerReal k` (coordinate integer casts) |
| RΛ and distance | `resonance Λ := KAM.Stability.resSpace (Λ : Set _)`; `resonanceDistance Λ w` with `projection_distance` proving minimum attainment |
| integer basis and Gram matrix | `Module.Basis (Fin d) ℤ Λ`, `basisMatrix`, `gram` |
| Π, Q | `proj V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)`, `compProj V v = v - proj V v` |
| geometric / analytic cutoff | `eBall n K`, existing `KAM.NormalForm.zBall n Ka` |
| maximal K-lattice | `maximalK K Λ`; generation is `klattice` via `AddSubgroup.closure` |
| zones and blocks | `zone lam Λ`, `zoneStratum K lam d`, `blocks K lam Λ` |
| λ1,…,λn | `lam : ℕ → ℝ`, only dimensions 1,…,n used; no λ0 dependence |
| covering data | `CoverParams n`, source-premise predicate `CoverParams.Valid` |
| DΛ | `actionBlock c P freqR Λ`, for any `P : Set ι` and `freqR : ι → (Fin n → ℝ)` |
| complex tube, real tube, W | existing `polyNbhd (KAM.Stability.cpx P) r`, `realNbhd P r`, `realStrip P r` |
| h,f and reality | total complex functions, existing `InClass`, `RealOn`, `HasFiniteWNorm`, `WBound` |
| frequency and real Hessian | frozen `KAM.frequencyMap h`, `KAM.Nekhoroshev.realPart h`; upstream `hessR` |
| real Hamiltonian | existing `KAM.Stability.realH (fun w => h w.2 + f w)` |
| S1–S4 | `Theorem1Setting P r0 s m M ell h f`; no hypotheses about the final orbit |
| Ω0 and ΩΛ | `(omega0Ball S I0 hI).maximum`, `(blockBall S heps heps0 Λ hΛ I0 hI).maximum` |
| arbitrary orbit | `J.OrdConnected`, `0∈J`, `∀t∈J, HasDerivAt z (F (z t)) t` |

Widths are positive geometric widths; Fourier weights remain `exp(2πs|k|₁)`. Phase space is
`(Fin n → ℝ) × (Fin n → ℝ)`, angles first. `F` agrees with the Hamiltonian field only on W;
**no containment of `z(J)` in W is assumed**. Both endpoints of the time interval use `HasDerivAt`.
`P` may be empty in the setting and pure parameter lemmas. `hI : (z 0).2∈P` supplies nonemptiness
where an orbit or maximum needs it. Part 8 theorem assumptions use n≥1; some algebraic helpers are
valid also for n=0. Part 9 uses n≥2, supplied downstream by frozen n≥3.

Every production file uses copyright, `module`, interface `public import`, module docstring and
`@[expose] public noncomputable section`. All definitions in Appendix A must unfold. Classical
choice is local to these noncomputable definitions; no global function/matrix instances are added.

## 3. Reuse and upstream interface (to reconcile)

The Part 6–7 declaration **types**, not approximate replacements, are authoritative in
`/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean`. Its explanatory design document was not
present at its referenced `PART67-LEAN-DESIGN.md` path during this run; the signatures were read directly.
All names below are exact. No unresolved invented upstream statement is used.

| Upstream node / exact export | Hypotheses supplied here → conclusion consumed | Owning import planned by upstream |
|---|---|---|
| p1 norm-compare: `KAM.Nekhoroshev.norm_le_euclid`, `modeSize_euclid_compare`, `lattice_ball_inclusions` | explicit vector, real cutoff → norm comparisons and cutoff inclusions | `KAM.Nekhoroshev.Interfaces.Norms` (present) |
| p1 constants data: `KAM.Nekhoroshev.HeadParams.expo` | dimension → exact exponent `1/(2n)` | `KAM.Nekhoroshev.Interfaces.Constants` (present) |
| p4 domains/norm: `KAM.Weighted.polyNbhd`, `Dom`, `InClass`, `WBound`, `HasFiniteWNorm`, `WBound.mono` | smaller tube and unchanged width → restricted class/bound | `KAM.Weighted.Domains`, `Norm` (present) |
| p5 reality: `KAM.Canonical.RealOn` | real inclusion in `Dom` → imaginary part zero | `KAM.Canonical.Setting` (present) |
| p6 setting: `KAM.NormalForm.zBall`, `freq`, `dotC`, `IsNonresonant`, `FreqLipschitz` | singleton real center and `cutoffs`, holomorphic-real frequency identity → exact analytic nonresonance | `KAM.NormalForm.Setting` (design) |
| p6 lipschitz: `KAM.NormalForm.lipschitz` | holomorphic h; bound `‖fderiv ℂ (freq h) I‖≤√n M` derived from S1 and symmetry → `FreqLipschitz (cpx {I0}) r (√n M) h` | `KAM.NormalForm.Setting` (design) |
| p7 setting: `KAM.Stability.cpx`, `realNbhd`, `realStrip`, `realH`, `hessR`, `freq_realInclusion`, `realHamiltonian_eq_realH` | S1 on local tube → complex frequency is frozen real frequency; Part 10 Hamiltonian bridge | `KAM.Stability.Setting` (design) |
| p7 gradient: `KAM.Stability.resSpan` | underlying lattice set → real span (reused literally) | `KAM.Stability.Gradient` (design) |
| p7 resonance data: `KAM.Stability.IsOrthProj`, `exists_orthProj`, `resSpace`, `IsCloseToRes`, `IsQuasiConvex` | subspace → projector existence; projection distance → closeness; S2 → exact quasi-convexity | `KAM.Stability.Energy` (design) |
| p7 nonresonant: `KAM.Stability.nonresonant` | `D={I0}`, `r=rΘ`, `K=Ka`, `α=αΘ`, `L=√n M`, `p=9/8`; S1/S4 and block_hyp → max drift≤rΘ/2 on contained orbits with `|t|5eps≤srΘ exp(κ/6)` | `KAM.Stability.Nonresonant` (design) |
| p7 resonant-prop2: `KAM.Stability.resonant_prop2` | `D={I0}`, subgroup Λ, `K=Ka`, `p=9/8`, `δ=δΛ`; all source binders discharged by block_hyp; maximum upper-bounds frequency ball → Euclidean drift≤rΛ/2, full rank all time | `KAM.Stability.ResonantStability` (design) |
| p7 stopped-extension: `KAM.Stability.stopped_extension` | just-derived contained-orbit estimate, `ϱ=rΛ/2<rΛ`, `IsActionNorm` for max/Euclidean, monotone `blockAdm`, local field identity → containment AND drift for arbitrary F-orbit | `KAM.Stability.Transfer` (design) |

`KAM.Stability.isActionNorm_norm` and `isActionNorm_euclid` supply the exact action norm predicates.
The stopped-extension theorem's `hconf` binder is an intermediate theorem **proved by applying**
nonresonant/resonant_prop2, not an assumption of block_stab or thm1. The singleton's initial membership
comes from equality with I0. Restrict the arbitrary interval only inside this upstream application.
For resonant_prop2 the eight numerical requirements are `1<p`, `p≤3/2`, positive r/s/Ka/α/m/ell/δ,
`m≤M`, `eps≥0`, eps-smallness, δ-smallness, and all three radius inequalities; none may be omitted.
Use its exact complex Hessian operator formula, which S1 and block_hyp intentionally match.

K's `KAM.holomorphic_regularity_of_finiteDimensional` and real scalar restriction underlie the new
`local_real_regularity`. Do not apply p1 `holo_real_b/c` on an arbitrary P: those exports have
`Data n R s eps h f` hypotheses on the frozen action ball, which are unavailable here. Their local
proof argument is reusable, not their specialized theorem. Use the actual frozen `frequencyMap` and
`realPart` bodies; do not assume a newly defined frequency equals them.

Mathlib source search found `Submodule.basisOfPid` (PID.lean:298),
`AddSubgroup.toIntSubmodule` (Module/Submodule/Lattice.lean:413), `Matrix.PosDef.conjTranspose_mul_self`,
`Matrix.PosDef.det_pos`, `Matrix.det_mul`, `Matrix.det_transpose`, `Matrix.det_fromBlocks₁₁`
(SchurComplement.lean:369), `Matrix.isUnit_iff_isUnit_det`, `Int.isUnit_iff`, `Module.Basis.invertibleToMatrix`,
`LinearIndependent.iff_fractionRing`, and `IsCompact.exists_isMaxOn`. These are proof ingredients,
not a receipt that the blueprint's whole external fact is already one imported theorem.
In particular integer-to-real independence needs the new `integer_independent_real` (nonzero rational
minor/field-extension argument). `KAM.Measure.Lattice` concerns integer-vector counting, not covolumes;
no matching resonance geometry module was found in KAM. Existing canonical/ODE/Fourier layers are
consumed through the exact Part 6/7 theorem applications, not rebuilt here.

## 4. Node → declaration and proof-location inventory

Every row is an actual graph node, not a freshly inferred graph. Prefixes are retained. All new exports
are in `KAM.Nekhoroshev`. A proof-step row names its enclosing declaration and its local proof obligation;
it does not add the step's conclusion as a hypothesis or claim a separate implemented public theorem.
External rows route to the precise existing ingredients or a named new helper above.
The following locators are copied from the graph's `STATEMENT_SOURCE` / `PROOF_SOURCE` fields.

| Node | Export / proof owner | Statement locator | Proof locator |
|---|---|---|---|
| `bpN:p8:ext-free` | `Submodule.basisOfPid; AddSubgroup.toIntSubmodule` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-free@L17-L17` | `-` |
| `bpN:p8:ext-gram` | `Matrix.PosDef.conjTranspose_mul_self, det_pos; Matrix.det_mul, det_transpose` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-gram@L18-L18` | `-` |
| `bpN:p8:ext-schur` | `Matrix.det_fromBlocks₁₁` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-schur@L19-L19` | `-` |
| `bpN:p8:ext-units` | `Matrix.isUnit_iff_isUnit_det; Int.isUnit_iff; basis coordinates and inverse` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-units@L20-L20` | `-` |
| `bpN:p8:ext-indep` | `integer_independent_real; LinearIndependent.iff_fractionRing + nonzero minors` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-indep@L21-L21` | `-` |
| `bpN:p8:ext-basic` | `dot-product Cauchy–Schwarz; finite maximal element; finite eBall via coordinate box; span basis extraction` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:ext-basic@L22-L22` | `-` |
| `bpN:p8:lattice` | `Lattice, lattice, latticeDim, resonance; lattice_resonance` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice@L28-L31` | `-` |
| `bpN:p8:lattice-basis` | `lattice_basis, lattice_basis_change, lattice_basis_sub` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L33-L41` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-basis@L42-L46` |
| `stepN:p8:lb-basis` | `lattice_basis / lattice_basis_change / lattice_basis_sub; local lb-basis` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-basis@L43-L43` |
| `stepN:p8:lb-unimod` | `lattice_basis / lattice_basis_change / lattice_basis_sub; local lb-unimod` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-unimod@L44-L44` |
| `stepN:p8:lb-sub` | `lattice_basis / lattice_basis_change / lattice_basis_sub; local lb-sub` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lb-sub@L45-L45` |
| `bpN:p8:volume-def` | `volume_def` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:volume-def@L48-L51` | `-` |
| `bpN:p8:projection` | `projection, projection_distance, projection_matrix, projection_zero` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L53-L63` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:projection@L64-L68` |
| `stepN:p8:pr-alg` | `projection / projection_distance; local pr-alg` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-alg@L65-L65` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-alg@L65-L65` |
| `stepN:p8:pr-dist` | `projection / projection_distance; local pr-dist` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-dist@L66-L66` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-dist@L66-L66` |
| `stepN:p8:pr-nest` | `projection / projection_distance; local pr-nest` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-nest@L67-L67` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:pr-nest@L67-L67` |
| `bpN:p8:lattice-volume` | `lattice_volume, lattice_volume_index, lattice_volume_cyclic, lattice_volume_hadamard` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L70-L81` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:lattice-volume@L82-L88` |
| `stepN:p8:lv-ab` | `lattice_volume / lattice_volume_index / lattice_volume_cyclic / lattice_volume_hadamard; local lv-ab` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-ab@L83-L83` |
| `stepN:p8:lv-c` | `lattice_volume / lattice_volume_index / lattice_volume_cyclic / lattice_volume_hadamard; local lv-c` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-c@L84-L84` |
| `stepN:p8:lv-d` | `lattice_volume / lattice_volume_index / lattice_volume_cyclic / lattice_volume_hadamard; local lv-d` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-d@L85-L85` |
| `stepN:p8:lv-e` | `lattice_volume / lattice_volume_index / lattice_volume_cyclic / lattice_volume_hadamard; local lv-e` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-e@L86-L86` |
| `stepN:p8:lv-f` | `lattice_volume / lattice_volume_index / lattice_volume_cyclic / lattice_volume_hadamard; local lv-f` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:lv-f@L87-L87` |
| `bpN:p8:klattice` | `klattice, maximalK` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:klattice@L96-L99` | `-` |
| `bpN:p8:maximal` | `maximal` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L101-L111` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:maximal@L112-L118` |
| `stepN:p8:mx-char` | `maximal; local mx-char` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-char@L113-L113` |
| `stepN:p8:mx-exist` | `maximal; local mx-exist` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-exist@L114-L114` |
| `stepN:p8:mx-c` | `maximal; local mx-c` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-c@L115-L115` |
| `stepN:p8:mx-d` | `maximal; local mx-d` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-d@L116-L116` |
| `stepN:p8:mx-e` | `maximal; local mx-e` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:mx-e@L117-L117` |
| `bpN:p8:blocks` | `zone, zoneStratum, blocks` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks@L120-L127` | `-` |
| `bpN:p8:blocks-cover` | `blocks_cover` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L129-L132` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:blocks-cover@L133-L136` |
| `stepN:p8:bc-finite` | `blocks_cover; local bc-finite` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-finite@L134-L134` |
| `stepN:p8:bc-top` | `blocks_cover; local bc-top` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:bc-top@L135-L135` |
| `bpN:p8:sqrt` | `sqrt` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:sqrt@L140-L143` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:sqrt@L144-L146` |
| `bpN:p8:geometric` | `geometric` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L148-L158` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geometric@L169-L180` |
| `bpN:p8:geom-formula` | `geom_formula` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L160-L164` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:geom-formula@L165-L167` |
| `stepN:p8:gl-theta` | `geometric; local gl-theta` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta@L170-L170` |
| `stepN:p8:gl-theta2` | `geometric; local gl-theta2` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-theta2@L171-L171` |
| `stepN:p8:gl-setup` | `geometric; local gl-setup` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-setup@L172-L172` |
| `stepN:p8:gl-vol` | `geometric; local gl-vol` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-vol@L173-L173` |
| `stepN:p8:gl-proj` | `geometric; local gl-proj` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L176` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-proj@L174-L176` |
| `stepN:p8:gl-div` | `geometric; local gl-div` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L177-L179` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:gl-div@L177-L179` |
| `bpN:p8:covering` | `CoverParams, actionBlock, covering` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L184-L195` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:covering@L196-L201` |
| `stepN:p8:cv-params` | `covering; local cv-params` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-params@L197-L197` |
| `stepN:p8:cv-cover` | `covering; local cv-cover` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-cover@L198-L198` |
| `stepN:p8:cv-nonres` | `covering; local cv-nonres` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-nonres@L199-L199` |
| `stepN:p8:cv-radii` | `covering; local cv-radii` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:cv-radii@L200-L200` |
| `bpN:p8:cutoffs` | `cutoffs` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L203-L211` | `blueprint-N/parts/p8-resonance-geometry.tex#bpN:p8:cutoffs@L212-L214` |
| `stepN:p8:co-incl` | `cutoffs; local co-incl` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213` | `blueprint-N/parts/p8-resonance-geometry.tex#stepN:p8:co-incl@L213-L213` |
| `bpN:p9:ext-num` | `Real.rpow_mul, Real.rpow_natCast; numerical inequalities in elementary/thm1` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:ext-num@L18-L18` | `-` |
| `bpN:p9:ext-compact` | `IsCompact.exists_isMaxOn (frequency_maximum)` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:ext-compact@L19-L19` | `-` |
| `bpN:p9:setting` | `setting, Theorem1Setting, thmA, thmEps0, thmK, omega0Ball` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:setting@L25-L39` | `-` |
| `bpN:p9:elementary` | `elementary` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:elementary@L41-L48` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:elementary@L49-L53` |
| `stepN:p9:el-a` | `elementary; local el-a` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-a@L50-L50` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-a@L50-L50` |
| `stepN:p9:el-b` | `elementary; local el-b` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-b@L51-L51` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-b@L51-L51` |
| `stepN:p9:el-c` | `elementary; local el-c` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-c@L52-L52` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:el-c@L52-L52` |
| `bpN:p9:omega0` | `omega0, frequency_maximum` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:omega0@L62-L64` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:omega0@L65-L68` |
| `stepN:p9:om-incl` | `omega0 / frequency_maximum; local om-incl` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-incl@L66-L66` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-incl@L66-L66` |
| `stepN:p9:om-max` | `omega0 / frequency_maximum; local om-max` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-max@L67-L67` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-max@L67-L67` |
| `bpN:p9:block-hyp` | `block_hyp` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-hyp@L74-L85` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-hyp@L86-L93` |
| `stepN:p9:bh-dom` | `block_hyp; local bh-dom` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-dom@L87-L87` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-dom@L87-L87` |
| `stepN:p9:bh-eps` | `block_hyp; local bh-eps` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-eps@L88-L88` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-eps@L88-L88` |
| `stepN:p9:bh-rad` | `block_hyp; local bh-rad` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-rad@L89-L89` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-rad@L89-L89` |
| `stepN:p9:bh-nr` | `block_hyp; local bh-nr` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-nr@L90-L90` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-nr@L90-L90` |
| `stepN:p9:bh-lip` | `block_hyp; local bh-lip` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-lip@L91-L91` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-lip@L91-L91` |
| `stepN:p9:bh-small` | `block_hyp; local bh-small` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-small@L92-L92` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bh-small@L92-L92` |
| `bpN:p9:block-stab` | `block_stab, blockAdm` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab@L95-L101` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab@L102-L107` |
| `stepN:p9:bs-theta` | `block_stab; local bs-theta` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-theta@L104-L104` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-theta@L104-L104` |
| `stepN:p9:bs-res` | `block_stab; local bs-res` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-res@L105-L105` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-res@L105-L105` |
| `stepN:p9:bs-stop` | `block_stab; local bs-stop` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-stop@L106-L106` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:bs-stop@L106-L106` |
| `bpN:p9:thm1` | `thm1` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:thm1@L111-L123` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:thm1@L124-L136` |
| `stepN:p9:t1-par` | `thm1; local t1-par` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-par@L125-L125` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-par@L125-L125` |
| `stepN:p9:t1-b` | `thm1; local t1-b` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-b@L126-L126` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-b@L126-L126` |
| `stepN:p9:t1-a-choice` | `thm1; local t1-a-choice` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-choice@L127-L127` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-choice@L127-L127` |
| `stepN:p9:t1-a-theta` | `thm1; local t1-a-theta` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-theta@L128-L130` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-theta@L128-L130` |
| `stepN:p9:t1-a-res` | `thm1; local t1-a-res` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-res@L131-L134` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-res@L131-L134` |
| `stepN:p9:t1-a-concl` | `thm1; local t1-a-concl` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-concl@L135-L135` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-a-concl@L135-L135` |
| `bpN:p9:s-blocks#data` | `theoremCover` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:s-blocks@L72-L72` | `-` |
| `stepN:p9:t1-b#full-rank-zone` | `full_rank_zone` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-b#full-rank-zone@L126-L126` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:t1-b#full-rank-zone@L126-L126` |
| `stepN:p9:om-max#local-real-regularity` | `local_real_regularity` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-max#local-real-regularity@L67-L67` | `blueprint-N/parts/p9-poschel-theorem1.tex#stepN:p9:om-max#local-real-regularity@L67-L67` |
| `bpN:p9:block-stab#local-field` | `local_field` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab#local-field@L103-L103` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab#local-field@L103-L103` |
| `bpN:p9:block-stab#frequency-size` | `frequency_maximum, blockBall, block_frequency_radius` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab#frequency-size@L96-L96` | `blueprint-N/parts/p9-poschel-theorem1.tex#bpN:p9:block-stab#frequency-size@L96-L96` |

Coverage: **82 graph nodes**. Also sign the off-graph blueprint lemma `bpN:p9:m-le-M`
(p9:55–60, proof step `stepN:p9:mm-vec`) as `m_le_M`; its proof does not use the setting’s `hmM` field.

The local obligations are literal proof goals of the enclosing declarations. `gl-vol` establishes
`Vplus≤V‖Qk‖` and `Vplus≤KV` using equal-rank lattice volume monotonicity; `gl-proj` uses the
projection Pythagoras identity before taking square roots. `cv-radii` uses both `1≤volume` and
`volume≤K^d`. `om-max` first uses `local_real_regularity`, compactness and convexity, then the
Euclidean mean value inequality; no maximum is postulated. `bs-stop` uses the already obtained
contained-orbit estimate. `t1-a-theta` and `t1-a-res` prove the numerical lower bounds on block time
before `t1-a-concl` changes the admissible-time predicate. Their source equations remain required
local subgoals, even though no additional public helper theorem is mandated.

## 5. Departures and source issues

| Departure | Reason and exact effect |
|---|---|
| Natural-dimensional λ indexing | Only 1≤d≤n is consumed; Θ zone is univ by definition, not a fictitious λ0 zone. `zoneStratum` explicitly excludes 0 and n+1. |
| Gram determinant at d=0 | Empty determinant 1 gives exactly the declared volume of Θ; avoids an unnecessary exceptional definition. |
| Canonical projector by uniqueness | Same orthogonal projector as `AG⁻¹Aᵀ`; the matrix formula is an explicit theorem, not an equality assumed in a structure. |
| `FrequencyBall.maximum` as guarded sSup | Exact maximum value with explicit attainment theorem; valid also for radius 0 and frequency 0. No arbitrary Ω is substituted for the maximum in `thm1`. |
| Source zero-extension Hamiltonian vs total `realH` | `local_field` proves equality of the two fields on each open tube by local equality of Hamiltonians. Outside W the extension F is arbitrary in the statement. |
| `P≠∅` omitted from `thm1` | Strictly stronger and valid: initial membership already supplies a point of P. No other source premise is dropped there. |
| `m_le_M` uses `0≤ell` | Strictly stronger than positive ell; the transverse vector has dot product 0, so nonnegative ell suffices. Other premises remain explicit. |
| Part 8 linear algebra valid at n=0 in some helpers | Strictly stronger harmless algebraic statements; geometric/covering theorems keep n≥1. |
| Public conjunctive declarations with local proof steps | Keeps shared witnesses/constants and the two branches together; internal lemmas may be introduced with distinct names but may not replace the source result. |

Issues inherited from the blueprint must be recorded in prover handoffs. These are source/blueprint
observations, not fresh independent PDF-verification claims. No source PDF was changed or fetched.

- **P8-1, maximality ambiguity.** p8:96–99 and 220 / Pos93 p.200 quotes “not properly contained in any
  other lattice of the same dimension.” This could mean arbitrary subgroup or K-lattice. Blueprint
  explicitly adopts the weaker K-lattice maximality. Preserve it and its characterization; do not
  quietly strengthen to saturated lattices.
- **P8-2, missing source arguments.** p8 errata:221–223 / Pos93 p.202: “the maximal K-lattice Λ+
  generated by Λ and k together has dimension d+1≤n”, and its volume “is not bigger than” the old
  volume times the orthogonal component length. Generation followed by maximal extension needs
  two operations, and the volume comparison needs equal-rank monotonicity. `maximal` and
  `lattice_volume` supply those proofs. Source uniqueness of a rank-one lattice is unnecessary.
- **P8-3, cutoffs.** p8:13–15 records the historical claim `Ka≥√n Kg`; it has the wrong direction for
  the caller. Required: `Kg≥√n Ka`; Part 9 takes equality. The inequality on the analytic ball alone
  needs only `Ka≤Kg`; the stronger factor comes from the analytic radius condition.
- **P8-4, zero-rank closeness wording.** p8:207 says in cutoffs(b) “Also dist₂(ω(I),RΛ)<δΛ” without
  repeating the nontrivial-rank qualifier. This is true for Θ because RΘ is all space and auxiliary
  δΘ>0, but it is **not** a zone-radius identity for Θ. `covering` reserves the zone identity for
  positive rank; `block_hyp` obtains trivial closeness directly, never from λ0.
- **P9-1, strengthened radius.** p9 errata:146 / Pos93 p.190 and p.204 print `r0≤4l/m` and “The
  stability estimates now apply to all blocks simultaneously, if we have r0≤4l/m”. This does not
  provide `Mr0≤ell/2` on the full-rank block. Use the blueprint's disclosed `r0≤ell/(2M)` and report
  it as a strengthened source premise/proof-gap repair, not a numerical misprint.
- **P9-2, norm adaptation.** p9:147 / Pos93 p.202 “it suffices to assume ‖k‖≤K” does not allow the
  max-norm frequency Lipschitz estimate with the same analytic cutoff. Blueprint time exponent is
  `πsK/(3√n)`. This is a declared norm adaptation, not a Pos93 misprint. Never remove √n.
- **P9-3, exceptional boundary.** p9:149 / Pos93 p.191 prints “except when ‖ω(I0)‖≤mr0/8” and
  radius r0. Blueprint proves strict `<` and radius r0/2. Equality belongs to the nonexceptional
  branch. Keep both branches and their norm distinction.
- **P9-4, constants are not errata.** p9:148,150–151: `A=11M/m≥9M/m+√2`, `2^10/288>3` and
  `2^10/(5·8)=25.6>1` are valid. The proof uses `m≤M`, `n≥2`, `K≥1`, `volume≤K^d` and
  ΩΛ≤Ω0. Do not alter ε0, A, a, R0 or T0.
- **P9-5, stale consumers/dictionary.** p8:230 says Part 9 will check with `M=n M_C`; Part 9 is
  generic in M and its actual Part 1 caller uses Bc. Read this as an example, not an added premise.
  p9:156–160 mixes the equivalent scaled source dictionary and the period-one application: `thm1`
  is period-one and should be applied directly to h,f at width s/2. Upstream Part 1 constants use
  paired `2π` factors (`F` and `epsStar`) that cancel; do **not** feed a `tildef` of period `2π`
  to a period-one `InClass`, and do not divide the exponent by √n twice. Part 10 owns the assembly.

## 6. Exact module DAG and prover packages

All new modules are under `KAM/Nekhoroshev/`. Paths below are exact proposed production files, not
files created by this design. Each row is one prover package of 150–800 lines. File estimates are
strictly below 1500; split earlier if required. A facade has only public imports and module headers.
No package writes the same module as another concurrent package.

| Package | Exact module paths (prefix `KAM/Nekhoroshev/`) | Lines | Inputs / outputs | Wave |
|---|---|---:|---|---:|
| N89-G1 | `ResonanceGeometry/Lattice.lean` | 500 | upstream `resSpan`, `resSpace`, Mathlib PID; lattice/rank/bases and `integer_independent_real` | 1 |
| N89-G2 | `ResonanceGeometry/Projection.lean` | 600 | upstream `IsOrthProj`, `exists_orthProj`, `Norms`; unique `proj`, characterization, zero/nested/distance/matrix laws; G1 only for lattice-specialized formulas | 2 |
| N89-G3 | `ResonanceGeometry/Volume.lean` | 650 | G1, G2, Gram/Schur; `volume_def`, full `lattice_volume` and index/cyclic/Hadamard companions | 3 |
| N89-G4 | `ResonanceGeometry/Maximal.lean` | 500 | G3; `klattice`, `maximalK`, finiteness, all maximal parts and short independent generating sublattice | 4 |
| N89-G5 | `ResonanceGeometry/Blocks.lean` | 300 | G4; zones, strata, blocks and finite `blocks_cover` | 5 |
| N89-G6 | `ResonanceGeometry/Geometric.lean` | 650 | G5, G2/G3; `sqrt`, `geom_formula`, `geometric` with rank-one and higher-rank cases | 6 |
| N89-G7 | `ResonanceGeometry/Covering.lean` | 400 | G6 + exact `zBall` and norm comparisons; `CoverParams`, all `covering`, `cutoffs` | 7 |
| N89-P1 | `Poschel/Setting.lean`, `Poschel/Elementary.lean` | 450 total (200+250) | upstream Part 7 setting/energy predicates, `HeadParams.expo`; `setting`, constants, `elementary`; Setting does not import G7 | 1 |
| N89-P2 | `Poschel/Frequency.lean` | 450 | P1 Setting, holomorphic regularity, scalar restriction, compact maximum; local regularity, `m_le_M`, all maximum definitions/theorems; no `blockBall` here | 2 |
| N89-P3 | `Poschel/BlockHypotheses.lean` | 500 | G7, P1 Elementary, P2, `freq_realInclusion`, `lipschitz`; `block_hyp`, `full_rank_zone`, block radius guards, `blockBall`, `local_field`, `blockAdm` | 8 |
| N89-P4 | `Poschel/BlockStability.lean` | 350 | P3, exact `nonresonant`, `resonant_prop2`, `stopped_extension`; `block_stab` | 9 |
| N89-P5 | `Poschel/Theorem1.lean` | 400 | P4, G7, P2, Elementary; full joint `thm1` and time comparisons | 10 |

DAG (arrow means imports):

```text
Lattice → Stability.Gradient, Stability.Energy, Interfaces.Norms, Mathlib PID
Projection → Lattice, Stability.Energy, matrix Gram facts
Volume → Projection, Lattice, matrix Schur facts
Maximal → Volume
Blocks → Maximal
Geometric → Blocks, Projection, Volume
Covering → Geometric, NormalForm.Setting, Interfaces.Norms
Poschel.Setting → Stability.Setting, Stability.Energy, Weighted.Norm, Interfaces.Constants
Poschel.Elementary → Poschel.Setting
Poschel.Frequency → Poschel.Setting, Interfaces.Norms, Strip.Bridges, compactness
Poschel.BlockHypotheses → Covering, Poschel.Elementary, Poschel.Frequency, NormalForm.Setting
Poschel.BlockStability → Poschel.BlockHypotheses, Stability.Nonresonant,
                         Stability.ResonantStability, Stability.Transfer
Poschel.Theorem1 → Poschel.BlockStability
```

The upstream Part 7 projection-existence proof must remain independent of these Part 8 modules:
prove it by finite-dimensional dot-product linear algebra as its design specifies, not by importing
`ResonanceGeometry.Projection`. Otherwise the import graph would cycle. The same restriction applies
to the upstream `resSpan` and `resSpace` definitions. All required names in Appendix A's upstream
excerpts stay in their existing namespaces. The new N-facing modules export them by imports.
Part P may import the pure geometry modules without instantiating any Hamiltonian.

G1 proof plan: convert the subgroup with `toIntSubmodule`; use `basisOfPid (Pi.basisFun ℤ (Fin n))`;
prove real independence by minors or scalar extension; identify real span rank and reindex with Fin.
G2: strengthen the upstream existence to uniqueness by orthogonal decomposition; the difference
of two candidate images lies both in V and its dot-orthogonal space. Derive matrix formula with
Gram invertibility, including empty matrices. G3: determinant under unimodular basis changes,
integer positivity, then Schur complement for adding a vector and induction for Hadamard. G4:
finite generating subsets of the finite integer coordinate box; maximal element at fixed rank.
G5: largest occupied positive dimension, with Θ as the empty-strata case. G6: follow the five
explicit projection/divisor steps; keep positive denominators and square roots separate so the
algebra remains small. G7: specialize λd, use volume bounds in both directions and pull back blocks.

P1: unfold one numeric definition at a time; use `Real.rpow_mul` with positive base, no coercion
shortcuts or resource-budget changes. P2: prove local C²/continuity from holomorphy and reality on
the open tube; compactness of the closed Euclidean ball follows from max-norm closedness and
boundedness using `norm_le_euclid`. Obtain Lipschitz `M` in the **Euclidean** norm by integrating
the Hessian along the segment; using ambient max-norm operator norm here would lose a factor.
P3: restrict hypotheses to the singleton tube, then instantiate G7/cutoffs. Convert complex/real
frequencies explicitly. Use Hessian symmetry to turn S1 into the derivative bound on `freq`; max
input to Euclidean input costs √n once, giving `L=√n M`. Prove equality of the two real fields by
open-neighborhood equality, never by global equality of zero extensions.
P4: split Θ and nontrivial Λ, prove the upstream `hconf`, then apply stopped_extension with max
and Euclidean action norms respectively. Full rank uses the explicit disjunct of resonant_prop2;
Ω=0 uses multiplication form. P5: exceptional initial action belongs to full-rank block; the
nonexceptional case chooses a different block. For Θ use `(AK)^n≥A²` (n≥2) and `mr0≤8Ω0`.
For intermediate rank use `mrΛ²/eps≥2^10 A^(2d)≥2^10 A²` and ΩΛ≤Ω0; the latter comes from
ball inclusion `rΛ/2≤r0/(2AK)≤R0`, not from an assumed maximum comparison. Derive the common
time bound and then apply block_stab. No extra owner ruling or new premise is needed.

## 7. Provider and consumer assembly

No provider is written or sealed in this scope. Nothing here imports `KAM/Provider` or a frozen
theorem anchor. The signatures import frozen **definitions** only. Part 10 consumes the joint
`thm1` with these arguments: P is the real central action set, r0 is the Part 1 minimum,
s is half its original strip width, `m=p.mu`, `M=p.B`, `ell=p.ell`, h and f are the original
period-one Hamiltonian components. `const_tubes`, `const_hyp` (after canceling paired `2π`
factors), `const_perturbation`, `const_size`, `const_exceptional`, `const_time` and
`const_conclusion` discharge the source premises and rescale the conclusion. Do not introduce a
frequency-size hypothesis beyond the frozen headline's supplied hypotheses.

Choose the size bound `epsP = coth(πs_original/4)^n * eps`, so
`eps0P = p.epsStar/(2π)` and `epsP/eps0P = p.F*eps/p.epsStar`. Then
`thmA p.mu p.B = p.A`, `HeadParams.expo n` is unchanged, and the returned radius is
`(p.r0/p.A)/2 * (p.F*eps/p.epsStar)^a ≤ p.C*eps^a`. The exponent is
`πs_original/(6√n)*(p.epsStar/(p.F*eps))^a = p.c*eps^(-a)`.
The frequency maximum is that of the original h; scaled source time `A²πs_original/Ω_tilde`
is exactly `A²(s_original/2)/Ω_original`. This dictionary is needed to use Part 1's exact existing
signatures and prevents the period mismatch described above. Part 10 owns its separate exact
frozen-provider binder audit and existence/uniqueness/continuation assembly.

## 8. Risks and validation gates

- The integer/rational/real independence proof and equal-rank sublattice index calculation are real
  algebraic work, not paid external black boxes. Use determinant/minor witnesses and split helpers.
- Unique projection choice and basis-independent volume must land only after their characterizations
  are proved. Appendix A's `sorry` elaboration supplies no evidence of those proofs.
- The current Part 6–7 file is a design under audit. Any changed signature requires rechecking the
  singleton nonresonant, resonant and stopped-extension applications before dispatching P3–P5.
- All time comparisons must use actual attained maxima on the exact balls. Full rank, zero frequency,
  empty P, n=1 in pure geometry, d=0, and equality at the exceptional threshold require separate handling.
- Large conjunctions in `maximal`, `covering`, `block_hyp` and `thm1` are public joint contracts.
  Implement their proof through small lemmas; do not raise default resource limits.
- Source/PDF errata above are inherited from pinned blueprint text. No new numerical source misprint
  is asserted. The period dictionary is an implementation-sensitive interface issue for Part 10.

Validation receipts follow after the hard rules. They certify design syntax, coverage and repository
hygiene only. Every theorem body in Appendix A is `sorry`; no theorem or frozen root is proved.

## 9. Binding rules for every prover brief

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


The design-check gate overrides direct build commands for this design-only task. Production briefs
retain the repository build rule. Never edit frozen files, the manifest, generated README or root imports.

## 10. Validation receipts

- Final signatures: `/root/code/KAM-inp/.drafts/design/N89Signatures.lean`, 514 lines,
  SHA-256 `ad4f6dff495383a78c6f46031a3c8db43eba559e16298cea1dbb8f5a0acc9f5e`.
  Byte-identical to `.drafts/scratch/N89Signatures.lean` and Appendix A.
- Exact targeted check:
  `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n89 .drafts/scratch/N89Signatures.lean`.
  Exit **0**, **33** diagnostics, all “declaration uses 'sorry'” warnings; no other diagnostics.
  Log `.drafts/scratch/N89-elaboration.log`. No budget overrides or direct Lean/build invocation.
- A separate copy `.drafts/scratch/N89Axioms.lean` was checked through the same gate, exit **0**.
  `#print axioms` for `geometric`, `covering`, `block_hyp`, `block_stab`, `thm1` each reports
  **`[propext, sorryAx, choice, Quot.sound]`**. Log `.drafts/scratch/N89-axioms.log`.
  This is expected draft dependence, not proof closure or a standard-axioms certification.
- Mechanical inventory check: **82/82** graph nodes, exactly one row each; 15 upstream definition
  excerpts byte-identical to NPart67Signatures; 33 theorem bodies, each exactly `:= sorry`;
  514 lines (<1500), no forbidden commands or global instances.
- Repository lint: `PATH="/root/code/KAM-inp-design-n89/.drafts/scratch/gated-bin:$PATH" scripts/lint_sources.sh`,
  exit **0**. The local PATH adapter routes the linter's internal ABI Lean command through the
  required `inp_sig_check.sh` gate, restores the original PATH there, and serializes it after the
  signature/axiom checks; no repository script was edited. Output:
  `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`,
  `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`.
  Log `.drafts/scratch/N89-lint.log`.
- `git -C /root/code/KAM-inp-design-n89 diff --check`: exit **0**. Commit owns only this Markdown
  file. Frozen files, manifest, generated files, source blueprints and graph remain unedited.

## Appendix A. Exact signatures

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Nekhoroshev.Interfaces.Constants
public import KAM.Weighted.Norm
public import KAM.Canonical.Setting
public import KAM.ODE.Basic
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # N Parts 8–9 signatures: design only; no proofs.
Upstream excerpts below are verbatim definitions from NPart67Signatures.lean.
Replace excerpts with imports of their owning modules on implementation.
-/
@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.NormalForm
open KAM.Weighted
variable {n : ℕ}
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}

def freq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)

def dotC (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i

def IsNonresonant (D : Set (Fin n → ℂ)) (K α : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I ∈ D, ∀ k ∈ zBall n K \ Λ, α ≤ ‖dotC k (freq h I)‖

def FreqLipschitz (D : Set (Fin n → ℂ)) (r L : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ I ∈ polyNbhd D r, ‖I - I₀‖ < r → ‖freq h I - freq h I₀‖ ≤ L * ‖I - I₀‖

end KAM.NormalForm

namespace KAM.Stability
open KAM.Weighted KAM.Canonical KAM.NormalForm
variable {n : ℕ}
def cpx (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D

def realNbhd (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set (Fin n → ℝ) := {I | ∃ J ∈ D, ‖I - J‖ < ϱ}

def realStrip (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  univ ×ˢ realNbhd D ϱ

def realH (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (G (KAM.realInclusion₂ n x)).re

def hessR (hR : (Fin n → ℝ) → ℝ) (I ξ η : Fin n → ℝ) : ℝ := fderiv ℝ (fderiv ℝ hR) I ξ η

def resSpan (Λ : Set (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun k i => (k i : ℝ)) '' Λ)

structure IsOrthProj (P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Prop where
  idem : ∀ v, P (P v) = P v
  symm : ∀ u v, P u ⬝ᵥ v = u ⬝ᵥ P v

def resSpace (Λ : Set (Fin n → ℤ)) : Set (Fin n → ℝ) := {w | ∀ k ∈ Λ, ∑ i, (k i : ℝ) * w i = 0}

def IsCloseToRes (D : Set (Fin n → ℝ)) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (δ : ℝ) : Prop :=
  ∀ I ∈ D, ∃ w ∈ resSpace Λ, KAM.Nekhoroshev.euclid (KAM.frequencyMap h I - w) ≤ δ

def IsQuasiConvex (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (ℓ m : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ, ℓ * KAM.Nekhoroshev.euclid ξ < |KAM.frequencyMap h I ⬝ᵥ ξ| ∨
    m * KAM.Nekhoroshev.euclid ξ ^ 2 ≤ hessR (KAM.Nekhoroshev.realPart h) I ξ ξ

end KAM.Stability

namespace KAM.Nekhoroshev
open KAM.Weighted KAM.Canonical KAM.Stability
variable {n : ℕ}

/-! ## Part 8: lattice geometry -/
abbrev Lattice (n : ℕ) := AddSubgroup (Fin n → ℤ)
def lattice (Λ : Lattice n) : Submodule ℝ (Fin n → ℝ) := resSpan (Λ : Set _)
def latticeDim (Λ : Lattice n) : ℕ := Module.finrank ℝ (lattice Λ)
def integerReal (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)
def eBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | euclid (integerReal k) ≤ K}
def resonance (Λ : Lattice n) : Set (Fin n → ℝ) := resSpace (Λ : Set _)
def basisMatrix {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    Matrix (Fin n) (Fin d) ℤ := fun i j => (b j).val i

theorem lattice_basis (Λ : Lattice n) :
    latticeDim Λ ≤ n ∧ Nonempty (Basis (Fin (latticeDim Λ)) ℤ Λ) ∧
    Module.finrank ℤ Λ = latticeDim Λ ∧
    ∀ d : ℕ, ∀ b : Basis (Fin d) ℤ Λ,
      LinearIndependent ℝ (fun j => integerReal (b j).val) ∧ d = latticeDim Λ := sorry

/-- Field-extension step of ext-indep; not supplied merely by a rank API name. -/
theorem integer_independent_real {d : ℕ} (v : Fin d → (Fin n → ℤ))
    (hv : LinearIndependent ℤ v) : LinearIndependent ℝ (fun j => integerReal (v j)) := sorry

theorem lattice_resonance (Λ : Lattice n) :
    resonance Λ = {w | ∀ v ∈ lattice Λ, v ⬝ᵥ w = 0} ∧
    (latticeDim Λ = 0 ↔ Λ = ⊥) := sorry

def latticeBasis (Λ : Lattice n) : Basis (Fin (latticeDim Λ)) ℤ Λ :=
  Classical.choice (lattice_basis Λ).2.1

theorem lattice_basis_change {d : ℕ} {Λ : Lattice n}
    (b c : Basis (Fin d) ℤ Λ) :
    (∃ U : Matrix (Fin d) (Fin d) ℤ,
      basisMatrix c = basisMatrix b * U ∧ (U.det = 1 ∨ U.det = -1)) ∧
    (∀ U : Matrix (Fin d) (Fin d) ℤ, U.det = 1 ∨ U.det = -1 →
      ∃ c' : Basis (Fin d) ℤ Λ, basisMatrix c' = basisMatrix b * U) := sorry

theorem lattice_basis_sub {d : ℕ} {Γ Λ : Lattice n} (hΓ : Γ ≤ Λ)
    (b : Basis (Fin d) ℤ Λ) (c : Basis (Fin d) ℤ Γ) :
    ∃ N : Matrix (Fin d) (Fin d) ℤ,
      basisMatrix c = basisMatrix b * N ∧ N.det ≠ 0 := sorry

def gram {d : ℕ} (A : Matrix (Fin n) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  (A.map (Int.castRingHom ℝ)).transpose * A.map (Int.castRingHom ℝ)

def volume_def (Λ : Lattice n) : ℝ :=
  Real.sqrt (gram (basisMatrix (latticeBasis Λ))).det

/-- Well-defined canonical projection: unique orthogonal projector with prescribed range. -/
theorem projection_exists_unique (V : Submodule ℝ (Fin n → ℝ)) :
    ∃! P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      IsOrthProj P ∧ (∀ v, P v ∈ V) ∧ (∀ v ∈ V, P v = v) := sorry

def proj (V : Submodule ℝ (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Classical.choose (ExistsUnique.exists (projection_exists_unique V))

def compProj (V : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) : Fin n → ℝ := v - proj V v

theorem projection (V : Submodule ℝ (Fin n → ℝ)) :
    IsOrthProj (proj V) ∧
    (∀ v, proj V v ∈ V) ∧ (∀ v ∈ V, proj V v = v) ∧
    (∀ v w, w ∈ V → compProj V v ⬝ᵥ w = 0) ∧
    (∀ v, euclid v ^ 2 = euclid (proj V v) ^ 2 + euclid (compProj V v) ^ 2) ∧
    (∀ v, euclid (proj V v) ≤ euclid v ∧ euclid (compProj V v) ≤ euclid v) ∧
    (∀ v w, w ∈ V → (∀ u ∈ V, (v - w) ⬝ᵥ u = 0) → w = proj V v) ∧
    (∀ V' : Submodule ℝ (Fin n → ℝ), V ≤ V' → ∀ v,
      proj V' (proj V v) = proj V v ∧ proj V (proj V' v) = proj V v) := sorry

theorem projection_zero : proj (⊥ : Submodule ℝ (Fin n → ℝ)) = 0 := sorry

def resonanceDistance (Λ : Lattice n) (w : Fin n → ℝ) : ℝ :=
  euclid (proj (lattice Λ) w)

theorem projection_distance (Λ : Lattice n) (w : Fin n → ℝ) :
    compProj (lattice Λ) w ∈ resonance Λ ∧
    euclid (w - compProj (lattice Λ) w) = resonanceDistance Λ w ∧
    (∀ u ∈ resonance Λ, resonanceDistance Λ w ≤ euclid (w - u)) ∧
    Module.finrank ℝ (lattice Λ) +
      Module.finrank ℝ (LinearMap.ker (proj (lattice Λ))) = n := sorry

theorem projection_matrix {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    let A := (basisMatrix b).map (Int.castRingHom ℝ)
    ∀ v, proj (lattice Λ) v = (A * (A.transpose * A)⁻¹ * A.transpose).mulVec v := sorry

def addVector (Λ : Lattice n) (k : Fin n → ℤ) : Lattice n :=
  Λ ⊔ AddSubgroup.closure {k}

theorem lattice_volume (Λ : Lattice n) :
    (∀ d : ℕ, ∀ b : Basis (Fin d) ℤ Λ,
      volume_def Λ ^ 2 = (gram (basisMatrix b)).det) ∧
    (∃ q : ℤ, 0 < q ∧ volume_def Λ ^ 2 = (q : ℝ)) ∧
    1 ≤ volume_def Λ ∧ volume_def (⊥ : Lattice n) = 1 ∧
    volume_def (⊤ : Lattice n) = 1 ∧
    (∀ Γ : Lattice n, Γ ≤ Λ → latticeDim Γ = latticeDim Λ →
      volume_def Λ ≤ volume_def Γ) ∧
    (∀ k : Fin n → ℤ, integerReal k ∉ lattice Λ →
      latticeDim (addVector Λ k) = latticeDim Λ + 1 ∧
      volume_def (addVector Λ k) = volume_def Λ * euclid (compProj (lattice Λ) (integerReal k)) ∧
      compProj (lattice Λ) (integerReal k) ≠ 0) := sorry

theorem lattice_volume_index {d : ℕ} {Γ Λ : Lattice n}
    (b : Basis (Fin d) ℤ Λ) (c : Basis (Fin d) ℤ Γ)
    (N : Matrix (Fin d) (Fin d) ℤ) (hN : basisMatrix c = basisMatrix b * N) :
    volume_def Γ = |(N.det : ℝ)| * volume_def Λ := sorry

theorem lattice_volume_cyclic (g : Fin n → ℤ) (hg : g ≠ 0) :
    volume_def (AddSubgroup.closure {g}) = euclid (integerReal g) := sorry

theorem lattice_volume_hadamard {d : ℕ} (v : Fin d → (Fin n → ℤ))
    (hv : LinearIndependent ℝ (fun j => integerReal (v j))) :
    volume_def (AddSubgroup.closure (Set.range v)) ≤ ∏ j, euclid (integerReal (v j)) := sorry

def klattice (K : ℝ) (Λ : Lattice n) : Prop :=
  AddSubgroup.closure ((Λ : Set _) ∩ eBall n K) = Λ

def maximalK (K : ℝ) (Λ : Lattice n) : Prop :=
  klattice K Λ ∧ ∀ Λ' : Lattice n, klattice K Λ' → Λ ≤ Λ' →
    latticeDim Λ' = latticeDim Λ → Λ' = Λ

theorem maximal {K : ℝ} (hK : 0 ≤ K) (Λ : Lattice n) :
    (klattice K Λ → (maximalK K Λ ↔ ∀ k ∈ eBall n K, integerReal k ∈ lattice Λ → k ∈ Λ)) ∧
    maximalK K (⊥ : Lattice n) ∧
    (klattice K Λ → (∀ k, integerReal k ∈ lattice Λ → k ∈ Λ) → maximalK K Λ) ∧
    (klattice K Λ → ∃ Λ' : Lattice n, maximalK K Λ' ∧ Λ ≤ Λ' ∧ latticeDim Λ' = latticeDim Λ) ∧
    (∀ k ∈ eBall n K, k ≠ 0 → ∃ Λ' : Lattice n, maximalK K Λ' ∧ latticeDim Λ' = 1 ∧ k ∈ Λ') ∧
    (maximalK K Λ → ∀ k ∈ eBall n K, k ∉ Λ → integerReal k ∉ lattice Λ ∧
      latticeDim Λ < n ∧ klattice K (addVector Λ k) ∧
      latticeDim (addVector Λ k) = latticeDim Λ + 1) ∧
    (maximalK K Λ → latticeDim Λ = n → eBall n K ⊆ (Λ : Set _)) ∧
    (1 ≤ K → maximalK K (⊤ : Lattice n) ∧
      (maximalK K Λ → latticeDim Λ = n → Λ = ⊤)) ∧
    (K < 1 → (maximalK K Λ ↔ Λ = ⊥)) ∧
    (maximalK K Λ → 1 ≤ volume_def Λ ∧ volume_def Λ ≤ K ^ latticeDim Λ) := sorry

/-- λ is indexed by natural dimensions; only 1,...,n are consumed. -/
def zone (lam : ℕ → ℝ) (Λ : Lattice n) : Set (Fin n → ℝ) :=
  if Λ = ⊥ then univ else {w | resonanceDistance Λ w < lam (latticeDim Λ) / volume_def Λ}

def zoneStratum (K : ℝ) (lam : ℕ → ℝ) (d : ℕ) : Set (Fin n → ℝ) :=
  {w | 1 ≤ d ∧ d ≤ n ∧ ∃ Λ : Lattice n, maximalK K Λ ∧ latticeDim Λ = d ∧ w ∈ zone lam Λ}

def blocks (K : ℝ) (lam : ℕ → ℝ) (Λ : Lattice n) : Set (Fin n → ℝ) :=
  zone lam Λ \ zoneStratum K lam (latticeDim Λ + 1)

theorem blocks_cover {K : ℝ} (hK : 0 ≤ K) (lam : ℕ → ℝ)
    (hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < lam d) :
    {Λ : Lattice n | maximalK K Λ}.Finite ∧
    ∀ w : Fin n → ℝ, ∃ Λ : Lattice n, maximalK K Λ ∧ w ∈ blocks K lam Λ := sorry

theorem sqrt (A : ℝ) (hA : Real.sqrt 2 ≤ A) :
    1 ≤ A ^ 2 - 1 ∧ A - Real.sqrt 2 ≤ Real.sqrt (A ^ 2 - 1) - 1 := sorry

theorem geom_formula (V : Submodule ℝ (Fin n → ℝ)) (k w : Fin n → ℝ) (hk : k ∉ V) :
    let V' := V ⊔ Submodule.span ℝ {k}
    compProj V k ≠ 0 ∧
    proj V' w - proj V w = ((compProj V k ⬝ᵥ w) / euclid (compProj V k) ^ 2) • compProj V k ∧
    k ⬝ᵥ w = proj V k ⬝ᵥ proj V w + compProj V k ⬝ᵥ w ∧
    |compProj V k ⬝ᵥ w| = euclid (compProj V k) * euclid (proj V' w - proj V w) ∧
    euclid (proj V' w) ^ 2 = euclid (proj V w) ^ 2 + euclid (proj V' w - proj V w) ^ 2 := sorry

theorem geometric (hn : 1 ≤ n) {K E A : ℝ} (hK : 0 < K) (hE : 0 < E)
    (hA : E + Real.sqrt 2 ≤ A) (lam : ℕ → ℝ)
    (hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < lam d)
    (hratio : ∀ d, 1 ≤ d → d < n → A * K ≤ lam (d + 1) / lam d) :
    (∀ w ∈ blocks K lam (⊥ : Lattice n), ∀ k ∈ eBall n K, k ≠ 0 → lam 1 ≤ |integerReal k ⬝ᵥ w|) ∧
    (∀ Λ : Lattice n, maximalK K Λ → 1 ≤ latticeDim Λ → ∀ w ∈ blocks K lam Λ,
      resonanceDistance Λ w < lam (latticeDim Λ) / volume_def Λ ∧
      ∀ k ∈ eBall n K, k ∉ Λ → E * K * (lam (latticeDim Λ) / volume_def Λ) ≤
        |integerReal k ⬝ᵥ w|) := sorry

structure CoverParams (n : ℕ) where
  p : ℝ
  b : ℝ
  r0 : ℝ
  M : ℝ
  m : ℝ
  K : ℝ
  A : ℝ

def CoverParams.lam (c : CoverParams n) (d : ℕ) : ℝ :=
  c.b * c.m * c.r0 / (c.A * c.K) ^ n * (c.A * c.K) ^ d

def CoverParams.radius (c : CoverParams n) (Λ : Lattice n) : ℝ :=
  c.r0 / (c.A * c.K) ^ n * (c.A * c.K) ^ latticeDim Λ / volume_def Λ

def CoverParams.alpha (c : CoverParams n) (Λ : Lattice n) : ℝ := c.p * c.M * c.K * c.radius Λ

def CoverParams.delta (c : CoverParams n) (Λ : Lattice n) : ℝ := c.b * c.m * c.radius Λ

def actionBlock {ι : Type*} (c : CoverParams n) (P : Set ι) (freqR : ι → (Fin n → ℝ))
    (Λ : Lattice n) : Set ι := {I | I ∈ P ∧ freqR I ∈ blocks c.K c.lam Λ}

structure CoverParams.Valid (c : CoverParams n) : Prop where
  hn : 1 ≤ n
  hp : 0 < c.p
  hb : 0 < c.b
  hr0 : 0 < c.r0
  hM : 0 < c.M
  hm : 0 < c.m
  hK : 1 ≤ c.K
  hA : c.p * c.M / (c.b * c.m) + Real.sqrt 2 ≤ c.A

theorem covering {ι : Type*} (c : CoverParams n) (hc : c.Valid)
    (P : Set ι) (freqR : ι → (Fin n → ℝ)) :
    {Λ : Lattice n | maximalK c.K Λ}.Finite ∧
    (∀ I ∈ P, ∃ Λ : Lattice n, maximalK c.K Λ ∧ I ∈ actionBlock c P freqR Λ) ∧
    (∀ Λ : Lattice n, maximalK c.K Λ →
      (1 ≤ latticeDim Λ → c.delta Λ = c.lam (latticeDim Λ) / volume_def Λ) ∧
      (∀ I ∈ actionBlock c P freqR Λ, ∀ k ∈ eBall n c.K, k ∉ Λ →
        c.alpha Λ ≤ |integerReal k ⬝ᵥ freqR I|) ∧
      (Λ = ⊥ → c.alpha Λ ≤ c.lam 1 ∧
        ∀ I ∈ actionBlock c P freqR Λ, ∀ k ∈ eBall n c.K, k ≠ 0 →
          c.lam 1 ≤ |integerReal k ⬝ᵥ freqR I|) ∧
      (Λ ≠ ⊥ → ∀ I ∈ actionBlock c P freqR Λ, resonanceDistance Λ (freqR I) < c.delta Λ) ∧
      c.radius (⊥ : Lattice n) ≤ c.radius Λ ∧ c.radius Λ ≤ c.r0 ∧
      (Λ ≠ ⊤ → c.radius Λ ≤ c.r0 / (c.A * c.K))) ∧
    c.radius (⊥ : Lattice n) = c.r0 / (c.A * c.K) ^ n ∧ c.radius (⊤ : Lattice n) = c.r0 := sorry

theorem cutoffs (c : CoverParams n) (hc : c.Valid) {Ka : ℝ} (hKa : 0 ≤ Ka) :
    (KAM.NormalForm.zBall n Ka ⊆ eBall n Ka) ∧
    (eBall n Ka ⊆ KAM.NormalForm.zBall n (Real.sqrt n * Ka)) ∧
    (Ka ≤ c.K → ∀ Λ : Lattice n, maximalK c.K Λ →
      ∀ w ∈ blocks c.K c.lam Λ, ∀ k ∈ KAM.NormalForm.zBall n Ka,
        k ∉ Λ → c.alpha Λ ≤ |integerReal k ⬝ᵥ w|) ∧
    (∀ Λ : Lattice n, maximalK c.K Λ → ∀ w ∈ blocks c.K c.lam Λ,
      resonanceDistance Λ w < c.delta Λ) ∧
    (0 < Real.sqrt n * Ka → Real.sqrt n * Ka ≤ c.K → ∀ Λ : Lattice n,
      c.radius Λ = c.alpha Λ / (c.p * c.M * c.K) ∧
      c.radius Λ ≤ c.alpha Λ / (c.p * Real.sqrt n * c.M * Ka)) := sorry

/-! ## Part 9: setting, exact maxima, block hypotheses, stopped stability -/
structure Theorem1Setting (P : Set (Fin n → ℝ)) (r0 s m M ell : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hn : 2 ≤ n
  hr0 : 0 < r0
  hs : 0 < s
  hm : 0 < m
  hmM : m ≤ M
  hell : 0 < ell
  holo : DifferentiableOn ℂ h (polyNbhd (cpx P) r0)
  real : RealOn (Dom n (cpx P) r0 s) (fun w => h w.2)
  hess : ∀ I ∈ polyNbhd (cpx P) r0, ∀ v : Fin n → ℂ,
    euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v
  qc : IsQuasiConvex (realNbhd P r0) h ell m
  radius : r0 ≤ ell / (2 * M)
  f_class : InClass (cpx P) r0 s f
  f_real : RealOn (Dom n (cpx P) r0 s) f
  f_finite : HasFiniteWNorm (cpx P) r0 s f

/-- Graph name bpN:p9:setting, with the descriptive structure retained for projections. -/
abbrev setting := @Theorem1Setting

def thmA (m M : ℝ) : ℝ := 11 * M / m
def thmEps0 (n : ℕ) (r0 m M : ℝ) : ℝ := m * r0 ^ 2 / (2 ^ 10 * thmA m M ^ (2 * n))
def thmK (n : ℕ) (r0 m M eps : ℝ) : ℝ := (thmEps0 n r0 m M / eps) ^ HeadParams.expo n

def theoremCover (n : ℕ) (r0 m M eps : ℝ) : CoverParams n :=
  ⟨9 / 8, 1 / 8, r0, M, m, thmK n r0 m M eps, thmA m M⟩

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- Automatic m ≤ M: does not assume it, unlike the Theorem-1 setting. -/
theorem m_le_M (hn : 2 ≤ n) (hP : P.Nonempty) (hr : 0 < r0) (hs : 0 < s)
    (hell : 0 ≤ ell) (hh : DifferentiableOn ℂ h (polyNbhd (cpx P) r0))
    (hreal : RealOn (Dom n (cpx P) r0 s) (fun w => h w.2))
    (hess : ∀ I ∈ polyNbhd (cpx P) r0, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v)
    (hqc : IsQuasiConvex (realNbhd P r0) h ell m) : m ≤ M := sorry

theorem elementary (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M) :
    let A := thmA m M
    let K := thmK n r0 m M eps
    11 ≤ A ∧ 9 * M / m + Real.sqrt 2 ≤ A ∧
    r0 / A ≤ r0 / 11 ∧ r0 ≤ 4 * ell / m ∧
    1 ≤ K ∧ K ^ (2 * n) = thmEps0 n r0 m M / eps ∧
    (eps / thmEps0 n r0 m M) ^ HeadParams.expo n = 1 / K ∧
    eps = m * (r0 / (A * K) ^ n) ^ 2 / 2 ^ 10 ∧
    thmEps0 n r0 m M ≤ m * r0 ^ 2 / 2 ^ 10 ∧
    0 < K / Real.sqrt n ∧ Real.sqrt n * (K / Real.sqrt n) = K ∧
    K / Real.sqrt n ≤ K ∧ (theoremCover n r0 m M eps).Valid := sorry

/-- Local real regularity, independent of global action-ball hypotheses of Part 1. -/
theorem local_real_regularity (S : Theorem1Setting P r0 s m M ell h f) :
    ContDiffOn ℝ 2 (realPart h) (realNbhd P r0) ∧
    ContinuousOn (KAM.frequencyMap h) (realNbhd P r0) ∧
    (∀ I ∈ realNbhd P r0, ∀ v : Fin n → ℝ,
      KAM.realInclusion n (fderiv ℝ (KAM.frequencyMap h) I v) =
        fun i => fderiv ℂ (fun J => fderiv ℂ h J (KAM.realInclusion n v))
          (KAM.realInclusion n I) (Pi.single i 1)) := sorry

/-- Supremum is used only on this guarded domain: a compact nonempty ball inside U_r0 P. -/
structure FrequencyBall (S : Theorem1Setting P r0 s m M ell h f) where
  center : Fin n → ℝ
  mem : center ∈ P
  radius : ℝ
  nonneg : 0 ≤ radius
  lt : radius < r0

def FrequencyBall.points {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) :
    Set (Fin n → ℝ) := {I | euclid (I - B.center) ≤ B.radius}

def FrequencyBall.maximum {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) : ℝ :=
  sSup ((fun I => euclid (KAM.frequencyMap h I)) '' B.points)

theorem frequency_maximum {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) :
    B.points ⊆ realNbhd P r0 ∧ IsCompact B.points ∧ B.points.Nonempty ∧
    (∃ I ∈ B.points, B.maximum = euclid (KAM.frequencyMap h I)) ∧
    (∀ I ∈ B.points, euclid (KAM.frequencyMap h I) ≤ B.maximum) ∧
    euclid (KAM.frequencyMap h B.center) ≤ B.maximum ∧
    B.maximum ≤ euclid (KAM.frequencyMap h B.center) + M * B.radius := sorry

theorem omega0_radius (S : Theorem1Setting P r0 s m M ell h f) :
    0 ≤ r0 / thmA m M ∧ r0 / thmA m M < r0 := sorry

def omega0Ball (S : Theorem1Setting P r0 s m M ell h f)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) : FrequencyBall S :=
  ⟨I0, hI, r0 / thmA m M, (omega0_radius S).1, (omega0_radius S).2⟩

theorem omega0 (S : Theorem1Setting P r0 s m M ell h f)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) :
    let B := omega0Ball S I0 hI
    B.points ⊆ realNbhd P r0 ∧
    (∃ I ∈ B.points, B.maximum = euclid (KAM.frequencyMap h I)) ∧
    (∀ I ∈ B.points, euclid (KAM.frequencyMap h I) ≤ B.maximum) ∧
    euclid (KAM.frequencyMap h I0) ≤ B.maximum ∧
    B.maximum ≤ euclid (KAM.frequencyMap h I0) + M * r0 / thmA m M := sorry

theorem full_rank_zone (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M) :
    let c := theoremCover n r0 m M eps
    maximalK c.K (⊤ : Lattice n) ∧ c.radius (⊤ : Lattice n) = r0 ∧
    c.delta (⊤ : Lattice n) = m * r0 / 8 ∧
    (∀ v, proj (lattice (⊤ : Lattice n)) v = v) ∧
    (∀ I ∈ P, I ∈ actionBlock c P (KAM.frequencyMap h) (⊤ : Lattice n) ↔
      euclid (KAM.frequencyMap h I) < m * r0 / 8) := sorry

theorem block_hyp (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (hfb : WBound (cpx P) r0 s f eps) (Λ : Lattice n)
    (hΛ : maximalK (thmK n r0 m M eps) Λ)
    (I0 : Fin n → ℝ) (hI : I0 ∈ actionBlock (theoremCover n r0 m M eps) P (KAM.frequencyMap h) Λ) :
    let c := theoremCover n r0 m M eps
    let r := c.radius Λ
    let Ka := c.K / Real.sqrt n
    0 < r ∧ 0 < c.alpha Λ ∧ 0 < c.delta Λ ∧
    c.radius (⊥ : Lattice n) ≤ r ∧ r ≤ r0 ∧
    (Λ ≠ ⊤ → r ≤ r0 / (c.A * c.K)) ∧
    polyNbhd (cpx {I0}) r ⊆ polyNbhd (cpx P) r0 ∧
    realNbhd {I0} r ⊆ realNbhd P r0 ∧ realStrip {I0} r ⊆ realStrip P r0 ∧
    DifferentiableOn ℂ h (polyNbhd (cpx {I0}) r) ∧
    RealOn (Dom n (cpx {I0}) r s) (fun w => h w.2) ∧
    (∀ I ∈ polyNbhd (cpx {I0}) r, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v) ∧
    IsQuasiConvex (realNbhd {I0} r) h ell m ∧
    InClass (cpx {I0}) r s f ∧ RealOn (Dom n (cpx {I0}) r s) f ∧
    WBound (cpx {I0}) r s f eps ∧
    eps ≤ m * r ^ 2 / 2 ^ 10 ∧
    m * r ^ 2 / 2 ^ 10 = (9 / 8 : ℝ) / 9 * (m * r ^ 2 / 2 ^ 7) ∧
    r = c.alpha Λ / ((9 / 8 : ℝ) * Real.sqrt n * M * Ka) ∧
    Ka * (Real.sqrt n * M) * r = c.alpha Λ / (9 / 8 : ℝ) ∧
    r ≤ 4 * ell / m ∧ M * r ≤ ell / 2 ∧
    KAM.NormalForm.IsNonresonant (cpx {I0}) Ka (c.alpha Λ) (Λ : Set _) h ∧
    (Λ ≠ ⊥ → resonanceDistance Λ (KAM.frequencyMap h I0) < c.delta Λ) ∧
    IsCloseToRes {I0} (Λ : Set _) h (c.delta Λ) ∧ c.delta Λ ≤ m * r / 8 ∧
    KAM.NormalForm.FreqLipschitz (cpx {I0}) r (Real.sqrt n * M) h ∧
    (Λ = ⊥ → eps ≤ c.alpha Λ * r / (2 ^ 7 * 9 * Ka)) := sorry

theorem block_frequency_radius (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (Λ : Lattice n) (hΛ : maximalK (thmK n r0 m M eps) Λ) :
    0 ≤ (theoremCover n r0 m M eps).radius Λ / 2 ∧
    (theoremCover n r0 m M eps).radius Λ / 2 < r0 := sorry

def blockBall (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (Λ : Lattice n) (hΛ : maximalK (thmK n r0 m M eps) Λ)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) : FrequencyBall S :=
  ⟨I0, hI, (theoremCover n r0 m M eps).radius Λ / 2,
    (block_frequency_radius S heps heps0 Λ hΛ).1,
    (block_frequency_radius S heps heps0 Λ hΛ).2⟩

/-- Multiplication form includes Ω=0 and full rank as infinite time, with no division by zero. -/
def blockAdm (c : CoverParams n) (s eps Om : ℝ) (Λ : Lattice n) (t : ℝ) : Prop :=
  Λ = ⊤ ∨ if Λ = ⊥ then
    |t| * (5 * eps) ≤ s * c.radius Λ * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6)
  else |t| * (288 * Om * eps) ≤
    s * c.m * c.radius Λ ^ 2 * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6)

theorem local_field (S : Theorem1Setting P r0 s m M ell h f)
    {I0 : Fin n → ℝ} (hI : I0 ∈ P) {r : ℝ} (hr : 0 < r) (hrr : r ≤ r0) :
    IsOpen (realStrip {I0} r) ∧ realStrip {I0} r ⊆ realStrip P r0 ∧
    (∀ x ∈ realStrip {I0} r,
      KAM.hamiltonianVectorField ((realStrip {I0} r).indicator (realH (fun w => h w.2 + f w))) x =
        KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x) ∧
    (∀ x ∈ realStrip P r0,
      KAM.hamiltonianVectorField ((realStrip P r0).indicator (realH (fun w => h w.2 + f w))) x =
        KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x) := sorry

theorem block_stab (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (hfb : WBound (cpx P) r0 s f eps) (Λ : Lattice n)
    (hΛ : maximalK (thmK n r0 m M eps) Λ)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip P r0, F x = KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t)
    (hI : (z 0).2 ∈ P)
    (hblock : (z 0).2 ∈ actionBlock (theoremCover n r0 m M eps) P (KAM.frequencyMap h) Λ) :
    let c := theoremCover n r0 m M eps
    let B := blockBall S heps heps0 Λ hΛ (z 0).2 hI
    ∀ t ∈ J, blockAdm c s eps B.maximum Λ t →
      z t ∈ realStrip P r0 ∧ ‖(z t).2 - (z 0).2‖ ≤ c.radius Λ / 2 ∧
      (Λ ≠ ⊥ → euclid ((z t).2 - (z 0).2) ≤ c.radius Λ / 2) := sorry

theorem thm1 (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (hfb : WBound (cpx P) r0 s f eps)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip P r0, F x = KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t)
    (hI : (z 0).2 ∈ P) :
    let I0 := (z 0).2
    let Om0 := (omega0Ball S I0 hI).maximum
    (m * r0 / 8 ≤ euclid (KAM.frequencyMap h I0) →
      ∀ t ∈ J, |t| ≤ thmA m M ^ 2 * s / Om0 *
        Real.exp (Real.pi * s / (3 * Real.sqrt n) * thmK n r0 m M eps) →
      z t ∈ realStrip P r0 ∧
      ‖(z t).2 - I0‖ ≤ (r0 / thmA m M) / 2 *
        (eps / thmEps0 n r0 m M) ^ HeadParams.expo n) ∧
    (euclid (KAM.frequencyMap h I0) < m * r0 / 8 →
      ∀ t ∈ J, z t ∈ realStrip P r0 ∧ euclid ((z t).2 - I0) ≤ r0 / 2) := sorry

end Theorem1
end KAM.Nekhoroshev
```
