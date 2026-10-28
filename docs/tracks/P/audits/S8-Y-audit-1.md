# S8-Y independent package audit 1

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-s8y`.
Audited HEAD: `2a6ddf38e4124d7977056a4e9817f02caae03bec`.
Compared with `inp` at `872a014af58890f96058190624e431a0ed0228a5`, using `git diff inp...HEAD`.
Scope: only `KAM/Planetary/SecularForm/Symmetry.lean` (581 lines).
SHA-256: `4fe599faba5795a4a83ebc46dab191457efa4009f5699bc9b12dfd61f8763169`.

Overall verdict: **PASS WITH NOTES**. All five requested exports pass.
Notes: the permitted stale generated root, replayed upstream unused-variable warnings,
and the explicit infrastructure-only scope below. No repair is requested in Symmetry.lean.

This is an infrastructure package with no provider export or frozen theorem anchor.
Per-anchor seal readiness is therefore **N/A**. No frozen theorem, full blueprint
corollary, planetary headline, analytic expansion or torsion result is promoted by this report.
The user's explicit output path overrides the generic brief's main-worktree destination.

## Authority and exact statement checks

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief and S8-Y handoff;
checked the S8-Y row, coverage inventory and stronger-domain ruling in
`docs/tracks/P/design/P810-LEAN-DESIGN.md` (lines 101–109, 359, 424), both
`docs/tracks/P/design/DESIGN-P810-design-audit-{1,2}.md`, the original signature file
`/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, blueprint P Part 8 lines
16–28 and 56–85, the track-P coordinate conventions, and the relevant frozen definitions.
The design audits concern signatures, not proof closure; the present audit checks actual proofs.

The original signature file has SHA-256
`492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`.
An independent whitespace-normalized comparison returned:

```text
rotateSlow HEADER_MATCH True
rotateSlow BODY_MATCH True
rotatePhysical HEADER_MATCH True
rotatePhysical BODY_MATCH True
symmetries HEADER_MATCH True
evenness HEADER_MATCH True
evenness_taylor HEADER_MATCH True
```

Fresh scratch declarations reproduce the three theorem types directly from that original
signature file under `audit_` names, with bodies respectively
`by exact symmetries D hx t θ`, `by exact evenness D hx b θ`, and
`by exact evenness_taylor D hI b k`. Two copied design definitions are compared with
implementation definitions by `example : @audit_rotateSlow = @rotateSlow := rfl`
and the analogous `rotatePhysical` equality. These checks use the production carriers,
not shadow versions of Data, secular or the chart. Frozen/provider type and seal probes
are inapplicable because this package has neither.

## Declaration inventory

Names in the first six rows are relative to `KAM.Planetary`; all later theorem
names are relative to `KAM.Planetary.SecularForm`. PASS rows below concern source
fidelity and proof inspection; machine validation is recorded separately below.
Auxiliary conditional statements have distinct names and are discharged at their use sites.

| Node / role | Lean declaration (line) | Verdict | Reason |
|---|---|---|---|
| sy-1 | `poincare_antipode` (53) | PASS | Kepler uniqueness gives F+π; both physical blocks change sign. No mass positivity needed. |
| sy-2 | `poincare_rotate` (98) | PASS | F+θ and rotation covariance; Γ and Λ fixed. |
| sy-3 | `poincare_reflect` (140) | PASS | F becomes −F; position uses σ and momentum −σ. |
| e-diff / ev-inv | `cell_integral_add` (253) | PASS | Arbitrary lattice-periodic function, arbitrary vector shift; stronger than continuous version. |
| e-diff / ev-inv | `cell_integral_neg` (270) | PASS | Reflection image is a translated cube; measure-preserving substitution. |
| ev-tay | `iteratedFDeriv_odd_eq_zero` (304) | PASS | Local evenness and odd order suffice for totalized iterated derivatives; generic auxiliary result. |
| chart dictionary | `planetBlock_assemble` (344) | PASS | Literal block order (λ,ξ;Λ,η). |
| chart domain | `assemble_mem_iff` (348) | PASS | Exactly Λ>0 and (ξ²+η²)/2<Λ per planet. |
| chart domain | `mem_slowDom_iff` (352) | PASS | Angle-independent domain characterization. |
| chart domain | `assemble_mem_slowDom` (356) | PASS | Supplies chart membership at every fast angle. |
| sy-1/2/3 assembly | `poincareProd_assemble` (360) | PASS | Literal body-wise product chart. |
| block assembly | `ofPlanets_map` (366) | PASS | Arbitrary block functions, no assumed symmetry conclusion. |
| block assembly | `neg_ofPlanets` (372) | PASS | Componentwise sign identity. |
| symmetries domain | `rotateSlow_mem` (376) | PASS | Preserves Λ and ξ²+η². |
| bpP:p8:symmetries | `symmetries` (386) | PASS | Exact design type; all three chart identities, correct reflection signs. |
| sy-f | `pairPotential_map` (421) | PASS | Conditional additive length-preserving map lemma; applies map_sub to distances. |
| sy-f | `perturbation_map` (429) | PASS | Conditional transport lemma for additive A,B; preserves pair distances and square of total momentum. |
| sy-f / S1 | `perturbation_antipode` (455) | PASS | Discharges map and chart conditions using proved S1. |
| sy-f / S2 | `perturbation_rotate` (468) | PASS | Discharges rotation norm identities and proved S2. |
| sy-f / S3 | `perturbation_reflect` (477) | PASS | Discharges σ and −σ identities and proved S3. |
| lattice dictionary | `assemble_add_fastShift` (487) | PASS | Exact 2π integer fast shift; slow blocks fixed. |
| ev-inv | `perturbation_periodic` (496) | PASS | Supplies periodicity from actual product-chart lattice theorem. |
| ev-inv auxiliary | `secular_eq_of_shift` (505) | PASS | Explicit integrand transport premise; supplied by antipode/rotation lemmas in evenness. |
| ev-inv auxiliary | `secular_eq_of_neg` (516) | PASS | Explicit integrand transport premise; supplied by proved reflection in evenness. |
| bpP:p8:evenness / ev-inv | `evenness` (526) | PASS | Exact four invariances, both models; whole slowDom as approved stronger domain. |
| bpP:p8:evenness / ev-tay | `evenness_taylor` (555) | PASS | Every odd iterated derivative tensor vanishes at 0 for actions in actionDomain. |

The four public definitions `sigmaRefl`, `rotBlock`, `rotateSlow`, `rotatePhysical`
are separately classified below. No other public declaration is omitted.
The full polynomial-invariant structure, action analyticity of coefficients and
quadratic-form conclusion printed in blueprint lines 76–79/84 are allocated to cooperating
packages in the design; S8-Y does not claim to establish them.

## Expanded binder audit

Exact requested exports: the following table includes every binder, with repeated standing
Data fields expanded. The references are blueprint Part 8 lines 16–21, 56–66, 75–83,
and the exact corresponding design signatures. SOURCE means source data/domain;
STANDING means the physical Data structure; TYPING means carrier formation.
There are no quantified constants or witnesses whose dependence could widen.

| Export(s) | Binder | Bin | Source / meaning |
|---|---|---|---|
| rotateSlow, rotatePhysical | implicit n : ℕ | TYPING | Number of planet blocks; signatures. |
| rotateSlow, rotatePhysical | t : ℝ | SOURCE | Arbitrary rotation angle, p8:56. |
| rotateSlow | x : Slow n | SOURCE | (ξ,Λ,η), whole literal carrier. |
| rotatePhysical | z : Phase (n*2) | SOURCE | All physical positions and momenta. |
| symmetries, evenness, evenness_taylor | implicit n : ℕ | TYPING | Fin n coordinate carrier, p8:16. |
| symmetries, evenness, evenness_taylor | D.G : ℝ | STANDING | Gravitational constant, p8:16. |
| symmetries, evenness, evenness_taylor | D.m0 : ℝ | STANDING | Central mass, p8:16. |
| symmetries, evenness, evenness_taylor | D.m : Fin n → ℝ | STANDING | Planet masses, p8:16. |
| symmetries, evenness, evenness_taylor | D.hG : 0 < D.G | STANDING | p8:16. |
| symmetries, evenness, evenness_taylor | D.hm0 : 0 < D.m0 | STANDING | p8:16. |
| symmetries, evenness, evenness_taylor | D.hm : ∀ i, 0 < D.m i | STANDING | p8:16. |
| symmetries, evenness, evenness_taylor | D.hn : 0 < n | STANDING | n≥1, p8:16. |
| symmetries, evenness | implicit x : Slow n | SOURCE | Arbitrary slow point, exact signatures. |
| symmetries, evenness | hx : x ∈ slowDom D | SOURCE | Original chart domain; evenness stronger-domain ruling at design:359. |
| symmetries | t : Vec n | SOURCE | Arbitrary λ, p8:59–64. |
| symmetries, evenness | θ : ℝ | SOURCE | Arbitrary simultaneous rotation, p8:63/76. |
| evenness, evenness_taylor | b : Bool | SOURCE | Both fixed and moving models, p8:76. |
| evenness_taylor | implicit I : Vec n | SOURCE | Fixed admissible actions at circular torus. |
| evenness_taylor | hI : I ∈ actionDomain D | SOURCE | Positive ordered-axis image, design signature; source circular torus data. |
| evenness_taylor | k : ℕ | SOURCE | Every odd order 2k+1, p8:76/83. |

Expanded counts per export (Data is replaced by its seven fields, not counted twice):
rotateSlow/rotatePhysical each TYPING=1, SOURCE=2, STANDING=0;
symmetries and evenness each TYPING=1, SOURCE=4, STANDING=7;
evenness_taylor TYPING=1, SOURCE=4, STANDING=7.
For every export RULED=0, EXCESS=0. The stronger-domain permission is explicitly
in the audited design, and does not introduce a new premise.
There are no extra instances on these five exports.

Other public helpers have only their displayed algebraic/domain data. In particular,
`perturbation_map` assumes a chart identity only as a generic conditional transport lemma;
its three calls discharge that identity with `symmetries`. Likewise `secular_eq_of_shift`
and `secular_eq_of_neg` are conditional change-of-variable helpers; `evenness` supplies
their transport premises rather than assuming evenness. The generic odd-derivative helper
assumes local evenness, which `evenness_taylor` proves on an open neighbourhood.
Its normed-group and real normed-space instances are typing requirements, not proof fields.

## Definition classification

All nine new definitions are literal formulas; there is no abbrev, structure, choice-defined
object, fallback branch, clipping or junk-value repair. Each row has
BODY_MATCH=OK, PUBLIC_CARRIER=OK (for private definitions: complete internal carrier),
WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL,
CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS.

| Definition (line) | Classification / complete-body meaning |
|---|---|
| `KAM.Planetary.sigmaRefl` (32) | Public literal plane reflection ![v₀,−v₁]. |
| `KAM.Planetary.rotBlock` (89) | Public literal one-planet rotation: λ+θ, rotated (ξ,η), unchanged Λ. |
| private `twoPiUnit` (187) | Unit of ℝ given by positive 2π, with proof of nonzeroness. |
| private `twoPiBasis` (191) | Standard Pi basis scaled by the unit 2π. |
| `SecularForm.rotateSlow` (338) | Public exact design formula; rotates every (ξᵢ,ηᵢ), preserves Λ. |
| `SecularForm.rotatePhysical` (341) | Public exact design formula; rotates each qᵢ and pᵢ. |
| private `SecularForm.rotHom` (446) | Additive-hom bundle of the literal rotation. |
| private `SecularForm.sigHom` (449) | Additive-hom bundle of σ. |
| private `SecularForm.sigHom'` (452) | Additive-hom bundle of −σ. |

Private `countable_span` (232) proves countability of the actual integer span of the scaled
basis; it does not supply a mathematical premise by an invented instance. It derives
countability from the range of integer coordinate vectors.

The imported `Data` expands to exactly G,m0,m,hG,hm0,hm,hn. `Slow` is the literal
right-associated triple (ξ,Λ,η); `assemble` gives (λ,ξ;Λ,η). `slowDom` means
chart membership at λ=0, proved equivalent here to the same membership at all λ.
`secular` literally calls frozen `secularAverage` with I=Λ,p=η,q=ξ and unchanged
normalizer (2π)^(-n). `slowSecular` simply fixes actions. Physical distances use
planeLength = sqrt(sum of coordinate squares), not the ambient Pi max norm.

## Proof refutation checks

1. At lines 66–75, 113–125 and 157–166, Kepler uniqueness is applied with a genuinely
   proved planeLength(v)<1. The transformed roots are F+π, F+θ and −F. Γ, Λ,
   k and J are unchanged; the reflection anticommutes with quarter-turn, accounting for
   the minus on momentum. Product assembly respects the frozen coordinate dictionary.
2. Translation uses the actual lattice 2πℤⁿ, with a scaled standard basis. The closed cube
   differs almost everywhere from its half-open fundamental domain. Its translate is another
   fundamental domain. Mathlib's `IsAddFundamentalDomain.setIntegral_eq` is valid without
   integrability: `Mathlib/MeasureTheory/Group/FundamentalDomain.lean:407–417` explicitly
   splits on integrability, transfers it between domains, and uses integral_undef in the
   nonintegrable case. Thus this is not an illicit subtraction of two totalized integrals.
   Reflection is measure preserving and sends the closed cube to its translate by −2π.
3. The pair potential preserves all distances, including zero distances under the existing
   real inverse convention. The moving correction preserves the square of the **sum** of
   momenta via map_sum, not merely each planet's individual square. No collision-free
   hypothesis or integrability premise is silently consumed.
4. The evenness proof explicitly reverses angle shifts with −π and −θ and reverses λ
   for reflection; combining simultaneous sign change and η-reflection gives ξ-reflection.
   These change whole vectors, not each planet independently; cross terms are retained.
5. Generic odd derivatives use local equality, exact pullback by the continuous linear
   equivalence −id, multilinearity and (−1)^odd=−1. This remains true for Mathlib's
   totalized iterated derivatives without assuming smoothness. At lines 557–574,
   actionDomain supplies positive actions and continuity supplies a neighbourhood of zero
   inside slowDom. The actual evenness theorem is applied there. This proves the tensor
   equality, not merely a diagonal evaluation or scalar directional derivative.

## Hygiene and independent validation

All checks below were launched sequentially with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no two auditor-controlled Lean/Lake/checker jobs overlapped.

### Exact-type, definition-body and axiom probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8YAudit.lean
exit 0
'KAM.Planetary.poincare_antipode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincare_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincare_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cell_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cell_integral_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_odd_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetBlock_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.assemble_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.mem_slowDom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.assemble_mem_slowDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincareProd_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.ofPlanets_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.neg_ofPlanets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rotateSlow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.symmetries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairPotential_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_antipode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.assemble_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_eq_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_eq_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.evenness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.evenness_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The scratch probe contains all 26 `#print axioms` commands, one per declaration in
the inventory. The three copied types and two rfl comparisons elaborated without
diagnostics. An initial scratch run exited 1 solely because the two copied definitions
lacked the original noncomputable context; marking these scratch definitions
`noncomputable` corrected the harness. That initial run already reported the same
26 clean axiom closures; no production file changed.

### Independent kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Symmetry
replaying KAM.Planetary.SecularForm.Symmetry
exit 0
```

One invocation covers the only new module, including its private implementation lemmas.
Verbose output was captured in `.lake/abi-scratch/S8Y-kernel.log` and removed after recording.

### Source lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (552 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the generated-root staleness explicitly permitted by the brief.
No regeneration was attempted. All other lint checks passed.

### Targeted gate build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8y KAM.Planetary.SecularForm.Symmetry
[inp-gate] slot 1 acquired 11:53:44 for KAM.Planetary.SecularForm.Symmetry
⚠ [9093/9111] Replayed KAM.Kepler.Energy
⚠ [9094/9111] Replayed KAM.Planetary.Poincare.Chart
⚠ [9100/9111] Replayed KAM.Kepler.Mass
Build completed successfully (9111 jobs).
exit 0
```

The displayed build output omits the repeated unused-variable hint paragraphs.
All 11 warning headers are recorded verbatim here:

```text
warning: KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:212:42: Variable name `hm` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:212:55: Variable name `hκ` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:247:37: Variable name `hm` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:247:50: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:147:57: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:157:52: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:500:5: Variable name `hw` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:524:52: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:524:65: Variable name `hκ` is not explicitly referenced.
```

These are replayed warnings in unchanged dependencies, not findings in the scoped file.
The build used the existing worktree overlay and was incremental; no clean rebuild was requested.

The first gate request waited without acquiring a slot; the auditor stopped only that
waiting wrapper (exit 143), after verifying its only child was sleep, to run the other
checks sequentially before resubmitting the build. No compilation was interrupted.


All project-owned imports were traversed recursively: 65 modules, no provider,
no frozen theorem, 47 frozen definitions, all manifest state SEALED.
No draft theorem import occurs. The 581-line file has its copyright, module command,
public imports, module docstring, exposed public noncomputable section and closing end.
A forbidden-token/resource-option scan returned `[]`. Both coordinates and Fourier
conventions retain the prescribed Fin-function carriers; no EuclideanSpace appears.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
`git diff --check inp...HEAD`: empty, exit 0.
The only committed package change is the new Symmetry.lean. The existing untracked
S8-Y-handoff.md was not edited. Audit probes are confined to .lake/abi-scratch and removed
at closeout; only this report is added by the auditor. No state-changing git command,
root regeneration, production source edit, clean/update or package-cache mutation was used.

## Notes, uncertainty and suspected errata

No new suspected source/blueprint defect, unauthorized premise, signature deviation or
mathematical implementation deviation was found in the scoped file. The stronger
slowDom result is already documented at design:359. Omitting analytic regularity for
vanishing odd totalized derivatives is a valid strengthening; it does not prove that an
analytic Taylor expansion exists outside the analytic polydisc.

The frozen average docstring says “Its uses require integrability explicitly”
(`KAM/Frozen/Planetary/Defs/SecularAverage.lean:38`). Here unconditional transport
is justified by preservation of integrability and by both integrals being zero otherwise.
This is the stronger-domain case explicitly authorized in the design, not an erratum or
an inference of subtraction identities outside their valid domain.

No pinned PDF was re-audited; this is the requested implementation-versus-blueprint/design
package audit. No claim is made about other S8 packages, downstream consumers or anchors.

## Closeout

All required checks are complete. No unresolved mathematical finding or audit validation
remains for the requested scope. The exact signatures and literal rotation bodies pass,
all 26 public theorem axiom closures are clean, kernel replay exits 0, the targeted gate
build exits 0, and source lint has only its expressly allowed generated-root failure.
The probe and kernel log were deleted. The final HEAD, inp revision, package diff and
protected-path diff were rechecked and unchanged. Only this audit report was written
outside .lake/abi-scratch; the pre-existing handoff remains untouched.
