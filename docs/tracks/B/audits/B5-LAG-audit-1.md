# B5-LAG independent audit 1

Audit date: 2026-11-03. Worktree: `/root/code/KAM-inp-b5lag`.
Audited HEAD: `5cf7ca4663b765afafb153bbf5d1d3046475588d`.
Comparison: `inp` = `a362154c24ec6fc4797d55c8a6a08a5eb29d5995`, using
`git diff inp...HEAD` (four new Lean modules and the handoff, 648 insertions).
The user's exact worktree report path overrides the generic brief's main-worktree output instruction.

## Verdict

**PASS WITH NOTES for B5-LAG items 1–4 and the certificate adapters.**
No frozen anchor is assigned to this package: it implements ordinary Track B helper theorems,
not an I/N/P provider or a seal. Consequently provider/frozen type equality and a copied frozen
seal-body probe are not applicable. This verdict approves the reviewed helper package within
its stated premises; it does not seal an anchor or establish B5-CHART, B5-NF or B5-ROUTE.

Controlling text: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the requested package audit
brief, `B5-LAG-handoff.md` AUDIT FOCUS, both B5-LAG/B1-common prover briefs,
`docs/tracks/B/SPEC.md`, `FREEZE-PROPOSAL.md`, `B5-DESIGN.md`, OD-B13–B15,
and program-B plan §3.4 (lines 426–457). There is no Track B `statement.md` and no assigned
B5-LAG node in blueprint-I/N/P; the explicit B5 design and package items are the comparison
statements. No unrelated I/N/P anchor is substituted.

## Findings and notes

1. **Lagrangian property is derived.** `TorusLagrangian.lean:37–79` first uses
   `Identities.fi_dLagrange` after proving the derivative of the zero invariance error is zero
   by equality on a neighbourhood. It then obtains holomorphy, periodicity and zero average
   of the actual `lagrangeMat K`, and applies the proved `Sharp.cohData_crude.apriori` at
   right-hand-side bound zero. `CohData` is constructed by a theorem, not supplied by a
   caller as a hidden uniqueness assumption. The loss `min δ 1` meets the estimate's
   restriction and its output strip contains `T_(r-δ)`. No Gram/torsion inverse, immersion,
   Lagrangian premise, or `geometry_sep` is used. Standing data impose dimension, parameter,
   Hamiltonian regularity/bounds and Diophantine conditions; these are genuine standing
   premises explicitly allowed by AUDIT FOCUS. The result is not advertised as a theorem
   under holomorphy alone.
2. **Certificate premises are explicit.** `g1Hyps_standing` projects source fields of
   `G1Hyps`; it does not assume a new geometric conclusion. `CertifiedTorusAt` is the
   unchanged conjunction inside `CertifiedTorus`, via `Application.certifiedTorus_iff`
   (`Iff.rfl`). `sinf > 1` gives `sinf ≥ 1`, and `Iso.Linear.isDiophantine_smul` proves the
   same-γ lower bound since `|k·(sω)| = s|k·ω|`. The existing sharper scaled-γ theorem
   is compatible but unnecessary here. `G1Hyps` and `hdio` are the existing soundness
   premises. **`CertifiedTorus` alone does not provide them**; retain both in consumers
   of the Lagrangian corollaries. Frequency, energy and projection need no `hdio`.
3. **The real slice has the intended meaning.** Definitions are literal real coordinate
   projections and `u=x-id`. Primary winding gives equivariance of x and periodicity of
   u,v. `ContDiff ℝ (⊤ : ℕ∞)` means smoothness, sufficient for C³; the proof starts from
   `analyticOnNhd_realRestriction`. The derivative inclusion lemmas identify actual real
   derivatives with restrictions of the complex derivative. Expanding `lagrangeMat` and
   taking real parts gives exactly
   `Σ_l (Dx e_i)_l (Dv e_j)_l = Σ_l (Dx e_j)_l (Dv e_i)_l`.
   The helper `torusReal_lagrangian` deliberately assumes pointwise complex vanishing:
   it is a conversion lemma, not the derivation theorem. The certificate corollary
   discharges that premise with item 1. There is no circular assumption in the composed route.
4. **Frequency sign and energy agree with frozen conventions.** Frozen
   `invarianceError = X_h ∘ K - DK·ω`; zero error therefore gives `DK·ω = X_h ∘ K`.
   Both vector fields are `(∂_I H,-∂_θ H)`. The proof uses
   `hamiltonianVectorField_eq_of_real`, injectivity of real inclusion and the real derivative
   bridge. `realHam h = Re ∘ h ∘ ι₂`; no time or 2π rescaling occurs. The energy proof
   substitutes the actual certificate value `E0` and takes its real part.
5. **Projection estimate is quantitative.** The vector Cauchy bound tests arbitrary
   directions e on closed complex discs of radius `δ/‖e‖`, inside the strip since
   `0 < δ < ρ`, then takes the coordinate sup norm. Thus the constant is exactly `d/δ`,
   with no lost dimension factor. The projection proof splits the derivative into
   the reference angle displacement and the angle component of `K-Kc`, uses the
   product norm bound, and restricts to real directions isometrically. The hypothesis on
   the reference derivative is needed only at real points, **weaker** than the design's
   strip-wide premise. Strict `δ<ρ` is intentional and meets AUDIT FOCUS; no endpoint
   `δ=ρ` is claimed. The numerical `<1` check and the chart itself belong to later packages.
6. **Core imports and hygiene.** `KAM.Application.Certified` and `.RealTorus` are core
   imports in `KAM/Root/Application.lean:9,36`, not opt-in application libraries.
   Recursive KAM import inspection found 142 modules, no provider imports, no frozen
   theorem imports and no DRAFT_SORRY imports. New sources obey the ambient carrier,
   module, width, file-size and proof-escape rules. Warnings in builds are inherited
   dependencies, not these four modules.

## Declaration-by-declaration comparison

All names below have prefix `KAM.EffectiveStability.`. PASS refers to the declaration's
stated purpose, not to an unproved downstream chart or confinement theorem.

| Node/item | Declaration | Verdict | Reason/note |
|---|---|---|---|
| 1, differential identity | `fderiv_lagrangeMat_omega_eq_zero` | PASS | Zero error differentiated locally; actual pullback matrix. |
| 1, general Lagrangian | `lagrangeMat_eq_zero_of_exact` | PASS | Zero average and cohomological estimate force vanishing for any strict loss. |
| 2, coordinate | `torusRealX` | PASS | Literal first real coordinate. |
| 2, coordinate | `torusRealV` | PASS | Literal second real coordinate. |
| 2, displacement | `torusRealU` | PASS | Literal x minus identity. |
| 2, winding | `torusRealX_add_int` | PASS | Correct additive lattice equivariance. |
| 2, periodicity | `torusRealU_add_int` | PASS | Displacement is lattice-periodic. |
| 2, periodicity | `torusRealV_add_int` | PASS | Momentum is lattice-periodic. |
| 2, regularity | `torusRealPair_contDiff` | PASS | Smooth real restriction from analyticity. |
| 2, regularity | `torusRealX_contDiff` | PASS | Smooth projection. |
| 2, regularity | `torusRealV_contDiff` | PASS | Smooth projection. |
| 2, regularity | `torusRealU_contDiff` | PASS | Smooth displacement, C³ consumer probe passes. |
| 2, derivative bridge | `fderiv_torusRealX_incl` | PASS | Exact complex/real angle derivative agreement. |
| 2, derivative bridge | `fderiv_torusRealV_incl` | PASS | Exact complex/real momentum derivative agreement. |
| 2, real symmetry | `torusReal_lagrangian` | PASS | Conditional conversion; hΩ paid by item 1 in certificate corollary. |
| 3, inclusion bridge | `realInclusion₂_realRestriction` | PASS | Equality of actual real points for real-on-reals K. |
| 3, frequency | `torusReal_frequency` | PASS | Correct sign and Hamiltonian; no Diophantine assumption needed. |
| 3, energy | `torusReal_energy` | PASS | Direct real restriction of complex energy equality. |
| 4, Cauchy | `norm_fderiv_real_le_of_strip_bound` | PASS | Operator sup norm with exact constant 1/δ. |
| 4, projection | `torusRealU_fderiv_le` | PASS | Reference-plus-displacement estimate; weaker real-only reference bound. |
| certificate standing | `g1Hyps_standing` | PASS | Source data projected; Diophantine scaling correct for s≥1. |
| certificate domain | `certifiedTorusAt_mem_D` | PASS | Centre of positive-radius certified ball belongs to D. |
| certificate item 1 | `certifiedTorusAt_lagrangian` | PASS | Derived from exact invariance, hG, hdio. |
| certificate item 2 | `certifiedTorusAt_realLagrangian` | PASS | Required DxᵀDv symmetry; loss ensures real points lie in smaller strip. |
| certificate item 3 | `certifiedTorusAt_frequency` | PASS | Frequency sinf•ωstar retained exactly. |
| certificate item 3 | `certifiedTorusAt_energy` | PASS | Energy E0 retained exactly. |
| certificate item 4 | `certifiedTorusAt_projection` | PASS | Uses actual certificate disp; reference holomorphy restricted to rhoInf. |

## Definition classification

Exactly three new public definitions; no new abbreviations or structures:

- `torusRealX K φ := (realRestriction K φ).1`;
- `torusRealV K φ := (realRestriction K φ).2`;
- `torusRealU K φ := torusRealX K φ - φ`.

Each is the intended total object on its whole carrier, with exposed bodies and no junk
fallback or branch. No global Phase alias, EuclideanSpace or changed norm carrier occurs.
`Standing`, `CohData`, `CertifiedTorusAt`, `realRestriction` and `realHam` are reused,
unchanged definitions. Total `fderiv` is used only with regularity available at the points
where its derivative meaning is needed.

## Verification receipts

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and a 4 GB, no-swap
systemd scope. Define the command prefix used below:

```sh
SCOPE='systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0'
```

Builds used the required compile gate, one module per invocation (the gate itself runs
`nice -n 5 lake build`):

```sh
$SCOPE nice -n 10 env LEAN_NUM_THREADS=1 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b5lag KAM.EffectiveStability.TorusLagrangian
# exit 0: Build completed successfully (3202 jobs).
# Repeat, separately, for TorusRealSlice: exit 0, 3192 jobs.
# Repeat, separately, for TorusProjection: exit 0, 3194 jobs.
# Repeat, separately, for TorusLagrangianCert: exit 0, 3300 jobs.
```

Replayed warnings are in `Strip/CohomologicalRussmannLattice`,
`Strip/CohomologicalRussmannBound`, `Certificate/Arith/PiHigh`, `Certificate/Expr/Basic`,
`Certificate/Sound/Static` and `Certificate/Sound/Ham` only.

The scratch probe imported `KAM.EffectiveStability.TorusLagrangianCert`, printed axioms
for **all 24 new public theorems**, and elaborated (a) smoothness ⇒ C³, (b) an existential
`CertifiedTorus` consumer deriving Lagrangian vanishing on `rhoInf/2` from hG and hdio.

```sh
$SCOPE nice -n 10 env LEAN_NUM_THREADS=1 nice -n 5 \
  lake env lean .lake/abi-scratch/B5LagAudit.lean
# exit 0; all 24 lines: '<fully qualified theorem>' depends on axioms:
# [propext, Classical.choice, Quot.sound]
```

An initial auditor probe used the nonexistent class name `CertArith.CertArith` and exited 1;
correcting it to the existing `KAM.Certificate.CertArith` resolved that scratch-only error.
The final probe has only two tactic-style warnings in its own `convert` line. No audited
source was changed. Full axiom output follows.

```text
'KAM.EffectiveStability.fderiv_lagrangeMat_omega_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.lagrangeMat_eq_zero_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealX_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealU_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealV_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealPair_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealX_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealV_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealU_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_torusRealX_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_torusRealV_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusReal_lagrangian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realInclusion₂_realRestriction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusReal_frequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusReal_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_real_le_of_strip_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRealU_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.g1Hyps_standing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_mem_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_lagrangian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_realLagrangian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_frequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorusAt_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation, all four package modules:

```sh
$SCOPE nice -n 10 env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.EffectiveStability.TorusLagrangianCert \
  KAM.EffectiveStability.TorusLagrangian \
  KAM.EffectiveStability.TorusRealSlice \
  KAM.EffectiveStability.TorusProjection
# exit 0
```

```text
replaying KAM.EffectiveStability.TorusProjection
replaying KAM.EffectiveStability.TorusRealSlice
replaying KAM.EffectiveStability.TorusLagrangian
replaying KAM.EffectiveStability.TorusLagrangianCert
```

Additional static checks:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-b5lag KAM.EffectiveStability.TorusLagrangian \
  KAM.EffectiveStability.TorusRealSlice KAM.EffectiveStability.TorusProjection \
  KAM.EffectiveStability.TorusLagrangianCert
# exit 0: short-name check OK (no reused public short name)
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# exit 0: empty output
```

File sizes (all lines): TorusLagrangian 81; TorusRealSlice 184; TorusProjection 154;
TorusLagrangianCert 123. A Python scan of every line in these four files with
`len(line)>100` returned `[]`. Source review found no forbidden proof escapes or
resource-limit overrides. Every file has copyright, `module`, public imports, a module
docstring and `@[expose] public noncomputable section`.

## Source fidelity, deviations and remaining scope

No suspected mathematical defect in the reviewed design/source claims, no changed frozen
statement and no implementation deviation requiring repair was found. The narrower
real-only reference-derivative premise is a strengthening, not a lost conclusion.
The generic proof is not a minimal-assumption nonresonance theorem: it retains the allowed
Standing package. Consumers must retain that scope. The helper's pointwise hΩ premise is
not permitted as a replacement for the independently proved certificate Lagrangian theorem.

B5-CHART's matrix symmetry was checked algebraically against design item 2. This worktree
has no completed B5-CHART consumer to compile against; no claim is made about a future
chart's implementation or integration. Certificate periodicity and smoothness are obtained
by applying the general lemmas to hT's holomorphy, primary and real fields with hG.hρinf;
no additional certificate-only wrapper is required for those properties.

Only this report was added outside `.lake/abi-scratch/`. No git mutation, production
source edit, generated-root repair, application build or frozen/manifest edit was made.
The auditor scratch file is removed after validation. Audit workflow memory was used only
as a checklist; every package fact and receipt above was checked in this worktree.

## Repository lint

```sh
$SCOPE nice -n 10 env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted generated-root staleness. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4549 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.875s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The ABI receipt checks 314 core frozen declarations; the two opt-in KAMLunarBand
exports are checked only by file hash, exactly as the lint states. No opt-in library
was built and no claim of its kernel validation is made. No additional lint failure
was suppressed. The stale generated part is `KAM/Root/EffectiveStability.lean`;
regeneration remains the orchestrator's task under the audit brief.

Final status: **PASS WITH NOTES**, all four modules built and replayed, all 24 new theorem
axiom sets standard, no source repair requested. Remaining notes concern explicit premises,
strict strip loss, future consumer integration, and the allowed generated-root staleness.
