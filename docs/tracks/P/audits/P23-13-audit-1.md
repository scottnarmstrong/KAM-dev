# P23-13 independent package audit 1

Overall verdict: **FAIL for the assigned full Revision 2 `osc_iter` contract**.
The implemented `oscStepMap`, `osc_flowHyp`, `osc_iter_core`, and `osc_fp_class`
pass their narrower definition/statement/proof checks. This is useful partial
infrastructure, but is not release-ready for P23-15. There is no frozen anchor or
provider export in this package, so no anchor is declared seal-ready.

## Scope and authority

Audited HEAD `71f22ef8b7085732b3bc049389030cc144652093` in
`/root/code/KAM-inp-p2313`. Read AGENTS.md, PLAN, DECISIONS, the package audit
brief, P23-13 handoff/AUDIT FOCUS, track-P statement/source records, Revision 2
of `docs/tracks/P/design/P23-LEAN-DESIGN.md`, both design audits, the shared
`/root/code/KAM-inp/.drafts/design/P23Signatures.lean`, and P2/N6 blueprint clauses.
The local `.drafts/design/P23Signatures.lean` is absent; the explicitly named
shared copy exists and matches the relevant design definitions/contract.

The handoff narrows the formal audit to `Averaging/OscillatorStep*.lean`;
the only match is `KAM/Planetary/Averaging/OscillatorStep.lean` (235 lines).
Its five new support modules were read as proof dependencies and included in
kernel replay; they are not represented here as a separate exhaustive declaration
fidelity audit. `OscillatorBracket.lean` is upstream P23-11, not a newly claimed
P23-13 implementation.

Both requested comparisons were made:

- `git diff inp...HEAD`: seven oscillator files, 2305 insertions. Git warns
  `multiple merge bases, using f390de8f741ebb8dab2d17ff12ec7f7e5b6d4f46`.
  The other merge base is `067d05299d279b03358836845306555c8d0b7d93`.
  `inp` was `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9` when inspected.
- `git diff inp-p2311...HEAD`: includes unrelated landed work (69 files), so
  the focus comparison was restricted to `OscillatorStep*.lean`. It yields
  exactly the same new 235-line file. `inp-p2311` was
  `f998421f9c4a627b9b0acadbf543334bcb4e1469`.

Only this report was edited in the source tree. Temporary probes were placed in
this worktree's `.lake/abi-scratch/` and removed. No state-changing git was used.
The user's exact report destination overrides the generic brief's MAIN-worktree
output instruction.

## F1 — Major: the required step contract remains incomplete

Authority: design L11, L18–20, row P23-13 L277, and Appendix A L781–838;
blueprint `blueprint-P/parts/p2-averaging.tex` L183–195 and inherited
`blueprint-N/parts/p6-normal-form.tex` L93–105. Design L20 explicitly says:
“P23-13 is not ready for that consumer until every conjunction of the revised
`osc_iter` is proved and audited.”

At `OscillatorStep.lean:69`, `osc_iter_core` omits the remainder class/bound
and the entire conditional reality clause. At L153, `osc_fp_class` recovers
exactly the missing class clause on V. Two obligations still have no theorem:

1. The weighted remainder inequality at design L825–827:

   ```text
   oscBound D (r-2ρ) (rp-2ρp) (rq-2ρq) (S-2σ) fp
     ((1 - 2*exp 1*(1+m)*δ/(2*π*α*d))⁻¹ *
       (2*(1+m)/(2*π*α*d)*(Rsum+δ) + exp(-(2*π*K*σ))) * δ)
   ```

   Here `d = min (ρ*σ) (ρp*ρq)` and `Rsum` is the exact weighted finite
   source decomposition in design L800–801. No iterated oscillator bracket,
   Lie-series/composition equality, integral remainder transfer, or proof
   of this estimate is exported by the focused module. The Hamiltonian
   identity is algebraic from the definition of fp; it supplies no bound.
2. Design L833–838: under reality of the original h, g and f, prove reality
   of φ and gp on the original domain, fp on V, and realness of Ψ on U.
   `OscFlowHyp.real_flow` needs reality of φ as input, so it does not by
   itself discharge this conditional contract.

`osc_iter` itself is absent. The handoff openly discloses both gaps; this
finding is a failure of full package completion, not an allegation that the
smaller theorems are false or that the handoff concealed their scope.
P23-15 cannot infer the contraction/remainder estimate or preserve the required
real iteration from these exports. The proposed follow-up size and numerical
ratio calculations in the handoff are not Lean proof receipts.

The required repair is to prove these clauses on the same explicitly defined
Ψ, gp and fp and assemble the full Revision 2 statement. No output-shaped
premise, renamed smaller result, or isotropic instantiation closes F1.

## Declaration and node verdicts

Names below are in `KAM.Planetary`. PASS for a helper applies to its stated
partial claim, not the full assigned node.

| Node / obligation | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Step map data | `oscStepMap`, Step L33 | PASS | Exact design definition; original flow domain O and time 1. |
| Flow source hypotheses | `osc_flowHyp`, Step L43 | PASS | Derives every bundled field from the original source premises; positivity and smallness are proved. |
| Partial `bpP:p2:osc-iter` | `osc_iter_core`, Step L69 | PASS WITH NOTES | Exact original premises and exact surviving clauses; full node incomplete (F1). |
| Remainder class | `osc_fp_class`, Step L153 | PASS | Exact fp expression, holomorphic and fast-periodic on V; stronger than the design projection because hn/hm are unnecessary. |
| `stepP:p2:oi-transfer` | Core and imported generator/flow helpers | PASS WITH NOTES | Parametric homological and arbitrary-gauge flow transfer implemented; oscillator Lie-series/composition transfer remains absent. |
| `stepP:p2:oi-ratio` | No corresponding proof in scope | FAIL | Required quantitative series estimate is not implemented. |
| `stepP:p2:oi-range` | `osc_flowHyp` proves only flow smallness | FAIL | Does not establish the shrunken-loss composition ratio/equality and transformed remainder estimate. |
| `stepP:p2:oi-disp` | Final core conjunct, Step L113–117, proof L139–150 | PASS | Four block estimates, exact constants, on U. |
| Full `bpP:p2:osc-iter` | Required `osc_iter` absent | FAIL | F1: remainder bound, conditional reality, and final assembly missing. |

A literal text comparison with the shared signature established that
`oscGen` and `oscStepMap` are exact matches. The whole `osc_iter_core` statement
is exactly the revised design theorem after renaming it, deleting only the
unused Rsum let, the fp class/bound conjuncts, and the final reality conjunct.
Thus it has no hidden extra premise, changed binder order, changed constant,
weaker domain for retained assertions, or wider constant dependence.

U is the three-halves-loss domain, O the single-loss flow domain, and V the
twice-loss domain. Holomorphy/maps-to, lattice law, symplecticity and displacement
are on U; injectivity, inverse and derivative estimate are on V; generator and
normal-form class/bound are on the original domain. Gauge displacement is u,
and the derivative estimate is 2u, as required. `osc_fp_class` obtains
V ⊆ U, maps Ψ(V) into the original domain, composes holomorphic functions,
and uses the exact same lattice-equivariant Ψ to prove fast periodicity.

The P23-11 oscillator estimates and canonical arbitrary-gauge flow results
are actual proof inputs. The homological bound comes via the generic
`homological_param` used in `OscillatorGen`, not by attempting to instantiate
N's full isotropic iterative theorem. The P23-05 direct wrapper itself is not
imported by Step; its underlying generic homological machinery is reused.
That is compatible with the planned proof route for the implemented clauses;
it supplies none of the missing anisotropic composition estimate.

## Definition classification and hypotheses

The only new definition in the focused module is `oscStepMap`: **intended
object on its whole carrier**, exactly the design's total time-one flow
construction. The inherited `Canonical.flow` chooses a solution on [-1,1]
when one exists, otherwise returns the initial point. This is the same
explicit flow used by the design. The proof invokes `SmallField` and gauge
interior results on U/V, where existence/uniqueness is proved; it does not
exploit the fallback to manufacture a displacement or inverse statement.
Outside the asserted domains no physical flow claim is made.

For dependency context, `oscGen` is the specified truncated Fourier
homological polynomial; `oscZero` is the literal zero Fourier coefficient;
`oscFreq` reads the action-frequency block; block scalings and `oscScale`
implement positive anisotropic linear equivalences; `fastShift` is the fast
integer-angle translation; `oscO` is the single-loss domain; `W` is the
same gauge equivalence; `blkθ`, `blkI`, `blkq`, `blkp` are coordinate projections.
`OscFlowHyp` bundles radius positivity, generator class/bound, nonnegative E,
and the smallness inequality. It contains no flow/remainder/realness conclusion.
Step constructs this bundle, rather than assuming the hard step.

The inherited oscillatory class is holomorphy and only fast-angle periodicity;
`oscBound` includes `WSummable` and an actual weighted Fourier sum bound at
each parameter, preventing a divergent-tsum default argument. Coordinate order
is `((θ,q),(I,p))`, flattened to `(θ,(I,p,q))`; ambient types remain finite Pi
spaces. Frozen field and coordinate definitions were checked without edits.

## Independent validation

The validation invocations recorded below were sequential, with
`LEAN_NUM_THREADS=1` and `nice -n 5` (the build gate supplies nice).
Process deviation: an initial lint launch omitted the explicit thread setting;
its later ABI subprocess was terminated, and lint was rerun with the required
environment and priority after the build. Its incomplete receipt is not used.
No overlapping Lean elaboration was observed in this worktree.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313 KAM.Planetary.Averaging.OscillatorStep
```

Exit 0; exact output:

```text
[inp-gate] slot 2 acquired 09:19:47 for KAM.Planetary.Averaging.OscillatorStep
Build completed successfully (9118 jobs).
```

The targeted dependency closure includes all five support modules; no root
build, cleanup, cache download, or package update was requested.

### Signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313Audit.lean
```

Exit 0. The probe independently copied both design definitions and checked
definitional equality by `rfl`. It copied the actual `osc_iter_core` and
`osc_fp_class` statements under fresh names, applying each export to exactly
its explicit binders in order. All three new public theorem axioms in the
focused module, plus both generator/zero-mode bounds, were printed:

```text
'KAM.Planetary.osc_flowHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_iter_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_fp_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscGen_class_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscZero_class_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The brief's provider/frozen `type_of%` and seal-body tests are **not applicable**:
no provider or frozen theorem anchor is implemented here. Passing a fresh-name
copy of the smaller theorem does not establish the full `osc_iter` type.

A negative applicability probe copied the full shared Revision 2 theorem under
`audit_full_osc_iter`, replacing its body with
`by exact osc_iter_core hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg`:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313FullContract.lean
```

Exit 1 as expected; diagnostic begins:

```text
.lake/abi-scratch/P2313FullContract.lean:64:2: error: Type mismatch
  osc_iter_core hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
has type
```

The remainder of the diagnostic prints the smaller conjunction and the full
expected conjunction including the missing remainder/reality clauses. This
confirms that the core cannot be used as the full design theorem; the failure
is not a failure to elaborate the implemented helpers.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorStep KAM.Planetary.Averaging.OscillatorGen KAM.Planetary.Averaging.OscillatorFlow KAM.Planetary.Averaging.OscillatorFlowMap KAM.Planetary.Averaging.OscillatorFlowProps KAM.Planetary.Averaging.OscillatorClassAlgebra
```

Exit 0; exact output:

```text
replaying KAM.Planetary.Averaging.OscillatorClassAlgebra
replaying KAM.Planetary.Averaging.OscillatorFlowProps
replaying KAM.Planetary.Averaging.OscillatorFlowMap
replaying KAM.Planetary.Averaging.OscillatorFlow
replaying KAM.Planetary.Averaging.OscillatorGen
replaying KAM.Planetary.Averaging.OscillatorStep
```

All six requested modules were replayed in one invocation.

### Source hygiene and imports

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted stale generated root; exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (496 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus lint is PASS WITH THE ALLOWED ROOT NOTE, not a literal zero exit.
The focused file has 235 lines, no lines over 100 Unicode characters, a
copyright header, `module`, public interface imports, module docstring and
`@[expose] public noncomputable section`. No forbidden proof escape or resource
override was found. L66 disables only `linter.unusedVariables` locally, not
heartbeats, recursion depth or synthesis budgets.

A recursive KAM import scan found 72 modules, no provider, and no frozen theorem
module. Its 12 frozen definition modules all have manifest state SEALED:
ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC,
IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm,
and Planetary Fast, Phase, Slow. No DRAFT_SORRY dependency is used.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD -- KAM/Planetary/Averaging/OscillatorStep.lean
git diff --check
```

All exit 0, with no diff/check output (the first two include Git's disclosed
multiple-merge-base warning). Protected paths are unchanged.

## Uncertainties, defects and deviations

No new suspected pinned-source erratum or false blueprint statement was found.
The relevant blueprint already discloses its oscillator extension as a source
gap at P2 L196: “the extension is stated by its (short) list of changes”.
This audit checked that obligation against the implementation; it did not
independently re-audit CP10's pinned PDF. F1 is an implementation gap, not a
new source erratum.

The Step docstring L20–22 and theorem comment L67–68 describe omitted fp
properties; the entire final reality clause is also absent, including reality
of φ, gp and Ψ. The handoff gives the more complete accounting. “Same hypotheses
and lets” at L68 is slightly imprecise: the unused Rsum let is deleted.
Neither wording changes the proved type, but downstream summaries should retain
the full gap list.

The six-module split is a reasonable disclosed implementation deviation from
the estimated single 700-line file; support file lengths are 242, 175, 149,
315 and 86, all below 1500. Splitting does not waive the full-contract gate.
No source/production change was made by this audit. Only the named report is
the audit deliverable. P23-15 remains blocked by F1.
