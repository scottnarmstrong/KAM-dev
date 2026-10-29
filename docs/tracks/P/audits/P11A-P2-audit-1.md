# P11A-P2 independent audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11ap2`.
Audited HEAD: `ca049e2c26ed76c462911470d14febf89cdff453`.
Reference `inp` at inspection: `d69dedecde7104870d7281ffe9dba51228f5e523`.

## Scope and verdict

**Overall verdict: PASS WITH NOTES for the delivered P11A-P2 infrastructure.**
The signed `total_chart` and delivered hc-rot suppliers pass; every delivered signed definition
matches. No blocking proof, premise, carrier, signature or hygiene defect was found. Notes concern
the expressly permitted stale generated root, minor module-documentation overstatements, and the
precise scope of blueprint-node coverage. There is no frozen theorem anchor to declare seal-ready.

The controlling scope is the **ORCHESTRATOR RULING (OVERNIGHT 20:40)** and **AUDIT FOCUS** in
`docs/tracks/P/audits/P11A-P2-handoff.md`. Only these three modules are audited:

- `KAM/Planetary/Preparation/Holomorphic.lean` (140 lines).
- `KAM/Planetary/Preparation/HolomorphicRotation.lean` (168 lines).
- `KAM/Planetary/Preparation/Polar.lean` (259 lines).

The user explicitly directs this report into the package worktree, overriding the generic brief's
main-worktree output instruction. No production source, frozen file, manifest or generated root was edited.
No frozen theorem anchor or provider export is delivered in this scope, so frozen/provider type equality
and frozen seal-body checks are not applicable. The signed infrastructure theorem is checked directly
against its design type instead; no campaign theorem sealing is claimed.

`git diff inp...HEAD` has eight new files, 1374 insertions. Git reports multiple merge bases and selects
`083f2668aee61b74c25c44b42fdb8cca87ac634a`; the other merge base is
`9a2d476a62964f40e17fda514f6e67c2ac24c074`. The full comparison was inspected. Five files
(BasePoint, Basic, Patch, PatchHessian, Working) belong to inherited P11A-P1, merged at `03ce0f0d`.
The corroborating `git diff 03ce0f0d..HEAD --stat` contains exactly the three scoped files and 567 insertions.
The inherited package is not independently recertified here.

Read authorities: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief, handoff,
track P statement conventions, P11A-LEAN-DESIGN node contracts and period-conversion requirement,
blueprint-P/parts/p11-cp09-preparation.tex:63–92, and the consumed frozen definitions.
Canonical signature artifact:
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA-256
`627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee`.

## Declaration and node findings

Names below are in `KAM.Planetary`; locators are relative to `KAM/Planetary/Preparation/`.
PASS here means fidelity and correctness of the delivered declaration, not closure of an entire
blueprint node where that node includes separately assigned construction or transport.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| holo-chart signature carrier | `p11WorkingDom`, Holomorphic:32 | PASS | Exact signed definition: fast angle strip, action ball, two slow Cartesian balls, Pi max norms. |
| holo-chart data | `P11SecularData`, Holomorphic:38 | PASS | Exact signed structure, same field order and types; data only, with no assumed construction or proof fields. |
| hc-lift input expression | `p11ChartInput`, Holomorphic:58 | PASS | Exact signed formula: `L=J/(2π)`, fast angle `2πθ` plus the derivative correction, and the rotated slow momenta/positions in frozen `assemble` order. |
| working Hamiltonian | `p11WorkingH`, Holomorphic:68 | PASS | Literal `h(J)+eps*F(z)` on the entire complex phase carrier. |
| hc-mean signature object | `p11FastMean`, Holomorphic:70 | PASS | Literal existing unit-cube `torusAverage` in fast angles; no changed normalization. |
| holo-chart specification | `P11SecularSpec`, Holomorphic:73 | PASS | Every signed clause, quantifier, constant, radius and carrier preserved, modulo line wrapping. A proposition defining the desired specification, not an assumed theorem. |
| holo-chart full specification | `P11SecularFullSpec`, Holomorphic:131 | PASS | Exact conjunction with the explicit Euclidean frequency bound. No ambient norm substitution. |
| total-chart complex formula | `p11PolarC`, Polar:33 | PASS | Exact principal-complex-root formula and canonical period-one trigonometric arguments, with fast coordinates unchanged. |
| total-chart real formula | `p11PolarR`, Polar:40 | PASS | Exact real restriction of that formula, with no independently substituted polar chart. |
| tc-polar period conversion | `p11PolarScaleL`, Polar:103 | PASS | Genuine linear map, multiplying slow angles by `2π` and slow actions by its inverse on every input. |
| tc-polar continuous conversion | `p11PolarScale`, Polar:115 | PASS | Continuous-linear realization of the same linear map, not a replacement function. |
| tc-polar identification | `p11PolarR_eq`, Polar:164 | PASS | Proves equality to the established `polarMap` on every point with positive slow actions. The sole premise is the natural chart-domain condition. |
| bpP:p11:total-chart / tc-polar / polar tc-lat | `total_chart`, Polar:193 | PASS | Exact signed theorem: real analyticity, symplectic multiplier 1, slow integer periodicity, and equality only modulo that same lattice. No extra dimension, fast-action, or chart hypothesis. |
| hc-rot extension supplier | `p11_rotation_complex`, HolomorphicRotation:32 | PASS | From real entrywise analyticity and real orthogonality, constructs positive `t2≤t1`, full/entrywise complex differentiability, real agreement, and complex orthogonality. No extension or complex matrix identity is assumed. |
| hc-rot bound supplier | `p11_rotation_bounds`, HolomorphicRotation:99 | PASS | Given `r<t2` and entrywise holomorphy, proves fixed `B,B′≥1` bounding the row sums of `rho` and `rhoᵀ∂_l rho`, uniformly in the smaller ball. |

The seven signed Holomorphic declarations, the two signed polar definitions, and the `total_chart`
header match the canonical signature after removing comments and whitespace. The structure comparison
includes every field. A fresh Lean probe additionally copies all eight signed definition bodies and
proves equality to the installed definitions by `rfl`, and copies the `total_chart` header under a fresh
name with body `by exact KAM.Planetary.total_chart`, followed by a `type_of%` check. No draft module
containing placeholder proofs is imported.

## Definition classification and proof review

All new definitions/structures are accounted for in the table. The only additional private definition,
`polTrans` (Polar:45), is the literal translation vector `(0, Fin.append c 0)` for fast momenta.
There is no conditional default, chosen solver, fabricated chart, or altered source object.

`p11PolarC` is a total expression using the standard principal complex square root. The physical polar
interpretation and analyticity are asserted only when every slow action is positive. No smoothness
across the branch cut or at zero is claimed. `p11PolarR` remains exactly its real restriction outside
that domain as well. The signed derivative and integral expressions (`p11ChartInput`, `p11FastMean`)
use Mathlib's ordinary total `fderiv` and Bochner integral; the file introduces no extra fallback and
proves no geometric or averaging property from unguarded off-domain values. Raw `P11SecularData`
can be arbitrary data; only the separately defined specification constrains it. Its existence is not
smuggled into a structure field, instance or theorem premise.

The polar proof's key extension from Part 7 is legitimate. Part 7's `polarDom` also constrains fast
actions; `exists_trans` chooses one common fast-action translation putting either one or two given
positive-slow-action points into that domain. `polarMap_add_trans` proves exact commutation with this
translation. Thus analyticity and the derivative identity transfer back to the whole positive-slow-action
set, and the quotient-injectivity proof can use a common translation and cancel it. The derivative
chain rule is justified by actual analyticity and a neighborhood equality on the open positive set,
not by the total derivative's value at a nondifferentiable point. The linear conversion is directly
proved symplectic for the frozen momentum-first form: its reciprocal scaling factors cancel.
The periodicity proof converts slow integer shifts to the established `2π` lattice; quotient
injectivity recovers unchanged fast angles/actions and integer differences of slow angles.
This works for all `n`, including the empty-coordinate case; it is stronger than requiring physical `n≥2`.

For rotation extension, each entry is complexified using the existing P0 supplier. Finiteness of the
entry set gives a common positive radius, also bounded by `t1`. The real-slice identity theorem is
applied entrywise to `sum_k rho[k,i]*rho[k,j]-delta[i,j]`; the real orthogonality premise supplies its
real zeros. This is transpose orthogonality, not Hermitian unitarity, and no complex isometry bound
is inferred. Real agreement retains any SO(n) property of a future chosen real rotation; these
building blocks do not themselves select that rotation or prove a determinant clause.

For the bounds, a closed ball of radius `r` is compact and contained in the open holomorphy ball
by the strict premise `r<t2`. Finite-dimensional holomorphy supplies continuous derivatives there.
Bounds for finite sums of all absolute entries and all derivative entries dominate each requested
row sum, and `max 1 b` supplies the required lower normalizations. The result is slightly more general
than a positive-radius application: if `r<0`, the asserted target ball is empty, so no bad value is used.
The constants may depend on the fixed rotation, center and radii, exactly as required; they do not
depend on the later evaluation point, row, or derivative direction.

The locally scoped `Matrix.Norms.Elementwise` is confined to the bounds theorem; both its advertised
bounds and the corresponding specification are sums of scalar complex norms. There is no global
matrix norm change or harmful root shadow. Every public declaration name has a single declaration
site in KAM; short general helper names in Polar are private.

## Scope notes, uncertainties, errata and deviations

The full blueprint `bpP:p11:total-chart` at p11-cp09-preparation.tex:87 also says
“Consequently ... the chart Xi_0 := Psi_c composed with the polar chart satisfies (Q1)--(Q2)”.
Its `tc-lat` proof at line 91 concerns this physical composite. The signed `total_chart` covers the
preceding polar statement; `total_chart_transport` is the designated companion for the consequence.
Under the explicit split ruling this is a scope boundary, not a missing-delivery finding. Similarly,
`hc-rot` selection of the physical SO(n) rotation, its eigenvalue data, and the radius assembly are
not proved by the two general suppliers and must not be marked closed by this audit.

`holo_chart`, hc-lift through hc-mean construction, and `total_chart_transport` belong to P2b..P2f.
Their absence is expressly not a finding in this audit. The Holomorphic module docstring (lines 17–23)
and Polar docstring (lines 14–15) still describe `holo_chart`/`total_chart_transport` as if present in
these modules. This is a minor documentation overstatement after the split, with no proof/API effect.
The handoff/ruling correctly states their actual absence.

No suspected defect in a pinned mathematical source or blueprint formula was found in the delivered
scope. No mathematical statement or carrier deviation was introduced. This audit makes no new
external-paper claim; the formal source of comparison is the supplied blueprint and signature.

## Independent validation

All audit Lean/Lake/checker invocations were serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`. The build wrapper itself invokes `nice -n 5 lake build`; lint's ABI subprocess
inherits the environment and niceness. No library-wide build or cache operation was requested.

Targeted build, exit **0**:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap2 KAM.Planetary.Preparation.Polar KAM.Planetary.Preparation.HolomorphicRotation KAM.Planetary.Preparation.Holomorphic
```

Decisive output (inherited replay warnings omitted):

```text
[inp-gate] slot 3 acquired 21:18:02 for KAM.Planetary.Preparation.Polar KAM.Planetary.Preparation.HolomorphicRotation KAM.Planetary.Preparation.Holomorphic
Build completed successfully (9245 jobs).
```

The replay warnings were existing unused-variable/unused-simp, deprecation and style notices
in dependency modules. The targeted build had no elaboration errors or resource-budget changes.

Exact-body/type and axiom probe, final exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11P2Audit.lean
```

```text
'KAM.Planetary.total_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rotation_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rotation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
KAM.Planetary.p11PolarScaleL {n : ℕ} : Phase (n + n) →ₗ[ℝ] Phase (n + n)
KAM.Planetary.p11PolarScale {n : ℕ} : Phase (n + n) →L[ℝ] Phase (n + n)
```

These are all four new public theorems. No `sorryAx` occurs. The earlier scratch-only attempt
exited 1 because the extraction mistook `let O :=` for the theorem's proof delimiter and
therefore generated an incomplete type. Its recovery warning about `sorry` was confined to
that invalid scratch declaration. The corrected extraction compares the full theorem header,
including the let-bound domain and all four conjuncts, and the clean rerun above passed.
No production file was changed to fix the scratch probe.

Kernel replay, one invocation, exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Polar KAM.Planetary.Preparation.HolomorphicRotation KAM.Planetary.Preparation.Holomorphic
```

Exact output:

```text
replaying KAM.Planetary.Preparation.Holomorphic
replaying KAM.Planetary.Preparation.HolomorphicRotation
replaying KAM.Planetary.Preparation.Polar
```

Source lint, exit **1 solely for the permitted generated-root diagnostic**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (926 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint diagnostic occurred. The brief explicitly permits this stale-root line and forbids
editing the generated root; therefore it is a recorded exception, not an unqualified lint exit-0 claim.

Additional static/import checks:

- All 199 modules in the recursively computed KAM import closure were inspected for import
  boundaries. Its 58 frozen modules are definitions, all manifest state `SEALED`; there is
  no imported frozen theorem, `DRAFT_SORRY` anchor, or provider. Production quarantine holds.
- No forbidden proof escape, resource override or `EuclideanSpace` appears in the three files.
- Each file has copyright, `module`, public imports, a module docstring and
  `@[expose] public noncomputable section`; definitions can unfold as required.
- Maximum line lengths are respectively 99, 96, 100 Unicode characters; file lengths are
  respectively 140, 168, 259, below 1500.
- Repository declaration searches find one declaration site for each of the 15 public names.
  All scoped declarations are under `KAM.Planetary`; general short helpers are private.
- `git diff --check inp...HEAD` and `git diff --check` exit 0, with no whitespace findings.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with empty diff.
  The only accompanying stderr is the documented multiple-merge-base warning. The generated
  root was not regenerated.


## Source identity and final integrity

```text
e0af5ed534361c57cc3496601d667705c66295e9a7979e667904da4094074a47  Holomorphic.lean
163a893e6ce207c4814f800bbc57b90889461e12ea0703a229c406e3fa828e24  HolomorphicRotation.lean
f8018163e1baebc61b90d95401f8900bf1ad6f3e39ab3c3973586aae236a52b4  Polar.lean
```

After validation, `.lake/abi-scratch/P11P2Audit.lean` and the audit-created import-list scratch
file were removed. Final `git status --short` contains only the pre-existing untracked handoff
and this new report. Final `git diff --check` and protected-path comparison are clean (apart from
the documented Git merge-base warning); audited source hashes above were rechecked unchanged.
The report has no trailing whitespace and is at the exact absolute path requested by the user.
No git state-changing command was run.
