# SO-GRAPHR independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sographr`.
Audited HEAD: `c2bcc8ef43117354606bbd6dcdecad71159fd1eb`.
Comparison `inp`: `677cbecf7fde33eeabd06a7484d249c4758b65b9`.
Merge base: `4fedb4218230e02a739fc45cedb82c17c970d902`.
The live `inp` ref advanced during validation to
`b09cc13973973e2b5848066267c34d14e744eaba`. Final recheck of
`git diff inp...HEAD` still shows exactly the same sole 224-line module;
merge base and empty protected-path diff are unchanged, and diff whitespace
validation still exits 0.

## Verdict

**PASS WITH NOTES for SO-GRAPHR.** Both signed declarations pass exact statement,
proof, completeness, naming, and axiom review. The notes concern the permitted
generated-root lint exception and the implementation's local scaling helper.
There is no frozen theorem anchor or provider export in this package; this verdict
approves the scoped unfrozen helper slice, not a frozen seal or lunar certificate.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the supplied
`docs/tracks/SO/audits/SO-GRAPHR-handoff.md`, including AUDIT FOCUS. The user's exact
worktree report destination overrides the generic brief's main-worktree destination.
Reviewed the entire `git diff inp...HEAD`: the only committed change is the new
224-line `KAM/SpinOrbit/Graph/Rot.lean`. The handoff was already untracked.

Controlling statement/design evidence:

- `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean:411–452`, §I.5,
  with outer namespace `KAM.SpinOrbit` at line 237.
- `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`,
  Revision 6: O5 row at line 102, graph route at lines 537–549, dependency row
  at line 588, package row at line 623, signed declarations at lines 2426–2462.
- `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md:85–91`, owner ruling O5.
- Landed dependencies `KAM/SpinOrbit/Graph/Inverse.lean`,
  `KAM/SpinOrbit/Rotated.lean`, `KAM/SpinOrbit/Barrier.lean`,
  `KAM/Certificate/Clock.lean`, and the frozen strip, primary, real,
  Diophantine, invariance-error, and complex Hamiltonian-field definitions.

There is no local `docs/tracks/SO/statement.md` or SO blueprint in this checkout;
the handoff's exact external design and signature files specify this slice.
No I/N/P frozen theorem is claimed or changed.

## Declaration review

| Node / slice | Fully qualified declaration | Verdict | Reason |
|---|---|---|---|
| SO-GRAPHR shear | `KAM.SpinOrbit.SoGraph.torus_of_rot` (Rot.lean:32) | PASS | Signed header byte-identical; produces all eleven fields of the landed `SoGraph.Torus` with the original frequency `(ν,1)`, correct two periodicities, derivative and flow laws. |
| SO-GRAPHR local scaling helper | `KAM.SpinOrbit.isDiophantine_smul_scale` (Rot.lean:83) | PASS | Proves positive scaling with margin `s*γ`, directly from the defining inequality, for arbitrary `n,γ,τ`; no extra arithmetic or nonresonance premise. Unsigned helper with a distinct public name. |
| SO-GRAPHR barrier wrapper | `KAM.SpinOrbit.soBarrier_of_exact_rotTorus` (Rot.lean:103) | PASS | Signed header byte-identical, including all binders and conclusion. Constructs an original-flow `SoBarrier lo hi`; assumes neither a graph nor invariance of a graph. |

These are all three new public declarations. The two signed declarations assigned
to `Graph/Rot` are both present, with exactly the signed fully qualified names.
`SoGraphCert`, `checkSoGraph`, and certificate-to-barrier wrappers in the same
signature section belong to the later `Graph/Cert` slice, not SO-GRAPHR.

No new `def`, `abbrev`, `structure`, class, instance, or inductive type occurs.
Thus the new-definition classification is empty. Local `set`/`have` bindings are
explicit frequencies, coordinate functions, and proved facts, with no junk fallback.
In particular the conclusion uses the actual `SoBarrier` from Barrier.lean:33–40:
continuous doubly periodic graph, invariance under `soField` on `Set.univ`, and
the asserted lower and upper bounds.

## Soundness and original-flow attachment

1. Rot.lean:114–126 removes the positive rational time factor `c`, using
   `invarianceError_const_mul` and cancelling the nonzero complex scalar. The
   resulting frequency is `((c:ℝ)⁻¹*sinf) • ωstar`, with no assumption `c ≤ 1`.
2. Lines 127–138 scale the Diophantine margin to `(c:ℝ)⁻¹*γ > 0` and apply
   `clock_frequency` with the proved clock derivative of `H'`. They obtain clock
   frequency one and the real identity `Q₁(x,y)=y+c₀`.
3. Lines 139–212 extract real derivatives from the complex invariance equation
   and the proved conjugacy `X_H' = L⁻¹ X_H ∘ L`. For the local rotated frequency
   `ν=((c:ℝ)⁻¹*sinf)*ωstar 0`, these are `Q₀'=P₀-1` and
   `P₀'=-soVq(Q₀+y+c₀,y+c₀)` along `(x+t*ν,y+t)`.
4. `torus_of_rot`, instantiated with parameter `ν+1`, applies the shear
   `(x,y) ↦ (x-y,y)`. The reconstructed original angle is
   `Q(x,y)=Q₀(x-y,y)+y+c₀`, original momentum `P₀(x-y,y)`, and clock `y+c₀`.
   The angle derivative in time is `P₀`, spatial monotonicity is preserved,
   and integer shear plus primary equivariance gives the required periodicities.
5. Lines 213–220 package the landed core's continuous graph and
   `T.soGraph_invariant`, both periodicities, and `hlo/hhi` at the inverse
   coordinates. This is the same graph construction as `soBarrier_of_torus`,
   using its core directly. Inverse.lean:222 proves invariance under the original
   `soField` by ODE uniqueness for every applicable solution. Thus the wrapper
   gives the SO-CONF barrier, rather than merely a rotated graph or one orbit.

All hypotheses are the signed exact-torus regularity/equivariance/reality,
invariance, Diophantine, monotonicity, and momentum-range inputs. The wrapper
does not assume a KAM existence theorem's conclusion as an unexplained helper
field: its declared job is conversion of an already supplied exact torus.
Existence of that torus and transfer of certificate bounds remain downstream
client obligations, outside this slice.

The transitive KAM source-import scan found no provider and no frozen theorem
module. Its 17 frozen dependencies are definitions, each manifest state `SEALED`.
The six directly relevant frozen definitions listed above were read to check
their literal carriers and laws; no change of norm, law, or ambient space occurs.

## Independent validation

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and
`nice -n 5`; lint's ABI subprocess inherited those settings. No budget override,
clean, update, or cache download was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sographr KAM.SpinOrbit.Graph.Rot
```

Exit 0. Output ended:

```text
Build completed successfully (3209 jobs).
```

Replayed dependency warnings were at `KAM/ODE/Exit.lean:36`
(unused section variable) and `KAM/Certificate/Expr/Basic.lean:85`
(unused explicit variable). No warning originated in Rot.lean.

### Signature, body-application, and axiom probe

An independent Python comparison extracted each declaration from `theorem NAME`
through the text before `:=` in the live signed file and in Rot.lean:

```text
torus_of_rot: signed header byte-identical
soBarrier_of_exact_rotTorus: signed header byte-identical
```

The temporary `.lake/abi-scratch/SOGRAPHR_audit.lean` imported only the audited
module, copied both signed headers under fresh names in the same namespaces,
and filled them using exactly the implementation export applied to every
explicit binder, in order:

```lean
exact torus_of_rot hm hQc hPc hQ₀ hQ₁ hP₀ hP₁ hdQ hmono hflowQ hflowP
exact soBarrier_of_exact_rotTorus hc hρ hholo hprim hreal hinv hγ hdio hm hmono hlo hhi
```

It also elaborated `example : type_of% @<implementation> := @<fresh copy>`
for both declarations, and printed types and axioms of all three exports.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGRAPHR_audit.lean
```

Final run exit 0, no warnings or errors. The first scratch run failed because
the auditor omitted the signed `open SoGraph` context for `realPt`; restoring
that context fixed the probe. This was a scratch setup error, not a package
failure. No fallback proof from that failed run is used as evidence.

```text
'KAM.SpinOrbit.SoGraph.torus_of_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isDiophantine_smul_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_exact_rotTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Frozen/provider equality and actual anchor seal-body checks are inapplicable;
the analogous signed-statement/application probes above cover this package.
The scratch probe was removed after validation.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Rot
```

Exit 0; output:

```text
replaying KAM.SpinOrbit.Graph.Rot
```

This single invocation covers the only new theorem module, including the helper.

### Source, naming, and protected paths

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sographr KAM.SpinOrbit.Graph.Rot
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --exit-code -- KAM
```

All exit 0; short-name output:

```text
short-name check OK (no reused public short name)
```

Both protected-path and working-source diffs are empty. A separate source scan
using `scripts/check_lean_modules.py`'s comment/string mask compared all three
names with public declaration headers throughout other KAM files and Mathlib,
without a signed-name exemption:

```text
KAM public header collisions: []
.lake/packages/mathlib/Mathlib public header collisions: []
FORBIDDEN []
ROOT ESCAPES ['namespace KAM.SpinOrbit', 'namespace SoGraph']
```

No harmful root shadow or namespace escape was found. The module has the copyright,
`module`, two `public import`s, module docstring, and exposed public section.
It has 224 total lines and maximum line length 98 Unicode characters. No new
source contains `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`,
`EuclideanSpace`, or a resource override.

### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1315 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure was reported. `KAM.lean` was left untouched as required.

## Notes, errata, and scope limits

The implementation introduces `isDiophantine_smul_scale` instead of calling the
design narrative's `soIsDiophantine_smul` (design line 102; signed-file docstring
line 433). Their mathematical types agree up to names of arguments and theorem;
the latter is assigned to the separate frequency slice. No signed declaration
of SO-GRAPHR is renamed or omitted. The handoff's reference to the older
`isDiophantine_smul` needing `s ≥ 1` is accurate for
`KAM/Iso/Linear/Tools.lean:38`, but the current lunar signature already specifies
positive scaling with the scaled margin (`SOSignaturesLunar.lean:334–335`).
This is an implementation-route deviation, not a defect in a signed statement.

Likewise the wrapper constructs the graph from `T` directly instead of calling
`soBarrier_of_torus`; all fields are supplied from precisely that theorem's
landed core. Neither deviation adds a premise or weakens the conclusion.

No suspected mathematical defect in the pinned design, signatures, or frozen
definitions was found. No external source theorem is newly transcribed here;
this audit does not independently re-audit the landed clock, rotation, inverse,
or confinement packages. No repository source or manifest was edited by the
auditor. Only this report and the subsequently removed scratch probe were written.
