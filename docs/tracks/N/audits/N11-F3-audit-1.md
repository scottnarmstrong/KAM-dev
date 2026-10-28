# N11-F3 independent package audit 1

Overall verdict: **PASS WITH NOTES** for N11-F3 (`bpN:p11:hom`). The two signed
declarations match exactly, the assigned slice is complete, and no proof or
statement-fidelity failure was found. The notes concern inherited build/lint
diagnostics only. This package supplies infrastructure; it neither implements
nor seals the frozen `partialConvex_nekhoroshev` anchor.

## Scope and inputs

Audited only `KAM/Nekhoroshev/Partial/Homological.lean`, at HEAD
`7eab48194248ab4325c53cd65aab9c57298d1e05`, against `inp` at
`d343cead359c794f416340f529531719f7b449d2`.
`git diff inp...HEAD` contains precisely this new 172-line module.
The pre-existing untracked handoff is preserved.

Read AGENTS.md, PLAN.md, DECISIONS.md, the external package-audit brief, the
N11-F3 handoff and its AUDIT FOCUS, the N11 design and both design audits,
the delivered signatures, the Part-11 homological proposition and graph
contract, the track-N partial-convex statement and frozen anchor, and the
relevant carrier, analytic-class, weighted-bound and Part-6 definitions/proofs.
The user's exact worktree report destination overrides the generic brief's
main-worktree destination. No subagents, source edits or state-changing git
commands were used. All audit Lean/Lake commands were serialized with
`LEAN_NUM_THREADS=1` and `nice -n 5` (the build gate supplies `nice`).

Input SHA-256:

| Input | SHA-256 |
|---|---|
| Audited Lean file | `15f68d6bdf60edf722792f88d1e1f3b8caee5b81404d741072a12c4c21d925f3` |
| `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| `docs/tracks/N/design/N11-LEAN-DESIGN.md` | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |

The last two pins agree with design audit 2. Audit 1's unrelated design
failures were repaired there; its `hom` row already passed. Neither design
audit is treated as evidence that the present proof compiles.

## Declaration and node ledger

Names below are in `KAM.Nekhoroshev`. Line numbers refer to the audited module.

| Node / role | Declaration | Verdict | Evidence |
|---|---|---|---|
| `bpN:p11:hom`, generator | `homGenerator` (31) | PASS | Signature and literal body equal delivered signatures L320–322; exact specialization of `homGenParam`. |
| `bpN:p11:hom`, full conclusion | `hom` (111) | PASS | Signature equals delivered signatures L324–342; fresh copied-statement application elaborates. All graph conclusions exported. |
| Private domain bridge | `fastAction_mem_polyNbhd` (35) | PASS | Projects an actual witness of the block tube to the singleton fast tube using the max norm; no nonemptiness assumption or new radius loss. |
| Private derivative bridge | `fderiv_liftFast` (47) | PASS | Chain rule through an explicit continuous linear projection, guarded by differentiability of h at the actual fast action. |
| Private coordinate identity | `fastAction_single_slow` (61) | PASS | Slow coordinate directions project to zero. |
| Private coordinate identity | `fastAction_single_fast` (71) | PASS | Fast coordinate directions project to the corresponding basis vector. |
| Private bracket bridge | `wfield_liftFast` (78) | PASS | Field is exactly `(freq h (fastAction z), 0)`; slow weighted terms vanish for every c. |
| Private linear algebra | `fderiv_eq_sum` (101) | PASS | Expands the actual linear derivative on `(v,0)` in the finite fast basis. |
| Frozen root, context only | `partialConvex_nekhoroshev` | NOT A SEAL AUDIT | No provider export is added by F3. Frozen-type and seal-body probes are inapplicable to this infrastructure-only slice. |

Design node inventory L210 and package row L357 assign only `bpN:p11:hom`
to Homological. There are no additional graph nodes or unsigned public exports
in this file. The contract at `docs/graph/N/DEPGRAPH.md:16260` and
`blueprint-N/parts/p11b-partial-nf.tex:119–124` is fully covered: both class
memberships, the extended bracket equation, the two projection/truncation
bounds, generator bound, zero resonant projection and conditional reality.
The Fourier formula is the literal definition of `homGenerator`.

The bound U generalizes using the exact norm as the bound: `WBound` includes
summability and an upper bound, so no unguarded infinite norm is used.
The factors are precisely `q*U/(2*pi*alpha)`, with `abar=2*pi*alpha` as in
blueprint L117. Positive R,s,alpha and q>=1 are the signed source/typing data;
no fast/slow dimension restriction, slow-loss inequality, frequency upper
bound or conclusion-shaped hypothesis is added. hR and hU are unused in the
proof, but retained exactly as signed.

## Proof and definition review

`homological_param` at `NormalForm/Homological.lean:342` is applied with
m=n+(k+k), D=b.base, r=R, delta=U and
omega(J)=freq h (fast projection J). Its premises are proved on the actual
extended tube: fast projection preserves the radius, holomorphic h has
holomorphic derivative on the open fast tube, and the supplied literal
`DivisorBound` transfers along that projection. The canonical equal-dimension
homological theorem is not used. No fresh divisor theorem is required since
the signed theorem already takes the direct divisor bound.

The returned c2/c1 supply the resonant/generator classes, c7/c8/c9 the three
bounds, and c4 the directional equation. The private field and linearity
identities turn c4 into the required `extBracket` equation with the correct
sign and no slow contribution. The coefficient-zero clause c5 proves
`projMode Lambda phi=0` term by term, including modes outside Lambda through
the indicator. Conditional reality transfers the real fast-frequency premise
to real extended parameters and uses c10 with the outputs reordered. This
retains the indispensable real-frequency guard; it does not infer reality
from holomorphy alone. The additional upstream support and resonant-projection
identity clauses are not needed for any remaining conclusion of this node.

**Definition classification:** the sole new definition is `homGenerator`.
It is an exposed, noncomputable literal Fourier-generator wrapper on the whole
EC carrier. There are no new structures, abbreviations, instances, fallback
branches or replacement analytic objects. Its total complex division is
exactly the prescribed formula; on the theorem's domain every active divisor
is nonzero because alpha/q>0. The active mode set is finite. No theorem relies
on an off-domain division or divergent-series fallback.

The 69-module KAM import closure contains no provider and no frozen theorem.
Its 21 frozen imports are all manifest `SEALED` definitions. The new public
names occur only here in production KAM sources, are namespace-qualified and
do not reuse public helper short names or create root shadowing. Private
helpers do not extend the public interface.

## Fresh validation

Mechanical comparison extracted the two signed declarations from the external
signature file and compared them with the implementation (excluding only the
theorem proof body):

```text
homGenerator EXACT signed text/body match: True
hom EXACT signed text/body match: True
lines: 172 max Unicode line: 100
```

1. Targeted gated build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11f3 KAM.Nekhoroshev.Partial.Homological
   ```

   Exit 0. Gate: `[inp-gate] slot 2 acquired 19:54:08`.
   Final output: `Build completed successfully (3223 jobs).`
   The replayed dependency `KAM.Nekhoroshev.Stability.Gradient` warned at
   `168:5` that `hgr` is not explicitly referenced. No audited-file warning.

2. Temporary exact-signature/body and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11F3Audit.lean
   ```

   Exit 0, no warnings. The probe copied the signed generator under a fresh
   name and checked function equality by rfl; it copied the full signed hom
   statement under an anonymous example and applied
   `hom b h f hR hs hK halpha hq Lambda hh hdiv hU hf hb` (using the original
   Unicode binder names in the actual probe). No placeholder proofs.

   Exact axiom output:

   ```text
   'KAM.Nekhoroshev.hom' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.homGenerator' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Homological
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Nekhoroshev.Partial.Homological
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the explicitly permitted stale generated root. Complete
   output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (903 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated file was regenerated. The lint ABI subprocess inherits the
   single-thread environment and niceness; it ran after the kernel invocation
   completed. No unrelated Lean command ran concurrently within this audit.

## Findings, limitations and closeout

No new suspected source/blueprint defect, deviation, hidden premise or unpaid
inequality was found in this slice. Blueprint L120 explicitly says the reality
clause is false without real omega; the implementation preserves that guard.
Existing design notes about the adjoint proof locator and open-ball endpoint
belong to other packages and are not exercised here. No pinned-PDF re-audit or
claim of full partial-convex theorem closure is made.

Protected-path comparison
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
`git diff --check` passes. No resource-budget overrides, forbidden proof escapes,
EuclideanSpace, file-size or 100-character-line violation occurs in the audited
file; copyright, module declaration, public imports, module docstring and
exposed public noncomputable section are present.


Final artifact checks: the report's whitespace check produced no diagnostics;
its `git diff --no-index --check /dev/null <report>` exit 1 represents the new
file difference. `git diff --check` exits 0. Auditor-created probe and log files
in `.lake/abi-scratch/` were deleted after recording results. Only this report
is a persistent auditor edit. The pre-existing handoff remains untouched.
