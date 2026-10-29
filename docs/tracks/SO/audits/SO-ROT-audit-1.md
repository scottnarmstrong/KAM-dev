# SO-ROT independent audit 1

Overall verdict: **PASS WITH NOTES**. The complete signed SO-ROT slice passes statement,
definition, proof, naming, and kernel checks. The note is the explicitly permitted stale generated
`KAM.lean`; it remains untouched. There is no frozen theorem anchor or provider in this package,
so anchor type/seal-body probes are not applicable. This verdict approves this infrastructure
slice; it does not assert the lunar certificate or confinement theorem has been proved.

## Scope and authority

Audited on 2026-10-29 in `/root/code/KAM-inp-sorot`, HEAD
`4fedb4218230e02a739fc45cedb82c17c970d902`, against `inp`
`074bd0c53603bf8359098c8ae887756ead170f09` using the full `git diff inp...HEAD`.
That diff consists solely of the new, 156-line `KAM/SpinOrbit/Rotated.lean`.
The pre-existing untracked `docs/tracks/SO/audits/SO-ROT-handoff.md` was read and left untouched.
Only this report is a repository edit by the auditor. Temporary probes were confined to
`.lake/abi-scratch/` and deleted after verification. No state-changing git command was used.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the handoff including AUDIT FOCUS.
The user's exact report destination overrides the generic brief's main-worktree destination.
The SO-specific scope overrides the generic I/N/P anchor list: audit only `Rotated.lean`.
The governing SO statements are owner ruling O5 and Revision 5 design rows O5/frame and O5/H',
§6, module/package tables (design lines 75–76, 428–442, 537, 572), and Appendix A-L §I.2.
There is no local `docs/tracks/SO/statement.md`; the handoff identifies the external signed design
and signature file as the authority for this slice.

Inputs pinned by SHA-256:

- `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean`, §I.2, lines 245–312:
  `9eafc5968a3dd2aa9257d5fc48be9886c6ca2ae5c2c72c2d63514fae02f68a7e`.
- `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`:
  `9b53ffc81a9af6d56042d89a9de4e733c27cc281f182b8be3e82ec1c09245657`.
- `KAM/SpinOrbit/Rotated.lean`:
  `10a50294d42f366b5d5cd784ead527757d04f9c20b67ea21e19f7f19bfca6397`.

## Declaration-by-declaration verdicts

Every name below is fully qualified by **`KAM.SpinOrbit.`**, including
`KAM.SpinOrbit.invarianceError_const_mul` (not `KAM.invarianceError_const_mul`).
The namespace agrees with the signed file's namespace at line 237.
All 14 signed declarations are present; the remaining five are proved auxiliary theorems.
All signed headers match exactly after whitespace normalization, with unchanged explicit/implicit
binders, premises, carriers, constants, and conclusions. All five signed definition bodies also
match exactly after whitespace normalization. Nine signed theorem examples copied the expected
headers and closed by applying the actual export to precisely its explicit binders in order.
Five fresh copies of signed definitions were checked equal to the actual definitions by `rfl`.

| Node | Lean declaration (prefix above) | File line | Verdict | Reason |
|---|---|---:|---|---|
| §I.2 map | `soRotMap` | 31 | PASS | Exact rotated-to-original shear on all complex phase points. |
| §I.2 inverse | `soRotMapInv` | 35 | PASS | Exact inverse shear on the same carrier. |
| §I.2 left inverse | `soRotMapInv_soRotMap` | 38 | PASS | Unconditional identity for every phase point. |
| §I.2 right inverse | `soRotMap_soRotMapInv` | 41 | PASS | Unconditional identity in the other direction. |
| §I.2 symplectic | `soRotMap_symplectic` | 46 | PASS | Preserves the signed canonical alternating pairing for all u,v. |
| §I.2 Hamiltonian | `soRotHC` | 54 | PASS | Exactly `soHC (soRotMap z)`. |
| Auxiliary linearity | `soRotMap_add_smul` | 56 | PASS | Proves linearity along arbitrary complex directions; no premises. |
| Auxiliary regularity | `soRotMap_differentiable` | 60 | PASS | Proves complex differentiability everywhere. |
| Auxiliary regularity | `soRotHC_differentiable` | 64 | PASS | Proves differentiability of the actual composition. |
| Auxiliary chain rule | `fderiv_soRotHC_apply` | 67 | PASS | Full differential identity, using proved differentiability. |
| §I.2 vector field | `hamiltonianVectorFieldℂ_soRotHC` | 76 | PASS | Exact inverse-map conjugacy, with frozen vector-field convention. |
| §I.2 expression | `soRotHamExpr` | 86 | PASS | Exact signed division-free expression and rational coefficients. |
| Auxiliary modes | `soRotHamExpr_foldr` | 93 | PASS | Mode identity for every list of natural indices; stronger than range-7 use. |
| §I.2 evaluation | `soRotHamExpr_eval` | 110 | PASS | Equality to the landed `soHC` composition on the entire carrier. |
| §I.2 clock | `soRotHamExpr_clock` | 117 | PASS | Derivative in `phaseBasis (.inr 1)` is exactly one. |
| §I.2 scaled expression | `soRotHamExprScaled` | 124 | PASS | Exact multiplication by an arbitrary rational c. |
| §I.2 scaled evaluation | `soRotHamExprScaled_eval` | 126 | PASS | Exact evaluation for every rational c, including zero. |
| §I.2 scaled clock | `soRotHamExprScaled_clock` | 130 | PASS | Clock derivative exactly c, with no extra premise. |
| §I.2 time scaling | `invarianceError_const_mul` | 140 | PASS | Exactly signed general n,H,K,ω,θ statement with only `c ≠ 0`. |

## Definitions and attempted refutations

The only new definitions are `soRotMap`, `soRotMapInv`, `soRotHC`, `soRotHamExpr`, and
`soRotHamExprScaled`. There are no new abbreviations, structures, instances, or bundled assumptions.
All five are intended objects on their whole stated carriers, exposed by the public noncomputable
section. None uses a junk value, conditional fallback, hidden field, or restricted-domain encoding.

The map sends `(Q0,Q1,P0,P1)` to `(Q0+Q1,Q1,P0,P1-P0)` and its inverse sends
`(q,phi,p,J)` to `(q-phi,phi,p,p+J)`. Direct expansion gives A-transpose B = identity;
the two inverse proofs and the alternating-pairing proof establish these identities without
analytic assumptions. An extra scratch `rfl` probe checked the physical projection exactly:
`((soRotMap z).1 0, (soRotMap z).2 0, (soRotMap z).1 1) =
(z.1 0 + z.1 1, z.2 0, z.1 1)`.
Thus momentum is precisely P0 and the physical q,phi projection is exact. The downstream
barrier wrapper and final confinement theorem are outside this slice.

For list index j = 0,...,6, the physical harmonic index is m = j+1. Substitution into
`2q - m phi` gives `2Q0 + (2-m)Q1 = 2Q0 + (1-j)Q1`, exactly the stored mode
`[2, 1 - (j : ℤ)]`. The j=1 (physical m=2) mode is independent of Q1.
The kinetic/clock part becomes `P1 + P0²/2 - P0`. Evaluation is proved against the
landed `soHamExpr_eval` and `soHC`, rather than an unrelated Hamiltonian definition.
The direction `.inr 1` changes P1, so its derivative is one, and c after rational scaling.

For the general scaling theorem, the frozen definition is
`invarianceError H K ω θ = X_H(K θ) - fderiv ℂ K θ (ofReal ∘ ω)`.
The missing differentiability premise is sound: nonzero complex scalar multiplication is
invertible, and `fderiv_const_smul_of_invertible` respects the totalized derivative even
when H is not differentiable. The temporary `Invertible` instance is constructed from
`hc`, not assumed. Linearity of the continuous linear map `fderiv ℂ K θ` handles arbitrary K.
The inverse frequency scaling and sign agree exactly with the frozen definition.
There are no conclusion-shaped hypotheses or assumed hard proof steps.

## Independent checks

Every Lean/Lake invocation was serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`;
the build used the required gate. Lint's ABI subprocess inherited these settings and ran
after the other Lean processes finished. No dependency cache, frozen file, generated root,
manifest, or source file was modified.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sorot KAM.SpinOrbit.Rotated
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 15:09:23 for KAM.SpinOrbit.Rotated
⚠ [2896/2912] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2912 jobs).
```

The omitted warning hint suggests renaming/removing the imported module's unused binder.
No warning was emitted from `Rotated.lean`.

### Signed probes and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SORotAudit.lean
```

Final exit 0, all 14 signature/body comparisons and the physical projection probe passed.
The scratch file imported only `KAM.SpinOrbit.Rotated`, opened `KAM KAM.Certificate`, and
used a `noncomputable section` and namespace `KAM.SpinOrbit`. Its examples copied the signed
headers verbatim and used `exact <export> <explicit binders>`; its five copied definitions
were named `auditExpected_<name>` and compared by `rfl`. An initial scratch-only attempt
omitted `noncomputable section` and exited 1 for its copied `soRotHC`; adding the same section
as the production file corrected the probe. No package change was necessary.

Exact axiom output from the successful invocation:

```text
'KAM.SpinOrbit.soRotMapInv_soRotMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_soRotMapInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHC_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_soRotHC_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hamiltonianVectorFieldℂ_soRotHC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExpr_foldr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExpr_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExprScaled_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExprScaled_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.invarianceError_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Rotated
```

Exit 0. Exact output:

```text
replaying KAM.SpinOrbit.Rotated
```

This single invocation covers the only new module; there are no separate provider or lemma modules.

### Naming, imports, size, protected paths

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sorot KAM.SpinOrbit.Rotated
```

Exit 0: `short-name check OK (no reused public short name)`.
This checks other KAM declarations, pending package branches, and Mathlib short names
(with the tool's stated signed-design exemptions). All declarations are in `KAM.SpinOrbit`;
there is no root declaration, alias, namespace redirection, or harmful root shadow.

A recursive source import scan found 42 KAM modules, no provider imports, and no frozen theorem
imports, hence no DRAFT_SORRY dependency. Frozen imports are definitions only, including the
actual `InvarianceError` and `HamiltonianVectorFieldC` definitions read during this audit.
No imported frozen theorem manifest-state exception is needed.

The source has 156 total lines and maximum line length 100 Unicode characters. Copyright,
`module`, public interface imports, module docstring, and exposed public section are present.
The slice token scan found none of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
`EuclideanSpace`, `native_decide`, or `set_option`; no resource-budget overrides occur.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with no output. The entire protected-path diff is empty.

### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1314 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the generated-root exception explicitly allowed by the audit brief.
The orchestrator must regenerate the root on integration. No substantive source lint,
module check, frozen-anchor guard, or ABI check failed.

## Uncertainties, source defects, deviations

No suspected pinned-source defect, blueprint contradiction, or introduced mathematical deviation
was found in the audited slice. No extra premise, weaker conclusion, changed constant dependence,
carrier substitution, or omitted signed declaration was found. Auxiliary lemmas have distinct names
and prove their steps rather than importing proof obligations as hypotheses.

This audit does not revisit the unrelated packed-product design contract F12/F13, certify
numerical data, prove the later rotated barrier wrapper, or seal any theorem anchor.
The physical projection checked here supplies exactly the coordinate identity those later
consumers require. The only integration note is the expected generated-root refresh.

Final disposition: **SO-ROT PASS WITH NOTES**, complete signed slice, with all independent
checks completed and the permitted generated-root exception recorded.
