# N6-4 independent package audit 1

Overall verdict: **PASS** for N6-4 infrastructure (`bpN:p6:telescope`).
No frozen anchor is proved or sealed by this package; per-anchor seal verdicts and
provider/frozen ABI and seal-copy probes are **not applicable**. This is not a
claim of normal-form, track-N, or root closure.

## Scope and pinned evidence

Audited 2026-10-28, worktree `/root/code/KAM-inp-n64`, HEAD
`1258c595912a3b914d64e9c630e91dd60224111a`, compared with `inp`
`88983f74ff9952994d1de31d0ed671307437b563` using `git diff inp...HEAD`.
The sole committed change is the 130-line
`KAM/Nekhoroshev/NormalForm/Telescope.lean`.
SHA-256: `e8a2aedd37d19f32fd7eb1c5a47fde9cb3dc522c6612e49c12a71f987fd3942d`.
The pre-existing untracked `N6-4-handoff.md` was read and preserved.

Authority: supplied package brief and handoff AUDIT FOCUS; AGENTS.md,
`docs/PLAN.md`, `docs/DECISIONS.md`; track-N statement conventions;
`blueprint-N/parts/p6-normal-form.tex:148–153`;
`docs/tracks/N/design/PART67-LEAN-DESIGN.md` v2, N6-4 row (250),
proof plan (296–298), N4/N5 disposition (445–449), Appendix A.5 (829–853).
Read both `docs/tracks/N/design/DESIGN-N67-design-audit-{1,2}.md`,
particularly the openness convention and finite-sum proof correction.
The supplied `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean`
retains the documented SHA-256
`c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`.
No delegation or state-changing git commands; no source changes.
The user's exact worktree report destination overrides the brief's generic
instruction to write into the main inp worktree.

## Declaration ledger

| Node | Declaration (module line) | Verdict | Evidence |
|---|---|---|---|
| `bpN:p6:telescope` | `KAM.NormalForm.chain` (30) | PASS | Definition body byte-identical to design A.5; correct right-to-left application order, m+1 factors. |
| same, domain component | private `chain_mapsTo` (34) | PASS | Induction composes MapsTo with the final factor; all intermediate memberships have the correct indices. |
| same, displacement component | private `chain_disp` (45) | PASS | Splits displacement at Φ(m+1)z, applies the induction bound there, adds the last factor using the seminorm triangle inequality. |
| same, derivative component | private `chain_diff_sympl` (71) | PASS | Open source domains yield ordinary differentiability at both composition points; fderiv_comp followed by both form identities. |
| `bpN:p6:telescope` | `KAM.NormalForm.telescope` (105) | PASS | Signature byte-identical to v2; all four conjunctions proved. Injectivity uses InjOn.comp with the required MapsTo. |

Only `chain` and `telescope` are new public source declarations. Private helpers
were also inspected; their assumptions are precisely the relevant subsets of
the public statement's source data. No project assumption structure or instance
hides a proof obligation.

### Binder and conclusion fidelity

Let E = `(Fin n → ℂ) × (Fin n → ℂ)`. The following table expands every
outer and conditional input binder of the public theorem. Anonymous implication
arguments are named descriptively here. Quantifiers inside predicate families
are displayed, including their membership/index guards.

| Input | Bin | Source or convention |
|---|---|---|
| `{n : ℕ}` | TYPING | Blueprint phase space ℂ^(2n); no positive-dimension restriction is needed. |
| `{U : ℕ → Set E}` | TYPING | Blueprint nested domains. |
| `{Φ : ℕ → E → E}` | TYPING | Total representatives of the blueprint's restricted maps; MapsTo enforces their domain/codomain. |
| `{m : ℕ}` | TYPING | Blueprint finite composition endpoint. |
| `hU : ∀ i ≤ m, U(i+1) ⊆ U i` | SOURCE | Blueprint nested domains. |
| `hmap : ∀ i ≤ m, MapsTo (Φ i) (U(i+1)) (U i)` | SOURCE | Blueprint Φ_i : U_(i+1) → U_i, including every point's membership. |
| `μ : Seminorm ℂ E` | TYPING | Blueprint arbitrary seminorm, conditionally quantified in displacement clause. |
| `d : ℕ → ℝ` | TYPING | Design §0.3 any-bound formulation. |
| `hd : ∀ i ≤ m, ∀ z ∈ U(i+1), μ(Φ i z-z) ≤ d i` | SOURCE | Individual displacement bounds; no assumption about the composite. |
| `hopen : ∀ i ≤ m, IsOpen (U(i+1))` | STANDING | Design v2 N4 / audit-2 N4: holomorphy uses open domains; confined to derivative clause. |
| `hdiff : ∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U(i+1))` | SOURCE | Each factor holomorphic. |
| `hsympl : ∀ i ≤ m, ∀ z ∈ U(i+1), ∀ v w : E, symplFormC (DΦ_i(z)v) (DΦ_i(z)w) = symplFormC v w` | SOURCE | Each factor preserves the canonical form. |
| `hinj : ∀ i ≤ m, InjOn (Φ i) (U(i+1))` | SOURCE | Each factor injective, confined to injectivity clause. |

Counts for these expanded input binders: SOURCE 6, STANDING 1, TYPING 6,
RULED 0, EXCESS 0. Internally quantified i,z,v,w are ordinary source indices,
points and vectors; their bounded-index/membership guards are exactly those
shown, with no extra class assumptions. No numerical constants or widened
constant dependence occur.

The conclusions retain MapsTo, all-seminorm displacement, holomorphy plus form
preservation, and conditional injectivity. The sum runs over range (m+1), so
m=0 is one factor, not an empty composition. No positivity of d, boundedness,
nonempty domain, or hidden global regularity assumption is added.
The any-bound formulation avoids assigning an invalid real supremum to an
unbounded displacement set; whenever the blueprint's finite supremum exists,
it is an admissible bound. This is exactly the adopted v2 formulation.

The symplectic form is the existing literal
`Σ i, (v.2 i * w.1 i - v.1 i * w.2 i)` in
`KAM/Canonical/Setting.lean:65`; preserving it is equivalent to the stated
matrix identity. The sign convention has no effect on form preservation.
No periodicity or reality theorem is claimed by this node's statement.

## Definition classification

`chain` is the only new definition; there are no new abbrevs or structures.
It is a literal finite composition on arbitrary `E : Type*`, with zero and
successor equations exactly as in A.5. The generic carrier is legitimate because
composition itself requires no analytic or vector-space structure. It covers
all natural indices, including zero, and all total maps; there is no fallback,
choice, valid-locus reconstruction, or deferred characterization.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

## Independent validation receipts

All auditor-started Lean work was serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no resource-budget override, clean, cache fetch, dependency update,
or full library rebuild was requested.

1. Targeted build, through the required compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n64 KAM.Nekhoroshev.NormalForm.Telescope
```

Output and exit:

```text
[inp-gate] slot 1 acquired 06:39:57 for KAM.Nekhoroshev.NormalForm.Telescope
Build completed successfully (2889 jobs).
exit 0
```

2. Exact design-type probe and axiom inspection:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N64Audit1.lean
```

The probe imports the package, opens Set and KAM.Canonical, and reconstructs
A.5's theorem under namespace N64Audit1, using the actual exported chain.
Its body is exactly `by exact KAM.NormalForm.telescope hU hmap`.
It also elaborates both directions of
`example : type_of% @N64Audit1.telescope := @KAM.NormalForm.telescope`
and its converse, plus rfl checks of chain's zero and successor equations.
A separate textual extraction confirmed both the chain body and the full
public theorem signature byte-identical to A.5. Output:

```text
'KAM.NormalForm.chain' does not depend on any axioms
'KAM.NormalForm.telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Probe-development note: the first probe duplicated the recursive chain under a
fresh name and attempted rfl equality of the two recursive constants; Lean
rejected their definitional identification at variable m. The corrected exact-type
probe uses the actual exported chain, whose literal body and defining equations
were independently checked. This was a probe construction error, not a package
failure; no package source was changed.

3. Kernel replay (one invocation; there is no provider or separate helper module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.Telescope
```

```text
replaying KAM.Nekhoroshev.NormalForm.Telescope
exit 0
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (422 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is PASS under the brief's explicit generated-root exception: the only
failure is the expected stale generated KAM.lean. No forbidden tokens,
long lines, size, module, frozen-byte, or ABI failures were reported.
The generated root was not edited.

5. Scope/hygiene: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
produced no output (exit 0). The package has 130 physical lines, longest line
95 Unicode characters; no line exceeds 100. It has the copyright, module command,
public import, module docstring, exposed public section and namespace closure.
The forbidden-token/resource-override scan found none.

A recursive project-import inspection found 21 project modules, no provider,
no frozen theorem and no DRAFT_SORRY anchor. The only frozen modules in this
closure are SEALED definitions: ComplexStrip, HamiltonianVectorField,
HamiltonianVectorFieldC, IsPrimaryOnStrip, IsRealOnReals, OmegaZero. Their actual
files and manifest states were read; none is changed by the package.

## Findings, limitations, and closeout

No material defect, new pinned-source erratum, blueprint contradiction,
conclusion-shaped hypothesis, weakened conclusion, or introduced deviation was
found. The documented open-domain interpretation (N4) and any-bound displacement
form are preserved. Design audit 2's unrelated N6/N7 notes concern other packages
and do not obstruct N6-4.

There is no frozen target in Parts 6–7 (design v2 introduction), so no unrelated
I/N/P frozen theorem seal is certified here. Future consumer assembly and its
own source obligations remain outside this audit. The independent checks above
certify this module's stated infrastructure result only.

Only this report is retained as an auditor-created repository change. The
pre-existing handoff and all source, frozen, manifest and generated files are
preserved; auditor probe files were removed after validation.
