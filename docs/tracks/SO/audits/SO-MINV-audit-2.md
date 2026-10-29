# SO-MINV independent audit 2

Overall verdict: **PASS WITH NOTES**. Audit 1's blocking namespace defect is resolved.
Both signed declarations match exactly, with sound proofs and no added premises.
No frozen anchor is implemented by this infrastructure package; anchor/provider seal-body
checks are not applicable. This verdict concerns only `KAM/Certificate/MatrixInv.lean`.

Audited 2026-10-29 at HEAD `f8d067f8bc003d76284b6280acfd21cb465f874f`, against
`inp` = `1c8cbfd1dad1fca3fb7260162646d619ac2a5a50`. Read the full
`git diff inp...HEAD`: one new Lean file (82 lines), the prior audit and the handoff.
The code diff from audited commit `934fe8c2` adds only the namespace opening and closing.
The checkout was initially clean. Only this report was added; the scratch probe was removed.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff (including Round 2)
and `SO-MINV-audit-1.md`. The user's exact worktree-local output path overrides the generic
brief's main-worktree destination. The handoff's explicit SO-MINV-only focus controls scope.

Compared with `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`, namespace at line 55,
§F lines 693–715 (signed declarations) and 732–747 (Gram consumer), and Revision 3 of
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §1.9 items 8–9
(lines 130–148), module/package assignment (lines 364, 408), and Appendix A
(lines 1225–1243). These supply the SO-specific statement/blueprint authority;
there is no local `docs/tracks/SO/statement.md` and no SO-MINV frozen anchor to compare.
The draft signature file was read as text, never imported, so its placeholder proofs cannot
enter the audit probe's dependencies.

## Numbered findings

1. **Audit 1 F1 resolved; PASS.** The namespace opens at implementation line 27 and closes
   at line 82. `KAM.Certificate.matrix_inv_of_approx_inverse` and
   `KAM.Certificate.ModelMatrix.HasShape` now elaborate at their exact signed names.
   The theorem header and shape definition body are byte-identical to the draft extracts
   (apart from the implementation's additional `@[expose]` attribute on the definition).
   Fresh Lean probes check the complete theorem type and explicit application in binder
   order `hδ hδ1 hB`, the shape type and definition body. No root-level declaration remains
   in this source. There are no public helper declarations or reused helper short names;
   repository search found these declaration names only in this module.
2. **Slice complete; PASS.** The general approximate-inverse theorem and F7 shape predicate
   are the complete assigned MatrixInv slice. The generic `List (List β)` predicate also
   applies to the future model-matrix abbreviation; that abbreviation and `Encloses`, Gram
   checking, torsion construction and averaging checking belong to other packages.
   No namespace-move regression or hidden extra premise was found.
3. **Permitted hygiene note.** Repository lint reports the stale generated `KAM.lean`.
   The brief explicitly permits that exception; no generated file was regenerated.
   The design's dependency sketch lists `Matrix/Neumann, Matrix/Inverse`; this proof instead
   imports Mathlib directly. This is an implementation-level dependency deviation with no
   change to the signed interface, hypotheses, result or intended norm.

| Node / declaration | Verdict | Reason |
|---|---|---|
| §F `KAM.Certificate.matrix_inv_of_approx_inverse` (lines 37–80) | PASS | Exact signed name, complete binder sequence, carriers, assumptions, norm and conclusion; only permitted axioms; kernel replay passes. |
| F7 `KAM.Certificate.ModelMatrix.HasShape` (lines 32–33) | PASS | Exact signed name/type/body; total law-free predicate; exposed for downstream unfolding. |
| Package / frozen anchor | PASS WITH NOTES / not applicable | Assigned infrastructure slice complete; permitted generated-root lint exception; no anchor sealing claim. |

## Mathematical and definition review

The proof sets `E = 1 - B*A`; its norm is strictly below one, so `B*A` is a unit.
Multiplicativity of determinant yields `IsUnit A.det`. For `X = (B*A)⁻¹`,
`X*(B*A) = 1` proves `A⁻¹ = X*B`. The identity `X = 1 + X*E` gives
`(1-δ)‖X‖ ≤ 1`; `δ < 1` justifies division. Submultiplicativity then proves both
`‖A⁻¹‖ ≤ β/(1-δ)` and, using `A⁻¹-B = X*E*B`, the inverse-error bound.
Nonnegativity of δ and β follows from the norm premises. No invertibility, symmetry,
positivity, conclusion-shaped assumption or backend law is smuggled into the statement.
The signed `Nonempty ι` premise supports the unit norm identity.

Definition classification: `ModelMatrix.HasShape` is the sole new definition. Its whole-carrier
body is exactly `M.length = k ∧ ∀ r ∈ M, r.length = k`, for every natural k and every
list matrix, including k = 0. It has no fallback, truncated block or junk denotation.
There are no new abbreviations, structures or other definitions.

The `Matrix.Norms.Operator` scope selects maximum row-sum norm. The probe independently
checks `‖A‖ = (↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) : ℝ)` via
`Matrix.linfty_opNorm_def`. Thus the bound and inverse-error radius match the Gram
consumer, and the theorem also applies to the complete bordered torsion matrix.
This checks applicability of the interface, not correctness of future consumer algorithms.

## Independent checks and receipts

All Lean/Lake commands ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource-budget override was used. No source, frozen file, manifest, generated file,
package dependency or git state was changed.

```text
git diff --stat inp...HEAD
 KAM/Certificate/MatrixInv.lean           |  82 +++++++++++++++
 docs/tracks/SO/audits/SO-MINV-audit-1.md | 168 +++++++++++++++++++++++++++++++
 docs/tracks/SO/audits/SO-MINV-handoff.md |  35 +++++++
 3 files changed, 285 insertions(+)
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
[no output; exit 0]
git diff --check inp...HEAD
[no output; exit 0]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sominv KAM.Certificate.MatrixInv
[inp-gate] slot 1 acquired 12:26:41 for KAM.Certificate.MatrixInv
Build completed successfully (2484 jobs).
[exit 0]
```

The scratch probe `.lake/abi-scratch/SOMinvAudit2.lean` imported only
`KAM.Certificate.MatrixInv`, opened the signed operator-norm scope, copied the literal
signed theorem header under `auditSignedType`, and proved it by
`exact KAM.Certificate.matrix_inv_of_approx_inverse hδ hδ1 hB`. It also checked
`example : type_of% @auditSignedType := @KAM.Certificate.matrix_inv_of_approx_inverse`.
The literal signed shape definition was copied under `auditSignedShape`; its complete type
was checked with `type_of%`, and equality of both functions was proved by `rfl`.
The same probe checked the row-sum norm identity and printed both signed names and axioms.

```text
Python literal extraction comparison:
Theorem signed header byte equality: True
Shape signed definition byte equality: True
Source lines: 82 Maximum Unicode line length: 94
Forbidden tokens: []

LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOMinvAudit2.lean
KAM.Certificate.matrix_inv_of_approx_inverse.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A B : Matrix ι ι ℂ} {δ β : ℝ} (hδ : ‖1 - B * A‖ ≤ δ) (hδ1 : δ < 1) (hB : ‖B‖ ≤ β) :
  IsUnit A.det ∧ ‖A⁻¹‖ ≤ β / (1 - δ) ∧ ‖A⁻¹ - B‖ ≤ δ * β / (1 - δ)
KAM.Certificate.ModelMatrix.HasShape {β : Type} (k : ℕ) (M : List (List β)) : Prop
'KAM.Certificate.matrix_inv_of_approx_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.HasShape' does not depend on any axioms
[exit 0]

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.MatrixInv
replaying KAM.Certificate.MatrixInv
[exit 0]
```

Static review: 82 lines, maximum 94 Unicode characters per line; copyright, `module`,
public imports, module docstring and `public section` present. No `sorry`, `admit`, `axiom`,
`unsafe`, `opaque`, `native_decide`, `EuclideanSpace` or `set_option`. Imports are Mathlib
only; no provider or frozen theorem, including any DRAFT_SORRY anchor, is imported.
The theorem is the only new public theorem, and its axioms are listed above.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1291 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
[exit 1]
```

The stale generated root is the sole lint diagnostic and is the exception explicitly
allowed by the audit brief. Module lint, frozen-anchor integrity and elaborated ABI checks
all pass. The generated root was left untouched.

## Source defects, deviations and uncertainties

No suspected blueprint or pinned-source mathematical defect was found in this slice;
there is therefore no defect quotation or erratum proposed. Audit 1's namespace deviation
is repaired. The direct-Mathlib dependency deviation and generated-root note are recorded
above. The handoff's approximate line count (~95) is not the current exact count (82).
No remaining uncertainty affects this slice's interface or proof. No claim is made that
this infrastructure seals an I/N/P anchor, validates the complete checker, or establishes
the lunar confinement theorem.

Final cleanup removed `.lake/abi-scratch/SOMinvAudit2.lean`. Final repository checks:
`git diff --check` exits 0; `git status --short` lists only
`?? docs/tracks/SO/audits/SO-MINV-audit-2.md`. The protected-path comparison remains empty.
