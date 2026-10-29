# SO-MINV independent audit 1

Overall verdict: **FAIL — signed interface mismatch**. The mathematics and kernel replay pass,
but neither declaration exists under its signed fully qualified name. No frozen anchor is
implemented or sealed by this infrastructure package; seal-body comparison is not applicable.

Audited on 2026-10-29 in `/root/code/KAM-inp-sominv`, HEAD
`934fe8c2bbef9e4a39901a24609828998dbadc99`, against `inp`
`1c8cbfd1dad1fca3fb7260162646d619ac2a5a50` using the full `git diff inp...HEAD`.
That diff contains exactly one new file, `KAM/Certificate/MatrixInv.lean` (78 lines).
The pre-existing untracked handoff was read and left untouched. Only this report was added;
temporary probes were confined to `.lake/abi-scratch/` and removed after checking.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package-audit brief,
and `docs/tracks/SO/audits/SO-MINV-handoff.md`. Followed the user's exact report destination
over the generic brief's main-worktree destination. The handoff's AUDIT FOCUS limits this audit
to `KAM/Certificate/MatrixInv.lean`; this is SO infrastructure, not an I/N/P provider seal.
Compared against `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`, especially lines
55, 693–715 and 732–747, and Revision 3 of
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, especially §1.9
items 8–9 (lines 130–148), §7 (lines 364, 410), and Appendix A (lines 583, 1225–1243).
No external-source theorem claim is needed for this elementary matrix lemma.

## Findings and declaration table

**F1 (blocking): missing `KAM.Certificate` namespace.** The signature file opens
`namespace KAM.Certificate` at line 55 and closes it at line 1230; both §F declarations
are inside it. The design's Appendix A independently opens that namespace at line 583.
The implementation has no namespace command: its declarations at lines 30 and 35 are
`_root_.ModelMatrix.HasShape` and `_root_.matrix_inv_of_approx_inverse`.
The handoff's claim “Declarations (types verbatim from SOSignatures.lean §F)” is correct
for the textual types and definition body, but does not establish the required signed names.

| Node / signed declaration | Actual Lean declaration | Verdict | Reason |
|---|---|---|---|
| §F `KAM.Certificate.matrix_inv_of_approx_inverse` | `_root_.matrix_inv_of_approx_inverse`, lines 35–78 | FAIL interface; PASS mathematics | Signed name absent. Binder sequence, hypotheses, carriers, norm, constants and conclusion otherwise match exactly; no added premise. |
| F7 `KAM.Certificate.ModelMatrix.HasShape` | `_root_.ModelMatrix.HasShape`, lines 30–31 | FAIL interface; PASS definition | Signed name absent. Generic carrier and complete definition body match exactly; `@[expose]` is appropriate. |

The requested correction is to place these declarations in `namespace KAM.Certificate`,
then rerun signature and downstream-name checks. No correction was made during this audit.
There are no public proof helpers to collide with reused short names. The root exports are an
unintended interface leak; no pre-existing duplicate declaration or separate shadowing defect
was found by the repository name search. The missing signed exports themselves are a concrete
consumer-interface failure, regardless of whether an unqualified downstream lookup could
occasionally find a root declaration.

## Proof, definitions and consumer applicability

The inverse proof uses `E = 1 - B*A` and the strict bound inherited from `hδ` and `hδ1`
to obtain `IsUnit (B*A)`. Multiplicativity of determinant gives `IsUnit A.det`.
Writing `X = (B*A)⁻¹` gives `A⁻¹ = X*B` and `X = 1 + X*E`.
Thus `(1-δ)‖X‖ ≤ 1`, and `1-δ > 0` justifies division. The final two estimates follow
by submultiplicativity and `A⁻¹-B = X*E*B`. Nonnegativity of δ and β follows from the
norm premises, rather than being added as an assumption. No symmetry, positivity of A,
conclusion-shaped premise or hidden invertibility assumption is used. The `Nonempty ι`
premise is already in the signed declaration and supports `norm_one`.

`ModelMatrix.HasShape` is the only new definition: an exact, total, law-free shape predicate
on all `List (List β)`. Its body requires exactly k rows and length k for every row, including
the intended empty-matrix case k = 0. It has no fallback or junk denotation. Its meaning
was checked by a reflexivity probe against the literal conjunction in the signature.

The matrix norm is the maximum row sum under `Matrix.Norms.Operator`, not the default
entrywise maximum. A fresh probe proved its equality to
`↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊)` using `Matrix.linfty_opNorm_def`.
Consequently the bounds have exactly the form needed for the Gram inverse and inverse-error
budget `δ*β/(1-δ)`, and apply equally to the whole bordered torsion matrix.
The mathematical slice is complete: the general inverse lemma and F7 shape predicate are
present. `ModelMatrix`, `Encloses`, matrix algorithms, Gram and torsion producers/checkers
belong to other packages and are not missing obligations here. The signed API slice remains
incomplete because of F1. This audit does not certify those future algorithms or consumers.

## Independent checks

All Lean/Lake commands ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion or synthesis budget override was used.

1. Full diff and protection checks:

   ```text
   git diff --stat inp...HEAD
    KAM/Certificate/MatrixInv.lean | 78 ++++++++++++++++++++++++++++++++++++++++++
    1 file changed, 78 insertions(+)
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [no output; exit 0]
   git diff --check inp...HEAD
   [no output; exit 0]
   ```

2. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sominv KAM.Certificate.MatrixInv
   [inp-gate] slot 1 acquired 12:20:47 for KAM.Certificate.MatrixInv
   Build completed successfully (2484 jobs).
   [exit 0]
   ```

3. Signature/body and norm probe:

   A Python comparison extracted the theorem declaration through its result type from both
   files and the entire `HasShape` definition (excluding the additional expose attribute).
   Both comparisons returned `True`. This textual check deliberately does not erase F1.
   The Lean probe imported only `KAM.Certificate.MatrixInv`, copied the exact signed theorem
   declaration under the fresh name `auditSignedType`, and used the body
   `matrix_inv_of_approx_inverse hδ hδ1 hB`. It also checked the shape conjunction by
   `Iff.rfl` and the row-sum norm identity described above.

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOMinvAudit.lean
   'matrix_inv_of_approx_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
   [exit 0; #print also confirmed the root theorem and root shape definition]
   ```

4. Exact signed-name negative probe, importing only the package module:

   ```lean
   import KAM.Certificate.MatrixInv
   #check KAM.Certificate.matrix_inv_of_approx_inverse
   #check KAM.Certificate.ModelMatrix.HasShape
   ```

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOMinvNames.lean
   .lake/abi-scratch/SOMinvNames.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `KAM.Certificate.matrix_inv_of_approx_inverse`
   .lake/abi-scratch/SOMinvNames.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `KAM.Certificate.ModelMatrix.HasShape`
   [exit 1; expected reproduction of F1]
   ```

5. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.MatrixInv
   replaying KAM.Certificate.MatrixInv
   [exit 0]
   ```

6. Static hygiene: 78 total lines, maximum line length 94 Unicode characters. Zero occurrences
   of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace` or
   `set_option`. Copyright, `module`, public interface imports, docstring and `public section`
   are present. Imports are Mathlib only: no provider or DRAFT_SORRY anchor is imported.
   The theorem is the only new public theorem; its axiom set is recorded above.

7. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1291 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   [exit 1]
   ```

   This is the explicitly permitted generated-root exception, with no other lint diagnostic.
   `KAM.lean` was not regenerated. Hygiene therefore passes with this note; it does not remove F1.

## Source defects, deviations and limits

No suspected mathematical defect in the design or pinned sources was found in this slice.
F1 is an implementation deviation from the signed namespace, not a proposed source erratum.
The handoff's approximate file size (~95 lines) differs from the actual 78 lines without
affecting mathematics. The design's planned use of existing Matrix/Neumann and Matrix/Inverse
modules is replaced here by direct Mathlib imports; no source premise or conclusion changes
as a result. No frozen file or manifest was changed. The audit leaves the blocking namespace
repair to the prover/orchestrator and makes no campaign-theorem or downstream-checker claim.
