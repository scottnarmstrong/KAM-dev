# SO-MINV prover handoff (branch inp-sominv, 934fe8c2; track SO package run by the main orchestrator)


Files: `KAM/Certificate/MatrixInv.lean` (new, ~95 lines). Nothing else touched (KAM.lean not regenerated;
lint reports it out of date, which is expected: orchestrator regenerates).

Declarations (types verbatim from SOSignatures.lean §F):
- `matrix_inv_of_approx_inverse` (proved): X = (BA)⁻¹ exists by `isUnit_one_sub_of_norm_lt_one`; det A unit
  from det(BA); A⁻¹ = X B; X = 1 + X E gives ‖X‖ ≤ 1/(1-δ); A⁻¹ - B = X E B.
- `ModelMatrix.HasShape` (def, generic in the entry type β). It lives here per the design F7 text; it does
  not define the `ModelMatrix` abbrev (that belongs to Model/Ops, which can add it; namespace coexists).
  Note: the design's `ModelMatrix.Encloses` is NOT in this module (needs CertModel).

Checks:
- `inp_lake_build.sh ... KAM.Certificate.MatrixInv`: Built successfully, no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message is
  "KAM.lean is out of date" (generated).
- `#print axioms matrix_inv_of_approx_inverse`: [propext, Classical.choice, Quot.sound].
- No line >100 columns; no heartbeat options; no sorry.

Uncertainties: none. `HasShape` is `@[expose]` so it unfolds downstream.
Errata/deviations: none.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 3); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Design section F (matrix inverse part, Revision 3 F7 shape predicate ModelMatrix.HasShape). Check that the Neumann-defect inverse bound is stated in the form the Gram and torsion checks of the design consume.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/MatrixInv.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.

## Round 2 (orchestrator fix, commit 27dee06f)

Audit 1 failed only on the interface: the two declarations sat in the root namespace instead of `KAM.Certificate`.
The orchestrator wrapped the module body in `namespace KAM.Certificate ... end KAM.Certificate`; nothing else
changed. Rebuilt through the compile gate (success) and the short-name check passed.
ROUND 2 FOCUS: are `KAM.Certificate.matrix_inv_of_approx_inverse` and `KAM.Certificate.ModelMatrix.HasShape` now
exactly the signed declarations (re-run your exact-type probe against the signature file)? Any new issue from the
namespace move? Verdict and numbered findings.
