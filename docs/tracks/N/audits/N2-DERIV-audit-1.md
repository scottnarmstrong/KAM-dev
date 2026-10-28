# Independent package audit: N2-DERIV

Overall verdict: **PASS WITH NOTES**. All six public declarations pass statement/definition fidelity and proof checks. The only package integration note is the explicitly permitted stale generated root. No proof, premise, carrier, Hessian-orientation, or line-length defect was found.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-n2d`.
Audited HEAD: `480b27e8c29c3a91d1217a359cfcb66e548594b2`.
Comparison branch `inp-n2k`: `7106799a90cc6a07d8b4e0159c15120225a17e97`.
Observed `inp`: `25f3d65bb0d5a30674a6e5286c44befb321e7e9d`.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff and its AUDIT FOCUS,
`docs/tracks/N/design/N2-LEAN-DESIGN.md`, its actual audit path
`docs/tracks/N/design/DESIGN-N2-design-audit-1.md`, the original signatures at
`/root/code/KAM-inp/.drafts/design/N2Signatures.lean`, Track N statement conventions, and
`blueprint-N/parts/p2-qc-zero.tex`. Applied the lean-statement-audit method to the scoped infrastructure.

The user's later scope instruction controls: compared
`git diff inp-n2k...HEAD -- KAM/Nekhoroshev/QcZero`, which adds only
`KAM/Nekhoroshev/QcZero/Derivative.lean` (169 lines). Kernel is an inherited, already audited
interface; IterativeMap, Telescope, Stability/*, Hamiltonian/* and Newtonian/Assembly were not audited.
The user's explicit absolute report path overrides the generic brief's main-worktree destination.
Only this report is a lasting audit edit. No subagents or state-changing git operations were used.

This is infrastructure, not provider or anchor sealing. **Per-anchor seal verdict: N/A**;
N-QC is contextual, already sealed, and unchanged. No provider/frozen-type or seal-body probe is
applicable to this package. Instead, all five implemented theorem types were checked against fresh
copies of their exact design declarations. No new root or frozen theorem closure is asserted.

Input SHA-256:

| Input | SHA-256 |
|---|---|
| Derivative.lean | `afc5c2ac1bd7f5b5365323d2745a0f1aa5d729110a3411c3b203064c6fcac9b0` |
| Part-2 blueprint | `ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d` |
| Original N2Signatures.lean | `6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a` |
| N2-LEAN-DESIGN.md | `42377b6eccc4cac2f9f35feaabd620ea56ded53d38052dfbff84ada06eb7a726` |

## Declaration ledger

Names are in `KAM.Nekhoroshev`; implementation locations are in Derivative.lean.

| Node | Declaration / line | Verdict | Reason |
|---|---|---|---|
| bpN:p2:qc-deriv, stepN:p2:qd-sym | real_hessian_matrix / 30 | PASS | Literal real second-derivative coordinates; body/type token-identical to design signature. |
| stepN:p2:qd-first | qd_first / 90 | PASS | Genuine differentiability and full coordinate formula for the first component. |
| stepN:p2:qd-freq | qd_freq / 99 | PASS | C1 on U, differentiability at I, and correctly oriented D(Dh)[v][e_i]. |
| stepN:p2:qd-sym | qd_sym / 116 | PASS | Schwarz symmetry, matrix reconstruction, and full quadratic identity. |
| stepN:p2:qd-prod | qd_prod / 134 | PASS | Genuine derivative with both u-frequency and lambda-Hessian contributions. |
| bpN:p2:qc-deriv | qc_deriv / 150 | PASS | HasFDerivAt with exactly the N2-KERNEL bordered CLM; valid for arbitrary real lambda. |

All five theorem headers are token-identical to the original signature file, including section
hypotheses. Successful elaboration of the fresh declarations confirms those hypotheses survive
Lean's section elaboration. Blueprint source locations: p2-qc-zero.tex:33–46 (lemma and four steps).
There is no extra dimension, nonzero-frequency, quasi-convexity, holomorphy, positivity, or lambda
nonvanishing premise. No existential constant or widened dependence occurs. The quadratic identity
in qd_sym is an explicit bilinear expansion strengthening the short symmetry receipt and supplies
the subsequent blueprint line 56 consumer's identity.

## Expanded binder audit

The following table enumerates the common outer binders once, with the affected declarations
explicitly specified. SOURCE inputs cite the blueprint lemma at lines 33–37; TYPING inputs encode
its coordinates, functions, and test directions. No project-owned logical bundle hides premises.

| Declaration(s) | Binder | Bin | Evidence |
|---|---|---|---|
| all five theorems | implicit n : Nat | TYPING | R^n coordinate convention; all dimensions allowed |
| all five theorems | implicit U : Set (Fin n → Real) | TYPING | Domain in line 34 |
| all five theorems | implicit h : (Fin n → Complex) → Complex | TYPING | Frozen realPart supplies h_R |
| all five theorems | hU : IsOpen U | SOURCE | Open U, line 34 |
| all five theorems | hh : ContDiffOn Real 2 (realPart h) U | SOURCE | h_R in C2(U), line 34 |
| all five theorems | implicit I : Fin n → Real | TYPING | Action point in line 34 |
| all five theorems | hI : I ∈ U | SOURCE | I in U, line 34 |
| qd_first, qd_prod, qc_deriv | lam : Real | TYPING | Arbitrary lambda in line 34 |
| qd_first, qd_prod (conclusion quantifiers) | v : Fin n → Real | TYPING | Test direction in lines 35,39,45 |
| qd_first, qd_prod (conclusion quantifiers) | u : Real | TYPING | Scalar test direction in lines 35,39,45 |
| qd_freq (conclusion quantifiers) | v : Fin n → Real | TYPING | Derivative direction, line 41 |
| qd_freq (conclusion quantifiers) | i : Fin n | TYPING | Coordinate evaluation, line 41 |
| qd_sym (first conjunct) | i : Fin n | TYPING | Hessian row, line 35 |
| qd_sym (first conjunct) | j : Fin n | TYPING | Hessian column, line 35 |
| qd_sym (second conjunct) | v : Fin n → Real | TYPING | Matrix action, line 43 |
| qd_sym (third conjunct) | v : Fin n → Real | TYPING | Quadratic evaluation, line 56 |
| real_hessian_matrix | implicit n : Nat | TYPING | Coordinate dimension |
| real_hessian_matrix | h : (Fin n → Complex) → Complex | TYPING | Frozen real restriction |
| real_hessian_matrix | I : Fin n → Real | TYPING | Evaluation point |

Outer-binder counts per theorem: qd_first, qd_prod, qc_deriv each SOURCE=3, TYPING=5;
qd_freq and qd_sym each SOURCE=3, TYPING=4. STANDING=0, RULED=0, EXCESS=0 throughout.
Including conclusion quantifiers adds respectively 2,2,0,2,4 TYPING binders to
qd_first, qd_prod, qc_deriv, qd_freq, qd_sym. The definition has three TYPING inputs.
There are no instance premises or bundled conclusion assumptions.

## Definition classification

Only one new definition; no abbrev, structure, class, or global norm instance.
`real_hessian_matrix` is a literal coordinate definition, exposed by the section attribute:
`Q i j = fderiv Real (fderiv Real (realPart h)) I (Pi.single i 1) (Pi.single j 1)`.

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK
- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A
- DEFINITION_VERDICT: PASS

This is exactly the design's total coordinate expression, with no custom off-domain branch or
selected witness. Mathlib fderiv is total, as it is in the frozen definitions; no mathematical
Hessian claim outside the C2 locus is used. Every analytic theorem retains open/C2/membership
guards. On that locus qd_sym proves symmetry, action reconstruction and the quadratic identity.
The scratch probe also checked the defining equation by rfl on the whole declared carrier.
Read the actual frozen FrequencyMap, RealPart and IsStrictlyQuasiConvex bodies; frequencyMap is
definitionally the realPart derivative evaluated on coordinate vectors. No substitute object appears.

## Proof refutation and N2-KERNEL consumption

The seven private lemmas (lines 34–82) introduce no assumptions beyond their displayed data and
local C2 guard. Openness plus membership gives a neighborhood for ContDiffAt. The derivative of
the derivative is obtained with regularity order 1 from C2; continuous linear evaluation and
hasFDerivAt_pi give the frequency derivative. First projection and scalar product rules prove
the two components independently.

The critical orientation check passes: frequency differentiation gives D2h[v,e_i], whereas Q i j
is D2h[e_i,e_j]. `sym_hess` (73–76) applies ContDiffAt.isSymmSndFDerivAt to the actual C2 proof;
`hess_apply` (78–82) swaps the slots before finite-basis expansion. qd_sym then proves both
matrix action and the double-sum quadratic identity. No unproved Hessian transpose is assumed.

qc_deriv combines the component HasFDerivAt proofs via prodMk and identifies the resulting CLM
by extensionality. It actually rewrites with the inherited `bordered_map_apply` at line 157.
Thus N2-KERNEL's map is consumed at the term level, with correct ordered product carriers,
first row and scalar/action contributions. General kernel bijectivity is not needed for a
derivative identity and is not used as a premise. The code factors its own component derivative
helpers rather than calling hasFDerivAt_isoenergetic wholesale; this matches the design proof
plan's independently proved first/product receipts and changes no statement.

The transitive project import closure contains nine dependencies: QuasiConvex, QcZero.Kernel,
and seven frozen definitions. It contains **zero providers and zero frozen theorem modules**,
so no DRAFT_SORRY anchor is reachable. The frozen N-QC theorem was read only as context and is
not imported into the audited module.

## Independently rerun checks

All Lean/Lake invocations below were sequential, with LEAN_NUM_THREADS=1 and niceness 5.
The build used the required compile gate; no clean, update, cache fetch, library rebuild,
resource override, generated-root edit, or package-directory edit was performed.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n2d KAM.Nekhoroshev.QcZero.Derivative
   ```

   Exit 0. Output:

   ```text
   [inp-gate] slot 1 acquired 07:06:48 for KAM.Nekhoroshev.QcZero.Derivative
   Build completed successfully (2362 jobs).
   ```

   The gate invokes nice -n 5 lake build. This was a targeted overlay build, with no warnings.

2. Exact design-type, definition-equation, elaborated-binder and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N2DerivAudit.lean
   ```

   Exit 0; no errors or warnings. The probe imported only Derivative, copied each of the five
   original theorem headers and their common section variables under audit_<name>, and used
   `exact <name> hU hh hI` (plus lam for qd_first, qd_prod, qc_deriv). It printed each full
   elaborated type with #check @<name>, checked the Hessian equation by rfl, and issued
   #print axioms for all six public declarations. Exact axiom output:

   ```text
   'KAM.Nekhoroshev.qd_first' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qd_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qd_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qd_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qc_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.real_hessian_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the sole in-scope module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.QcZero.Derivative
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Nekhoroshev.QcZero.Derivative
   ```

4. Repository source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the permitted generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (441 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No 100-character-line violations or forbidden-token diagnostics. Independent counting:
   169 total lines, maximum 100 Unicode characters, no lines above 100. Standard copyright,
   module, public imports, module docstring, exposed public noncomputable section all present.
   Direct forbidden-token/resource-override search found no matches (rg exit 1).

5. Integrity and comparison:

   `git diff --check inp-n2k...HEAD -- KAM/Nekhoroshev/QcZero`: exit 0, no output.
   The scoped name-only diff lists only Derivative.lean. The requested original
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty; git warns that
   multiple merge bases exist and uses `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`.
   Against inp-n2k the protected-path diff lists KAM.lean only, due to inherited root-generation
   commits `4f65a1f`, `9e16b5e`, `f1451bf`, including the modules excluded by the user's scope note.
   `git show --stat HEAD` confirms the package commit changes only Derivative.lean and its
   `.drafts/handoff-N2-DERIV.md`. The inherited root difference is not attributed to this package.

## Findings, uncertainties, errata and closeout

N1 (nonblocking integration note): regenerate KAM.lean in the orchestrator checkout after landing;
this audit leaves it untouched as required. Lint's exit 1 is reported literally, not as an
unqualified lint pass.

No suspected pinned-source erratum, blueprint mathematical defect, new hypothesis, or semantic
deviation was found in the scoped derivative nodes. Existing design-audit notes about Track-I
cross-reference wording and unrelated premise-drop inventory concern inherited documentation,
not a defect introduced by Derivative. No fresh pinned-BM11 PDF audit or audit of inherited
implementation proofs was performed; the source-fidelity comparison is to the named blueprint,
design signatures, frozen objects and owner conventions.

All assigned checks are complete. The temporary probe was removed. The original untracked
N2-DERIV-handoff.md was preserved. The report is the only newly retained audit file. This is
package-level PASS WITH NOTES, with no new anchor seal or campaign-closure claim.
