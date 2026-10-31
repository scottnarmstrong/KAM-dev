# W3-SETTING-DIVF independent package audit 2

Date: 2026-10-31. Auditor: maud-wpka-2. **Verdict: PASS for the F1 correction.**
F1 is resolved: the general predicate now expresses a W-valued Hamiltonian field without
requiring a smoothing lift. The N1 documentation correction also passes. This is a tight-delta
acceptance of commit `97061ff5`, not a new audit of the entire package or a seal-ready verdict
for any frozen anchor. No provider or seal is present.

## Snapshot, authority, and scope

- Worktree/report destination: `/root/code/KAM-inp-wpka`, resolving to
  `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpka`.
- Detached HEAD: `97061ff5b0112721cbaa6577f5f90782ff10d94f`.
- Comparison `inp`: `9c6d9128c2032acd1fb764896a149d5153119206`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, combined handoff/AUDIT FOCUS,
  and round-1 finding F1 and note N1. Applied the lean-statement-audit skill's body/carrier,
  expanded-premise and consumption checks as helper-package audit methodology.
- The detached checkout's `docs/tracks/W/audits/W3-SETTING-handoff.md` ends at line 53 and
  lacks the requested F1-fix section. Read that section at the same relative path in
  `/root/code/KAM-inp-wpk`, lines 55–67. Its account matches the reviewed commit; its reported
  43-module build is prover evidence, not this auditor's validation or audit scope.
- Inspected `git diff inp...HEAD` for comparison context, then reviewed **only**
  `git show 97061ff5 -- KAM`: HamClass (48 additions/10 deletions), Forms (2/2), Lambda (5/3).
  The `Lie*` group-3 modules present in the checkout are excluded. Unchanged group-1/2
  mathematics retains its round-1 assessment; it was not re-audited.
- Source comparison: `blueprint-W/parts/w3-birkhoff.tex`, `bpW:w3:hamfield-def`, lines 154–168.
  Checkout and `git show inp:blueprint-W/parts/w3-birkhoff.tex` have identical SHA256
  `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161`.
  This checks the adopted blueprint, not a fresh PDF transcription.

## Findings and declaration verdicts

The source says “A map $X_P:U\to\mathfrak W$” and requires
`DP(w)v = Omega(X_P(w),v)`. W+ membership and analyticity into W+ belong to the later
class-A clause. The new `IsBirkHamFieldW.deriv_eq` uses `birkOmega ha hp (X w) v`
directly. It neither embeds X nor asks for a preimage under the W+ inclusion.
`birkFieldW_eq` applies nondegeneracy to `X w - X' w`; `birkFieldW_coord` evaluates
at the physical unit vector at weight p, obtaining exactly the source sign and factor i.

| Node / item | Declaration / location | Verdict | Reason |
|---|---|---|---|
| hamfield-def, F1 | `IsBirkHamFieldW`, HamClass:56 | PASS | General field in W, direct Omega, differentiability and identity on U only. |
| general uniqueness | `birkFieldW_eq`, HamClass:62 | PASS | Equality at every w in U for two general fields of the same P; no lift assumption. |
| general coordinates | `birkFieldW_coord`, HamClass:71 | PASS | `birkCoord a p (X w) l = -i sgn(l) DP(w)e_{-l}`. |
| smoothing predicate rename | `IsBirkHamFieldPlus`, HamClass:84 | PASS | Original narrower predicate preserved under a distinct name; X is read at p+1. |
| class-A projection | `IsBirkClassA.hamField`, HamClass:105 | PASS | Produces Plus from the existing class fields; class-A structure and existential definition are unchanged. |
| smoothing to general | `IsBirkHamFieldPlus.toW`, HamClass:111 | PASS | General field is explicitly `birkEmbed ∘ X`, not the same weighted coordinate vector X. |
| smoothing uniqueness | `birkField_eq`, HamClass:117 | PASS | Renamed premise only; nondegeneracy followed by injectivity of the embedding. |
| smoothing coordinates | `birkField_coord`, HamClass:132 | PASS | Renamed premise only; physical field coordinates remain at p+1. |
| forms use | `birkDiag_field`, Forms:128 | PASS | Now returns Plus; proof and smoothing estimate assumptions unchanged. |
| Lambda, N1 | module docstring and `not_exists_birkXLam_bounded` docstring, Lambda:25,296 | PASS | Both now claim exactly no bounded linear operator with the specified coordinates. The theorem type/body are unchanged. |

**N1's mathematical coverage limit remains:** the negative export does not itself prove the
stronger assertion that the multiplier fails to map every W point to W. No such stronger
theorem is certified here. Correcting its description resolves the documentation overclaim.
There is no new failing inequality or source mismatch in the F1 delta.

## Definition classification and expanded premises

`IsBirkHamFieldW` and `IsBirkHamFieldPlus` are literal predicates, not selected objects or
assumed existence theorems. Both operate on total ambient maps restricted by identities on U.
They do not construct a vector field from arbitrary P or assert existence for all P.
On the source's open U, `DifferentiableOn` supplies the intended differentiability; the
explicit full-fderiv identity is present in either predicate. Allowing other U as helper
parameters does not add a premise to the open-domain source statement.

For each of the two predicates:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

`IsBirkClassA` and `BirkClassA` have no body change. The former still includes the
smoothing pairing and analyticity of X into its p+1 weighted-coordinate carrier; the latter
still existentially quantifies that smoothing field. This is the intended source class.
No changed definition has junk values, a fallback branch, or deferred characterization.

The following table expands the logical bundles of the affected theorem premises. Each
named binder/field is assigned a bin; shared rows apply separately at each occurrence.
Source references are the definition above, and `bpW:w3:forms` for the diagonal helper.

| Applies to | Binder / expanded field | Bin | Authority |
|---|---|---|---|
| field lemmas and projection/conversion | `a` | TYPING | Weight parameter. |
| same | `p` | TYPING | Weight parameter. |
| same | `ha : 0 ≤ a` | STANDING | Source weights; helper permits p≥0 instead of requiring p≥1/2. |
| same | `hp : 0 ≤ p` | STANDING | Sufficient standing weight restriction; no stronger source premise. |
| same | `U` | TYPING | Domain. |
| same | `P` | TYPING | Scalar Hamiltonian. |
| same | `X` | TYPING | Candidate field, interpreted at the predicate's weight. |
| uniqueness, both variants | `X'` | TYPING | Second candidate field. |
| uniqueness / coordinate, both variants | `w` | TYPING | Point of ambient W. |
| uniqueness / coordinate, both variants | `hw : w ∈ U` | SOURCE | Identity asserted on U. |
| coordinate, both variants | `l` | TYPING | Arbitrary signed nonzero index. |
| each field-predicate premise `h`, also `h'` in uniqueness | `differentiableOn` | SOURCE | P complex differentiable on U. |
| same | `deriv_eq` | SOURCE | Defining identity for every point in U and every direction; Plus uses the inclusion. |
| class-A projection premise | `h.isOpen` | SOURCE | Open U. |
| same | `h.rho_mem` | SOURCE | Rho-invariance (rho is involutive). |
| same | `h.real` | SOURCE | Reality of P. |
| same | `h.analytic` | SOURCE | Analytic P on U. |
| same | `h.field` | SOURCE | Smoothing Hamiltonian pairing. |
| same | `h.analytic_field` | SOURCE | Analytic X into W+. |
| diagonal helper | `a`, `p` | TYPING, each | Weight parameters. |
| same | `ha`, `hp` | STANDING, each | Same sufficient weight restrictions. |
| same | `n` | TYPING | Multilinear arity minus one. |
| same | `c` | TYPING | Smoothing constant. |
| same | multilinear form `𝔓` | TYPING | Source form. |
| same | multilinear map `N` | TYPING | Candidate gradient. |
| same | `hS.nonneg` | SOURCE | Nonnegative smoothing constant. |
| same | `hS.symm` | SOURCE | Symmetry of form. |
| same | `hS.pairing` | SOURCE | Definition of smoothing gradient. |
| same | `hS.bound` | SOURCE | Defining smoothing bound, unchanged from round 1. |

Counts (expanded top-level logical inputs; quantifiers inside defining identities stay with
their identity): uniqueness, each variant: SOURCE 5, STANDING 2, TYPING 7;
coordinate, each variant: SOURCE 3, STANDING 2, TYPING 7;
`toW`: SOURCE 2, STANDING 2, TYPING 5;
`hamField`: SOURCE 6, STANDING 2, TYPING 5;
`birkDiag_field`: SOURCE 4, STANDING 2, TYPING 6.
RULED 0 and EXCESS 0 for every row/theorem. A defining field-predicate premise is appropriate
for uniqueness, extraction, and conversion; no concrete existence result is assumed here.

## Independent checks and exact receipts

All Lean/Lake activity below was serial and inside the owner's D53 scope:
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
No resource override was introduced. Lint's child Lake/Lean invocation inherited the enclosing
scope's limits. No clean rebuild, application build, or group-3 build was requested.

1. Targeted builds through the compile-gate driver:

   ```sh
   /root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpka KAM.Wave.Birkhoff.Forms KAM.Wave.Birkhoff.Lambda
   ```

   The driver took slot 1 and ran the following separately, in order:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.Birkhoff.Forms
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.Birkhoff.Lambda
   ```

   Exact success lines, respectively:

   ```text
   Build completed successfully (3303 jobs).
   Build completed successfully (3307 jobs).
   ```

   These are warm import-closure builds and include HamClass. The driver's overall exit was
   **1**, despite both Lake builds succeeding. As in round 1, its final
   `[ $rc -ne 0 ] && { ...; exit $rc; }` leaves status 1 when rc=0. No `[w_build] FAILED`
   diagnostic occurred. The driver was not edited. Warnings were replayed dependency
   deprecations/unused simp arguments, not errors in the F1 delta.

2. Prescribed lint only, with an enclosing D53 scope:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpka
   ```

   Exit **0**, exact output:

   ```text
   check_lean_modules: PASS (3600 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   This whole-checkout mechanical lint does not extend the mathematical audit to group 3.
   The named application exports received file-hash checks only, as the output states.

3. Seven exact statement/construction/composition probes and ten axiom checks:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/maud_wpka_2.lean
   ```

   Exit **0**, no errors or warnings. The scratch file imports only Forms and Lambda.
   Its seven examples check: construction of the general predicate from differentiability
   and the direct Omega identity; every constant field Y0 for `P(w)=Omega(Y0,w)` with
   **arbitrary `Y0 : BirkSpace` and no smoothing premise**; exact general uniqueness;
   exact general coordinate formula; Plus-to-W conversion; class-A-to-Plus-to-W composition;
   and `birkDiag_field hS` followed by `.toW` for the explicitly embedded diagonal field.
   The arbitrary-Y0 example does not formalize the round-1 nonliftable sequence; it checks
   directly that the corrected API needs no lift at all.

   Representative exact construction and consumption checks:

   ```lean
   example (hP : DifferentiableOn ℂ P U)
       (hD : ∀ w ∈ U, ∀ v, fderiv ℂ P w v = birkOmega ha hp (X w) v) :
       IsBirkHamFieldW a p ha hp U P X := ⟨hP, hD⟩

   example (h : IsBirkClassA a p ha hp U P X) :
       IsBirkHamFieldW a p ha hp U P
         (fun w => birkEmbed a (p + 1) p (by linarith) (X w)) := h.hamField.toW
   ```

   Exact axiom output for every checked declaration:

   ```text
   'KAM.Wave.IsBirkHamFieldW' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.IsBirkHamFieldPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkFieldW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkFieldW_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.IsBirkClassA.hamField' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.IsBirkHamFieldPlus.toW' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkField_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkDiag_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.not_exists_birkXLam_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The temporary probe was deleted after validation. No provider/frozen-type probe applies.

4. Kernel replay and name checks were already run by the launcher according to the user.
   Their receipts are unavailable here; neither was rerun, and no exit code is invented.
   They remain launcher evidence rather than independently inspected receipts. This audit's
   independent observations are the builds, lint, exact probes and axiom checks above.

5. `git diff 97061ff5^ 97061ff5 --check -- KAM`: exit **0**, no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   Exact old-name search outside `Lie*` finds no remaining `IsBirkHamField` reference.
   Changed file lengths: HamClass 202, Forms 201, Lambda 325; all below 1500.
   Existing module headers/public imports/exposed public sections are preserved; the delta
   introduces no proof escape, provider import, frozen import, or resource override.

Raw transient logs: `/tmp/maud-wpka-2-{build,lint,probe}.log`.

## Limits, errata, and handoff

No new suspected blueprint/source defect or mathematical deviation was found in this delta.
F1 was an implementation correspondence defect and is now corrected without changing the
blueprint. N1 remains an explicit limit on formal coverage. Round-1 findings outside F1/N1,
including cosmetic N2, were not reopened. Group-3 `Lie*`, real restriction, later W3 results,
W5/W8 assembly and frozen `nlw2` are not certified by this report.

Only this report is an intentional persistent edit. No Lean source, frozen declaration,
manifest, generated root, or README was edited; no state-changing git command was run.
