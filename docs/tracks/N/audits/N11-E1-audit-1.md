# N11-E1 independent package audit 1

Overall verdict: **PASS WITH NOTES for the N11-E1 infrastructure slice**. The assigned flow,
weighted-symplectic and real-conjugation contracts are proved with the exact signed statements.
This package supplies no provider for a frozen theorem and is not a seal of N-PARTIAL-CONVEX.
The frozen `KAM.Nekhoroshev.partialConvex_nekhoroshev` remains DRAFT_SORRY; its eventual seal
and provider/frozen-type probe are outside this three-module audit.

## Scope and authority

Audited HEAD: `c198ff11a966d692e9ba3fd91709b4de7a6740d5`.
Comparison `inp`: `e262c35780384516b9eb2b21264c361a52841ef9` at initial inspection.
`git diff inp...HEAD` warns of multiple merge bases and selects
`ca5b8ed55a4e550447c36b2ad3a71b0f6eada37d`. Its 83-file diff includes inherited work;
only `KAM/Nekhoroshev/Partial/{Flow,SymplecticLinear,Symplectic}.lean` is audited for proof correctness,
as explicitly required by AUDIT FOCUS. The complete three target files are new in that diff.
The package-only series `51329710^..c198ff11` changes exactly these three files.

Read AGENTS.md, PLAN.md, DECISIONS.md, the external package brief, handoff/focus,
N11 design and both design audits, the live signature delivery, the relevant Part-11 blueprint
statements/proofs and design node inventory, track-N statement, frozen partial-convex anchor,
and relevant frozen real-part/solution/field definitions. Audit 1's design failures concern other
packages; audit 2 closes those interface findings. Its warning that elaboration is not proof
closure remains applicable. The explicit user destination overrides the generic brief's main-worktree destination.
No production, frozen, manifest, graph or generated file was edited. Only this report is persistent;
temporary probes are confined to `.lake/abi-scratch/` and removed at closeout.

Pins:

| Input | SHA-256 |
|---|---|
| Live N11Signatures.lean | `fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| Flow.lean | `e4252c3ab5f55918e9866de85849ef192d6147abe0698a7c550a8732da206040` |
| SymplecticLinear.lean | `ca78a2a47320c4dac2faf79d9e5c5671e4cd4145e2650ce5dfd7abf8be546cbb` |
| Symplectic.lean | `00b25fbffaeb7750b359192e5ad9e5f47d79613b16dd07c98dce1ce10321b655` |

## Signed interfaces and graph completeness

All seven theorem headers (`ext_flow`, `flow_real`, `symplectic`, `symplectic_bracket`,
`symplectic_det`, `symplectic_form`, `conj`) compare byte-for-byte equal to the live signatures.
`extForm`'s type and body also compare byte-for-byte equal. The 20:50 ruling authorizes
`ext_flow`; the design inventory/Appendix still says `flow` (design lines 191 and 666).
This is a documented name reconciliation, not a changed mathematical statement.

The complete slice consists of design inventory rows 191–192 and 231–232:

| Graph node | Establishment | Verdict |
|---|---|---|
| `bpN:p11:flow` (B:51–56) | `ext_flow` supplies membership/displacement; generic `Canonical.flow_a` supplies existence/uniqueness, `flow_b` continuity/holomorphy/variational identity, `flow_c` inverse/derivative bound and `flow_d` translation covariance, all generic in E and directly imported; `flow_real` supplies unequal-product reality. | PASS |
| `bpN:p11:symplectic` (B:58–63) | `flow_extForm` and `symplectic_form` give inverse-weight form invariance; `symplectic`/`canonical_at_iff` give the dual matrix identity; `symplectic_det`, `symplectic_bracket`, `symplectic_field` give determinant, arbitrary-observable bracket and actual field transport. | PASS |
| `bpN:p11:conj` (C:20–25) | `conj` proves the exact signed real-orbit contract for `reExtMap Ψ`, with the original two-sided `HasDerivAt`; no new orbit or field-equivalence hypothesis. | PASS |
| `stepN:p11:cj` (C:24) | The proof at Symplectic.lean:347–394 transports the actual inner real field to the complex derivative, uses local Ht=H∘Ψ, then the proved field identity and real restriction; domain membership is established explicitly. | PASS |

The signed flow wrapper deliberately states only part of the source flow package; direct generic
imports supply the other clauses on `EC n k`, without assuming an equal-size canonical carrier.
The signed real-conjugation contract is used by the planned real-orbit transfer consumers;
complex curve transport in B:59(c) follows from the proved `symplectic_field` and the chain rule
(the audit additionally probes this literal complex-orbit consequence). Positivity of c for the
nondegenerate form/determinant is the standing block condition; bracket/field identities need no
such restriction and are valid for c=0. No dimension, sign, norm, constant-dependence or extra
source premise was introduced.

## Every new public theorem

All names below are in `KAM.Nekhoroshev`. Auxiliary exports have explicit mathematical contracts;
none is substituted for a narrower unsigned graph-node statement.

| Node | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| `bpN:p11:flow` | `ext_flow` (Flow.lean:35) | PASS | SIGNED exact header; membership and displacement from generic flow_b/flow_a. |
| `helper` | `extImCLM_apply` (Flow.lean:48) | PASS | Literal componentwise imaginary-part evaluation. |
| `helper` | `extImCLM_eq_zero_iff` (Flow.lean:51) | PASS | Kernel is exactly the real locus, including zero-dimensional factors. |
| `bpN:p11:flow` | `flow_real` (Flow.lean:68) | PASS | SIGNED exact header; imaginary-part Picard induction and factorial convergence; arbitrary open domain. |
| `helper` | `regroupBwd_fst` (SymplecticLinear.lean:48) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_fast` (SymplecticLinear.lean:51) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_q` (SymplecticLinear.lean:55) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_p` (SymplecticLinear.lean:59) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupFwd_fst_left` (SymplecticLinear.lean:63) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupFwd_fst_right` (SymplecticLinear.lean:67) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupFwd_snd_left` (SymplecticLinear.lean:71) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupFwd_snd_right` (SymplecticLinear.lean:75) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_fwd` (SymplecticLinear.lean:79) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupFwd_bwd` (SymplecticLinear.lean:89) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroup_apply` (SymplecticLinear.lean:131) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroup_symm_apply` (SymplecticLinear.lean:133) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `extForm_eq` (SymplecticLinear.lean:143) | PASS | Literal form agrees with regrouped standard form, even when c=0. |
| `helper` | `extForm_eq_regroup` (SymplecticLinear.lean:156) | PASS | Same identity for the continuous linear equivalence (c≠0). |
| `helper` | `wfield_eq_wfieldOf` (SymplecticLinear.lean:170) | PASS | Definitional identity for the actual field. |
| `helper` | `regroupBwd_single_b1` (SymplecticLinear.lean:182) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_single_b2` (SymplecticLinear.lean:192) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_single_b3` (SymplecticLinear.lean:203) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `regroupBwd_single_b4` (SymplecticLinear.lean:213) | PASS | Coordinate evaluation / inverse identity for the explicit regrouping; no extra source assumption. |
| `helper` | `wfieldOf_eq` (SymplecticLinear.lean:227) | PASS | Exact weighted field of a functional under the nonzero-weight regrouping. |
| `helper` | `conjLin_apply` (SymplecticLinear.lean:259) | PASS | Literal application of L A L⁻¹. |
| `helper` | `bracket_pair` (SymplecticLinear.lean:262) | PASS | Chain rule expands the two functional brackets exactly. |
| `helper` | `sep_dual` (SymplecticLinear.lean:290) | PASS | Standard separating dual on finite-dimensional complex coordinates. |
| `helper` | `canonical_at_iff` (SymplecticLinear.lean:294) | PASS | Pointwise functional ExtCanonical iff transported Y J(η∘Y)=Jη. |
| `helper` | `hamiltonianJ_dualOfVec` (SymplecticLinear.lean:326) | PASS | Standard nondegenerate form recovers the vector from its negative pairing. |
| `helper` | `form_of_bracket` (SymplecticLinear.lean:333) | PASS | Finite-dimensional surjectivity/injectivity derived from bracket identity, never assumed. |
| `helper` | `wfield_eq_regroup` (Symplectic.lean:36) | PASS | Transport of actual totalized derivative field; no differentiability premise needed. |
| `helper` | `extForm_fderiv_skew` (Symplectic.lean:45) | PASS | Transport of Hessian skew identity; all regularity supplied by source hypotheses. |
| `helper` | `continuousOn_symplFormC_curves` (Symplectic.lean:77) | PASS | Coordinatewise finite-sum continuity; no resource override. |
| `helper` | `extForm_const` (Symplectic.lean:91) | PASS | Explicit conditional linear-ODE helper; zero derivative and initial identity prove preservation. |
| `helper` | `flow_extForm` (Symplectic.lean:121) | PASS | Actual flow derivative satisfies the variational equation and the helper hypotheses. |
| `bpN:p11:symplectic` | `symplectic` (Symplectic.lean:138) | PASS | SIGNED exact header; flow_extForm and dual canonical identity. |
| `bpN:p11:symplectic` | `symplectic_field` (Symplectic.lean:158) | PASS | Literal source field identity; dual separation and chain rule; also valid at c=0. |
| `bpN:p11:symplectic` | `symplectic_bracket` (Symplectic.lean:177) | PASS | SIGNED exact header; chain rule and symplectic_field; arbitrary holomorphic observables. |
| `helper` | `canonical_form_regroup` (Symplectic.lean:194) | PASS | Actual derivative preserves the standard form after regrouping. |
| `bpN:p11:symplectic` | `symplectic_det` (Symplectic.lean:202) | PASS | SIGNED exact header; conjugate derivative determinant and standard-form determinant ±1. |
| `bpN:p11:symplectic` | `symplectic_form` (Symplectic.lean:219) | PASS | SIGNED exact header; canonical_form_regroup transports the literal inverse-weight form. |
| `bpN:p11:conj; stepN:p11:cj` | `conj` (Symplectic.lean:347) | PASS | SIGNED exact header; source map contract, local derivative transport, complex chain rule and real restriction. |

## Definition classification

| New definition | Classification on its whole carrier |
|---|---|
| `extImCLM` (Flow:45) | Literal componentwise imaginary-part real CLM, kernel exactly the real locus. |
| `regroupFwd` (SymplecticLinear:38) | Total explicit map `(θ,(I,q,p)) ↦ ((θ,q),(I,p/c))`. At c=0 the slow momentum is zero by field inverse convention; this case is used only for the valid direct form identity, never as an equivalence. |
| `regroupBwd` (:43) | Total explicit reverse coordinate map with p multiplied by c; inverse claims require c≠0. |
| `regroupEquiv` (:101), `regroup` (:128) | Linear / continuous linear equivalence with explicit nonzero-weight proofs, no fallback or junk branch. |
| `extForm` (:139) | Exact signed fast alternating pairing plus c⁻¹ times the slow pairing. Total also at c=0; nondegeneracy conclusions require c>0. |
| `wfieldOf` (:163) | Literal coordinate weighted Hamiltonian field of a complex linear functional; exactly the existing actual field evaluated at fderiv. |
| `conjLin` (:255) | Literal conjugate L A L⁻¹ of an arbitrary CLM; c≠0 retained. |
| `dualOfVec` (:318) | Continuous complex functional w↦−symplFormC(a,w); no choice of replacement field. |
| private `extCxCLM`, `extReCLM` (Symplectic:240,340) | Componentwise inclusion/real-part CLMs, verified against actual extCx/extRe. |

There are no new abbrevs, structures or global instances. The local `idx_tail` tactic macro
only discharges finite-index coordinate cases. The conditional `extForm_const` assumes a
skew derivative relation to prove form preservation; it is an explicitly named internal ODE
helper, and `flow_extForm` proves its hypotheses for the actual flow. The given `ExtConjHyp`
is the upstream source map contract, not an orbit/confinement conclusion. The indicator in the
upstream `realHamiltonianExt` is used only at interior points of its real domain, after proving
local equality with the actual real restriction.

## Hygiene and independent verification

All auditor Lean/Lake invocations are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No limits were overridden. The build uses the mandatory campaign compile gate; it acquired slot 3
at 21:13:37 UTC. No source was rebuilt from scratch, cache fetched or dependency tree edited.

1. **Targeted build**, exit 0:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-n11e1 KAM.Nekhoroshev.Partial.Flow \
     KAM.Nekhoroshev.Partial.SymplecticLinear KAM.Nekhoroshev.Partial.Symplectic
   ```

   Final output: `Build completed successfully (3235 jobs).`
   Replayed upstream warnings in `Stability/Gradient.lean` and `Partial/Coordinates.lean`
   concern unused binders/tactics/simp arguments. No warning/error was emitted for the three
   audited modules. These upstream linter warnings are not hidden as package diagnostics.

2. **Exact statement/body, application and axiom probe**, exit 0:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11E1Audit.lean
   ```

   Seven copied signed statements under fresh `audit_` names use direct `by exact` applications
   to the production exports, with all explicit binders supplied in order. Seven further
   `example : type_of% @<fresh export> := @<production export>` tests elaborate. The copied
   `extForm` body is definitionally equal by `rfl`. An additional complex-curve test establishes
   the literal B:59(c) orbit consequence from `symplectic_field`, holomorphy, image membership
   and `HasDerivAt`, with no reality assumption. No warnings/errors.

   All **42** public theorem commands `#print axioms KAM.Nekhoroshev.<name>` (the complete
   ledger above) returned exactly `[propext, Classical.choice, Quot.sound]`. In particular:

   ```text
   'KAM.Nekhoroshev.ext_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.flow_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.symplectic_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.symplectic_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.symplectic_det' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.symplectic_form' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.conj' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No frozen provider seal-body test is applicable to this package: there is no new provider export.



3. **Kernel replay**, exit **0**, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Nekhoroshev.Partial.Flow KAM.Nekhoroshev.Partial.SymplecticLinear \
     KAM.Nekhoroshev.Partial.Symplectic
   ```

   Complete output:

   ```text
   replaying KAM.Nekhoroshev.Partial.Symplectic
   replaying KAM.Nekhoroshev.Partial.SymplecticLinear
   replaying KAM.Nekhoroshev.Partial.Flow
   ```


4. **Source lint, frozen guard and ABI**, actual exit **1**, solely the generated-root exception
   explicitly permitted by the brief:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (925 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   All substantive lint checks pass. The generated root was not regenerated. Lint's internal
   ABI probe was run only after kernel replay finished and inherited the one-thread environment
   and niceness. No additional Lean/Lake process was launched by this auditor while it ran.

## Static hygiene and inherited comparison notes

- The three files have respectively **133/356/400 lines**, maximum line widths **98/98/99**.
  They have copyright headers, `module`, public imports, module docstrings and
  `@[expose] public noncomputable section`. No forbidden token, ambient EuclideanSpace,
  resource override, new instance or harmful root declaration appears.
- `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py
  /root/code/KAM-inp-n11e1 KAM.Nekhoroshev.Partial.Flow
  KAM.Nekhoroshev.Partial.SymplecticLinear KAM.Nekhoroshev.Partial.Symplectic`
  exits 0: `short-name check OK (no reused public short name)`.
  Signed names are governed by the signature file, including the ruled rename; private
  copies in Conj remain private. All new exports are in `KAM.Nekhoroshev`, not `_root_`.
- Recursive source-import inspection found 81 KAM modules in the closure, no provider import,
  no frozen theorem import, and 23 frozen definition modules, all **SEALED** in the manifest.
  Thus no DRAFT_SORRY theorem can enter via the inspected KAM import closure. The axiom
  probe independently confirms the absence of `sorryAx` in all new public results.
- `git diff --check inp...HEAD -- KAM/Nekhoroshev/Partial/Flow.lean
  KAM/Nekhoroshev/Partial/SymplecticLinear.lean KAM/Nekhoroshev/Partial/Symplectic.lean`
  exits 0 (apart from the multiple-merge-base warning).
- The full `git diff --check inp...HEAD` exits **2**, with inherited extra blank lines at EOF
  in `docs/tracks/P/audits/B07-audit-1.md:175` and `B07-audit-2.md:284`. No target-file finding.
- The full protected-path command `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
  is **not empty**. It contains inherited generated-root additions and the N-HEAD-C seal:
  `QuasiConvexNekhoroshevComplexBound.lean` changes its proof body to its provider and the
  manifest moves that anchor DRAFT_SORRY→SEALED (historical commit `7c254d1a`). README is unchanged.
  These are disclosed rather than attributed to N11-E1. The same protected-path comparison over
  the actual package series, `git diff --quiet 51329710^ HEAD -- KAM/Frozen manifest KAM.lean README.md`,
  exits **0**. The brief's literal full-branch empty-diff gate therefore has an inherited
  exception; it is not evidence of a package edit to a protected file.

## Documentation/source findings and limits

1. **Minor docstring mismatch**, `KAM/Nekhoroshev/Partial/Symplectic.lean:89–99`:
   “A path `Y` of linear maps with `Y' = D Y`” does not describe `hYd`, which states
   `HasDerivAt Y (D x) x`. The actual theorem and proof are correct: hskew pairs D with Y,
   and `flow_extForm` instantiates D with DF∘Y. Suggested wording is “Y′=D”. No proof repair needed.
2. **Known signed-name discrepancy**, design `N11-LEAN-DESIGN.md:191,666` still says `flow`.
   The live signed delivery line 213 and the 20:50 orchestrator ruling say `ext_flow`.
   Production follows that authority exactly; documentation should eventually follow it.
3. **Previously reported issues remain outside this slice**, design lines 314–335:
   Nek77's unavailable Part-II proofs, the new energy argument, the preimage open-ball reading
   at C:31 and the stale adjoint proof locator B:69–86 (actual end B:73). Neither this package
   nor its audit closes those source/graph obligations. No new pinned-source erratum was found.
4. The blueprint's claim that Part-5 reality applies “verbatim” on the unequal carrier is
   handled by the explicitly assigned `flow_real` proof, as required by both design audits.
   The Picard argument does not introduce conjugation invariance of the complex domain.

The extra public linear-algebra helpers and helper module are implementation additions already
disclosed in the handoff; they introduce no source-facing premise or changed signed declaration.
No upstream theorem seal, whole-campaign closure or independent pinned-PDF audit is asserted.

## Closeout

The N11-E1 slice passes proof, exact-signature, definition, node-completeness, axiom and kernel
checks. The notes are the nonblocking docstring/name documentation discrepancies and the
explicitly distinguished inherited comparison/generated-root findings. This is infrastructure
acceptance only; no frozen anchor is declared seal-ready by this report.

Final artifact checks: the package whitespace check exits 0. The report comparison
`git diff --no-index --check /dev/null <report>` returns 1 because it is a new-file comparison,
with no whitespace diagnostics; an independent trailing-whitespace/final-newline check passes; scratch signature/axiom/complex-orbit
probe and its captured outputs, kernel output and lint output were removed after incorporating
receipts above. Final working-tree status contains only this new report and the pre-existing
untracked handoff. No production correction or state-changing git command was performed.
