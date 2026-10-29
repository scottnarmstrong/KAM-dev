# P11A-P8 independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-p11ap8`.
Audited HEAD: `3a1ff30bf4f0de6b17be19a7234a99b727d000a7`.

## Verdict and scope

**PASS WITH NOTES for the signed definitions slice in
`KAM/Planetary/Preparation/PreparedData.lean`.** No frozen theorem is proved or
seal-ready on the strength of this slice. There are no provider exports or new
public theorems in the audited file; frozen-type and seal-body probes are therefore
not applicable.

The controlling scope is the handoff's “ORCHESTRATOR RULING (OVERNIGHT 01:05)”:
“this audit covers ONLY the first module” and “The theorems prepared and amount
are NOT in this file and are not findings (P8e assembles them).” Accordingly this
is not a PASS for the original whole P8 package. Definitions specify outputs;
they do not establish existence, the prepared theorem, or an amount lower bound.
The user-specified report path in this worktree overrides the generic brief's
main-worktree output instruction.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief,
P11A-P8-handoff.md, the relevant design rows/revisions/signature appendix, the
live signed signature file, Track P statement, blueprint Step E and amount,
and the imported frozen FixedHamiltonian definition and manifest/import closure.
No production source, frozen file, manifest, generated file, or git state was edited.

## Signed declarations and definition classification

All names below are in `KAM.Planetary`. Locators refer to PreparedData.lean.
Every declaration in this file is signed. There are no unsigned public helpers,
no graph-node-named substitute exports, and no reused short declaration names
(the eight names each have one declaration site in KAM).

| Node / role | Declaration (line) | Verdict | Classification and reason |
|---|---|---|---|
| `bpP:p11:sec-E#data`, carrier | `P11PreparedData` (27) | PASS | Data structure with exactly the signed fields N, P, chain, checkW and Inhabited derivation. Contains functions, not assumed theorem proofs. |
| Prepared complex frequency | `p11PreparedFreq` (33) | PASS | Complex Fréchet derivative of N evaluated on coordinate vectors; exact signed body. Total derivative convention outside regularity domains makes no extra analytic claim. |
| Prepared real frequency | `p11PreparedFreqR` (35) | PASS | Real parts of that derivative at real inclusion; exact signed body. |
| Prepared normal form contract | `P11PreparedSpec` (37) | PASS | Proposition specifying stage identities, analytic/reality/periodicity domains, frequency and derivative bounds, unscaled J-jets, target-block scaling, scalar positive-order bounds and literal fixed-Hamiltonian identity. No existence is assumed or proved by defining this predicate. |
| Fixed vector bound | `p11M0` (74) | PASS | Exactly `(2*n+1 : ℝ)^(mu+1)*(2*L+1)`; no nu/epsilon dependence. |
| Actual normalized slow-stage frequency | `p11SlowNormalizedFreq` (76) | PASS | Derivative of the selected h0+g2 at `(J, eps*(2*pi+rho))`, with slow block divided by eps. No replacement by a limiting frequency. |
| Full consumer contract | `P11PreparedFullSpec` (85) | PASS | Base spec plus actual slow-frequency identification on the unscaled J-domain, diagonal vector jets including order zero, and scalar order-zero bound. All signed conjuncts retained. |
| Shared witness selector | `p11PreparedData` (107) | PASS WITH NOTES | Exactly the signed dependent-if: chooses a FullSpec witness if one exists, otherwise default. Existence/specification is not asserted unconditionally. A scratch theorem verifies choose_spec under the existential. |
| Imported jet gauge, not newly declared here | `p11JetBound` (WeakMeasure/Basic.lean:57) | PASS (context) | Signature-identical body: all j ≤ mu including zero, diagonal p11dg when true, full p11op when false. This file does not redefine or shadow it. |

The structure and six of the seven defs have byte-identical declaration text to
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` (structure starts at 1046;
last selector at 1132). P11PreparedSpec has one whitespace-only re-wrap of the
fast-map/polar/slow/rescale chain (signature line 1069; implementation 50–51).
A per-declaration comparison removing whitespace found 8/8 matches, preserving
binders, fields, type annotations, operators, quantifiers and bodies. Seven fresh
copied signed defs were also checked by Lean with
`example : @original = @auditSigned_original := rfl`, so their elaborated bodies
and types agree, not merely their printed interfaces.

Signature-file SHA256:
`fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.
Audited source SHA256:
`35e26831b3e48fdeedc22399e9d5269ba73e4a8ca43baaae25783541e7512fe0`.

## Blueprint and consumer review

Reference: `blueprint-P/parts/p11-cp09-preparation.tex:189–222` and design
`docs/tracks/P/design/P11A-LEAN-DESIGN.md:176–186,200,842–886`.

* N and P have the exact rescaled identities `(h0+g2)/eps` and `f3/eps`.
  The chain order is secular chart after fast map after polar after slow Psi
  after rescaling. The final identity uses the frozen fixedHamiltonian,
  not a surrogate Hamiltonian or assumed conjugacy premise.
* U is actionNbhd of the prepared box with radius 1, V is the sigma/72 strip
  times U, and the complex frequency/derivative bounds use radius 3/4.
  These are the signed neighborhood formulation of the prepared normal form.
  They do not claim holomorphy on all of the larger informal E outside U.
* The normalized frequency relation retains diag(1,eps), not eps on both
  target blocks. The unscaled J estimate has every real rho of norm < 5/4
  and every J with norm distance < s2/4, with exponent
  `5*tau+2+(tau+1)*(mu+1)` and no lost J derivative factors.
* FullSpec identifies checkW with actual derivatives of h0+g2 on this domain.
  It retains vector diagonal jets through mu, scalar full-tensor bounds for
  1 ≤ j ≤ mu+1, and the additional scalar order-zero bound. The Euclidean
  gauge is explicit in p11euclid/p11dg/p11op, while ordinary Pi norms remain
  max norms. No EuclideanSpace or implicit norm-instance substitution occurs.
* The fixed vector constant M0 and scalar constant
  `2^(mu+1)*(2*L+1)^2` have precisely the signed dependence. The repeated
  unscaled closeness conjunct is redundant but unchanged from the signature.
* Design Revision 2 F2 and N3 explicitly require this FullSpec and the same
  selected Q in prepared/amount/data_star, with choice specifications proved
  before use. All required predicates are available here. A repository search
  finds no downstream implementation consuming these new names yet, so actual
  consumer proof closure is not certified. The signed future consumers
  (signature 1124–1141,1298–1300) demand this same FullSpec and selector.

Slice completeness: the old node table maps prepared and six pr-* steps to
Preparation/Prepared, amount and three am-* steps to Preparation/Amount;
none is mapped to Preparation/PreparedData. The data row at design line 200
names p11Rescale, p11PreparedBox and P11PreparedData. The first two already
exist in imported SlowData.lean:31,34 and are re-exported through public imports.
The third and all eight declarations requested for this definitions slice are
present. No proof-node completion follows from these declarations. Missing
prepared/amount proofs are explicitly outside the handoff's split scope.

Whole-carrier review: P11PreparedData is arbitrary function data; the specs are
predicates restricting it only on their stated domains. fderiv, division by zero,
and the default selector remain total on arbitrary inputs exactly as signed.
This module proves no bound by exploiting any fallback. In particular eps=0,
nonholomorphic arbitrary Q, and failure of FullSpec existence confer no source
claim. Future positive-small-epsilon construction must discharge the recorded
existence and regularity gates. This is consistent with design N3 at 881–886.

## Diff and protected-path note

Ran the requested `git diff inp...HEAD`, including its full file inventory,
and inspected the complete audited-module delta and protected-path delta.
Git reports:

```text
warning: inp...HEAD: multiple merge bases, using 11a05936187b0e9191a65fbbab67b3ba7ea89048
```

`git merge-base --all inp HEAD` returned that base and
`6d56fa0ea591c35f99f27058b992f7b1eb8b2f17`.
The live inp ref was observed at `3fee37f84e289f174909fccc380e894a1f46b276`;
it is an active orchestrator branch. The requested diff has 22 files, including
unrelated PlanarAssembly/WeakKAM/PlanarTwoPlanetKAM and graph/audit changes.

The brief's literal empty protected-path check **does not pass for the full
three-dot diff**: KAM.lean imports change, PlanarTwoPlanetKAM's body changes
from sorry to its provider application, and the manifest state becomes SEALED.
README.md has no delta. These are inherited P-PLANAR/generated-root history,
not changes introduced by this definitions slice: logs identify sealing commit
38b4d910 and regeneration commits 2a45f5d9/463375ee/3d55c7ab.
The package commit `53e67413` changes only PreparedData.lean; this command is empty:

```sh
git diff 53e67413^ 53e67413 -- KAM/Frozen manifest KAM.lean README.md
```

This is a recorded branch-hygiene exception under the explicit module-only
scope, not an assertion that the requested protected-path diff was empty,
nor an audit or approval of the unrelated anchor seal.

## Independent validation

All Lean-related invocations were serial and used `LEAN_NUM_THREADS=1` and
`nice -n 5`; lint's internal ABI Lean invocation inherits both settings.
No clean, update, cache operation, heartbeat override or production edit was used.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8 KAM.Planetary.Preparation.PreparedData
   ```

   Exit 0. Output ends `Build completed successfully (9418 jobs).`
   Replayed dependency warnings include deprecated/unused declarations;
   no error or audited-module warning was reported.

2. Signed-body and selector probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P8Audit.lean
   ```

   Exit 0. Seven rfl checks passed. The conditional selector specification
   proof also passed; its use of dif_pos emitted only a deprecation warning.
   Exact axiom output:

   ```text
   'KAM.Planetary.p11PreparedFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedFreqR' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P11PreparedSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11M0' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11SlowNormalizedFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P11PreparedFullSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedData' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation, sole audited module):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedData
   ```

   Exit 0. Output: `replaying KAM.Planetary.Preparation.PreparedData`.

4. Import and static hygiene: transitive local import scan found 372 modules,
   no provider modules, no frozen theorem imports, and 64 imported frozen
   definition anchors, all SEALED. No DRAFT_SORRY dependency was found.
   Audited file has 112 total lines; longest line is 97 Unicode characters.
   Module/copyright/public-import/docstring/public-section/expose conventions
   are present. No forbidden proof tokens, resource settings, or harmful root
   shadow declarations were found. Names remain under KAM.Planetary.
   `git diff --check inp...HEAD` exits 0 (same multiple-base warning).

5. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the expected generated-root exception permitted by the brief.
   Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1188 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated root was not regenerated. No other lint failure occurred.

## Suspected defects, deviations and remaining uncertainty

No new suspected pinned-source, blueprint, frozen-statement or signed-contract
defect was established in this definitions-only slice. No source erratum was
silently repaired. The only implementation deviation is the nonsemantic line
re-wrap in P11PreparedSpec. The protected-path history note and expected stale
root lint exception are recorded above; neither is silently treated as empty.

The signed specs still require substantial construction proofs downstream;
no implication of satisfiability or positive amount is supplied by this audit.
The selector probe establishes the precise conditional specification only.
The scope does not include proving chart canonicity, Cauchy estimates, or
checking the inherited P-PLANAR seal. Audit probes and logs are removed after
recording the checks. The report is the auditor's only repository write.
