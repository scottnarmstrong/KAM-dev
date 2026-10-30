# SO-KDEPTH independent audit 1

Date: 2026-10-30. Auditor: Codex (`maud-sokdepthl-1`).

**Verdict: PASS WITH NOTES for the D39 implementation package.** No blocking soundness,
statement, axiom, import-quarantine, or protected-path finding. This package has no frozen
anchor to seal. The three existing certificate-soundness exports retain their statements and
pass independent axiom inspection and kernel replay. The only lint exception is the expected
stale generated Certificate root, to be refreshed at landing. This verdict approves the checker
implementation delta, not a completed lunar certificate or an R1 resource guarantee.

| Existing consumer / anchor surface | Verdict | Scope |
|---|---|---|
| `KAM.Certificate.checkTorusCertificate_sound` | PASS WITH NOTES | Unchanged export, standard axioms only, replay passed. |
| `KAM.CertificateSharp.checkTorusCertificateSharp_sound` | PASS WITH NOTES | Exists on this landing branch; unchanged export, standard axioms only, replay passed. |
| `KAM.CertificateSharp.V2.checkTorusCertificateV2_sound` | PASS WITH NOTES | Unchanged V2 interface, standard axioms only, replay passed. |
| I/N/P frozen anchors | N/A | No provider or frozen declaration is changed or proposed for sealing. |

## Frozen inputs and authority

- Worktree: `/root/code/KAM-inp-sokdepthl`.
- Audited HEAD: `fe8aecff6e3a3d8e4e70bc722dc779fb43cd8050`.
- Observed `inp`: `4a46fd6476e6cef375650b0ff949c4f74c735aaa`.
- `git merge-base inp HEAD`: `a5f010ebcb430f2c7a9b15726507db29321760eb`.
- Implementation commit: `f1dc41bf`, the landing-branch cherry-pick of `f1f3b760`.
  The subsequent two commits supply the handoff and audit focus.
- Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the absolute package-audit brief,
  and the complete SO-KDEPTH handoff. D39 at docs/DECISIONS.md:313 says
  “every signed statement and the certificate format unchanged; the soundness lemmas
  re-proved and independently audited.” This controls the implementation audit.
- Source contract: docs/tracks/SO/design/SO-LEAN-DESIGN.md, especially the landed model
  interface at :1378–1416 and composition contract at :1586 onward; actual `inp` declarations
  are the unchanged-signature baseline. There are no I/N/P blueprint nodes assigned by this
  D39 package, and no `docs/tracks/SO/statement.md` exists. Unrelated frozen I/N/P claims
  were not re-audited.
- The user's exact absolute report destination overrides the generic brief's main-worktree
  destination. Report and disposable `.lake/abi-scratch/maud-*` artifacts only; no source
  repair, git mutation, generated-root refresh, or subagent work.

Tier-2 focused audit: freeze, mechanical declaration inventory, proof/definition inspection,
separate adversarial edge-case and value-order checks, then hygiene. Acceptance criteria:
unchanged old headers and moved commands; valid new contracts; no hidden mathematical
premises; standard axiom closure; targeted consumer/tests, kernel replay, and permitted lint.
Inputs were rehashed at closeout.

| Audited file | SHA-256 | Physical lines |
|---|---|---:|
| `KAM/Certificate/Arith/BalancedSum.lean` | `a1405d40d23b133c1f86219de9870dc35e28dfe622e087b5268d406d7d7d9ed0` | 78 |
| `KAM/Certificate/Model/Basic.lean` | `df5854a0c2c40dc69e0e05b813d2b1795703aedbe99a2048fdc8ce2e90b04653` | 263 |
| `KAM/Certificate/Model/Terms.lean` | `9c10b1552ff977bf43bf89f81cac7fd55a511415f2bffa7f75aa7ae6a14a2a91` | 547 |
| `KAM/Certificate/Expr/Compose.lean` | `ab8d1ab4ddfdffa7bdd0535e7220cf2f3e9e225548adf239a93f302a198f6c2e` | 503 |
| `KAM/Certificate/Model/FixedEq.lean` | `795f0e30da29bb97646985b09461149d554d7fc1e5edd397b69cb27ec68dd509` | 81 |

The handoff hash is `8c5643d5363b060ce33b28052d7ae8a43796860ab16f2ba4d6b5a105becc138e`.
Manifest hash: `674c73210fe8aeef703101ebe014dbc3e8569cb12f54a14dba1a7ff418d76aab`.

## Statement and proof ledger

Read the entire `git diff inp...HEAD`, not just the checker commit: exactly the five Lean
files below plus the handoff. A comment-masked command inventory compared every old
header (binders, binder information, types and conclusion text, preserving textual headers)
in Basic, Terms and Compose with HEAD. **95/95 existing headers retained**, including the
seven commands relocated from Terms to BalancedSum. Those seven complete commands
(statements and bodies) are byte-identical after trimming separating trailing whitespace.
No other existing header was removed. The surrounding backend/law scopes are retained.

All declarations below are in `KAM.Certificate`; module labels abbreviate the file paths in
the snapshot table. Existing declarations not listed separately retain their headers and
bodies; they were covered by the full diff and header inventory.

| Node / locator at HEAD | Declaration | Verdict | Reason |
|---|---|---|---|
| D39 / BalancedSum:31 | `sumPairsUp` | PASS | Moved verbatim; adjacent pairs, odd last item carried. |
| D39 / BalancedSum:36 | `pairRounds` | PASS | Moved verbatim; arbitrary round count. |
| D39 / BalancedSum:43 | `sumUp` | PASS | Moved verbatim; 64 rounds then foldr, not an unbounded complexity theorem. |
| D39 / BalancedSum:48 | `sumPairsUp_ge` | PASS | Moved verbatim; upper-sum bound; no positivity premise needed. |
| D39 / BalancedSum:57 | `pairRounds_ge` | PASS | Moved verbatim; transitive propagation of the upper bound. |
| D39 / BalancedSum:62 | `foldr_upAdd_ge` | PASS | Moved verbatim; uses exact denotation of ofInt 0. |
| D39 / BalancedSum:70 | `sumUp_ge` | PASS | Moved verbatim; joins pair-round and terminal-fold bounds. |
| D39 / Basic:175 | `CertPoly.weightedNormUp_ge` | PASS | New; nonnegativity and strip bound from checkWeight and membership; same summands as before. |
| D39 / Terms:366 | `mergeRowsLevel` | PASS | New; adjacent merges and unchanged singleton. |
| D39 / Terms:372 | `mergeRowsTree` | PASS | New; empty/singleton exits; fuel-zero linear fallback; otherwise next balanced level. |
| D39 / Terms:387 | `directItemsLinear` | PASS | New compatibility name for the former directItems body. |
| D39 / Terms:433 | `ErrRep` | PASS | New literal representation inequality; no computational default. |
| D39 / Terms:437 | `RowsRep` | PASS | New inductive invariant; empty total 0, push totals S+T. |
| D39 / Terms:442 | `errRep_merge` | PASS | New; triangle inequality plus mergeErrTerms_spec pays both old budgets and merging error. |
| D39 / Terms:457 | `errRep_nil` | PASS | New; unconditional empty representation; lawful class omitted. |
| D39 / Terms:460 | `rowsRep_level` | PASS | New; empty/singleton cases unchanged, paired totals reassociated. |
| D39 / Terms:468 | `rowsRep_foldl` | PASS | New; arbitrary accumulator; needed for fuel-zero fallback. |
| D39 / Terms:476 | `rowsRep_tree` | PASS | New; all fuel values and row shapes covered. |
| D39 / Compose:173 | `composeOpsAux` | PASS | New; matches the Option before consuming the next operation; none remains absorbing. |
| D39 / Compose:185 | `composeOpsAux_eq` | PASS | New; equality with the old fold for every initial Option, backend and operation list. |
| D39 / Compose:201 | `composeOps_eq` | PASS | New; old initial-state fold recovered, without lawful-backend premise. |
| D39 / FixedEq:28 | `CertFixed.eq_of_m` | PASS | New; constructor injectivity, no axioms. |
| D39 / FixedEq:31 | `sumPairsUp_fixed_m` | PASS | New; exact integer mantissa sum under one pairing round. |
| D39 / FixedEq:40 | `pairRounds_fixed_m` | PASS | New; exact mantissa sum under any number of rounds. |
| D39 / FixedEq:45 | `foldr_upAdd_fixed_m` | PASS | New; exact integer mantissa sum of the old fold. |
| D39 / FixedEq:53 | `sumUp_fixed_m` | PASS | New; exact sum for any summand function and list. |
| D39 / FixedEq:61 | `CertPoly.weightedNormUp_fixed_eq` | PASS | New; equality in CertFixed P with the old weighted fold for arbitrary W and Q. |
| D39 / Basic:96 | `CertPoly.weightedNormUp` | PASS | Changed body only; balanced upper sum; exact fixed-backend equality established. |
| D39 / Basic:134 | `weightedNormUp_bound` | PASS | Header and old foldr proof unchanged; compatibility theorem remains available. |
| D39 / Basic:218 | `CertModel.norm_le_supBound` | PASS | Exact inp header; re-proved using weightedNormUp_ge. |
| D39 / Terms:382 | `directItems` | PASS | Changed body only; balanced merge of product rows. |
| D39 / Terms:488 | `directItems_spec` | PASS | Exact inp header; derives RowsRep from rowItems_spec and discharges it with rowsRep_tree. |
| D39 / Compose:181 | `composeOps` | PASS | Changed body only; same initial state, new strict Option loop. |
| D39 / Compose:466 | `composeOps_sound` | PASS | Exact inp header; rewrites with composeOps_eq. |
| D39 / Terms:438 | `RowsRep.empty` | PASS | Constructor: zero total of the empty rows. |
| D39 / Terms:439 | `RowsRep.push` | PASS | Constructor: combines a represented row and represented tail into their sum. |

The representation hypotheses of `errRep_merge`, `rowsRep_level`, `rowsRep_foldl` and
`rowsRep_tree` are explicit internal induction interfaces. `directItems_spec` supplies them
from `rowItems_spec`; it does not acquire a representation, sorting, associativity, successful
certificate, or other conclusion-shaped premise. `weightedNormUp_ge` uses the existing
backend laws, checked weight, polynomial data and strip membership; it establishes both
nonnegativity and the evaluation bound. The per-term estimate uses `w ≥ 1`, nonnegative
coefficient norm and outward rational conversion before the nonnegative multiplication law.
`CertModel.norm_le_supBound` consumes this new producer at the same parameters.

`composeOpsAux_eq` includes arbitrary initial `none`/`some` states and empty/nonempty
programs. The `none` induction verifies that early failure agrees with the former fold.
The old initial state is used unchanged by `composeOps_eq`; the soundness proof rewrites
through that equality. The equality is relative to the same `composeStep` and backend,
not an assertion that every backend's entire old and new checker computes identical bounds.

## Definition classification

| Definitions | Classification / whole-carrier check |
|---|---|
| `sumPairsUp`, `pairRounds`, `sumUp` | Existing computational upper sums moved verbatim; all list sizes and round counts defined. |
| `CertPoly.weightedNormUp` | Intended outward weighted sum with the same terms and weights, regrouped. General-backend value may change, with a proved upper bound. |
| `mergeRowsLevel`, `mergeRowsTree` | New total computational schedules. Empty and singleton rows handled; fuel-zero fallback is the actual linear merge with its own proof, not junk data. |
| `directItems` | Same per-pair products and error terms, different merge schedule; defined and sound even for unsorted or repeated keys. |
| `directItemsLinear` | Literal old implementation under a distinct compatibility name. |
| `ErrRep` | Literal mathematical inequality `‖S - errTermsEval n L θ‖ ≤ errTermsErr n L θ`. |
| `RowsRep` | Inductively certified sum of represented rows. Both constructors are constructive invariant introduction rules, not assumed source conclusions. |
| `composeOpsAux`, `composeOps` | Total Option-valued program evaluator with preserved success/failure behavior. `none` is the existing fail-closed behavior, not an invented mathematical object. |

BODY_MATCH and PUBLIC_CARRIER: OK for each row. Characterization-based choice and
choice independence: N/A; none of these objects is constructed by arbitrary choice or a
partial-valid-locus fallback. No new structure hides an additional analytic premise.

## Value preservation and kernel-depth assessment

1. **Composition:** `composeOpsAux_eq` and `composeOps_eq` prove equality to the old fold
   for every backend; neither needs LawfulCertArith. The mirror's composition control loop
   needs no change for this rewrite itself.
2. **Weighted norm:** `CertFixed.eq_of_m` reduces equality to the integer mantissa.
   The four mantissa-sum lemmas establish exact addition through all pair rounds and the
   terminal fold. `CertPoly.weightedNormUp_fixed_eq` is equality of backend values for
   every precision P, W and polynomial, without weight validity or positivity restrictions.
   Therefore the mirror's current right fold is bit-identical on FixedB(P). For an arbitrary
   rounded backend it must use the same 64 pair rounds and final right fold to reproduce
   the Lean value; soundness alone does not assert value equality.
3. **Direct product:** the handoff's strict-row argument is correct: merging strictly
   increasing rows produces a unique strictly increasing union of the keys. Each key gets
   the same fixed-backend coefficient and error sums: `add` and `upAdd` are integer
   addition and `addErr = 0`. The row multiplication/errors are unchanged. Zero coefficients
   are retained in both schedules, so cancellation does not disturb key support. This is
   a mathematical argument, **not a new universally quantified Lean equality theorem**.
   A common padded key width makes translation by `packAddZ` preserve the factor's strict
   order. Bare “sorted factors” on the unrestricted ragged-list carrier do not by themselves
   prove strict rows: `[] < [0]`, yet adding `[0]` sends both to `[0]`. This qualifies the
   handoff's phrase “true for sorted factors”; it is not a counterexample to soundness or
   to its equality claim under the explicit strict-row hypothesis.
4. **Bit-safe mirror prescription:** build `rowItems(a_i, bs)` in original factor order;
   merge neighboring rows left-to-right, carrying an odd final row; repeat at most 64
   levels, stopping at empty/singleton; at zero remaining fuel foldl mergeErrTerms from []
   over the remaining rows. Inside every merge keep the same key comparison, tie addition
   order and nested error additions. Do not silently sort, combine or drop terms. This
   schedule works without needing a sorted-row equality theorem. The checked Python mirror
   `scripts/spin_orbit/sofx_model.py:191` still uses the old linear fold; no mirror file was
   edited by this checker-only package or audit.
5. **Depth:** adjacent balanced additions and merges remove the former length-deep arithmetic
   and lazy-merge accumulation on the changed paths for the intended finite workloads.
   `composeOpsAux` matches the current Option before the next step, removing the chain of
   unevaluated binds; it does not eagerly normalize every model in the state. A 64-round
   schedule is not an unlimited asymptotic guarantee: beyond 2^64 items/rows its residual
   linear fallback can again have length-dependent depth. Both fallbacks remain sound.
   No claim is made that arbitrary expressions or all future checker paths are depth-safe.

Adversarial inspection covered zero rows, a singleton, odd rows, zero fuel, nonzero fuel,
early composition failure and unconstrained backend values. No blocking finding survived.
The sorted-key qualification and finite-fuel qualification above are scope notes; no source
repair is proposed. A separate second pass checked whether the invariant hypotheses leak
into `directItems_spec` (they do not), and whether lawful addition requires positivity (it
does not). All work was performed by this independent auditor; no second-agent receipt is
being represented as independent verification.

## Independent verification receipts

All auditor Lean/Lake commands were serial, with `LEAN_NUM_THREADS=1`; direct Lean and
leanchecker commands ran under `nice -n 5`. Build calls used the prescribed compile gate,
which itself runs `nice -n 5 lake build`. Existing overlay/cache artifacts were reused;
these are successful targeted build checks, not claims of a clean full rebuild. No library
clean, cache fetch, dependency edit, toolchain edit or resource-budget override was performed.

### Targeted builds and tests

For each module M below, separately and sequentially:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-sokdepthl "$M"
```

`KAM.Certificate.Model.FixedEq`: exit 0, `Build completed successfully (2915 jobs).`
The following 42 further invocations all exited 0 (155.51 seconds combined, including gate
and cache validation). There are **33 test modules**: 20 base, 7 Sharp, 6 V2.

```text
KAM.Certificate.Soundness: exit 0, 3.60s
KAM.CertificateSharp.Sound: exit 0, 3.36s
KAM.CertificateSharp.V2.Engine: exit 0, 3.07s
KAM.CertificateSharp.V2.RouteARefinedEngine: exit 0, 3.87s
KAM.SpinOrbit.Graph.Cert: exit 0, 3.49s
KAM.SpinOrbit.LunarAssembly: exit 0, 3.66s
KAM.SpinOrbit.Lock.Confine: exit 0, 3.28s
KAM.SpinOrbit.Lock.Coords.Conjugacy: exit 0, 3.54s
KAM.SpinOrbit.Lock.Coords.Inverse: exit 0, 4.00s
KAM.Certificate.Tests.Ball: exit 0, 4.55s
KAM.Certificate.Tests.ComplexExp: exit 0, 3.46s
KAM.Certificate.Tests.Compose: exit 0, 3.12s
KAM.Certificate.Tests.Defs: exit 0, 3.07s
KAM.Certificate.Tests.Gram: exit 0, 2.93s
KAM.Certificate.Tests.Model: exit 0, 3.03s
KAM.Certificate.Tests.Negative: exit 0, 3.23s
KAM.Certificate.Tests.Packed: exit 0, 3.15s
KAM.Certificate.Tests.Positivity: exit 0, 3.10s
KAM.Certificate.Tests.Rat: exit 0, 3.04s
KAM.Certificate.Tests.RatData: exit 0, 3.25s
KAM.Certificate.Tests.Torsion: exit 0, 2.76s
KAM.Certificate.Tests.Toy2: exit 0, 3.26s
KAM.Certificate.Tests.Toy2Data: exit 0, 3.07s
KAM.Certificate.Tests.Toy2d: exit 0, 3.52s
KAM.Certificate.Tests.Toy2dData: exit 0, 4.86s
KAM.Certificate.Tests.Toy3: exit 0, 4.46s
KAM.Certificate.Tests.Toy3Data: exit 0, 4.66s
KAM.Certificate.Tests.ToyLit: exit 0, 4.21s
KAM.Certificate.Tests.Witness: exit 0, 4.29s
KAM.CertificateSharp.Tests.BallsTrig: exit 0, 4.53s
KAM.CertificateSharp.Tests.Corner: exit 0, 4.15s
KAM.CertificateSharp.Tests.Frame: exit 0, 3.31s
KAM.CertificateSharp.Tests.FreqTests: exit 0, 4.52s
KAM.CertificateSharp.Tests.Margin: exit 0, 3.48s
KAM.CertificateSharp.Tests.Shared: exit 0, 3.11s
KAM.CertificateSharp.Tests.Step0Coh: exit 0, 3.60s
KAM.CertificateSharp.V2.Tests.FrameFacts: exit 0, 4.32s
KAM.CertificateSharp.V2.Tests.Frozen: exit 0, 4.15s
KAM.CertificateSharp.V2.Tests.Refined: exit 0, 5.02s
KAM.CertificateSharp.V2.Tests.RefinedR1: exit 0, 4.20s
KAM.CertificateSharp.V2.Tests.TrigCombined: exit 0, 4.35s
KAM.CertificateSharp.V2.Tests.TrigFacts: exit 0, 3.88s
```

Replay warnings in 32 distinct locations are all in unchanged dependencies/consumers
(unused arguments/variables/tactics or deprecations); none is in the five audited files.
The handoff's old statement that Sharp tests/soundness do not exist refers to its original
base, not this landing branch: both were found and checked here. The reported 10687-job
full KAM build is the orchestrator's receipt; it was not independently rerun.

### Exact old-header probes and axiom closure

Four transient examples used the literal `inp` headers of `weightedNormUp_bound`,
`CertModel.norm_le_supBound`, `directItems_spec` and `composeOps_sound`, and applied the
current export to its explicit binders in their original order. For example:

```lean
variable {α : Type} [CertArith α] [LawfulCertArith α]
example (n : ℕ) (as bs : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    ‖CertPoly.eval n ⟨as⟩ θ * CertPoly.eval n ⟨bs⟩ θ - errTermsEval n (directItems as bs) θ‖ ≤
      errTermsErr n (directItems as bs) θ := by
  exact directItems_spec n as bs θ
```

The same probe imports FixedEq, Compose and all three soundness modules and executes
#print axioms for every new/moved public theorem, the four compatibility/main contracts,
and the three consumer exports (25 checks):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-signatures-axioms.lean
```

Exit 0. Exact axiom output:

```text
'KAM.Certificate.CertFixed.eq_of_m' does not depend on any axioms
'KAM.Certificate.CertModel.norm_le_supBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.weightedNormUp_fixed_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.weightedNormUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeOpsAux_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeOps_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.directItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errRep_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errRep_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.foldr_upAdd_fixed_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.foldr_upAdd_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pairRounds_fixed_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pairRounds_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.rowsRep_foldl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.rowsRep_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.rowsRep_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumPairsUp_fixed_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumPairsUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumUp_fixed_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.weightedNormUp_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkTorusCertificateV2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No provider=frozen or seal-body probe applies: no provider or frozen theorem is part of
this implementation delta. Production imports add only BalancedSum; the audited modules
import no provider or DRAFT_SORRY anchor. The frozen strip definition they use is
`kam.complexStrip.v1`, `KAM.complexStrip`, state SEALED; its literal body remains
`{θ | ∀ i, |(θ i).im| < ρ}`.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Certificate.Arith.BalancedSum KAM.Certificate.Model.Basic \
  KAM.Certificate.Model.Terms KAM.Certificate.Model.FixedEq KAM.Certificate.Expr.Compose \
  KAM.Certificate.Soundness KAM.CertificateSharp.Sound KAM.CertificateSharp.V2.Engine
```

Exit **0**, one invocation. Exact output:

```text
replaying KAM.CertificateSharp.V2.Engine
replaying KAM.CertificateSharp.Sound
replaying KAM.Certificate.Soundness
replaying KAM.Certificate.Expr.Compose
replaying KAM.Certificate.Model.FixedEq
replaying KAM.Certificate.Model.Terms
replaying KAM.Certificate.Model.Basic
replaying KAM.Certificate.Arith.BalancedSum
```

### Fresh kernel-only depth / edge probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-depth.lean
```

Exit **0**, no output, no option overrides. Full reproducible probe:

```lean
import KAM.Certificate.Model.FixedEq
import KAM.Certificate.Expr.Compose
open KAM.Certificate KAM.Certificate.CertArith
noncomputable section
def auditW : CertWeight := ⟨0, 1⟩
def auditP : CertPoly (CertFixed 4) := ⟨List.replicate 4097 ([0], ⟨⟨1⟩, ⟨0⟩⟩)⟩
example : (auditP.weightedNormUp auditW).m = 4097 := by decide +kernel
-- Odd count exercises a carried singleton at every level.
def auditAs : List (CertKey × CC (CertFixed 4)) :=
  List.replicate 1025 ([0], ⟨⟨16⟩, ⟨0⟩⟩)
def auditBs : List (CertKey × CC (CertFixed 4)) := [([0], ⟨⟨16⟩, ⟨0⟩⟩)]
example : (directItems auditAs auditBs).map (fun t => t.2.1.re.m) = [16400] := by decide +kernel
example : directItems ([] : List (CertKey × CC (CertFixed 4))) auditBs = [] := by decide +kernel
-- Fuel zero: the fallback retains the representation and computes the exact fixed sum.
example : (mergeRowsTree 0 ((auditAs.take 5).map (fun s => rowItems s auditBs))).map
    (fun t => t.2.1.re.m) = [80] := by decide +kernel
-- A long successful composition must expose a state field, not merely `some`.
def auditK : CertEmbedding (CertFixed 4) := ⟨[], [], [], []⟩
def auditWit : Witnesses (CertFixed 4) := ⟨[], [], []⟩
def auditCfg : ModelConfig (CertFixed 4) := ⟨0, 0, 0, fun _ _ => none, []⟩
def auditPi : PiEnclosure (CertFixed 4) := ⟨⟨0⟩, ⟨0⟩, 0, 0⟩
example : (composeOps 1 auditK auditWit auditW auditCfg auditPi
    (List.replicate 2049 (.const 0 0 0))).map (fun st => st.len) = some 2049 := by decide +kernel
```

The deliberately old-fold control on the same 4097 identical fixed terms was run separately:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-old-control.lean
```

Exit **1** (expected negative control). Exact output:

```text
.lake/abi-scratch/maud-old-control.lean:7:44: error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit
```

The control used the old `terms.foldr (fun t acc => upAdd (upMul t.2.normUp
(ofRatUp ((1 : ℚ) ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)` and tested mantissa
4097. This failure is evidence of the original design issue; no suggested recursion-depth
increase was applied. The corresponding new weightedNormUp probe passes at default limits.

The handoff's 20000-term and real-R1 performance figures were not independently reproduced.
Its incomplete/OOM/interrupted R1 sub-checks are not promoted to successful certificates.

### Source hygiene

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Certificate.lean)
check_lean_modules: PASS (1641 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

The stale item is the generated root part `KAM/Root/Certificate.lean`; neither root nor its
parts were regenerated or edited. Unlike the original prover branch, this landing branch has
no `.drafts/kd` module-check failure. The current ABI count is 158, superseding the original
handoff's 144. All substantive source lint checks pass; landing must refresh the generated
root through the orchestrator's normal process.


Additional checks:

```sh
git diff inp...HEAD --check
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
git diff --name-only inp...HEAD -- KAM/CertificateSharp KAM/SpinOrbit/Lock
```

All exit 0, empty output. The latter consumer trees are byte-unchanged across the audited
diff; the rest of the diff changes no certificate data structure or signed consumer file.
All five files have the copyright/module/public imports/module docstring/public section
scaffold and exposed unfolding definitions. Line counts: 78, 263, 547, 503, 81;
maximum line widths respectively 95, 99, 99, 99, 97 characters. No banned tokens,
resource overrides or EuclideanSpace appear in their executable code.

## Closeout, uncertainties, errata and deviations

- Completed: full branch diff, old-header/moved-body comparison, every new definition and
  theorem classified, producer-to-consumer proof inspection, old-header applications,
  43 targeted build invocations, all 33 tests, 25 axiom probes, eight-module kernel replay,
  fresh default-limit positive probes and a discriminating old-fold negative control.
- No suspected defect in a pinned mathematical source or blueprint was discovered. The
  handoff's sorted-factor shorthand needs the padding/strict-row qualification above;
  its original-base Sharp absence statements are superseded by its own landing addendum.
- No new premise, carrier change, certificate-format change or mathematical deviation was
  introduced. Frozen files and manifests remain untouched. No anchor is claimed newly sealed.
- FixedEq is intentionally not yet imported by production modules; its equality theorem
  independently certifies fixed-backend value preservation. Existing Terms importers still
  reach BalancedSum through the public model import chain.
- Remaining limits: generic rounded-backend values depend on grouping; directItems list
  equality is argued on strict rows, not proved universally in Lean; finite-fuel depth
  qualifications and actual R1 memory/runtime remain as stated above.
- Only this report persists as an auditor-authored repository change. Temporary probes and
  audit logs under `.lake/abi-scratch/maud-*` were removed after transcribing their receipts.
