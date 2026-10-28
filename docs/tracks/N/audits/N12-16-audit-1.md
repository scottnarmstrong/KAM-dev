# N12-16 independent package audit 1

Audit date: 2026-10-28. Audited HEAD: `f4b6fc279c6c7d448abcbc5c451d592f78dcd594`.

## Verdict and scope

**PASS WITH NOTES** for N12-16, supported by the completed check receipts below. The two public helpers implement their approved contracts without added premises. This is an infrastructure-package judgment for the future N12-18 `averaging_mean` provider, not a seal of the frozen anchor. `KAM.Nekhoroshev.averaging_mean` remains `DRAFT_SORRY` in the manifest; this package adds no provider export or seal body.

Audited production file: `KAM/Nekhoroshev/Averaging/Mean.lean`, 169 lines, SHA-256 `5feb7c2cfbeef99dbc9842d9ceb0c6162aa16593595bcc9891f450007a4c066a`.
Read AGENTS, PLAN, DECISIONS, the package audit brief, handoff, design row N12-16 and consumer table, both design audits, approved signature file, Part 12 mean proof, track statement, frozen mean anchor and relevant definitions, and the consumed GoodSet/Stopped/flow interfaces. The delta design audit resolves the earlier unrelated `wreg` omission. No subagents or production edits were used. The user's exact worktree report path overrides the generic brief's main-worktree destination.

The approved external signature file is `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`, SHA-256 `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`. Both `mean_family` and `averaging_mean_core` have identical whitespace-normalized declaration headers; temporary examples also check their elaborated applicability.

## Comparison caveat

Executed `git diff inp...HEAD` as requested. At comparison, `inp` was `31f0bfbf70c07b1eefd006237f331c00e003a0e5`; Git warned:

```text
warning: inp...HEAD: multiple merge bases, using fdd44199ddea0cb6007c938ddf930ee3e6eefc24
```

That comparison includes 120 files / 18775 insertions from other merged work. The requested `inp-n1215...HEAD` comparison likewise includes inherited changes because that ref is not the immediate package parent. Neither broad diff is represented as a one-file diff. `git show --stat HEAD` and `git diff HEAD^ HEAD --name-only` isolate the N12-16 commit and show exactly the 169-line new Mean file; its parent is `835a711` (merge of N12-15).

The literal protected-path test `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: it contains inherited additions to `KAM.lean`. The root's last change before this package is `872a014`, the orchestrator regeneration commit. Frozen files, manifest and README have no changes in that comparison. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the generic branch-wide hygiene condition has an inherited exception; no N12-16 protected-path edit was found. The root was not regenerated during this audit.

## Declaration and node ledger

All declaration names below are in `KAM.Nekhoroshev`.

| Node / declaration | Lean location | Verdict | Reason |
|---|---|---|---|
| Private equality helper | `averagingError_eq_flow`, Mean:33 | PASS | Pointwise equality on exactly the time interval gives equality of the two supremum images; no regularity assumption or changed error definition. |
| `stepN:p12:me-flow` | `mean_family`, Mean:44–68 | PASS | Converts the supplied genuine solution to `ODE.IsSolutionIn` and applies the proved `avgMaximal_spec` maximality clause. Initial membership is established from the inner ball. Both full-window existence and equality are conclusions. |
| `stepN:p12:me-cont` | `mean_family`, Mean:69–86 | PASS | Restricts continuity of the genuine flow maximum to K, transfers it by equality, then proves integrability on compact K. Nonempty time image and bounded actions guard the real sSup; every displacement is bounded by it. |
| Public `mean_family` contract | Mean:44–55 | PASS | Exactly the approved signature. Arbitrary family values away from K do not enter regularity or integrability. Bound is `0 ≤ m ≤ 3R/2`. |
| `bpN:p12:s-mean#data` | `averaging_mean_core`, Mean:103–104 | PASS | Chooses `A=13*A₁>0` after fixed data/K, before ε, Φ and κ. A₁ is obtained from `bad`, not assumed. Core permits ε≤1. |
| `stepN:p12:me-good` | Mean:108–114 | PASS | On good data at R/8 the attained flow maximum is ≤ avgStopped; equality transfers it to the supplied family. |
| `stepN:p12:me-bad` | Mean:115–121 | PASS | On bad data, `R/8 ≤ avgStopped` and `m ≤ 3R/2 = 12*(R/8)` imply `ofReal m ≤ 12*avgStopped`. The lower bound is nonstrict, including equality at the threshold. |
| `stepN:p12:me-mean` | Mean:122–129 | PASS | Uniform pointwise bound `ofReal m ≤ 13*avgStopped` integrates to the exact required ENNReal mean bound, with no measure normalization. |
| `stepN:p12:me-markov` | Mean:131–165 | PASS | Positive λ=A√ε/κ; E={x∈K : λ<m(x)} is measurable by continuity on the subtype K. Integrating over E and cancelling the finite positive ofReal λ gives volume E≤ofReal κ. Complement bound holds at every time. |
| Public `averaging_mean_core` contract | Mean:89–101 | PASS | Exactly the approved signature and frozen error/volume carriers. ε₀=1 is the designed strengthening. No family measurability or bound premise is introduced. |
| Frozen `averaging_mean` consumer | frozen anchor + design:388–395 | PASS WITH NOTES | Thin assembly with ε₀=1 checked against the literal frozen telescope in a fresh theorem. Actual provider export/type equality and literal provider seal application are N/A here: no provider was added. N12-18 still owns that export and sealing checks. |

## Proof and definition review

No new `def`, `abbrev`, `structure`, or global instance occurs in Mean. The local `A`, `lam` and `E` are exactly 13*A₁, A√ε/κ, and the superlevel subset of K. No junk fallback is introduced.

Inherited `AveragingData` contains only dimension/positivity, analyticity, perturbation and frequency-rank premises. `IsSolutionOn` asserts genuine two-sided Hamiltonian derivatives and membership in the action domain, so the supplied family is existence/typing data, not the desired estimate. `avgH` is definitionally the frozen real Hamiltonian with ε*f; phase types are real Pi products and action norms are the maximum norm.

The inherited `avgFlow` choice has an outside-domain fallback. Every use in this proof is guarded by initial-domain membership and the maximal time interval, established by maximality; no fallback value is used. `averagingError` is the frozen real supremum on Icc(0,1/ε). Positive ε makes that interval nonempty, and the actual solutions stay in the bounded action ball. The proof supplies its upper bound and each displacement-to-supremum comparison explicitly. The empty-K case is harmless.

`bad` comes from N12-15 and re-derives its witnesses from N12-14 `stopped`; those are proved results rather than extra bundled assumptions. The Mean proof uses the exact three `bad` conclusions: integral bound, threshold on bad data, and pointwise domination on good data. A recursive local KAM import scan visited 90 files and found **no provider imports and no frozen theorem imports**. Only frozen definitions occur, so no DRAFT_SORRY theorem or sealed-theorem exception is needed.

The proof replaces the blueprint's separate integral/measure split over good and bad data with the valid pointwise majorization `ofReal m ≤ 13*avgStopped`. On good data the sharper factor is 1, and on bad data it is 12. Using 13 uniformly preserves the prescribed A and conclusions. This is a proof-route simplification, not a source-statement deviation. It need not separately export the intermediate bad-set measure inequality, since this package promises the exact approved assembly signatures.

## Independent checks

Commands ran from `/root/code/KAM-inp-n1216`. The build completed before the signature/assembly probe, which completed before kernel replay, which completed before the authoritative lint rerun. Each authoritative invocation explicitly uses `LEAN_NUM_THREADS=1`; the build gate supplies `nice -n 5`, and other invocations specify it directly.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1216 KAM.Nekhoroshev.Averaging.Mean
```

Exit **0**. Output begins `[inp-gate] slot 2 acquired 12:40:12 for KAM.Nekhoroshev.Averaging.Mean` and ends:

```text
Build completed successfully (3248 jobs).
```

No Mean warning. Replayed dependency warnings concern unused variables/section variables, deprecated names and an existing `haveI` style suggestion in Shells, EnvelopeIntegrals, PicardFamilies, LocalDependence, CompactMaximum, ODE.Exit, CorrectorRegular and Transport. No elaboration budget override was used.

### Signature, frozen-consumer and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n1216-audit-probe.lean
```

Exit **0**. Each approved signature was copied into an `example` and discharged by the corresponding implementation theorem. A fresh `audit_frozen_assembly` copies the literal frozen theorem telescope and conclusion, constructs `AveragingData` from its source premises (`2 ≤ n` gives `1 ≤ n`), obtains the core witnesses and returns `(A,1)` with the positive-constant proofs. It imports Mean only, so it cannot use the frozen sorry or a provider. Its body is:

```lean
  let d : AveragingData n R s h f := ⟨by omega, hR, hs, hh, hf, hrank⟩
  obtain ⟨A, hA, hcore⟩ := averaging_mean_core d K hK hKI
  exact ⟨A, 1, hA, by norm_num, hcore⟩
```

Exact axiom output:

```text
'KAM.Nekhoroshev.mean_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.averaging_mean_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_frozen_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The frozen/provider `type_of%` comparison and proposed literal provider seal body are not claimed as tested: this package has no provider implementation. The fresh frozen-type assembly verifies consumer applicability without treating a placeholder provider as proved.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Mean
```

One invocation, exit **0**. Complete output:

```text
replaying KAM.Nekhoroshev.Averaging.Mean
```

### Source lint and static hygiene

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (630 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure, forbidden token, line-length or file-size finding was emitted. This is PASS under the audit brief's stated stale-root exception; the raw exit code is preserved here.

Static inspection: Mean has the copyright/license/authors header, `module`, one `public import`, module docstring and exposed public noncomputable section; no forbidden proof token, heartbeat/recursion/synthesis override or EuclideanSpace occurs. It is 169 lines, below 1500. `git diff --check HEAD^ HEAD` and `git diff --check` exit **0** with no output. Frozen/manifest/README comparison is empty; the inherited root exception is documented above.

## Defects, deviations and remaining limits

No suspected mathematical source, blueprint, frozen-statement or helper-signature defect was found in the audited surface. No errata-ledger change is proposed. Notes: inherited branch/root comparison exception above; existing dependency warnings; equivalent proof-route simplification above; and provider/seal work remains outside this package.

An initial `sh scripts/lint_sources.sh` was stopped (exit 143) after discovering its internal Lean ABI subprocess, because that invocation did not explicitly set the requested thread count/niceness. The authoritative lint rerun below uses `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` and is serialized with the other completed Lean checks. This is an audit execution correction, not a production change.

Only this report is retained. Audit probes are removed from `.lake/abi-scratch/`; no state-changing git operation, frozen edit, generated-root edit, package update or clean was performed.
