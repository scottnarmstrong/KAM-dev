# Seal audit SJSU-1: D76 T2-CONF, refute-first

**Verdict: FAIL — non-ledger replay gate remains open for two modules (rc=137).**
Byte identity, manifest, guard/ABI, Expr equality, axioms, facades/quarantine, builds and lint pass.
The updated combined core replay receipt passes; the non-ledger log ends `replayed=192 failed=2`.

Independent auditor; I authored none of the audited files. Method: `lean-statement-audit`.
Brief: `.drafts/g2/AUDIT-SEAL-launch.md`; model: `docs/tracks/B/freeze/SEAL-AUDIT-HH-1.md`.
Worktree `/mnt/HC_Volume_106379410/kam-sjsu-g2`, branch `inp-sjsu-g2`.

**Audited HEAD / freeze commit:** `faded37583893ac8c5991211ad7c085ba2dc0446`.
**Pre-freeze base:** `f9a5f9548` (main supplied by the launch).
**Approval object:** `793d59797:docs/explorations/sjsu-g2-t2conf-proposal.md`, draft v2;
D76, Scott Armstrong, 2026-11-06 16:05 UTC (`docs/DECISIONS.md`, also the program decision log).
D76 approves freezing and sealing in one pass with the exact approved declaration text.
There is consequently no intermediate DRAFT_SORRY anchor to compare.

Only this report and probes/evidence under `.drafts/g2/scratch/aud-seal/` are audit deliverables.
No source, manifest, generated root, receipt or producer was edited; no commit was made.
The unrelated untracked ledger outputs present at entry were preserved.

## 1. Byte identity — PASS

`identity.py` obtains the proposal with `git show` at the approval commit, independently slices its
fenced Lean blocks and the frozen declarations, writes the slices, and runs `cmp` for the four
complete approved blocks. This includes declaration docstrings, statement/type and definition bodies.
The module headers and freeze-time module docstrings are administrative wrappers, outside those
approved declaration spans. No declaration whitespace was normalized: slicing removes only the
Markdown/file delimiters. The data-table hash span ends at `]`, excluding the following newline;
the four complete fenced blocks include their final newline.

| Approved declaration text | Bytes | SHA256 (identical approved/frozen) |
|---|---:|---|
| `sjsuTerm` | 294 | `b84f570a83bff5c8d0b63cdf88dfb501368af7570bcb5d1b1c847fdf1981a2c0` |
| `sjsu18O2Terms` | 256 | `481e13d41937b4701750446fe95e001d2bbfde52431b3dd056d09f896842523c` |
| `sjsu18O2` | 695 | `4d0f371130fa2ab1548a62c7790d39e4fb469e027e9d60eb46498bd184b9e977` |
| confinement docstring + statement | 2103 | `c2b403032e8ee4b4cf322c18adfdfff8ef372a6a0adeacee9caef6fd28f02d88` |

All six definition-text hashes equal the approval table, including their row docstrings:

| Part | Rows | SHA256 |
|---|---:|---|
| 0 | 1324 | `6d39b3be7706097ab81b20247b2d22211a145253f23daec5df8806604a9e997b` |
| 1 | 1324 | `1d64722ff317478ba69bb2991177eafb3bc61631914a95374c8d8a46eb207de9` |
| 2 | 1324 | `5b2ccffe12002514218f8ff98b5123872b75ab1520d24ce9aa1bd7b8da22a8c7` |
| 3 | 1324 | `c6e58527b1d9dd7806d931825ecdcd2ee34c2a40aa0f32b974bcd15a127ccd63` |
| 4 | 1324 | `a26f0b35939a67d27a9616f96ad8ba6d82de23000602ccbca572218136aa39f5` |
| 5 | 1321 | `10cc55d4d29374655ef89e4fd71b943d25d4cb69250aafafc6ba99f715deb43b` |

The 7,941 rows were additionally parsed independently and compared in order, including every exponent
and coefficient string, against `complex_form.terms` in `applications/sjsu/data/sjsu18-o2.json`.
The JSON hash is `702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772`, as approved.
All nine frozen data files equal their committed HEAD bytes. The theorem statement and provider
statement slices are byte-identical, with no additional premise.

The anchor's complete seal body is one line, 79 UTF-8 bytes:

```lean
  by exact KAM.Provider.EffectiveStability.sjsu_secular_confinement z₀ hz₀
```

The provider applies exactly `KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof z₀ hz₀`.
Its only import is the implementation module `KAM.EffectiveStability.SJSU.Confinement.Proof`.

## 2. Manifest — PASS

The ten new IDs are `effectiveStability.d76.<name>.v1`, for `sjsuTerm`, `sjsu18O2Part0` through
`Part5`, `sjsu18O2Terms`, `sjsu18O2`, and `sjsu_secular_confinement`.
Each owns its one file under `KAM/Frozen/EffectiveStability/SJSU/` and exports
`KAM.EffectiveStability.<name>`. Their kinds are nine definitions and one theorem; all are SEALED.
All have Scott Armstrong's D76 approval dated 2026-11-06, approval/contract version 1,
NOT_SPLIT, and the proposal revision `793d59797` (D76 recorded at `1043ebed2`).
The theorem's implementation entry identifies the exact provider module/export named above,
with empty draft allowlists. All ten ABI hashes are nonzero 64-digit hexadecimal values.

Independent JSON comparison against `f9a5f9548` finds exactly these ten additions, no deletion or
modification of any previous entry, and no change to other manifest metadata. The only changed path
under `manifest/` is `frozen-anchors.json`. `docs/MANIFEST-CHANGES.md` has a row for each new ID.
Every frozen Lean file in the repository has exactly one manifest owner.

Recomputed full-file hashes match for all nine definitions. The independently enumerated transitive
frozen-definition import sets, excluding provider imports, exactly match all ten closure lists;
every listed file hash matches. Closure sizes are 0 for `sjsuTerm`, 1 per part, 7 for Terms, 8 for H,
and 13 for the theorem. The theorem includes the nine data definitions plus HamiltonianVectorField,
OscillatorAction, IsDiophantine and SymplecticForm (the last two are transitive imports).

The independently sliced prefix and suffix hashes match:

```
prefix 0a5f720c4f1ee09037954ea0fbd751c389adddfef8da98eab370730132e4855c
suffix 1f2d3361e67df6513a908669be93f0cc58c90f735bf44b2560787c0177a9caa8
```

## 3. Guard and ABI — PASS

`python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`
returns `FROZEN-ANCHOR GUARD OK`, rc=0. Checks and process exit statuses are recorded in the
final receipt table below. The KAMSJSU ABI
check reports `ABI HASHES OK (10 frozen declarations of KAMSJSU; ...)`. Its explicit scope is these
ten declarations; other applications and the core are not claimed to have been ABI-rechecked here.

## 4. Expression equality, mathematics and binders — PASS

The prescribed data check ran through `.drafts/g2/g2lake env lean .drafts/g2/freeze/check/ExprEq.lean`.
It proves the literal data lists equal the frozen constants by kernel decisions, then Terms and H
by ordinary equality; output: `'eq_sjsu18O2' depends on axioms: [propext, Classical.choice, Quot.sound]`.

The independent stdin probe is generated directly from the pinned proposal's theorem block, with
only its declaration name changed. Its body applies the actual anchor to both explicit arguments.
It compares `ConstantInfo.type` with `Expr ==`, plus equality of universe-parameter lists, without
reduction, rewriting or definitional-equality fallback. Results for the anchor, provider and
`KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof` are all:
`Expr == true; levelParams == true`.

Expanded input inventory (no implicit or instance premises, no project-owned assumption bundle):

| Input | Bin | Approved source |
|---|---|---|
| `z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)` | TYPING | v2 theorem, Cartesian phase point |
| `hz₀ : ∀ j, ... ∧ ...` | SOURCE | v2 theorem, literal initial box |
| `j : Fin 3` within `hz₀` | TYPING | v2 component quantifier |
| `hz₀` first conjunct | SOURCE component | v2 ξ bounds about `[0.03446271128616895, -0.0014352339355918572, -0.010122263133599879]` |
| `hz₀` second conjunct | SOURCE component | v2 η bounds about `[-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881]` |

Outer counts: SOURCE 1, STANDING 0, TYPING 1, RULED 0, EXCESS 0.
After replacing the `hz₀` wrapper by its two conjuncts and counting its component quantifier:
SOURCE 2, STANDING 0, TYPING 2, RULED 0, EXCESS 0. The component rows do not introduce new premises.
The nominal point satisfies these bounds, so the initial region is nonempty.

The conclusion retains `∃ T₁ > 5·10⁹`, then one trajectory with initial value, genuine `HasDerivAt`
Hamiltonian dynamics on `(-T₁,T₁)`, agreement with every other solution on an order-connected set
through zero wherever it meets that interval, and both eccentricity bounds for every component
and every `|t| ≤ 5·10⁹`. The variables/premises within the uniqueness clause are inside the
conclusion, not extra assumptions on the anchor.

`hamiltonianVectorField` is literally `(∂H/∂p, −∂H/∂q)`; here `q=η`, `p=ξ`.
`oscillatorAction p q j` is `(p j ^ 2 + q j ^ 2)/2`.
The Hamiltonian uses `(ξ−iη)/√2` and the real part of the exact rational coefficient sum, with
no fallback, choice or alternate carrier. The eccentricity uses the three fixed positive
`Lambda_star` literals and retains intervals `[0.026,0.062]`, `[0.009,0.085]`, `[0.006,0.063]`.
It asserts the approved secular-model observable, not full-system osculating eccentricity bounds.

All nine definitions are literal constructions on the approved carriers. For each:

```
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

The implementation Proof/Eta files are byte-identical to the files audited at `7d67c84d5`
by N9-AUDIT-1. Direct inspection confirms `_proof` supplies `sjsu_hη` and `sjsu_hTη` to `_of_rate`,
which supplies the actual N8 observable facts to `_of_N7`, which supplies the chart identity and
joint differentiability to `_of_obs`. These are proved inputs in the bodies, with distinct helper
names; none is smuggled into the frozen theorem's premises. The fresh compiled application and
Expr check establish the actual anchor → provider → N9 consumption. This seal audit reuses the
package audits; it does not repeat their numerical or analytic proofs.

## 5. Axioms — PASS

Fresh stdin `#print axioms` for the anchor, provider, N9 proof theorem and frozen Hamiltonian each
returns exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, project axiom or
`Lean.ofReduceBool`. Evidence: `expr-statement.out`; the data equality axiom output is in
`expr-data.out`.

## 6. Facades and quarantine — PASS

All nine `KAM/EffectiveStability/SJSU/Model/*.lean` files contain a frozen `public import` and no
definition/theorem/abbreviation. The exact same constants reach every former development consumer.
Across tracked Lean sources the only provider importers are the frozen anchor and
`KAMSJSU/Provider.lean`. The latter is the explicit generated-root exception documented by
`scripts/lint_sources.sh`, consistent with D51 and the HH seal template; no ordinary consumer imports
this provider. KAMSJSU contains the implementation, frozen and provider prefixes, and the implementation
prefix is `application_only`. `gen_root_imports.py --check` succeeds, covering library assignment,
root completeness and the prohibition on core-to-application imports. No generated file was edited.

The largest changed Lean module has 1,354 lines (data parts); anchor 61 lines, provider 43.
No heartbeat/resource override was introduced. `git diff --check f9a5f9548 HEAD` succeeds.

## 7. Builds and replay receipts

The build receipt `.drafts/g2/scratch/g2c/build_lib_freeze.log` was checked independently against
the complete current KAMSJSU source-module set: exactly 4,687 distinct module records, all rc=0,
66 built, 321 individually up to date and 4,300 skipped after successful batch up-to-date checks.
There is a start at 12:11:52Z and a completion at 12:55:56Z on 2026-11-07, with no FAILED record.
This validates the launch receipt's combined 4,621 skipped/up-to-date count. The driver substitution
is explicitly recorded in the program decision log (kam-18, 2026-11-06 21:31 UTC).

`seal-receipts.md` additionally records the 17 generated roots/parts build:
`Build completed successfully (13896 jobs)`, peak 3.8 GB. That line is inherited receipt evidence;
the fresh ABI check independently requires the entire KAMSJSU application to be up to date before
hashing, and fresh targeted builds check the actual anchor/provider without repeating the library.

The supplied replay list is independently equal to the complete non-ledger module set: 194 distinct
modules, including all 11 frozen/provider modules. Exactly 4,493 ledger modules are outside that set.
The launch authorizes core `--fast` plus this non-ledger replay, with the full ledger replay deferred
as a separate follow-up receipt; ledger declarations were kernel-checked during their builds.
This report does not claim a fresh replay of the 4,493 ledger modules or a full core/Mathlib replay.

Replay completed; the final verification and blocking findings are recorded below.

All checks independent of the replay were completed before starting the foreground `until` loop.
The loop is `wait-replay.sh` in the audit scratch directory, with start/finish receipt
`foreground-wait.out`. No replay was relaunched or backgrounded by this audit.

| Check (from repository root) | Exit | Evidence/result |
|---|---:|---|
| `python3 .drafts/g2/scratch/aud-seal/identity.py` | 0 | `identity.out`: all byte, hash, manifest, closure, facade and quarantine assertions pass |
| `python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` | 0 | `guard.out`: FROZEN-ANCHOR GUARD OK |
| `flock .drafts/g2/lake.lock python3 scripts/abi_hashes.py . manifest/frozen-anchors.json --check --lib KAMSJSU` | 0 | `abi.out`: ABI HASHES OK (10 declarations) |
| `.drafts/g2/g2lake env lean .drafts/g2/freeze/check/ExprEq.lean` | 0 | `expr-data.out`: kernel data/H equalities, standard axioms |
| `.drafts/g2/g2lake env lean --stdin < .drafts/g2/scratch/aud-seal/ApprovedStatement.lean` | 0 | `expr-statement.out`: three Expr/universe equality checks and four clean axiom sets |
| `python3 scripts/gen_root_imports.py --check` | 0 | `roots.out`: empty, successful |
| `.drafts/g2/g2lake build KAM.Frozen.EffectiveStability.SJSU.SecularConfinement KAM.Provider.EffectiveStability.SJSUSecularConfinement` | 0 | `build.out`: Build completed successfully (13869 jobs) |
| `sh .drafts/g2/lint_noabi.sh` | 0 | `lint.out`: 23147 modules PASS; 29 guard tests OK; 8 root tests OK; FROZEN-ANCHOR GUARD OK |
| `python3 .drafts/g2/scratch/aud-seal/receipts.py` | 0 | `receipts-check.out`: complete build/replay-list sets; N9 files unchanged |
| `git diff --check f9a5f9548 HEAD` | 0 | no output |

Lint used the prescribed worker variant of `scripts/lint_sources.sh` (`WORKER-RULES.md`, Lint
addendum): identical source checks without its uncontrolled default core-ABI invocation. The
required KAMSJSU ABI invocation was performed separately under the prescribed lock. The full
`scripts/lint_sources.sh` was not run. Targeted builds emitted cached dependency deprecation and
linter warnings; none was an error or a change in the frozen declaration texts.


## 8. Final replay verification — core PASS; non-ledger FAIL

Both foreground waits completed. `foreground-wait.out` records the non-ledger wait from
13:58:29Z to observed completion at 15:22:41Z, followed by the core-resumption wait from 15:22:41Z
to observed completion at 16:14:22Z, all on 2026-11-07. The actual log markers are:

```
replay_nonledger.log: # done 2026-11-07T15:21:55Z replayed=192 failed=2
replay_core2.log:     # done 2026-11-07T16:14:08Z replayed=191 failed=0
```

**Core PASS under the user's updated receipt instruction.** The 14:06 UPDATE in
`seal-receipts.md`, subsequently supplied explicitly by the user, authorizes judging core replay
by run 1 plus the resumed run. Run 1 is not an rc=0 receipt: `replay_core.out` reports batch 50
rc=143 and overall failure after 196/387 modules; kam-g2 attributes that interruption to earlyoom
at peak 16,911 MiB. I retain that fact rather than rewriting it as success. All 49 preceding batches
have rc=0. Its log contains 196 unique successful replay lines, equal to `core/replayed_run1.txt`.

The independent verifier reconstructs the core `--fast` set from the manifest and library mapping,
not just `expected.txt`: exactly 387 modules. `core/remaining.txt` is exactly that set minus run 1,
191 unique modules. The resumed log has exactly one successful final record per remaining module,
zero FAILED records, and `failed=0`. The union is the exact 387-module set with no gap or duplicate.
There are 21 failed-batch retry notes in run 2, all recovered by its final per-module records.
The historical `# core --fast rc=1` in the non-ledger log remains the interrupted run-1 status;
this audit does not claim that literal field is zero.

**Non-ledger FAIL.** There is exactly one final record for every module in
`replay-nonledger.txt` (194 distinct modules), with no missing or extraneous record. Exactly 192
are `replayed`; these include all 11 frozen/provider modules, including the actual anchor and
provider. The two unresolved final failures are:

| Required module | Exact evidence in `replay_nonledger.log` | Result |
|---|---|---|
| `KAM.EffectiveStability.SJSU.Ham.HtBridgeInst` | lines 32–33: individual retry `# rc=137 for ...HtBridgeInst:` followed by `2026-11-07T14:18:13Z ... FAILED` | FAIL |
| `KAM.EffectiveStability.SJSU.Ham.Hw` | lines 42–43: individual retry `# rc=137 for ...Ham.Hw:` followed by `2026-11-07T14:50:33Z ... FAILED` | FAIL |

Both individual retries produced no printed kernel diagnostic. These resource/termination exits
leave the required replay receipts unpaid; they are not a mathematical refutation of either
module. The non-ledger log contains eight retry notes in total. Successful recovery of other
batches does not resolve these two final FAILED records. No further successful receipt for either
module is present in the supplied logs or their final update.

The next acceptance step is successful kernel replay receipts for these exact two modules, under
the orchestrator's resource rules. No Lean statement/proof change is requested by this finding.
No replay restart, resource-policy change or log repair was performed by this auditor.

`finish-replay.py` exits 1, deliberately identifying the failed zero-failure and successful-coverage
gates while still checking the complete resumed core receipt. Its output is `replay-check.out`;
`closeout.out` records the final coverage, frozen/provider success and unchanged source snapshot.
The transient approved-statement Lean probe was removed after recording its checks; `identity.py`
reconstructs it byte-for-byte from the pinned proposal when reproduction is needed.

Receipt fingerprints at closeout:

| File under `.drafts/g2/scratch/g2c/` | SHA256 |
|---|---|
| `replay-nonledger.txt` | `a67a3a1e13ca7216eab2c4cf3f88fbee05c1a15c7360b41ba563dc5e754c4cea` |
| `replay_nonledger.log` | `241056ccd1388bc2518a045027f4ff0a173e1494e8634d571cee19aa58d4dd39` |
| `replay_core.log` | `3c9a4ee722ed552b6d02b3ec30f6d9b8537c38b9b8bb192830a599d16424e20a` |
| `replay_core.out` | `39d3e16f00936109b729643a23067f2cdb0da4a70369292b1327f7be6a68d6f0` |
| `replay_core2.log` | `9e1a440ab009d1932fd81685c1a76610b61504aab71adc7a9b6b5881ee732bd9` |
| `core/expected.txt` | `2717444b588c823af2e02de0ebca05bdbaf34ed3d9de37104a29cdca8c0f0f17` |
| `core/remaining.txt` | `ad50bd307dbadfff63f78f7fe8a132b2747c904f549ee5b3638e1764d0a63c2e` |
| `build_lib_freeze.log` | `f3ca7eb727a702a0f577f3270557f74cc1f29789c2ff92f7cc2344256c09307c` |


## Verdict and handoff

| Launch check | Verdict |
|---|---|
| 1. Approved declaration bytes and provider statement/assembly | PASS |
| 2. Ten manifest entries, exact delta, closure and change rows | PASS |
| 3. Guard and KAMSJSU ABI | PASS |
| 4. Data equality and independent approved-statement Expr equality | PASS |
| 5. Anchor/provider axioms | PASS: exactly propext, Classical.choice, Quot.sound |
| 6. Facades, quarantine, roots and application placement | PASS |
| 7. Build receipts and fresh targeted build | PASS |
| 7. Updated combined core kernel receipt | PASS: 196 + 191 = 387, exact coverage |
| 7. Non-ledger KAMSJSU kernel receipt | **FAIL: 192/194 successful; two final FAILED records** |

**SEAL AUDIT: FAIL.** The exact approved theorem and data pass the declaration, compilation and
axiom checks, but acceptance of this seal remains blocked by the two named kernel replay receipts.
The deferred full ledger replay is also outside this audit's accepted replay scope, as explicitly
specified by the launch; no full-core/Mathlib or full-ledger replay claim is made.

Final HEAD is still `faded37583893ac8c5991211ad7c085ba2dc0446`; no tracked or staged file changed.
Deliverables: this report and the probes/logs under `.drafts/g2/scratch/aud-seal/` only.
Approach: literal-source byte comparison, expanded-input/body review, independent exact-type and
term-consumption checks, then completion-sensitive receipt validation. All exact commands and
outcomes are recorded above. No heartbeat or other design-signal override was used.

Suspected errata in the approved source: none. Declaration deviations introduced by the audited
freeze: none found. Operational deviations: the earlyoom-interrupted core replay and user-authorized
resumption, retained above. Uncertainty: no successful receipt yet for the two non-ledger modules;
rc=137 without a diagnostic does not establish a proof defect. No source repair was attempted.

READY g2-audit-seal-1


## Addendum 1b — resource-terminated retries and kam-18 acceptance ruling

**Final verdict under the revised ruling: PASS WITH NOTES.** This addendum supersedes the
original acceptance verdict under its earlier replay requirement. The historical FAIL verdict,
failed replay records and original audit evidence above remain intact. The ruling changes the
extra replay acceptance scope; it changes no theorem, definition, premise or axiom boundary.

Authority: the user's addendum request relays kam-18's ruling, recorded in the last two UPDATE
lines of `.drafts/g2/scratch/g2c/seal-receipts.md` (16:4x and 16:42): both resource-terminated
non-ledger modules move to the lam replay with the ledger, with the explicit status
**"lam replay pending (with the ledger); kernel-checked at build"**.
The original audited HEAD remains `faded37583893ac8c5991211ad7c085ba2dc0446`.

### Retry and journal verification — PASS as resource-interruption evidence

Read `replay_retry16.sh` and the complete `replay_retry16.log` in the receipt directory. The script
runs exactly these two modules serially, one leanchecker invocation per module, in a systemd scope
with `MemoryMax=16G` and `MemorySwapMax=0`. It accepts only rc=0 with the exact expected `replaying`
line. The actual log is:

```
# start KAM.EffectiveStability.SJSU.Ham.HtBridgeInst 2026-11-07T16:40:17Z
2026-11-07T16:40:38Z  KAM.EffectiveStability.SJSU.Ham.HtBridgeInst  FAILED rc=143
# start KAM.EffectiveStability.SJSU.Ham.Hw 2026-11-07T16:40:38Z
2026-11-07T16:41:26Z  KAM.EffectiveStability.SJSU.Ham.Hw  FAILED rc=143
# done 2026-11-07T16:41:26Z failed=1
```

The two module result lines are both failures; the footer's `failed=1` is the script's boolean
failure flag, not a count of failed modules. Neither retry is a successful replay receipt.
No kernel rejection diagnostic is printed.

Independently read the system journal with:

```
journalctl -u earlyoom.service --since '2026-11-07 16:40:15 UTC' --until '2026-11-07 16:41:30 UTC' --no-pager -o short-iso
```

The journal contains these two kill records, each immediately after a low-memory SIGTERM-limit
message and followed by a process-exited message:

| UTC, 2026-11-07 | Journal process | Exact action / VmRSS | Matching serial retry |
|---|---|---|---|
| 16:40:37 | `earlyoom[981348]` | `sending SIGTERM to process 1674807 uid 0 "leanchecker": badness 1001, VmRSS 15794 MiB` | `Ham.HtBridgeInst`, active 16:40:17–16:40:38 |
| 16:41:24 | `earlyoom[981348]` | `sending SIGTERM to process 1676041 uid 0 "leanchecker": badness 1008, VmRSS 16207 MiB` | `Ham.Hw`, active 16:40:38–16:41:26 |

This verifies external earlyoom termination, consistent with the recorded rc=143 values, rather
than a reported kernel rejection. The metadata wording `replay needs > 16 GB` is operational
shorthand for unsuccessful 16G attempts on this machine: these observations do not establish an
intrinsic memory lower bound greater than 16 GiB. The precise evidence is the two RSS values and
SIGTERM records above. This precision note does not affect the explicit lam-deferral ruling.

### Build/kernel-check evidence — PASS

Both exact modules have direct **built**, rc=0 entries in the already audited freeze build log
`.drafts/g2/scratch/g2c/build_lib_freeze.log`; neither claim relies merely on a skipped module or
a facade. Independently parsed the tab-separated rows and checked their module, status and exit:

| Exact module | Log line | UTC, 2026-11-07 | Status | Wall / recorded peak | rc |
|---|---:|---|---|---|---:|
| `KAM.EffectiveStability.SJSU.Ham.HtBridgeInst` | 1609 | 12:52:39 | built | 1.8s / 1800MB | 0 |
| `KAM.EffectiveStability.SJSU.Ham.Hw` | 109 | 12:21:01 | built | 1.8s / 1124MB | 0 |

The driver records `built` from Lake's successful module-completion output. Its rc is checked
before the run can complete; the original source/guard/lint checks excluded kernel-bypass escapes.
The Lean sources, manifest and scripts are unchanged from the audited HEAD. These are therefore
kernel-checked-at-build receipts for the audited modules. They are distinct from the two pending
additional leanchecker replays, and are not presented as completed independent replay receipts.

### MANIFEST-CHANGES working-tree delta — PASS

Read `git diff -- docs/MANIFEST-CHANGES.md` and independently compared its lines with
`git show HEAD:docs/MANIFEST-CHANGES.md`. Exactly one row changes, line 187: the D76 theorem
`effectiveStability.d76.sjsu_secular_confinement.v1`. Its ID, approval, frozen path, SEALED state,
provider assembly and other row fields are unchanged. Only its evidence field expands the old
`kernel replay; seal audit` wording to the explicit completed and pending scopes:

- core `--fast`: 387 modules;
- non-ledger KAMSJSU including Frozen/Provider: 192 of 194 modules OK;
- the two fully named modules and 4,493 ledger modules:
  `lam replay pending (with the ledger); kernel-checked at build`;
- audit reference `SEAL-AUDIT-SJSU-1`.

The row names both `KAM.EffectiveStability.SJSU.Ham.HtBridgeInst` and
`KAM.EffectiveStability.SJSU.Ham.Hw`; it does not claim that all 194 were replayed successfully.
This is a working-tree documentation delta, not a change to `manifest/frozen-anchors.json`.

### Acceptance and retained pending work

The replay gate was the original audit's only open acceptance item. All other original checks
remain PASS on the same audited source bytes. Under kam-18's explicit resource-deferral ruling:

```
DECLARATION / MANIFEST / ABI / EXPR / AXIOMS / QUARANTINE / BUILDS: PASS (original audited snapshot)
CORE REPLAY: PASS, exact combined 387-module receipt
NON-LEDGER REPLAY COMPLETED: 192 modules, including all 11 frozen/provider modules
RESOURCE-TERMINATED REPLAYS: deferred to lam by the explicit ruling, not reported as successes
FINAL SEAL AUDIT UNDER THIS RULING: PASS WITH NOTES
```

The pending replay work is named explicitly:

1. `KAM.EffectiveStability.SJSU.Ham.HtBridgeInst`;
2. `KAM.EffectiveStability.SJSU.Ham.Hw`;
3. the full KAMSJSU ledger, 4,493 modules.

All three items retain **"lam replay pending (with the ledger); kernel-checked at build"**.
No lam run or completion is evidenced or claimed by this addendum. No theorem statement or
proved input is weakened to obtain this verdict.

Verification used read-only log/journal reads, line/field assertions and the exact documentation
diff. No Lean/Lake command, build, replay or lint was rerun for this report-only addendum; the
previous successful checks are reused because `git diff HEAD -- KAM manifest scripts lakefile.lean`
is empty. The pre-existing working-tree changes in `docs/MANIFEST-CHANGES.md`,
`docs/graph/B/DEPGRAPH.md` and `docs/graph/B/tools/sync.json` were preserved; the graph deltas are
outside this addendum's scope. Only this report was edited, by appending this addendum.

Receipt fingerprints for this addendum:

| Evidence | SHA256 |
|---|---|
| `replay_retry16.log` | `916404d6640513108795b2e55e0d9a88efe01416c442cd9ad757de41b2279cac` |
| `build_lib_freeze.log` | `f3ca7eb727a702a0f577f3270557f74cc1f29789c2ff92f7cc2344256c09307c` |
| `seal-receipts.md` | `3416c0577fcf7ed5191d25fed7b4e540836b2fd9253dcd5c70952005e2aeee4e` |
| `docs/MANIFEST-CHANGES.md` (working tree) | `4634193845f5aac8d1040026b314a077811e7f79fee6e4cee4a01a3c844c0166` |
| Original report before append | `6b3754307ac249d5ef1517a8af8d71a43f0c289d4296e8674df700ede04c4282` |

READY g2-audit-seal-1b
