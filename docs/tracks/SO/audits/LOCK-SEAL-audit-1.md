# LOCK-SEAL independent audit 1

Auditor: maud-lockdesign-1. Date: 2026-11-05 UTC.
Worktree: `/root/code/KAM-inp-lockdesign`; branch `inp-lockfreeze`.
Audited HEAD: `adae232ac577177306929c5490e16667ef6ab425`.
Comparison: `git diff inp...HEAD`, with `inp` at
`c8dae3fee32799b91f4217e63fa32d53142613dc`.

## Verdict per anchor

**PASS WITH NOTES** for each of `KAM.SpinOrbit.lunarSyncOrbit_spec`,
`KAM.SpinOrbit.lunarSyncOrbit_unique`, `KAM.SpinOrbit.lunarSyncOrbit_bound`, and
`KAM.SpinOrbit.lunar_sync_lock`. The seal proof delta passes the independent type,
source-elaboration, kernel-replay, axiom, bridge and ABI checks. No mathematical fix
is requested. These verdicts do not assert that the stale generated application/core
roots have already been regenerated or that the final D63 landing gate has run.
Those integration actions remain with the lander; no heavy data is rebuilt by this audit.

## Scope and controlling text

This is the Phase B seal audit specified by `LOCK-SEAL-handoff.md`, not a new audit of the
unchanged LOCK-DATA certificate internals. Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the LOCK-FREEZE brief, handoff,
four frozen anchors, their defining objects, bridge/providers, landed suppliers and
LOCK-DATA-audit-1's integration discussion. D45, D49, D51 and D63 control this seal.
The generic I/N/P brief's `docs/tracks/SO/statement.md` does not exist, and the I/N/P
blueprints contain no corresponding SO nodes. The applicable statement authority is
`docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` §1, approved exactly by D49,
and `SO-LOCK-DESIGN.md` §§0–1. No unrelated I/N/P theorem is claimed proved.
The user's explicit report destination overrides the generic brief's main-worktree destination.

## Statement, proof and definition review

The branch diff has 13 files: four frozen bodies, four providers, FrozenBridge, four
manifest-state changes, four MANIFEST-CHANGES rows, the application-prefix mapping and
handoff. A direct byte comparison after removing only the proof-marker interiors finds
all four frozen files identical to `inp`. All explicit binders are applied in order:
none; `ψ h`; `φ`; `q₀ p₀ φ₀ h₀`. Manifest JSON comparison finds precisely four changes,
all `state: DRAFT_SORRY -> SEALED`, for `spinorbit.lock.*` theorem entries. Existing
prefix/suffix/ABI hashes are unchanged. No frozen definition changes.

| Node / role | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Orbit predicate bridge | `KAM.SpinOrbit.Lock.frozen_isSyncOrbit_iff` | PASS | Both sides retain C², period one, oddness and the pointwise second-derivative equation; `soField_eq` identifies exactly the acceleration component. |
| Predicate identity | `KAM.SpinOrbit.Lock.frozen_isSyncOrbit_eq` | PASS | Function extensionality and propositional extensionality of the preceding equivalence; no extra premise. |
| Chosen orbit identity | `KAM.SpinOrbit.Lock.frozen_lunarSyncOrbit_eq` | PASS | Unfolds both identical dependent-if choice constructions and rewrites the entire predicate. No unsupported equality of arbitrary choices. |
| Action identity | `KAM.SpinOrbit.Lock.frozen_libAction_eq` | PASS | `rfl` on the full function, including its whole carrier and total real division. |
| LOCK-PO existence provider | `KAM.Provider.SpinOrbit.lunarSyncOrbit_spec` | PASS | Transports landed `Lock.syncOrbit_spec`; no hypotheses. |
| LOCK-PO uniqueness provider | `KAM.Provider.SpinOrbit.lunarSyncOrbit_unique` | PASS | Exactly `(ψ : ℝ → ℝ) (h : IsSyncOrbit ψ)`; conclusion is full function equality. Oddness is retained. |
| LOCK-PO bounds provider | `KAM.Provider.SpinOrbit.lunarSyncOrbit_bound` | PASS | Same pointwise absolute-value bounds `17/1000000`, `27/200000`, for every real phase. |
| LOCK-DATA headline provider | `KAM.Provider.SpinOrbit.lunar_sync_lock` | PASS | Exact frozen telescope from `Data.LockN65.lunar_sync_lock_N65`; only action/orbit identities are rewritten. |
| Existence anchor | `KAM.SpinOrbit.lunarSyncOrbit_spec` | PASS | Exact provider application; frozen signature preserved. |
| Uniqueness anchor | `KAM.SpinOrbit.lunarSyncOrbit_unique` | PASS | Exact provider application with `ψ h`; no restriction to a local class. |
| Bounds anchor | `KAM.SpinOrbit.lunarSyncOrbit_bound` | PASS | Exact provider application with `φ`; both bounds preserved. |
| Headline anchor | `KAM.SpinOrbit.lunar_sync_lock` | PASS | Exact provider application with all four explicit arguments. |

There are no new `def`, `abbrev`, `structure` or instance declarations in this delta.
Classification of the existing meaning-carrying definitions used by the bridges:

* Frozen/landed `IsSyncOrbit`: the intended full C² odd periodic orbit predicate;
  no bundled proof obligation or hidden quantitative assumption.
* Frozen/landed `lunarSyncOrbit`: total classical choice with zero fallback, exactly the
  approved definition. The predicate-identity proof transports the entire construction,
  including fallback. Landed `exists_isSyncOrbit` and `syncOrbit_spec` exclude fallback
  in theorem use; no result obtains its conclusion by relying on a junk orbit.
* Frozen/landed `libAction`: identical quadratic expression on all real Ω, functions ψ
  and physical triples. Real division and `deriv` are total; the headline fixes positive
  rational Ω and the actual smooth orbit, so no singular fallback supplies confinement.
* Frozen/landed `lunarOmega`: both the rational literal `8 / 65`. A separate `rfl`
  probe checks their equality; coercion to ℝ also matches in the headline application.
* `soField`: unchanged frozen physical vector field. `Model.lean:217` proves its explicit
  form `(p, -soVq q φ, 1)` from the derivative of the same frozen potential.

In particular the headline preserves global existence on all real time, the same initial
state, the actual `HasDerivAt` equation with the unchanged frozen `soField`, both bounds
around ψ*, strict `|q-φ| < 1/4`, and uniqueness among all global solutions of that IVP.
The sole initial premise remains the strict action bound `129/10000`; no barrier,
certificate pass, Diophantine property, existence or uniqueness conclusion is assumed.
All such inputs are supplied by the already landed AssemblyN65 theorem.

## Imports, ownership and protected paths

A recursive source-import walk from the four providers visits 14,006 KAM module names,
imports 36 frozen modules (all SEALED definitions), and finds no other provider.
Thus no DRAFT_SORRY theorem or provider supplies a proof. The provider/anchor quarantine
is maintained. No changed file imports a generated root.

`python3 -I scripts/gen_root_imports.py --lib-of ...` assigns FrozenBridge and the three
orbit providers to `KAM`, and the headline provider/anchor to `KAMLunarLock`.
Calling the generator's read-only `classify(load_config())` returns
`Ownership/import classification errors: []`, `Classified modules: 18237`.
The mapping therefore has no forbidden core-to-application edge.

`git diff inp...HEAD -- KAM.lean KAM/Root README.md KAMLunarLock.lean KAMLunarLock lakefile.lean`
is empty. `git diff --check inp...HEAD` exits 0 with no output. The generic protected-path
empty-diff requirement is intentionally inapplicable to the authorized four seal bodies
and four manifest-state edits; the exact exception is verified above. Generated files
remain untouched, as required by the Phase B handoff and rule 10.

## Independent validation

All Lean/Lake/checker operations are serial, `LEAN_NUM_THREADS=1`, default heartbeats,
under `nice -n 5` and a 10 GB memory cap, with no swap allocation to the job. No package
cache, heavy certificate proof, generated root or frozen source was modified.
No `.lake/build` was created in this worktree. The Phase B disk/build exception forbids
that build directory, so the nine changed sources were independently compiled into a
scratch overlay under `.lake/abi-scratch/LockSealAudit1/`, rather than a Lake rebuild.
This is exact-source elaboration, not a claim of a successful application-root build.

The scratch library was populated with symlinks to the handoff's dependency overlay,
then the nine audited `.olean` outputs were replaced by this audit's fresh compilations.
`LEAN_PATH` puts the complete scratch library first, followed by the main worktree's
`lake env printenv LEAN_PATH`, then the real remote lock library directory last.
An initial attempt with the scratch library last failed on a missing main-worktree
FrozenBridge object before provider elaboration. Correcting the search order and
recompiling every audited module resolved this setup error; it was not a proof failure.

Common command prefix (`CAP`), with `LEAN_NUM_THREADS=1` exported:

```sh
flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock \
  systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 nice -n 5
```

For each of the nine modules in the replay command below, the exact source command was:

```sh
$CAP lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true -Dlinter.deprecated=true \
  -R . -o "$SCRATCH/lib/${MODULE_AS_PATH}.olean" "${MODULE_AS_PATH}.lean"
```

All nine exit 0, with empty output. File sizes are 29–47 lines; all have the copyright,
`module`, interface imports, module docstring and public section. No forbidden proof
escape, resource override, conclusion-shaped hypothesis or meaning-changing carrier
was introduced. The triple state type is the pre-existing owner-approved SO statement.

Kernel replay command (one invocation, nine leaf modules):

```sh
$CAP leanchecker --verbose \
  KAM.SpinOrbit.Lock.FrozenBridge \
  KAM.Provider.SpinOrbit.LunarSyncOrbitSpec \
  KAM.Provider.SpinOrbit.LunarSyncOrbitUnique \
  KAM.Provider.SpinOrbit.LunarSyncOrbitBound \
  KAM.Provider.SpinOrbit.LunarSyncLock \
  KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitSpec \
  KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitUnique \
  KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitBound \
  KAM.Frozen.SpinOrbit.Theorems.LunarSyncLock
```

Exit 0; complete output:

```text
replaying KAM.Frozen.SpinOrbit.Theorems.LunarSyncLock
replaying KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitBound
replaying KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitUnique
replaying KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitSpec
replaying KAM.Provider.SpinOrbit.LunarSyncLock
replaying KAM.Provider.SpinOrbit.LunarSyncOrbitBound
replaying KAM.Provider.SpinOrbit.LunarSyncOrbitUnique
replaying KAM.Provider.SpinOrbit.LunarSyncOrbitSpec
replaying KAM.SpinOrbit.Lock.FrozenBridge
```

The replay checks the named module bodies against their imports; it does not replay
every imported certificate body. That unchanged chain belongs to LOCK-DATA.

Probe command: `$CAP lean "$SCRATCH/Probe.lean"`, exit 0. The probe imports the nine
modules above and contains each `example : type_of% @KAM.SpinOrbit.<name> :=
@KAM.Provider.SpinOrbit.<name>`, four fresh declarations copied from the actual frozen
telescopes with their actual seal bodies, and `example : KAM.SpinOrbit.lunarOmega =
KAM.SpinOrbit.Lock.lunarOmega := rfl`. All type/seal examples produce no diagnostics.
An initial probe generator accidentally matched the words "theorem" in a module docstring;
its syntax errors were corrected by matching the actual declaration line. The complete
corrected probe was rerun, including every axiom query; no package edit was needed.

Complete corrected `#print axioms` output (all eight exports and four new helpers):

```text
'KAM.SpinOrbit.lunarSyncOrbit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_sync_lock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunar_sync_lock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.frozen_isSyncOrbit_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.frozen_isSyncOrbit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.frozen_lunarSyncOrbit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.frozen_libAction_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

ABI probe command: `$CAP lean "$SCRATCH/Hash.lean"`, exit 0. It imports the four
actual sealed anchors, sets only `pp.all true` and `pp.oneline false`, prints a boundary
marker before each `#check @<export>`, and hashes the stripped result using the exact
SHA-256 normalization in `scripts/abi_hashes.py`. All four manifest hashes match:

```text
KAM.SpinOrbit.lunarSyncOrbit_spec: 3da1e71aa0ff41f1bb7ea4aa392df5889b3194f634061cac6bceeb9bf62a3c88 expected 3da1e71aa0ff41f1bb7ea4aa392df5889b3194f634061cac6bceeb9bf62a3c88 MATCH
KAM.SpinOrbit.lunarSyncOrbit_unique: 009cd93863ea628dbbec41f73c10e9677de4a59ec8f8228aacbabf29dfe1c882 expected 009cd93863ea628dbbec41f73c10e9677de4a59ec8f8228aacbabf29dfe1c882 MATCH
KAM.SpinOrbit.lunarSyncOrbit_bound: 66204b3b1d9f70de2381676d82a181bd3f34a68f3d1f8ac186212cd27d750e0d expected 66204b3b1d9f70de2381676d82a181bd3f34a68f3d1f8ac186212cd27d750e0d MATCH
KAM.SpinOrbit.lunar_sync_lock: 5ccf9ade60178773223d4deb74440bf1f7a23ba89225c542137cf525109aa4dc expected 5ccf9ade60178773223d4deb74440bf1f7a23ba89225c542137cf525109aa4dc MATCH
```

Full lint command: `$CAP sh scripts/lint_sources.sh`, from this worktree with the
serial environment above. Exit **1**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Frozen.lean, KAM/Root/Provider.lean, KAM/Root/SpinOrbit.lean, KAMLunarLock/Frozen.lean, KAMLunarLock/Provider.lean, KAMLunarLock.lean, lakefile.lean)
check_lean_modules: PASS (18345 Lean files, 0 comparator configurations)
.............................
----------------------------------------------------------------------
Ran 29 tests in 4.262s

OK
........
----------------------------------------------------------------------
Ran 8 tests in 0.008s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (315 frozen declarations of KAM; checked by file hash only, not built by this run: KAMHenonHeiles: KAM.EffectiveStability.henonHeiles_confinement (--lib KAMHenonHeiles); KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand); KAMLunarLock: KAM.SpinOrbit.lunar_sync_lock (--lib KAMLunarLock))
```

The sole failing check is expected generated-file staleness, explicitly assigned to
the lander by the Phase B handoff. Unlike the earlier handoff run, this run also passes
the complete 315-declaration core ABI stage using the audit environment. The headline
application ABI was independently checked above. No override was introduced.

No-build data check command (same cap and serial environment; compile gate):

```sh
$CAP /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65
```

Exit **0**. Gate and final output:

```text
[inp-gate] slot 1 acquired 15:04:34 for --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65
All targets up-to-date (17247 jobs).
```

The remaining output contains 110 cached warning diagnostics, chiefly unused simp arguments,
replayed from existing dependency traces; `--no-build` compiled no target. This confirms
the landed assembly snapshot, not regenerated application roots in this worktree.

## Uncertainties, errata and handoff

No suspected mathematical blueprint or pinned-source defect was found in the reviewed
seal delta. No new mathematical deviation was introduced. Historical design prose
marked provisional does not supersede D49's exact approved frozen text.

The scratch-overlay compilation is the deliberate build-method exception required by
the package brief (no new `.lake/build` here); every changed source was re-elaborated,
and every changed module was replayed independently. The unchanged certificate chain
was used as landed dependency evidence and was not re-audited or rebuilt.

The lander must regenerate the listed roots/parts and Lake block, then perform the
D63 application-up-to-date / `prebuild_heavy.py --check-all` landing checks on the final
merged state. Running that driver here could build generated files, contrary to the
report-only brief, so this audit does not claim that gate. The read-only ownership
classifier already passes. These integration notes account for PASS WITH NOTES;
there is no requested change to the four proofs, their statements or the bridges.

All temporary probes, fresh compiled outputs and audit scripts in this audit's
`.lake/abi-scratch/LockSealAudit1/` directory were removed after recording the results.
The only repository change made by this auditor is this report. No git mutation or
commit was performed.
