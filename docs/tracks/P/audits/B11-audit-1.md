# B11 independent package audit 1

Date: 2026-10-28. Scope: only `KAM/Planetary/WeakKAM/ContinuousSeries.lean`, as required by the handoff's AUDIT FOCUS. Tier-2 focused, refute-first review; no implementation changes.

## Verdict

**PASS WITH NOTES** for B11: the exact signature, proof, targeted build, fresh elaboration and kernel replay pass; the permitted stale generated-root lint exception is recorded below. This is an infrastructure package, with no provider export or frozen anchor to seal. The theorem supplies the local continuous-series bridge for `stepP:p11a:ps-lim`; B12 must still instantiate it twice and prove the remaining parameter-selection clauses. No campaign or frozen theorem closure is claimed.

## Frozen inputs and authority

Snapshot V1: HEAD `b4a630a98942ad087317f4e1fb9756008b0e0b8b`; compared `inp` `7e495e5036e22a1b8fe3efcb43da465c5e1c45e5`. `git diff inp...HEAD` contains exactly the new 36-line module. The handoff was already untracked at audit start.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the named B11 handoff, the design's B11 row/Appendix/GAP-1/B12 recipe, the two design audit reports, the signature, the local blueprint and track-P conventions. The design audits are located under `docs/tracks/P/design/`, rather than `audits/`; the signature is available in the main inp worktree. Those main-worktree inputs were read only. The user's exact report destination overrides the generic brief's main-worktree destination.

| Input | SHA256 at V1 |
|---|---|
| Audited `ContinuousSeries.lean` | `be08a4ddf55d1c3d868339bf9f362d5f8dec47108287e530f3987365442ab5d4` |
| `docs/tracks/P/design/P11B-LEAN-DESIGN.md` | `8b3fd811a8c13414699fb79dc55e7b1b74e90cebf697f89e76a053ecb52c0bdd` |
| `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` | `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596` |
| `blueprint-P/parts/p11a3-iteration-selection.tex` | `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c` |
| `docs/tracks/P/statement.md` | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |
| `docs/tracks/P/audits/B11-handoff.md` | `c83de8c6388fb53f70547c419af70bf2c0a5d5dec1e488f29192022a5999bb6c` |
| Main inp `docs/tracks/P/design/DESIGN-P11B-design-audit-1.md` | `50d14b68c31f4fa382346e60382e6790bb31cc3c1568df513df5b1b5b0627464` |
| Main inp `docs/tracks/P/design/DESIGN-P11B-design-audit-2.md` | `6e48bef98fee6e6619119a494672cb3c49a35992eead7330819b56e4c5f54eec` |

Authorization/decision log: report-only edits and temporary probes in this worktree's `.lake/abi-scratch/`; no git mutations, source repairs, generated-root regeneration or dependency modifications. Builds and verification are serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`; build uses the prescribed compile gate. All findings and verification evidence are kept in this single report. No subagents used.

## Declaration ledger and proof review

| Node / declaration | Lean declaration | Verdict | Evidence |
|---|---|---|---|
| B11; local supplier for `stepP:p11a:ps-lim` | `KAM.Planetary.continuous_series_on_compact` (`ContinuousSeries.lean`:25–34) | PASS | Statement bytes, from `theorem` through the type preceding `:=`, equal signature lines 412–419 and the design Appendix. It returns uniform convergence of range partial sums, continuity of the tsum on K, and pointwise summability, with precisely the specified premises. |

There is exactly one new public declaration and no new definitions, abbreviations, structures, instances or hidden helper exports. `rg -n 'continuous_series_on_compact' KAM` finds only this declaration, so no existing KAM name is reused.

The proof at lines 33–34 is a conjunction of three direct applications:

- `tendstoUniformlyOn_tsum_nat hB hbound` gives exactly the first conjunct.
- `continuousOn_tsum hv hB hbound` gives exactly the second.
- At each b in K, `Summable.of_norm_bounded hB (fun j => hbound j b hb)` gives the third.

The installed Mathlib declarations were read at `Mathlib/Analysis/Normed/Group/FunctionSeries.lean`:47–51,115–120 and `Mathlib/Analysis/Normed/Group/InfiniteSum.lean`:111–114. Completeness of E is explicit. No constants are chosen and no dependence or quantifier order changes. Norms are the given norm on E; the domain `SelectionR n` unfolds to `Fin n → ℝ`, with the existing Pi topology.

### Adversarial pass

Tried the possible failure modes separately from initial matching: absence of an `IsCompact K` premise, empty K, signed envelopes, off-carrier tsum fallback, and hidden conclusion premises. None refutes the theorem. The Weierstrass test works on arbitrary subsets, so the absence of compactness strengthens applicability and exactly matches the signature. If K is nonempty, the bound forces every B j nonnegative; if K is empty all conclusions are vacuous on K. Completeness plus the comparison test ensures genuine summability at every b in K, so the proof never relies on the nonsummable-tsum fallback there. Off K nothing is asserted. Continuity, a summable scalar envelope and the norm bound are the elementary bridge's intended inputs, not an assumed KAM construction or limit.

### Applicability and existing blueprint issue

At V1, `blueprint-P/parts/p11a3-iteration-selection.tex`:330 says “uniform Weierstrass test” and cites `bp:p1:uniform-limits`. The design GAP-1 at line 211 records that `KAM.uniform_limits` requires a fixed open complex domain and uniform derivative convergence. Those hypotheses are unavailable merely from restrictions to Kinf. B11 supplies the correct subset-continuity theorem without that domain requirement. The blueprint's mathematical Weierstrass argument is valid; its named analytic supplier has the documented interface mismatch. This is an already identified blueprint citation issue, not a new defect in the pinned primary source.

The B11 row at design line 237 lists only this theorem; the B12 recipe at line 286 says “use it twice on Kinf.” The blueprint has summable envelopes ell_j for frequency increments and 2 epsilon_j for scalar increments. Taking E to be `Fin n → ℝ` or ℝ supplies the required instances. Real restriction and continuity of each increment, envelope estimates, adding the initial continuous frequency, identifying the limit objects and tail bounds remain consumer obligations. This audit closes the local supplier gap, not the full ps-lim node or B12 implementation. No extra premise is needed beyond those already described by the design.

## Definition and import classification

New definitions: none. The pre-existing carrier `SelectionR n := Fin n → ℝ` in B01 `Data.lean`:40 is the intended whole carrier, not a fallback. B01's other objects are outside this package audit.

Direct imports are `Mathlib` and `KAM.Planetary.WeakKAM.Data`. Recursive KAM import inspection reaches 34 modules, no providers and no frozen theorem modules. All 12 reached frozen modules are manifest-listed SEALED definitions: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm and Planetary.Phase. No DRAFT_SORRY anchor is imported. Provider-type and seal-copy tests are inapplicable because B11 has neither a provider nor an anchor.

## Verification

All commands run from `/root/code/KAM-inp-p11b-b11`. Only one audit-owned Lean/Lake invocation ran at a time. Gate waiting was allowed to finish; no budgets were overridden.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b11 KAM.Planetary.WeakKAM.ContinuousSeries
   ```

   Exit 0; exact output:

   ```text
   [inp-gate] slot 1 acquired 15:45:19 for KAM.Planetary.WeakKAM.ContinuousSeries
   Build completed successfully (9080 jobs).
   ```

   The wrapper invokes `nice -n 5 lake build`. No warnings.

2. Fresh signature and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B11Audit.lean
   ```

   Scratch imported only the production module, reproduced the signature's complete type under `example`, and supplied `KAM.Planetary.continuous_series_on_compact K v B hv hB hbound` as its body. It used the same namespace opens and `{n : ℕ}`. The signature's statement substring was also compared mechanically against production: `Signature statement byte equality: True`. No draft signature or its sorry body was imported. Exit 0; exact output:

   ```text
   'KAM.Planetary.continuous_series_on_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This covers every new public theorem (one).

3. Kernel replay, one invocation for the sole package module (there is no provider module):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.ContinuousSeries
   ```

   Exit 0; exact output:

   ```text
   replaying KAM.Planetary.WeakKAM.ContinuousSeries
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the explicitly permitted stale generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint errors or forbidden constructs were reported. `KAM.lean` was not regenerated, as required.

5. Static/diff checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` emitted nothing (exit 0). `git diff --check` emitted nothing (exit 0). The audited module is 36 lines, with copyright, `module`, public imports, module docstring and `public section`; no new definitions need exposure. Its source has none of the forbidden proof escapes, resource overrides or `EuclideanSpace`. The unique-name search is recorded above. Audit-end SHA256 of the audited module still equals V1.

6. Cleanup/status: deleted the audit-created `.lake/abi-scratch/B11Audit.lean`. Final working-tree status contains only the pre-existing untracked B11 handoff and this new audit report. No production file changed. `git diff --no-index --check /dev/null docs/tracks/P/audits/B11-audit-1.md` passes.

## Findings, uncertainty and deviations

No mathematical/signature blocker found. The existing GAP-1 citation mismatch and remaining consumer work are explicitly bounded above. No new suspected primary-source erratum or implementation deviation. The theorem's “compact carrier” docstring is descriptive; the stronger arbitrary-subset statement is intentional and signature-exact. No edits outside this report and temporary scratch probes are authorized.


## Closeout

All one-of-one new declarations classified and checked against the exact design signature; proof reviewed against the installed Mathlib implementations; fresh statement elaboration, axiom census, targeted build and kernel replay passed. Lint completed with only the brief's accepted generated-root exception. No open audit blocker or unclassified finding. B11 is ready for package integration, subject to normal generated-root regeneration by the orchestrator. B12, primary-source theorem proofs, other B01 declarations and the broader P11B design are outside this proof audit.
