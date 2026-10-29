# SO-POS independent package audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sopos`.
Audited HEAD: `b7bd3b74bd1bb02c8c1de44a3b70476f6f4f33bc`.
Comparison: `git diff inp...HEAD`; inp read at
`6b9766378e78b6ea8d3a18c16a5f38e3665b4f18`, merge base
`b0ac8009e4a100a20315dc7b13eb5c0d1a89fcce`.

## Verdict

**PASS WITH NOTES** for SO-POS and both signed declarations. The signed slice is complete,
with no extra premises and no weakened conclusion. This is an infrastructure package, with no
frozen theorem anchor to seal. No campaign or lunar confinement theorem is closed by this audit.

The notes are the explicitly permitted stale generated root, documented rejection of nonzero
degree models, and unmeasured lunar-scale performance. No blocking soundness finding.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external package-audit brief,
`docs/tracks/SO/audits/SO-POS-handoff.md`, the accepted Revision 7 design at
`/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md` (§7 SO-POS row, §8 and §F signatures),
and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:806–816`.
The handoff's narrower SO-POS scope governs: only `KAM/Certificate/Positivity.lean` and
`KAM/Certificate/Tests/Positivity.lean` are audited. Unrelated I/N/P blueprint nodes and frozen
providers are not claimed as implemented. The full three-dot diff adds these two files and the
handoff only. The user's exact report destination overrides the generic brief's main-worktree path.

All declaration names below have prefix `KAM.Certificate.`. P denotes
`KAM/Certificate/Positivity.lean`; T denotes `KAM/Certificate/Tests/Positivity.lean`.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| SO-POS §F / P:66 | `checkRealLowerBound` | PASS WITH NOTES | Exact signed name and type; nonzero degree fails closed. |
| SO-POS §F / P:127 | `checkRealLowerBound_sound` | PASS | Exact signed name, premises, quantifiers, domain and conclusion. |
| Helper / P:35 | `CertPoly.conjSorted` | PASS | Reflection followed by reversal; denotation unchanged by reversal. |
| Helper / P:39 | `CertModel.starModel` | PASS | Reflected polynomial with original degree and radius. |
| Helper / P:44 | `CertModel.ofConst` | PASS | Zero key of chosen length, degree zero, supplied center/radius. |
| Helper / P:48 | `CertPoly.keyLen` | PASS | First stored key length; zero on empty input. |
| Helper / P:51 | `CertModel.realLowerModel` | PASS | Residual enclosure used only after the degree-zero gate. |
| Helper / P:76 | `CertPoly.eval_conjSorted` | PASS | Arbitrary polynomial and complex point; no sortedness assumption. |
| Helper / P:81 | `CertModel.mul_deg` | PASS | Degree addition in both product branches, without arithmetic laws. |
| Helper / P:86 | `CertModel.Encloses.starModel` | PASS | Conjugation preserves strip and error norm, including integer degree. |
| Helper / P:105 | `certKeyFun_replicate` | PASS | Arbitrary dimension and stored key length. |
| Helper / P:110 | `CertModel.Encloses.ofConst` | PASS | Source error bound on a real constant; no conclusion-shaped assumption. |
| Helper / P:120 | `CertModel.Encloses.ofPoly` | PASS | Exact polynomial enclosure; equality supplies the denoted function only. |
| Test datum / T:26 | `posTestW` | PASS | Rational weight and positive strip width. |
| Test datum / T:28 | `posTestCfg` | PASS | Ordinary configuration, no supplied product advice. |
| Test datum / T:30 | `posTestQ` | PASS | Rational real coefficients embedded as complex coefficients. |
| Test datum / T:32 | `posTestF` | PASS | Degree-zero cosine polynomial with variable constant. |
| Test / T:35 | `posTest_pass` | PASS | Empty SOS, lower bound 19/10 accepted by kernel decision. |
| Test / T:38 | `posTest_reject_slack` | PASS | Empty SOS, lower bound 2 rejected by kernel decision. |
| Test / T:41 | `posTest_sos` | PASS | Nonempty SOS with constant shifted to 4 accepted. |
| Test / T:44 | `posTest_sos_reject` | PASS | Corresponding insufficient residual slack rejected. |
| Test / T:47 | `posTest_deg` | PASS | Nonzero degree rejected by kernel decision. |

## Definitions and proof review

All ten new definitions are classified in the table. No new structure, instance, or abbrev hides
an obligation. Definitions are total data operations. `keyLen`'s empty-input zero is an indexing
choice for a zero Fourier key; `certKeyFun_replicate` proves that any such length denotes zero.
Mixed lengths, unsorted keys, duplicate keys and arbitrary advice are not soundness premises.
They can reduce cancellation or enlarge the residual, but cannot invalidate the theorem.
`conjSorted` preserves sortedness by reversal for the intended uniform-length sorted inputs;
its evaluation theorem holds without this producer invariant.

`realLowerModel` uses same-degree addition only on the accepted degree-zero path. For other
degrees the raw helper is merely a total data operation, without an asserted enclosure contract;
`checkRealLowerBound` rejects those inputs. A fresh generic probe proved rejection for every
`f.deg ≠ 0`, not merely degree 1. This is incompleteness, not an added theorem hypothesis.

The residual is doubled: `H = f + f* - 2 g g* - 2 m₀`. Conjugate reflection preserves the
complex strip, so both copies of the enclosed function are controlled. On every real point,
`Re H = 2 Re ff - 2 |g|² - 2 m₀`. The successful test gives
`|Re H| ≤ ‖H‖ ≤ 2(m₀-m)`. Its lower half and `|g|² ≥ 0` imply `m ≤ Re ff`.
No holomorphy, reality, dimension lower bound, sortedness or certificate-validity premise beyond
the signed enclosure, lawful arithmetic and successful weight/check tests is assumed. The real
point lies in the strip by the positive width derived from `hW`, even in dimension zero.

The rational constant is centered at `ofRatUp (-2*m₀)` with radius bounded upward by
`ofRatUp (-2*m₀) - ofRatDown (-2*m₀)`; this pays rounding on any lawful backend, not just ℚ.
SOS multiplication honors the first advice entry at `[7]`, appending direct advice for an absent
entry. A failing existing packed entry uses the upstream crude enclosure; it does not need to
fall through to direct advice. Scaling by -2 uses the upstream scalar product route.

The signed checker docstring describes the undoubled residual; the implementation's doubled
residual and doubled threshold are equivalent and documented at P:13–19. No constant or norm
is silently changed. The signature contains no completeness or timing guarantee.

## Exact validation and outputs

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Builds used the required gate; no library rebuild, clean, cache download, or update was requested.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sopos KAM.Certificate.Positivity KAM.Certificate.Tests.Positivity
   ```

   Exit 0: `Build completed successfully (2916 jobs).`
   Only replayed warning: `KAM/Certificate/Arith/PiHigh.lean:218:8`, unused simp argument
   `Nat.succ_eq_add_one`; outside scope. No warning in either audited file.

2. Python extraction compared each signed declaration header through its return type, normalizing
   whitespace only. Both `checkRealLowerBound` and `checkRealLowerBound_sound`: `True`.
   The namespace in both source and signatures is `KAM.Certificate`.

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOPosAudit.lean
   ```

   Final probe exit 0. It elaborated examples using both literal signed headers, plus a fresh
   copy of the signed theorem with body
   `by exact KAM.Certificate.checkRealLowerBound_sound hW cfg hf h x`, preserving every explicit
   binder in order. It also proved generic rejection for every nonzero integer degree.
   An initial probe incorrectly used the unapplied `@` functions under already-bound headers;
   its harness was corrected before the successful run. No package source was changed.

   All 12 new public theorems were queried with `#print axioms KAM.Certificate.<name>`:

   ```text
   CertPoly.eval_conjSorted          [propext, Classical.choice, Quot.sound]
   CertModel.mul_deg                [propext, Classical.choice, Quot.sound]
   CertModel.Encloses.starModel      [propext, Classical.choice, Quot.sound]
   certKeyFun_replicate              [propext, Quot.sound]
   CertModel.Encloses.ofConst        [propext, Classical.choice, Quot.sound]
   CertModel.Encloses.ofPoly         [propext, Classical.choice, Quot.sound]
   checkRealLowerBound_sound         [propext, Classical.choice, Quot.sound]
   posTest_pass                     [propext, Classical.choice, Quot.sound]
   posTest_reject_slack             [propext, Classical.choice, Quot.sound]
   posTest_sos                      [propext, Classical.choice, Quot.sound]
   posTest_sos_reject               [propext, Classical.choice, Quot.sound]
   posTest_deg                      [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Positivity KAM.Certificate.Tests.Positivity
   ```

   Exit 0:

   ```text
   replaying KAM.Certificate.Tests.Positivity
   replaying KAM.Certificate.Positivity
   ```

   The five tests use `decide +kernel`, including both false slack controls and the degree control.

4. Naming:

   ```sh
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sopos KAM.Certificate.Positivity KAM.Certificate.Tests.Positivity
   ```

   Exit 0: `short-name check OK (no reused public short name)`.

   ```sh
   LEAN_NUM_THREADS=1 bash /mnt/HC_Volume_106379410/orchestrator-tools/main_shadow_check.sh /root/code/KAM-inp-sopos KAM.Certificate.Positivity KAM.Certificate.Tests.Positivity
   ```

   Exit 0: `shadow check OK (no package name shadows a root constant)`.

5. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the permitted generated-root exception:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1348 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated root was left untouched as required. Source-token scan of the two files found
   no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `native_decide` or
   `EuclideanSpace`. Both have copyright, `module`, public imports, module docstring and public
   section; executable definitions are exposed by the section attribute. P has 178 lines and
   maximum line length 99; T has 50 lines and maximum line length 96.

6. Integrity:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```

   Both exit 0 with empty output. Traversing KAM imports from both scoped modules reaches
   32 KAM modules, no provider, and only one frozen module:
   `KAM.Frozen.Defs.ComplexStrip`, whose manifest state is `SEALED`
   (`manifest/frozen-anchors.json:55–64`). No DRAFT_SORRY anchor is imported.
   Audit scratch probes were deleted. Final working-tree change is only this report.

## Findings, uncertainties and errata

- Nonblocking completeness limitation: P:68 rejects all nonzero degrees. It is explicit in the
  module documentation and handoff, and independently proved for arbitrary degree. Callers
  needing derivative models must first convert to degree zero with the validated upstream
  `toDeg` interface. This audit does not establish that a future consumer does so.
- No performance measurement at lunar certificate size was supplied or independently made;
  the handoff's 1–1.5 minute estimate remains an extrapolation, not an audit receipt.
- Minor receipt discrepancy: the handoff's Files section says 177 lines for P; current P has
  178 lines. No mathematical or signature consequence.
- No suspected defect in a pinned mathematical source or the accepted SO-POS blueprint contract
  was found. No source erratum is proposed. The documented doubled residual is an equivalent
  implementation of the signed residual-slack contract, not a premise change.
- No source, frozen anchor, manifest, generated file or implementation was edited by this audit;
  no git state-changing operation was performed. This report is the sole repository deliverable.
