# P4-RAM independent package audit 1

Overall verdict: **PASS WITH NOTES** for P4-RA and P4-M, including
`KAM.Planetary.two_scale_diophantine_measure`. No blocking statement, definition,
adapter, or proof defect found. Notes: the explicitly permitted stale generated
root; whitespace-only wrapping of two signed types; infrastructure rather than
a frozen-anchor seal. This does not seal P-G or establish campaign/root closure.

## Scope and authority

Audited `/root/code/KAM-inp-p4ra`, HEAD
`f7937675c25729caf9c6f084f1f7e77646c09644`, against `inp` and, as requested by
AUDIT FOCUS, `inp-p4rb`. Observed refs: `inp` =
`05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; `inp-p4rb` =
`4a2457aa6adb8cf4b17d7dacd2fe9aa07074166f`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`be13c58bac4fe1ed59d899c98f6c4c8cec175e95`. Both comparisons list the four scoped
files below, plus ResonanceSlow and its existing P4-R0 audit/handoff. The latter
are dependencies, not fresh P4-RAM proof-audit scope.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, P4-RAM handoff/AUDIT
FOCUS, original P4-RA brief, P45 design and audits 1–4, authoritative shared
signatures, Part 4 blueprint, track P statement, relevant frozen definitions and
P-G anchor, and the imported measure-helper interfaces. The user-specified report
destination in this worktree overrides the generic brief's main-worktree path.

Scoped files:

| File under `KAM/Planetary/PGMeasure/` | Lines | Maximum Unicode line length |
|---|---:|---:|
| `ResonanceFast.lean` | 169 | 99 |
| `ResonanceFast/Pullback.lean` | 102 | 100 |
| `ResonanceFast/Sections.lean` | 166 | 99 |
| `TwoScale.lean` | 195 | 99 |

There is no provider export or frozen theorem implemented by this package.
Provider/frozen type identity and seal-body probes are therefore **not applicable**.
The P-G anchor is contextual input only. Exact signed-type application probes
were used instead; no frozen file was edited or copied with a new premise.

## Signed declarations and definitions

Authority: `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256
`6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`.
The same five declarations in the local design Appendix A agree with this file
after whitespace removal.

| Signed declaration | Byte comparison with signature authority |
|---|---|
| `measure_c1` | Complete definition byte-identical. |
| `measure_c2` | Complete definition byte-identical. |
| `resonanceBad` | Complete definition byte-identical in unchanged `Setting.lean`. |
| `resonanceBad_eq` | Raw type bytes differ only in whitespace/line wrapping; removing whitespace gives identical bytes. |
| `two_scale_diophantine_measure` | Raw type bytes differ only in whitespace/line wrapping; removing whitespace gives identical bytes. |

The theorem probes use the original signed telescopes and conclusions verbatim,
under fresh names, with bodies applying the actual exports to exactly the
explicit binders in order. Separate `rfl` examples check the copied constant
bodies. Thus no premise, quantifier order, carrier, norm, exponent, or constant
dependence is hidden by the formatting comparison. The handoff disclosed the
wrapping; literal raw-byte identity is not claimed for those two theorem types.

Every new definition is classified:

| Definition | Classification and whole-carrier behavior |
|---|---|
| `pullMap` | Literal total coordinate map `(y,xi) ↦ (d.g y,xi)`; no fallback. Its inverse/Lipschitz claims are restricted to the frequency image, where `hinv`/`hglip` apply. No off-image inverse property is used. |
| `pushMap` | Literal total map `(I,xi) ↦ (fastFrequency d.H0 I,xi)`; valid even where the total derivative has no analytic interpretation. The proof uses only core points inside W. |
| `fastModes` | Literal fast-nonzero modes satisfying the blueprint dominance inequality; exactly complementary to `largeModes` within the fast-nonzero modes. Equality belongs to the fast case. |
| `measure_c1` | Exact signed scalar formula. Compactness and positive core volume prove its `toReal` denominator finite and strictly positive. No division-by-zero fallback is used. |
| `measure_c2` | Exact signed scalar formula; positive dimensions and exponent guards give the intended finite lattice bound. |

No new abbreviation, structure, instance, or bundled proof premise occurs.
The S4 inputs in existing `MeasureData`, including N1–N3 and smallness, are source
premises, not conclusions being smuggled into a new structure.

## Declaration-by-declaration fidelity

All names below are in `KAM.Planetary`. “Internal” means internal to the package
proof plan under the AUDIT FOCUS ruling; these helpers are publicly exported Lean
declarations with distinct names, not signed replacements.

| Blueprint node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| dm-y, internal map | `pullMap` (Pullback:32) | PASS | Literal product inverse map; domain qualification respected. |
| dm-y, norm adapter | `norm_append_le` (Pullback:35) | PASS | Max norm on the exact flat coordinate carrier. |
| dm-y | `pullMap_lip` (Pullback:42) | PASS | `Lg ≥ 1` controls identity slow block; hglip controls fast block. |
| dm-y | `volume_pullMap_image_le` (Pullback:58) | PASS | Actual `KAM.lip_image`, exponent a+b, arbitrary outer-measure set. |
| dm-y, internal map | `pushMap` (Pullback:64) | PASS | Actual fast frequency, slow coordinates unchanged. |
| dm-y | `pullMap_pushMap` (Pullback:67) | PASS | Core lies in W; source inverse identity gives exact reconstruction. |
| dm-y | `pushMap_mem_sliceDomain` (Pullback:75) | PASS | Supplies the actual frequency-core and Q memberships. |
| dm-y | `mem_pullMap_image_of_resonant` (Pullback:85) | PASS | Rewrites the same scalar resonance through reconstruction. |
| dm-A, internal modes | `fastModes` (Sections:30) | PASS | Exact nonzero-fast and half-dominance conditions. |
| dm-A | `fast_dev_y` (Sections:34) | PASS | Derived N1 increment bound, with mu LN Lg and correct orientation. |
| dm-A, coordinate adapter | `sub_eq_single_of_line` (Sections:50) | PASS | Fast increment is one coordinate; slow block equal. |
| dm-A | `fastSection_line_diam` (Sections:62) | PASS | Lower increment ≥ half the maximal integer coefficient times distance; diameter ≤ 4 alpha, no convexity premise. |
| dm-A / Tonelli | `measurableSet_resonanceSet` (ResonanceFast:37) | PASS | Relative continuity from existing N1/N2 interface; Borelness derived. |
| dm-A / projection | `prod_erase_box` (ResonanceFast:49) | PASS | Exact `(2 Ry)^(a-1) (2 lambda)^b`; chosen fast coordinate implies a>0. |
| dm-A / per mode | `volume_resonanceSet_fast_le` (ResonanceFast:70) | PASS | Chooses maximal fast coefficient, bounds whole projection, applies line-diameter Tonelli. |
| dm-A / weight adapter | `latticeWeight_eq_inv` (ResonanceFast:105) | PASS | Real-power reciprocal identity on nonnegative l1; no new exponent assumption. |
| dm-A / sum | `fast_modes_measure_le` (ResonanceFast:112) | PASS | Nonzero-mode union, summable nonnegative weights, exact S1 constant. |
| measure proposition / constant | `measure_c1` (TwoScale:35) | PASS | Exact signed maximum and core-volume normalization. |
| measure proposition / constant | `measure_c2` (TwoScale:40) | PASS | Exact slow coefficient b LB S2. |
| freq / exact P1 bridge | `resonanceBad_eq` (TwoScale:42) | PASS | Complement equivalence for all F,D,thresholds,tau, no positivity restriction. |
| dm-sum / sign adapter | `latticeS_nonneg` (TwoScale:69) | PASS | m<tau suffices; no hidden dimension or conclusion premise. |
| dm-slow/y/A/B / cover | `resonanceBad_subset_union` (TwoScale:77) | PASS | Exhaustive fast-zero / fast-dominant / strict-large split, same thresholds. |
| two-scale-diophantine-measure / dm-sum | `two_scale_diophantine_measure` (TwoScale:99) | PASS | Exact signed estimate, all three supplied bounds actually consumed. |

## Adversarial proof review and consumer attachment

The fast increment uses the sum of the fast and slow absolute coefficients,
exactly `l1_split`, rather than a dimension-dependent estimate. N1 and the inverse
Lipschitz bound give `mu LN Lg |k|₁ |s|`; membership in `fastModes` makes this at
most half the maximal fast coefficient times `|s|`. Nonzero integral fast modes
make that coefficient at least one. Both resonant values have modulus below
alpha, giving diameter ≤ 4 alpha. This works for disconnected cores because it
compares two points directly; no segment through the core is assumed.

The projected box removes one fast coordinate, leaving a−1 fast and b slow
coordinates. The full nonzero-lattice sum bounds the smaller fast-mode union;
the threshold alpha1/|k|₁^tau matches `latticeWeight` by the reciprocal adapter.
Borelness needed by Tonelli is proved. The pullback estimate uses outer measure,
so no unproved measurability of the pullback image is needed.

`TwoScale.lean:118–120` obtains `slow_resonance_measure_le`,
`fast_modes_measure_le`, and `large_modes_measure_le` with the actual hQ,
shell, positive threshold, and mu hypotheses. Lines 133–138 pull back both fast
and large unions with `Lg^(a+b)`, apply the proved three-way cover, and sum their
measures. No resonance class is omitted or assumed bounded. The slow bound
already lives in action coordinates and receives no spurious pullback factor.

Lines 113–116 prove `0 < (volume core).toReal` and recover volume by `ofReal`;
lines 167–191 use the maximum of the exact fast and large coefficients. In
real notation the sum is
`x0*v*W + G*A*alpha1*W + G*B*alpha1*M/lambda*W`, bounded by
`(G/v*max A B*alpha1*(1+M/lambda)+x0)*v*W`, where
`G=Lg^(a+b)`, `M=mu^(tau-(a+b))`, `W=(2 lambda)^b`.
All signs and divisions are justified. Constants depend on fixed d only.
The complement bridge uses the existing P1 two-scale predicate, with exactly
the same l1 normalizer and strict/non-strict complement boundary.

## Independent checks

All Lean-bearing invocations used `LEAN_NUM_THREADS=1` and nice priority 5;
they ran serially in this audit. Source lint was paused before its ABI Lean
subprocess while the build finished, then resumed at nice priority 5. No clean,
update, cache retrieval, heartbeat/recursion/synthesis override, or state-changing
git operation was used.

1. Targeted gate build:

   ```text
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4ra KAM.Planetary.PGMeasure.TwoScale
   [inp-gate] slot 2 acquired 10:14:10 for KAM.Planetary.PGMeasure.TwoScale
   Build completed successfully (9080 jobs).
   ```

   Exit 0. Replayed existing warning at `Hamiltonian/Diophantine.lean:124:38`:
   `Variable name hγ is not explicitly referenced.` No scoped-file warning.

2. Source lint: `env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh`.
   The ABI phase inherited nice priority 5 as described above. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (509 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit 1, solely the stale-root exception explicitly allowed by the brief.
   This is not a literal lint exit-0 claim. No root regeneration was performed.

3. Signed application/constant-body probes and all 18 new theorem axiom prints:
   `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4RAMAudit.lean`.

   Exit 0, no warnings or errors; both exact signed applications and both
   definition-body examples elaborate. Exact axiom output:

   ```text
   'KAM.Planetary.measurableSet_resonanceSet' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.prod_erase_box' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_resonanceSet_fast_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.latticeWeight_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fast_modes_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.norm_append_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pullMap_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_pullMap_image_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pullMap_pushMap' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pushMap_mem_sliceDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.mem_pullMap_image_of_resonant' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fast_dev_y' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sub_eq_single_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fastSection_line_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.resonanceBad_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.latticeS_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.resonanceBad_subset_union' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.two_scale_diophantine_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Single-invocation kernel replay:

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.TwoScale KAM.Planetary.PGMeasure.ResonanceFast KAM.Planetary.PGMeasure.ResonanceFast.Pullback KAM.Planetary.PGMeasure.ResonanceFast.Sections
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PGMeasure.ResonanceFast.Pullback
   replaying KAM.Planetary.PGMeasure.ResonanceFast.Sections
   replaying KAM.Planetary.PGMeasure.ResonanceFast
   replaying KAM.Planetary.PGMeasure.TwoScale
   ```

5. Source scan found no forbidden token, `set_option`, or `EuclideanSpace` in
   the four files; all have copyright, `module`, public imports, module
   docstring and exposed public noncomputable section. File sizes and line
   lengths are listed above. Import traversal reaches 34 KAM modules, no
   provider and no frozen theorem module: only frozen definitions are imported.
   Consequently no DRAFT_SORRY theorem or unverified provider enters the proofs.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and the
   corresponding `inp-p4rb...HEAD` command produce no diff (the former emits
   the merge-base warning already recorded). `git diff --check inp...HEAD`
   exits 0. Final report validation: 23/23 declaration rows, balanced fences,
   no trailing whitespace, terminal newline, no pending-result placeholders.
   `git diff --check` exits 0; tracked working tree unchanged. The two manually
   created scratch files (probe and kernel log) were removed. Final status has
   only the pre-existing untracked handoff and this new untracked report.

## Notes, uncertainties, errata and deviations

No new suspected mathematical blueprint/source defect was found in the scoped
implementation. The blueprint explicitly declares the direct three-case proof
as a replacement for CP10's covering argument; that existing source deviation
is preserved, not silently changed. `blueprint-P/parts/p4-pg-measure.tex:144`
already quotes CP10's “c_i independent of epsilon and mu” and explains why the
cover-count interpretation is not uniform. This audit verifies the replacement
blueprint argument and does not independently re-audit the pinned CP10 PDF or
assert a new paper erratum.

The positive enclosing Ry convention is already documented by design audit 2
(F5) and retained in S4. No new premises or definition fallbacks were introduced.
P4-RA has no signed declarations of its own in the signature snapshot; the
AUDIT FOCUS expressly authorizes distinct internal helper names and citations.
The split across Pullback/Sections preserves the intended public import path.

The handoff lists TwoScale as 193 lines; the actual audited file has 195.
This is a harmless receipt discrepancy, not a proof or size-limit defect.
Wrapping accounts for the signed raw-byte differences recorded above. No
production repair or other deviation was introduced by the auditor. The only
persistent audit write is this report; the pre-existing untracked
`P4-RAM-handoff.md` is preserved.
