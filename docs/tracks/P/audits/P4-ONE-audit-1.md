# Independent package audit 1: P4-ONE

Overall verdict: **PASS WITH NOTES** for `bpP:p5:dio-one` / `KAM.Planetary.dio_one`.
No mathematical or statement defect was found in the assigned module. This is a helper-package
verdict, not seal-readiness of P-G or closure of the planetary campaign. No frozen anchor is proved
by this package; provider/frozen-type equality and a frozen seal-body probe are therefore **not
applicable**. `properlyDegenerateKAM` remains `by sorry` in its frozen anchor.

## Scope and authority

Audited `/root/code/KAM-inp-p4one`, HEAD
`5703c89ea859c22f24538d6fa92789d807a0ba1f`, only
`KAM/Planetary/PGMeasure/OneScale.lean` (205 lines). SHA256:
`666d42b166f48edc1c9697f5705f09dbdf93be7d6f67a5b5ec4c4c8c4a4ea79d`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the named package brief and P4-ONE handoff/AUDIT FOCUS;
P45 design Revision 3 (especially ownership row 493, explicit-constant repair F5 and Appendix A),
its three design audits, shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`,
`blueprint-P/parts/p5-pg-assembly.tex:96–102`, the p4 inverse statement at lines 51–60,
track-P statement, frozen P-G anchor, `IsDiophantine`, `FastFrequency`,
`HasFastDiffeomorphism`, the PGData setting and the three direct lemma dependencies.
The user's exact report destination overrides the generic brief's MAIN-worktree destination.

Ran the requested `git diff inp...HEAD`. Git warned:

```text
warning: inp...HEAD: multiple merge bases, using 4c7c4ac655554b0ef294d5920d07649c1405d59c
```

At inspection, `inp` was `aa359d8fcbe90f6489dc2c4a3ccaf7b5a8e7f8ec`.
The full selected-base diff contains 60 files / 10,207 insertions, including unrelated inherited
packages. It cannot substantiate a claim that the entire branch changes only OneScale.
`git show --stat HEAD` and `git diff HEAD^ HEAD --name-only` independently show the P4-ONE commit
adds only the 205-line OneScale module. Review scope remains exactly the handoff's OneScale files;
there is only one such file here.

Protected-path check:

```text
$ git diff --numstat inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
26	0	KAM.lean
```

Thus the generic whole-branch protected-path emptiness criterion is **not literally satisfied**:
the selected-base history includes 26 generated-root imports. Frozen files, manifest and README
have no diff. The P4-ONE commit itself changes none of these protected paths. This is an integration
note, not an edit introduced by P4-ONE; no generated file was repaired during this audit.

## Declaration-by-declaration review

All names below are in `KAM.Planetary`. Locations refer to OneScale.lean.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| p4:lip-inverse selected witness | `pgInverse` (36) | PASS with placement note | Definition byte-identical to shared signature and design Appendix A; selects the actual inverse witness. |
| p4:lip-inverse constant | `pgInverseL` (39) | PASS with placement note | Same signature body, same nested witness; at least 1, independent of gamma and small parameters. |
| p4:lip-inverse enclosure | `pgInverseR` (42) | PASS with numeric note | Same signature body; positive enclosing radius, not an exact maximum. |
| p4:lip-inverse specification helper | `pgInverse_spec` (46) | PASS | Direct chosen-witness specification; continuity, compact image, left-inverse identity on W, radius bound and Lipschitz estimate are proved outputs. |
| p5:dio-one explicit constant | `dioConstant` (55) | PASS | Literal body match: `2*(pgInverseL d)^a*latticeS (a+b) tau*(2*pgInverseR d)^(a-1)`. |
| p5:dio-one lattice comparison helper | `latticeS_mono` (59) | PASS | For `1 ≤ n ≤ m < tau`, the explicit lattice bound increases with dimension; denominator positivity is proved. |
| p5:dio-one resonance carrier | `resonantSlabs` (73) | PASS | Literal closed cube intersected with strict nonzero-integer resonance union, with l1 real-exponent divisor. |
| p5:dio-one slab summation helper | `volume_resonantSlabs_le` (78) | PASS | Proves bound in fast dimension a under a < tau, hence stronger range than the final a+b < tau requirement. |
| p5:dio-one image-measure helper | `volume_le_of_lipschitz` (137) | PASS | General outer-measure image bound, any subsets E,K,T and nonnegative L, no compactness/measurability premise. |
| bpP:p5:dio-one | `dio_one` (154) | PASS | Literal shared-signature telescope and conclusion; positive explicit constant and all gamma > 0; frozen predicate consumed exactly. |

The four signature definitions and `dio_one` telescope were compared programmatically against both
the shared signatures and the committed design Appendix A: all literal comparisons returned `True`.
There is no new structure, abbrev, instance, norm or carrier alias.

## Definition classification and proof inspection

`pgInverse`, `pgInverseL`, `pgInverseR` select a single consistent existential tuple produced by
`lip_inverse d.hW d.hVb d.hVW d.hfreq`. This theorem supplies witnesses from source hypotheses,
not a KAM conclusion. The inverse is a total function; its behavior outside the frequency image is
unconstrained by the inverse specification and never used by `dio_one`. All inverse evaluations
in that proof are at `fastFrequency d.H0 I` with `I ∈ V ⊆ closure V ⊆ W`. There is no fallback,
junk branch or totalized inverse used as an identity outside its valid domain.

`dioConstant` is the intended real formula on its entire carrier. Positivity is claimed and proved
only when `a+b < tau`; its total definition at other tau is not used to claim a measure estimate.
`resonantSlabs` is the intended set for every gamma,tau,R; its volume lemma explicitly requires
positive gamma,R and positive dimension. Natural subtraction `a-1` is harmless because `d.ha`
gives `a ≥ 1`.

The proof first bounds each slab by `affine_slab` with real normal k and offset zero. A nonzero
integer coordinate gives sup norm at least 1; the inverse normal factor can therefore be dropped.
The l1 real-power divisor equals `gamma*latticeWeight tau k` on each nonzero lattice vector.
Countable subadditivity and the summable `lattice_tail` bound give the fast-dimensional constant.
`latticeS_mono` then replaces `latticeS a tau` by the specified `latticeS (a+b) tau`.

For the image step, `hausdorffMeasure_pi_real` identifies a-dimensional Hausdorff measure with
Lebesgue volume for the actual Pi sup metric. `LipschitzOnWith.hausdorffMeasure_image_le`
works directly on the image of `K ∩ T`, so no McShane extension is required. This proves the
blueprint's image bound with its precise coefficient; it does not use an Euclidean norm or
an unproved volume-change identity. Monotonicity uses outer measure, so no missing measurable-set
premise is being hidden.

The bad-action set is contained in the inverse image union, rather than falsely identified with
all boundary-containing inverse images. Negating the frozen `KAM.IsDiophantine` gives exactly
the strict resonance inequality in `resonantSlabs`; no new predicate, period factor, gamma scaling,
cutoff or weakened quantifier is substituted. `PGData` contains the frozen source inputs; no extra
conclusion-shaped premise or produced analytic/KAM witness is introduced. Constants depend only
on fixed data and tau and are selected before gamma, r and mu.

## Integration and source notes

1. The three inverse selectors are located in OneScale rather than CompactLipschitz (design's
   lip-inverse ownership). No duplicate declaration currently exists in this worktree. Downstream
   users must import OneScale, or the orchestrator must move these exact definitions once and
   update imports. This is a placement/integration note, not a mathematical defect.
2. Blueprint p4:52 says `R_y := max_{Y_0}|y|`, while the implementation uses a positive enclosing
   radius from `lip_inverse`. This numerical enlargement is explicitly declared in P45 design
   lines 641–646 and retained by design audits 2–3 (F5); the literal design formula is preserved.
   Increasing R only enlarges the slab constant (a ≥ 1). This is an existing declared deviation
   from the exact-maximum convention, not a newly discovered source defect.
3. The frozen P-G anchor/doc statement retain historical “await owner approval” prose, while
   DECISIONS D20 records approval/freezing. That stale prose does not alter any audited type.
4. No new suspected pinned-paper erratum or blueprint contradiction was found. The CP10 attribution
   is the existing blueprint's “standard measure estimate; proof ours”; this focused audit does not
   claim a new independent comparison to a pinned CP10 PDF. No source was fetched or changed.

## Validation receipts

Targeted build (through the required gate):

```text
$ LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4one KAM.Planetary.PGMeasure.OneScale
[inp-gate] slot 2 acquired 08:53:39 for KAM.Planetary.PGMeasure.OneScale
⚠ [9062/9067] Replayed KAM.Planetary.PGMeasure.CompactLipschitz
warning: KAM/Planetary/PGMeasure/CompactLipschitz.lean:140:5: Variable name `hW` is not explicitly referenced.
Build completed successfully (9067 jobs).
exit 0
```

Only the inherited CompactLipschitz unused-variable warning was replayed; no OneScale warning.
No heartbeat, recursion-depth or synthesis budget was changed.

An untracked `.lake/abi-scratch/P4OneAudit.lean` imported only OneScale, copied the exact shared
`dio_one` telescope under `audit_dio_one`, and supplied `by exact dio_one d ht` (all explicit
binders in order). It also checked `example : type_of% @dio_one := @audit_dio_one` and the literal
constant by `rfl`. This is the applicable design-type/application probe; there is no provider seal
for this package. Command:

```text
$ LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4OneAudit.lean
'KAM.Planetary.pgInverse_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.latticeS_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_resonantSlabs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dio_one' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Kernel replay, one invocation including all three direct lemma modules:

```text
$ LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.OneScale KAM.Planetary.PGMeasure.CompactLipschitz KAM.Planetary.PGMeasure.AffineSlab KAM.Planetary.PGMeasure.LatticeTail
replaying KAM.Planetary.PGMeasure.LatticeTail
replaying KAM.Planetary.PGMeasure.AffineSlab
replaying KAM.Planetary.PGMeasure.CompactLipschitz
replaying KAM.Planetary.PGMeasure.OneScale
exit 0
```

Final lint, serialized after kernel replay, with inherited nice priority and thread limit
for its ABI Lean subprocess:

```text
$ LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (496 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the generic brief's explicitly allowed stale generated-root check.
No over-100-character line or other hygiene failure was reported.

Audit execution deviation: the initial lint invocation was started during the build's compile-gate
wait without an explicit nice/thread-limit prefix; after gate acquisition, its ABI Lean subprocess
and the cached-build Lake driver overlapped. This did not follow the requested process scheduling.
The final probe, kernel replay, lint rerun and subsequent targeted build rerun were issued
sequentially; each final Lean command uses `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper
supplies nice). No source change or proof-budget change was made to obtain a pass.

Serialized targeted build rerun (same gate command as above), after final lint completed:

```text
[inp-gate] slot 1 acquired 09:00:10 for KAM.Planetary.PGMeasure.OneScale
⚠ [9062/9067] Replayed KAM.Planetary.PGMeasure.CompactLipschitz
warning: KAM/Planetary/PGMeasure/CompactLipschitz.lean:140:5: Variable name `hW` is not explicitly referenced.
Build completed successfully (9067 jobs).
exit 0
```

Static checks: OneScale has 205 physical lines, maximum line length 100 Unicode characters,
zero overlong lines, no forbidden proof escapes, no `set_option`, no `EuclideanSpace`;
copyright, `module`, public imports, module docstring, exposed public noncomputable section are
present. A recursive source-import walk found 21 local KAM modules, 14 frozen definition modules,
**zero provider modules and zero frozen theorem modules**. Thus no DRAFT_SORRY theorem import or
unverified SEALED theorem premise is involved. All five new public theorems were axiom-printed.

`git diff --check inp...HEAD -- 'KAM/Planetary/PGMeasure/OneScale*.lean'` exited 0, no whitespace
errors (only the multiple-merge-base warning). No production source, frozen file, manifest,
generated root or README was edited by the auditor. Probe cleanup and report validation are
recorded below after completion.

Completion: the audit probe was deleted. `git diff --no-index --check /dev/null
/root/code/KAM-inp-p4one/docs/tracks/P/audits/P4-ONE-audit-1.md` exited 0. Final status contains
only this new report and the pre-existing untracked P4-ONE-handoff.md; no tracked file changed.
No remaining proof uncertainty was found within the assigned node. Integration notes and the
initial process-scheduling deviation above are retained explicitly; they do not assert P-G closure.
