# T20 independent package audit 2 — delta audit

**Overall verdict: PASS WITH NOTES. F1 is closed.** The two new public lemmas prove the
required pointwise, two-way nonzero-locus correspondence on the actual integer-mode
enumeration. The signed `KAM.Planetary.torsion` and T16's signed `p11c_phi4` are unchanged.
The note is the permitted stale generated root and its inherited ancestry diff, detailed below.
No frozen headline anchor is sealed by this helper package.

## Scope, authority and immutable delta

Audit date: 2026-10-29. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package
brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the AUDIT FOCUS in
`docs/tracks/P/audits/T20-handoff.md`, round 1, and `.drafts/handoff-T20.md`'s Round 2 fix.
Checked the relevant P11C design U9/L54 and L187, its design audit, signed torsion text,
Part-11b blueprint L250–257, track-P statement, and imported interfaces/definitions.
Implementation scope is only `KAM/Planetary/PlanarTorsion/Generic.lean`.
The user's exact absolute report path overrides the brief's generic main-worktree destination.

- Audited HEAD: `0f1091b964c85c11b5aa62f0b32b8c2a3a638515`.
- Round-2 baseline: `58f5ef10cb0571549a1c41ea8022912b58dd9321`.
- Comparison `inp` at capture: `68928d00aa4d02c9b2a11f2b9673d8bd47616645`.
- `git diff inp...HEAD` reports multiple merge bases and selects
  `d74db2d8a2ace1493c1f084a871138d80988b961`. Its inventory is 43 files,
  5,796 insertions and 132 deletions; inherited T16/integration work receives no new audit here.
- `git diff --stat 58f5ef10..HEAD` and `git diff 58f5ef10..HEAD --numstat` show exactly
  one file, `Generic.lean`, with **54 insertions and zero deletions**.
  These are additions between existing declarations, rather than a literal append at EOF.
  Removing precisely that added block reproduces the entire baseline file byte-for-byte.
  Thus every old proof, import, namespace and declaration is preserved, including torsion.
- `git diff 58f5ef10..HEAD -- KAM/Planetary/PlanarTorsion/Birkhoff/Defs.lean` is empty;
  the actual signed finite product is untouched. No replacement definition is introduced.

| Input | SHA-256 |
|---|---|
| `Generic.lean` | `e56e2e141f477f52d75a00c1d8722a7f27ab2a232c5d1e29b28f92576934c128` |
| `Birkhoff/Defs.lean` | `afc3fff9a51325f2ab9b8e1ffa1e8eb2b95d73fd3e58fb72bcea5d4de153cd3d` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7` |

## F1 refutation attempt and disposition

Design L187 says “Prove the locus bridge”; U9 says “prove its nonzero locus equals upstream
Phi4's locus.” Round 1 correctly rejected existence of a single good point as insufficient.
The new export at `Generic.lean:109–114` now states exactly:

```lean
∀ a ∈ p11c_axes, p11c_phi4 p a ≠ 0 ↔
  SecularSpectrum.good (SecularSpectrum.sigma (p11cSecularData p hp) a) ≠ 0
```

There is no extra nonvanishing, simplicity, enumeration, analyticity or genericity premise.
This is a pointwise equivalence for every admissible axis pair, rather than an existential
witness, an almost-everywhere assertion, or a single direction.

The intermediate lemma `p11cGe_phi4_ne_zero_iff_nr4` at L64–105 is stronger than the
physical-domain requirement: it holds for arbitrary `p : PlanarData` and `a : Fin 2 → ℝ`,
without `p.Valid` or cone membership. Its proof unfolds the actual signed product
(`Birkhoff/Defs.lean:35–38`) and actual upstream `nr4`/`k4`
(`SecularSpectrum/GoodPolynomial.lean:34–36`). In the forward direction:

1. For every integer mode with `0 < Σ |k i| ≤ 4`, each component lies in `[-4,4]`, since
   `|k i| ≤ Σ |k j|`. This justifies the genuine `Fin 9` value `(k i + 4).toNat`.
2. The proof establishes `((k' i).val : ℤ) - 4 = k i`, proves membership in the exact
   signed product filter, and transfers the factor's nonvanishing using the real cast
   equality. No mode is dropped at the endpoints or at nonzero total length four.
3. Upstream `nr4` also requires injectivity. The allowed integer mode `![1,-1]` has length
   two. Its nonzero linear form rules out equality of the two eigenvalues. The proof checks
   both possible unequal index pairs in `Fin 2`; it does not assume spectral simplicity.

In the reverse direction, each filtered `Fin 9` mode decodes to the integer mode
`fun i => ((k i).val : ℤ) - 4`. The filter is precisely its `k4 2` membership, so the
NR4 linear-form component proves each factor nonzero. Product nonvanishing follows in Lean.

Finally `good_ne_zero_iff` (`GoodPolynomial.lean:148–160`) accounts for both the discriminant
and all permutation factors in upstream `good`. Its proof transfers permutations to integer
modes preserving the l1 bound; it is not a normalization equality assumption.
`p11c_sigma_eq_sigma` (`SpectralAdapter.lean:291–294`) identifies the actual physical sorted
spectrum on `p.Valid` and `p11c_axes`. Rewriting these two proved characterizations completes
the exact requested bridge. Differing polynomial normalizations cause no locus gap.
**F1 does not survive the delta audit.**

## Declaration and node ledger

Names below have prefix `KAM.Planetary`. Unchanged proofs retain round-1 mathematical review;
all nine public theorems were freshly checked for axioms and replayed in the target module.

| Node / role | Declaration and current lines | Verdict | Reason |
|---|---|---|---|
| Required adapter correspondence | `p11cGe_phi4_ne_zero_iff_nr4`, 64–105 | PASS | Both directions on actual modes; injectivity proved; no logical premise. |
| Design U9 / L187 locus gate | `p11cGe_phi4_ne_zero_iff_good`, 109–114 | PASS | Literal pointwise two-way physical-axis equivalence; F1 closed. |
| `bpP:p11b:torsion` | `torsion`, 150–185 | PASS | Signed header byte-identical to signature L645–653; existing proof byte-unchanged. |
| `stepP:p11b:to-an` | `p11cGe_det_analytic`, 116–121 | PASS | Unchanged determinant proof; consumes entrywise `beta_properties`. |
| `stepP:p11b:to-pt` | `p11cGe_det_neg`, 123–148 | PASS | Unchanged negative witness from T19 relative error estimate. |
| `stepP:p11b:to-id` | `torsion`, 159–185 | PASS | Unchanged connected-cone genericity proof; new bridge identifies the source product locus. |
| Sigma analytic support | `p11cGe_sigma1_analyticAt`, 30–37 | PASS | Unchanged. |
| Product analytic support | `p11cGe_phi4_analytic`, 39–45 | PASS | Unchanged. |
| Axis domain equality | `p11cGe_axes_eq`, 47–49 | PASS | Unchanged. |
| Product nonzero witness | `p11cGe_phi4_exists`, 51–60 | PASS | Unchanged; now supplemented by full correspondence. |

The r=2 torsion conclusions transfer to upstream `good` because multiplication is nonzero
exactly when each factor is nonzero. Hence the pointwise bridge suffices for the blueprint's
joint locus; no change to the signed theorem or its proof is necessary. No graph node is
replaced by a weaker unsigned statement. T21's patch/frequency output is outside this audit.
Provider-to-frozen-type and seal-body tests are inapplicable: T20 has no provider or manifest
anchor. The signed helper type is checked directly instead.

## Definitions, binders and name hygiene

New `def`/`abbrev`/`structure`: **zero**, both in the delta and in Generic as a whole.
Definition classification and choice-independence checks: N/A for new definitions.
The imported product is the literal finite product on its entire carrier, without a fallback.
The intermediate `k'` is a local encoding with proved bounds and exact decoding.

Expanded new binders:

| Declaration | TYPING | STANDING | SOURCE | RULED / EXCESS |
|---|---|---|---|---|
| `p11cGe_phi4_ne_zero_iff_nr4` | `p`, `a` | None | None | 0 / 0 |
| `p11cGe_phi4_ne_zero_iff_good` | `p`, universally quantified `a` | `0 < p.G`, `0 < p.m0`, `∀ i, 0 < p.m i` | `a ∈ p11c_axes` | 0 / 0 |

`PlanarData` has only `G`, `m0` and the two masses; `Valid` unfolds to precisely the three
standing positivity clauses (`Setting.lean:31–38`). No hidden proof field, instance or
conclusion-shaped hypothesis is introduced. The source cone is unchanged.
All eight `p11cGe_` helper short names each have exactly one declaration in KAM; the two new
names are unique. The existing qualified `KAM.torsion` and `KAM.Planetary.torsion` remain
distinct. No namespace/root-shadow change occurs. Generic has 189 lines, maximum width 98;
all lines satisfy the requested 100-character cap. Module header, public imports, docstring
and exposed public section are present. Independent target scan finds no forbidden proof
escape, resource override or `EuclideanSpace`.

## Fresh verification

All Lean/Lake invocations were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`, including
lint's ABI subprocess. No clean, update, cache fetch, generated-root edit or git mutation.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 \
     /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-p11c-t20 KAM.Planetary.PlanarTorsion.Generic
   ```

   Exit **0**. Final output: `Build completed successfully (9322 jobs).`
   Upstream replayed warnings include unused variables, simp arguments and deprecations;
   no target error or heartbeat failure.

2. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Planetary.PlanarTorsion.Generic
   ```

   Exit **0**. Complete output: `replaying KAM.Planetary.PlanarTorsion.Generic`.

3. Signature, bridge and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T20Audit2.lean
   ```

   Exit **0**, no errors/warnings. The disposable probe copied the literal signed torsion
   header under `T20Audit2_signed_torsion`, with body `by exact KAM.Planetary.torsion p hp`,
   and checked `example : type_of% @T20Audit2_signed_torsion := @KAM.Planetary.torsion`.
   It also checked both new exact equivalence types independently. For each declaration
   below, `#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]`:

   ```text
   KAM.Planetary.p11cGe_sigma1_analyticAt
   KAM.Planetary.p11cGe_phi4_analytic
   KAM.Planetary.p11cGe_axes_eq
   KAM.Planetary.p11cGe_phi4_exists
   KAM.Planetary.p11cGe_phi4_ne_zero_iff_nr4
   KAM.Planetary.p11cGe_phi4_ne_zero_iff_good
   KAM.Planetary.p11cGe_det_analytic
   KAM.Planetary.p11cGe_det_neg
   KAM.Planetary.torsion
   ```

   Project import-closure scan: 276 modules, 58 frozen modules; all 58 corresponding
   manifest entries are SEALED, no unmanifested frozen paths, no provider imports.
   Imports are byte-unchanged from round 1. No DRAFT_SORRY anchor enters the proof.

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the explicitly permitted generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1148 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other hygiene failure was printed. The generated root was left untouched.

5. Protected paths and whitespace:

   `git diff inp...HEAD -- KAM/Frozen manifest README.md` is empty.
   Including `KAM.lean` reveals the same ten inherited generated import additions as round 1;
   `git log --oneline inp..HEAD -- KAM.lean` attributes them to `cea85d47 Merge inp-p11c-t19`.
   The round-2 protected-path diff, including generated files, is empty.
   `git diff --check inp...HEAD` exits **0**, with only the multiple-merge-base warning.
   The ancestry note is retained explicitly; the full protected-path comparison is not
   falsely reported empty. It is not a new T20 or auditor edit.

## Errata, limitations and closeout

No new suspected blueprint/pinned-source defect or implementation deviation was found.
Primary paper PDFs were not re-audited in this delta round. Round-1 findings on unchanged
proofs are retained; current build, kernel replay, all public axioms and exact signature
were independently rerun. This report closes only T20's F1 correspondence obligation and
gives no new verdict on T16, T19, T21 or a frozen headline theorem.

Only this report is a lasting audit edit, at the requested absolute worktree path.
The scratch probe was removed after verification. No source repair or weakened premise was
introduced. Final validation checks the report's whitespace, unchanged HEAD/target hash and
report-only git status.
