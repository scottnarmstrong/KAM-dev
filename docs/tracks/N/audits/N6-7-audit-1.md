# N6-7 independent package audit 1

Overall verdict: **PASS WITH NOTES**. The N6-7 reality result matches the approved design and blueprint. The repository note is the generated root's stale import list. This is an infrastructure package, not a frozen-anchor seal or closure of the Nekhoroshev headline.

## Scope and authority

Audited only:

- `KAM/Nekhoroshev/NormalForm/IterativeReal.lean` (132 lines).
- `KAM/Nekhoroshev/NormalForm/Iterative.lean` (19 lines).

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief, the N6-7 handoff and its AUDIT FOCUS, design v2 (including Appendix A), both design audits, blueprint Part 6, and track-N statements/frozen context. The user's exact worktree report destination overrides the generic brief's main-worktree destination. No production source was edited; no state-changing git command or subagent was used.

Snapshot: HEAD `66c3746f8b9043a5ce0287413f8f775e025dc0ac`; `inp` at intake `33c688a1d1c9d25d7099f328479f4f53b0301bb4`; `inp-n66` at intake `d3eba5a8e694dad6bf01c34c152dd6678db14f5c`.

`git diff inp...HEAD` reports multiple merge bases and selects `89f791e7f22039b1a5a3ac75858cf8484e971d00`. It contains the two scoped files plus inherited `IterativeRemainder.lean` (429 lines). `git diff inp-n66...HEAD -- KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean` is empty. Both scoped files are precisely the changes in HEAD's package commit (`git diff HEAD^ HEAD --stat`: 2 files, 151 insertions). Other changes visible against the moving `inp-n66` branch are inherited and outside this audit.

SHA-256:

| File | Hash |
|---|---|
| `IterativeReal.lean` | `577055f154a4916e0ba783026a1173fdef82320d955f51af8dd53b9eb88ffec2` |
| `Iterative.lean` | `026ee821cf45f8303056d072396380e8e25852e127a2efcf6a08e015103a6f1e` |
| Design v2 | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Blueprint p6 | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |

## Declaration ledger

All names below are in `KAM.NormalForm` except the facade module.

| Node / declaration | Lean locator | Verdict | Reason |
|---|---|---|---|
| `stepN:p6:it-real`, real frequency | `IterativeReal.lean:33`, `freq_im_real` | PASS | Derives real partial derivatives from holomorphy and reality on the whole real slice; does not assume real frequency. General helper permits arbitrary complex base sets and has no nonresonance or smallness premise. |
| Restriction helper (private) | `IterativeReal.lean:72`, `realOn_mono` | PASS | Literal restriction of the universal `RealOn` predicate; unused helper is harmless. |
| Radius transport (private) | `IterativeReal.lean:77`, `realOn_Dom_congr` | PASS | Substitution of equal radii; no domain change beyond equality. |
| `bpN:p6:iterative-direct` (e), hence `bpN:p6:iterative` (e) through the existing source wrapper | `IterativeReal.lean:89`, `iterative_direct_e` | PASS | Exact v2 signature (design L807–814); all four reality outputs on the intended domains. No additional premise or weakened conclusion. |
| Iterative facade | `Iterative.lean:8–10` | PASS | Only three public imports, of `IterativeMap`, `IterativeRemainder`, `IterativeReal`; no new declaration or proof. |
| Frozen/provider equality and seal-body checks | No frozen anchor/provider in N6-7 | N/A | No frozen export is claimed proved or seal-ready. Replaced with an exact design-signature probe, described below. |

## Refutation and fidelity checks

`freq_im_real` uses the real line `γ(t)=ιI+t eᵢ`. Openness of `polyNbhd D r` supplies a genuine neighbourhood of zero on which γ stays in the domain. At zero angles, `s>0` puts `(0,I+t eᵢ)` inside `Dom`; `hhr` therefore makes the imaginary part identically zero near zero. Restricting the complex derivative to real scalars and composing with `Complex.imCLM` computes its derivative as the imaginary part of the coordinate partial. Uniqueness with the derivative of the constant zero function proves the result. Holomorphy at the evaluation point guards `fderiv`; no totalized derivative fallback is used. Neither openness nor reality of the arbitrary base set D is assumed or needed.

For `iterative_direct_e`, the last conjunct of `homological_direct` supplies real `homGen` and `homRes`, using the newly proved real-frequency helper, symmetric Λ, and real f. The one-sided negation closure in `hΛ` is equivalent to symmetry because negation is involutive. Adding real g gives real `iterG` on the original domain. `H.compose` supplies composition data with input widths `(r−ρ,s−σ)` and generator widths `(r,s)`; `composition_real` therefore returns reality at `(r−ρ−ρ,s−σ−σ)`. Ring equalities transport this to `(r−2ρ,s−2σ)`. Subtracting real h and `iterG`, restricted by `Dom_mono`, proves the exact `iterF` result. Finally `(canonical_map_b H.canon).2` proves map reality on the larger `(r−3ρ/2,s−3σ/2)` domain, with the same flow domain as `iterMap`.

The bundled `IterHyp` fields (in inherited `IterativeMap.lean:52–70`) are source premises: positive parameters and losses, holomorphy, the direct divisor bound, finite decomposition and analytic/norm bounds, and smallness. `canon` and `compose` are proved consequences, not bundled conclusions. The carried δ bound is the approved design convention. The helper and main result preserve the prescribed `Fin n → ℝ/ℂ/ℤ` carriers and period-one definitions; there is no added dimension restriction, frequency bound or consumer-specific assumption.

Blueprint p6 L105 states “if Λ=−Λ, and h,g,f are real on real points, then φ, g₊, f₊ are real on real points and Φ maps real points to real points”; L126's proof derives real frequency from holomorphy and reality of h. These are exactly the implemented premises and argument. The direct-divisor corollary L129–137 retains all five iterative conclusions. No blueprint contradiction or new suspected pinned-source defect was found. No pinned-PDF re-audit is claimed beyond this specified design/blueprint package scope.

## Definition classification and import quarantine

There are **no new `def`, `abbrev` or `structure` declarations** in either scoped file. Local `set`/`let` expressions in the helper are the coordinate vector, included real point and affine real path; they denote their stated objects on their entire carriers. Inherited `iterMap` is the specified time-one Hamiltonian flow, `iterG=g+homRes`, and `iterF=H∘iterMap−h−iterG`; this package uses them only on their certified domains. Their off-domain values do not support any conclusion.

A recursive source-import scan starting at `KAM.Nekhoroshev.NormalForm.Iterative` visits 76 KAM modules and finds **zero provider imports and zero frozen theorem imports**. Consequently no imported DRAFT_SORRY theorem can supply either proof, and no imported frozen theorem requires a SEALED-state exception. Frozen definitions remain unchanged. The facade has only public imports and the required module/header/docstring/public-section structure; `IterativeReal` has the same required structure, with private tactic import and exposed public section.

## Independent validation receipts

Every Lean/Lake command was serialized with `LEAN_NUM_THREADS=1`; all direct invocations used `nice -n 5`. Builds went through the required compile gate. No resource override, clean, update, cache download or package-directory edit was used.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n67 KAM.Nekhoroshev.NormalForm.IterativeReal`

   Output: `[inp-gate] slot 2 acquired 07:11:25 for KAM.Nekhoroshev.NormalForm.IterativeReal`; `Build completed successfully (3227 jobs).` Exit **0**.

2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n67 KAM.Nekhoroshev.NormalForm.Iterative`

   Output: `[inp-gate] slot 2 acquired 07:12:00 for KAM.Nekhoroshev.NormalForm.Iterative`; `Build completed successfully (3228 jobs).` Exit **0**.

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N67Audit.lean`

   Probe imports only the facade, copies the complete design-v2 signature under `N67Audit.design_iterative_direct_e`, and proves it with `by exact KAM.NormalForm.iterative_direct_e H hΛ hhr hgr hfr`. It then checks `example : type_of% @design_iterative_direct_e := @KAM.NormalForm.iterative_direct_e`. Thus implicit binders, quantifier order, explicit premise order and conclusion all elaborate against the design without introducing draft `sorry` assumptions. A separate textual comparison of the original signatures, ignoring whitespace only, returned `True`.

   Exact output, exit **0**:

   ```text
   'KAM.NormalForm.freq_im_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.NormalForm.iterative_direct_e' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.IterativeReal KAM.Nekhoroshev.NormalForm.Iterative`

   One invocation replayed both scoped modules. Exact output, exit **0**:

   ```text
   replaying KAM.Nekhoroshev.NormalForm.Iterative
   replaying KAM.Nekhoroshev.NormalForm.IterativeReal
   ```

5. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exact output, exit **1**:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (445 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   **PASS WITH NOTES under the brief's explicit exception:** the only reported failure is the expected stale generated root. No 100-character-line, forbidden-token, module-format, frozen-integrity or ABI failure was reported. The root was left untouched as required.

6. Static hygiene: both files contain no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`; no new definition bodies require exposure. Counts are 132 and 19 physical lines, with **zero lines over 100 Unicode characters**, comfortably below 1500. Required module headers, docstrings and public sections are present.

7. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, exit **0** (only the same multiple-merge-base warning). `git diff --check`: **empty**, exit **0**. Auditor-created scratch was removed after validation; the pre-existing untracked handoff was preserved.

## Uncertainties, errata and deviations

No proof or statement blocker found. No default-heartbeat design signal occurred. No new suspected source erratum or mathematical deviation was introduced. Design-audit-2's unrelated planning/API notes do not alter the N6-7 target. This report certifies only the scoped package; inherited modules were inspected where needed for applicability, not independently re-audited in full. No frozen theorem seal or headline proof is certified.
