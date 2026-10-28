# Independent S10-S package audit 1

Overall verdict: **PASS WITH NOTES**. Both node contracts pass, and the independent build, signature/application probes, complete axiom check and kernel replay passed. Notes are the permitted stale generated root and inherited dependency warnings. No frozen anchor is implemented or sealed by this package; provider/frozen-type and seal-body checks are inapplicable (P810 design lines 459–467 explicitly retain this boundary).

## Scope and authority

Audited HEAD `93ebbc62daa83d766ba7ce199da7d60867621f1d`; comparison refs at audit time: `inp=05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, `inp-s10c=be0ea5a82bfa26156f8c3a2453d344ed92522b7c`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the assigned package brief and S10-S handoff, the track-P statement, P810 design and both design audits, and Part 10's norm/index/stability/scaling statements and proof. The user's exact report destination overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` adds DiagonalTensor (172 lines), FiniteType (450), and Stability (396). Per AUDIT FOCUS, this audit reviews only `KAM/Planetary/Nondegeneracy/Stability.lean`, with DiagonalTensor/FiniteType read as dependencies. `git diff inp-s10c...HEAD -- KAM/Planetary/Nondegeneracy/Stability*.lean` identifies exactly that new file. The unfiltered s10c comparison includes unrelated changes inherited on this branch; those are outside this audit.

The standalone signatures are absent in this worktree. Read `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` (SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`), matching design audit 2's revision-2 pin. Both theorem signatures match after whitespace normalization, including binder order, implicitness, premises and all conclusions. The corresponding signatures also appear in this worktree's design appendix. Design audits are at `docs/tracks/P/design/DESIGN-P810-design-audit-{1,2}.md` (also present here), rather than the handoff's abbreviated audits-directory location.

## Declaration review

Names below are relative to `KAM.Planetary.Nondegeneracy`; all are public. PASS denotes the scoped contract/proof review, not campaign closure.

| Node / proof role | Declaration (Stability.lean line) | Verdict | Reason |
|---|---|---|---|
| stability: coordinate bound | `abs_sum_mul_le_length2` (32) | PASS | Cauchy–Schwarz for Euclidean unit c; both signs. |
| coordinate functional | `coordForm` (43) | PASS | Literal finite sum of weighted continuous projections. |
| coordinate evaluation | `coordForm_apply` (45) | PASS | Exact finite dot product. |
| coordinate analyticity | `analyticOnNhd_coordForm` (48) | PASS | Linear composition of the given analytic map. |
| coordinate derivatives | `iteratedFDeriv_coordForm` (54) | PASS | Commutation with a fixed linear functional; finite differentiability suffices. |
| diagonal boundedness | `bddAbove_jetNorm` (64) | PASS | Bounds diagonal Euclidean outputs by sqrt(m) times ambient operator norm; no replacement of the target norm. |
| diagonal evaluation | `length2_diag_le_jetNorm` (79) | PASS | Zero order handled directly; positive orders use bounded sSup. |
| stability: source jet control | `abs_coordJet_le` (89) | PASS | Source jet bound implies scalar combination bound; no hard step assumed. |
| stability: supremum difference | `jetOp_le_add_of` (100) | PASS | Triangle inequality and bounded diagonal sSup; handles empty input sphere. |
| stability: scalar jet difference | `abs_scalarJet_sub_le` (112) | PASS | Order zero uses value/absolute-value inequality, higher orders both comparison directions. |
| stability: square identity | `sq_sub_eq` (140) | PASS | Exact W(2V+W) factorization. |
| st-prod / st-diff | `stability_pointwise` (147) | PASS | Diagonal Leibniz formula and sum of binomial coefficients yield exactly 2^nu theta(2M+theta). |
| bpP:p10:stability | `stability` (208) | PASS | All three signature conclusions; nonempty sphere/product justify infimum comparisons; positive-old-amount guard retained. |
| scaling: regularity | `analyticOnNhd_squaredForm` (257) | PASS | Literal squared coordinate form is analytic. |
| scaling: diagonal homogeneity | `jetOp_smul` (261) | PASS | Nonnegative scalar and actual scaled supremum set; also valid for empty sphere. |
| scaling: scalar homogeneity | `scalarJet_const_mul` (275) | PASS | Separate zero order and finite-order derivative scaling. |
| scaling: finite maximum | `jetMax_const_mul` (286) | PASS | Homogeneity by recursion over finite orders, with nonnegative scalar. |
| scaling: sphere bounds | `length2_weighted_bounds` (295) | PASS | a <= length2(w*c) <= b by weighted sum of squares; positivity/dimension guards explicit. |
| scaling: exact square identity | `sq_scale` (314) | PASS | Exact r^2 identity from weighted vector equality; conditional algebra helper has a distinct name. |
| bpP:p10:scaling (amount component) | `scaling_amount` (324) | PASS | Positive diagonal scaling gives lo^2 beta <= scaled beta <= hi^2 beta with all source data fixed. |

The stability theorem allows arbitrary certified nonnegative upper bounds M and theta instead of requiring equality to compact maxima. This is the explicitly documented strengthening (design line 356), not an additional source premise. Neither R-nondegeneracy nor positive perturbed amount is assumed. Compactness is unused in these particular comparison proofs, but remains in the exact design signatures. The helpers' derivative bounds are hypotheses only in distinctly named intermediate inequalities, and the main theorem discharges them from its source tensor bounds.

For scaling, t=length2(s*c) lies in [lo,hi], and normalized s*c/t lies on the output sphere. The squared scalar form and every finite jet maximum acquire t^2. The upper estimate uses inverse weights and tau>=1/hi, so tau^(-2)<=hi^2; no false termwise upper estimate for an infimum is used. Bounds hold for every natural mu, including zero. Input dimension d=0 is permitted: order-zero branches use values directly; positive-order empty diagonal spheres give zero and the supremum lemmas explicitly handle that case. Output m>0 and K nonempty guard all infimum comparisons.

The blueprint scaling remark (Part 10 lines 191–193) also mentions unchanged index and preserved R-nondegeneracy. This package owns the amount comparison only, as its signature/name state. `scaling` belongs to S10-R and index reasoning uses S10-C; this audit does not claim those separate exports are proved here.

## Definition classification and dependencies

The sole new definition is `coordForm`: intended continuous linear functional on its entire carrier, with no branch, default, choice or exceptional value. No new abbrev, structure or bundled theorem premise occurs. Existing `jetNorm`, `scalarJet`, `jetOp`, `jetMax`, `sphere`, `squaredForm` and `betaMu` are used literally. Their separate zero-order conventions and Euclidean diagonal norms agree with Part 10 line 197 and lines 210–213; ambient spaces remain Fin-function spaces with the Pi norm.

Direct imports: Mathlib, DiagonalTensor, FiniteType. A recursive source-import scan reached 68 KAM modules, no provider and no frozen theorem module (only frozen definitions). Thus no DRAFT_SORRY theorem is imported. No frozen theorem signature needs to be substituted or repaired for this helper package.

## Independent checks

Commands were run with one auditor-controlled Lean/Lake invocation at a time. The initial queued build was cancelled while awaiting a compile slot, and the initial lint was restarted before its ABI Lean stage so the definitive run below inherited both the requested thread count and niceness. No source was changed.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (554 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is PASS WITH NOTES under the brief's explicit stale-root exception. No generated file was regenerated.

Static checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/Nondegeneracy/Stability.lean
(no matches; exit 1)
wc -l KAM/Planetary/Nondegeneracy/Stability.lean
396 KAM/Planetary/Nondegeneracy/Stability.lean
```

Module header, copyright, public imports, module docstring and `@[expose] public noncomputable section`: PASS. Maximum line width: 100. Source SHA-256: `30c27e7887e81af56224c243e471dec09f32f0717573280e6178b5e6732fffab`.

Targeted build, independent rerun:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10s KAM.Planetary.Nondegeneracy.Stability
[inp-gate] slot 2 acquired 11:17:08 for KAM.Planetary.Nondegeneracy.Stability
✔ [9114/9114] Built KAM.Planetary.Nondegeneracy.Stability (114s)
Build completed successfully (9114 jobs).
exit 0
```

No scoped-file warning. Inherited replayed diagnostics were:

```text
warning: KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:212:42: Variable name `hm` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:212:55: Variable name `hκ` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:247:37: Variable name `hm` is not explicitly referenced.
warning: KAM/Planetary/Poincare/Chart.lean:247:50: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:147:57: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:157:52: Variable name `hκ` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:500:5: Variable name `hw` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:524:52: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Mass.lean:524:65: Variable name `hκ` is not explicitly referenced.
```

Fresh signature/application and complete axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10SAudit.lean
'KAM.Planetary.Nondegeneracy.abs_sum_mul_le_length2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coordForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analyticOnNhd_coordForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.iteratedFDeriv_coordForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.bddAbove_jetNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.length2_diag_le_jetNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.abs_coordJet_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetOp_le_add_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.abs_scalarJet_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sq_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.stability_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analyticOnNhd_squaredForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.scalarJet_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.length2_weighted_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sq_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.scaling_amount' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The scratch file imported only the scoped module and declared fresh copies `audit_stability` and `audit_scaling_amount` of the exact signatures, with bodies applying the original exports to all explicit binders in order. A separate whitespace-normalized comparison against the pinned design signature reported `True` for each. It then ran `#print axioms` for all 19 new public lemmas/theorems; output above is complete. There is no `sorryAx` or additional axiom.

Kernel replay (one invocation; the scoped module is the complete package, with all its helper declarations):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Stability
replaying KAM.Planetary.Nondegeneracy.Stability
exit 0
```

## Verdicts, uncertainties, errata and deviations

| Anchor / node | Verdict | Boundary |
|---|---|---|
| bpP:p10:stability | PASS WITH NOTES | Contract and proof pass; only the global lint exception and inherited warnings above. |
| bpP:p10:scaling (amount comparison) | PASS WITH NOTES | Exact amount contract and proof pass; separate index/R-nondegeneracy exports are outside S10-S. |
| Frozen anchors | Not applicable | No provider or seal delivered or audited here. |

No suspected defect in the scoped blueprint statements or a pinned source was found. No new paper erratum is alleged: the comparison lemmas are the blueprint's own arguments, and this was not a fresh external-PDF source audit. No hypothesis, norm, carrier, normalizer or conclusion was changed. No default-heartbeat design failure occurred. The explicit-bound strengthening of stability is already documented by the approved design; no new mathematical deviation was introduced.

This independently validates S10-S's helper package. It does not establish frozen-anchor closure, torsion, the nondegeneracy interface, or any physical headline. Dependencies were inspected for relevant definitions/imports and checked through the target's build and replay, rather than separately re-audited as packages.

Only this report was written in tracked repository space. The pre-existing untracked S10-S-handoff.md was preserved. Audit-created scratch probe and logs were deleted after their results were incorporated above. No git state-changing command was used; protected files and production Lean sources were not modified.
