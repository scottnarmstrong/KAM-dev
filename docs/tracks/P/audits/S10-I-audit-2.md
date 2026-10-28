# Independent S10-I audit 2 — delta audit

Overall verdict: **PASS WITH NOTES** for S10-I. Round-1 **F1 and F2 are closed**, and **N1 is explicitly covered**. The signed interface still passes. The notes concern the permitted stale generated root and the precise scope of the new partial-restatement companion; no blocking finding remains. No frozen anchor is assigned or sealed.

Scope: `/root/code/KAM-inp-s10i`, HEAD `5b7f2c7b1ae6427d16c7833ce72e1453511732e7`, Round-1 baseline `dc348ba5`, comparison `git diff inp...HEAD` (`inp` resolved to `d1a02150c8e815febce9e0fade2dd194d5ee7795`). The user's exact report destination overrides the generic brief's main-worktree destination. Audit only `KAM/Planetary/Nondegeneracy/Interface.lean`; no frozen anchor is assigned or sealed, so provider/seal-body checks are inapplicable. The original signed theorem is independently signature-probed instead.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief, both handoffs and audit 1; P810 design/node table and its two design audits; the original P810Signatures interface; Part-10 blueprint and graph interface/if-a–if-d records; track-P conventions; the new companions and their GoodAxes, Frequency, FiniteType, Stability and local-spectrum suppliers. This delta retains the prior audit's unchanged proof assessment, with fresh build, axioms and kernel validation.

## Delta and findings

`git diff dc348ba5 HEAD` changes exactly one file: 131 insertions, zero deletions. Removing the single Stability import and the appended companion block reconstructs the baseline byte-for-byte. The entire original `interface` statement **and proof** are byte-unchanged; its type text also equals the literal original signature. The 131 insertions comprise one import and 130 appended lines before the unchanged namespace endings. Actual file size is **322 lines**, correcting the handoff's 321; maximum line width is **100 characters**, with no lines over 100.

**F1 closed.** `min_mode_continuous_positive` explicitly exports continuity and pointwise strict positivity of the finite minimum on all `goodAxes D`, exactly the omitted function-level conclusion at `P-p10.nodes.md:1639` / blueprint line 251. `Finset.inf'` is the genuine finite minimum; `k4_toFinset_nonempty` constructs a one-coordinate unit integer mode from `2 ≤ n`. The mode set is exactly `0 < Σ |kᵢ| ≤ 4`. No empty-set fallback, assumed continuity, or assumed positive minimum occurs. The unchanged interface separately exports the compact-patch minimum and every modewise bound, completing if-b.

**F2 closed.** The public Stability import makes S10-S available. `interface_stability` (lines 277–318) specializes its exact squared-scalar bounds to `frequency D`, on `B = action D '' ball a0 (2*r0)` and `K = action D '' closedBall a0 r0`. Perturbations are analytic on B; M and θ are nonnegative upper bounds for precisely the original jets through μ. All three conclusions retain the constants `2^ν*θ*(2*M+θ)`, `2^μ*θ*(2*M+θ)` and the half-amount smallness guard. For every `μ ≥ μ0`, the proof derives `0 < betaMu ... μ` from β positivity, its exact defining equality and monotonicity before invoking the guarded positive-amount conclusion. It assumes neither perturbation nondegeneracy nor the desired amount bound.

**N1 closed.** `patch_spectrum` returns analytic sorted spectrum, strict monotonicity (hence simplicity), negativity and local analytic SO(n) diagonalizing rotations around every point of the closed good patch. The local eigenvalue function is named s, as in the upstream local-analytic theorem; ordered diagonalization identifies its spectrum. `patch_rnd` returns ν on the action image, 2σ on the axis ball, and their positive componentwise rescalings/permutations; the full action-frequency rescaling/permutation clause includes its unscaled instance by choosing all scales 1 and the identity permutation. These are the carriers in `rnd` (Frequency:171–177); the action/axis inverse transports the secular assertion to action coordinates. No carrier or frequency normalization is changed. Both companions apply to the very same outer patch supplied by interface; `2*r0 > 0` follows from r0 positivity.

**Restatement/simultaneity note (harmless).** The handoff's phrase “rather than reusing it” needs precision: the *statement* of `interface_stability` repeats only part of the interface conclusion, but its *proof* directly reuses `interface` at lines 300–302 and keeps that single choice of a0, r0, α, β and μ0 throughout. The original and companion types do not contradict each other. The companion is not a literal conjunction containing every original clause: it omits, for example, the modewise α bound and index minimality. Do not treat two independent existential eliminations as yielding identical witnesses. This causes no package gap: the original complete interface remains available, and the general imported stability theorem and patch companions apply to any of its witnesses, as the new proof demonstrates. No premise or distinct patch choice is hidden in this restatement.

## Node and declaration coverage

All declarations are in `KAM.Planetary.Nondegeneracy`.

| Node / role | Declaration / location | Verdict | Reason |
|---|---|---|---|
| `bpP:p10:interface`, signed type | `interface`, 76–188 | PASS | Literal signature, unchanged proof, shared witnesses. |
| `bpP:p10:interface`, retained parent clauses | `interface` and companions | PASS | F1/F2/N1 supplied; restatement scope noted above. |
| `stepP:p10:if-a` | `exists_good_patch`; `patch_spectrum`, 232–252 | PASS | Simultaneous zero avoidance; simple negative analytic spectrum and local rotations. |
| `stepP:p10:if-b` | `min_mode_continuous_positive`, 205–228; `interface` | PASS | Literal finite-minimum function plus compact positive minimum/bounds. |
| `stepP:p10:if-c` | `image_action_open`; `interface`; `patch_rnd`, 257–271 | PASS | Original action patch and full frequency; ancillary nondegeneracy/scaling delivered. |
| `stepP:p10:if-d` and S10-S tail | `interface`; `interface_stability`, 277–318 | PASS | Original least index/amount and monotonicity; specialized guarded stability. |
| Original helper | `image_action_open`, 34–47 | PASS | Unchanged, no added hypothesis. |
| Original helper | `exists_good_patch`, 49–73 | PASS | Unchanged, one joint good patch. |
| New helper | `k4_toFinset_nonempty`, 192–201 | PASS | Explicit admissible integer mode from source dimension hypothesis. |

Definition classification: no new top-level def, abbrev, structure or instance, and no new fallback object. The new finite minimum uses a proved nonempty finite set. Local B/K are the actual action images. `Data` contains physical positivity and dimension data only. Patch inclusion and radius positivity are the source patch hypotheses, discharged for the interface witnesses; they do not assume the spectral/R-nondegeneracy conclusions. No conclusion-shaped premise, coupling dependence, widened constant dependence or norm substitution was introduced.

## Independent verification receipts

All Lean/Lake commands below ran serially, from this worktree, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No production edit, state-changing git command, root regeneration or package-cache mutation was performed.

Targeted build: `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10i KAM.Planetary.Nondegeneracy.Interface` — **exit 0**. Output: `[inp-gate] slot 2 acquired 18:27:54 for KAM.Planetary.Nondegeneracy.Interface`; `Build completed successfully (9148 jobs).` Only upstream replayed warnings (Energy, Poincare.Chart, Mass, Coefficients, Definiteness, LocalAnalytic.Unique, Weyl, SymmetricRelation.Analytic); none in Interface. This was a targeted overlay build, without cleaning or rebuilding the library from scratch.

Signature/axiom probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10IAudit2.lean` — **exit 0**. The probe copies the literal original signature under `audit2_signature`, with body `by exact interface D hn ha hη f hf hne`, and prints axioms of every public declaration. Exact output:

```text
'KAM.Planetary.Nondegeneracy.image_action_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_good_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.interface' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.k4_toFinset_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.min_mode_continuous_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.patch_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.patch_rnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.interface_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
```


Kernel replay: `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Interface` — **exit 0**. Exact output: `replaying KAM.Planetary.Nondegeneracy.Interface`. All package declarations are in this single module; no provider or separate lemma module is assigned.

Source lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` — **exit 1**, solely the brief-permitted generated-root mismatch. Complete substantive output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (804 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Hygiene verdict: **PASS WITH NOTES** under the explicit generated-root exception. The root was left untouched.

Static checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and `git diff --check inp...HEAD` both exit 0, no output. Baseline reconstruction and original statement/proof byte comparisons return True; fresh original-signature comparison returns `SIGNATURE_TEXT_IDENTICAL True`. All eight public short names occur as declarations only in Interface when searching all KAM Lean sources. Namespace inspection finds no root declaration or shadow. Recursive KAM import closure: 102 modules, no provider and no frozen theorem/DRAFT_SORRY anchor; all 47 reached frozen definition files have matching SEALED manifest entries. No forbidden proof escape, resource override or EuclideanSpace occurs. Module header/import/docstring/public-section format is intact.

## Errata and limits

No new suspected pinned-source/blueprint defect or mathematical deviation found. F1/F2 were delivery gaps and are now repaired; N1 is explicitly supplied. The only handoff correction is the 322-line count and the precise partial-restatement interpretation above. Existing Part-10 source errata are inherited, not independently re-audited here. No frozen theorem or downstream campaign theorem is closed by this package audit.

The auditor-created signature/axiom probe was deleted after validation. Final whitespace and placeholder checks passed; `git diff --check` exited 0. Final `git status --short` contains only `?? docs/tracks/P/audits/S10-I-audit-2.md`. No tracked file was modified by the auditor.
