# SO-EXPR-B2 independent audit 1

Verdict: **PASS WITH NOTES**. The signed `KAM.Certificate.HamExpr.jet_d3` is proved with exactly its signed premises, and the B2 third-order jet slice is complete. Notes concern the brief-permitted stale generated root and the explicit distinction between handwritten export names and generated structure-field names (below). No frozen anchor is being sealed by this package; seal-body/provider-type probes are therefore inapplicable.

Audited worktree: `/root/code/KAM-inp-soexprc`. HEAD: `c1f589484272db19f2ae292ac3df3785d651639b`. Initial comparison ref `inp`: `f8405551c09bb7baf63ad01547cc2ecb8d372bbc`. At final validation it had advanced externally to `b0f0147d8a7134d88cd04d068195207ce9d2ce04`; both comparisons have merge base `b67f81c3fc7ef65992f3ae6b749262e9fcb182a1`, and a fresh byte-for-byte comparison confirmed their complete three-dot diffs are identical. Final protected-path and diff-whitespace checks were repeated successfully. Inspected the complete `git diff inp...HEAD`: four Lean files, 538 insertions and 139 deletions. The existing untracked handoff was read and left untouched. Report destination follows the user's explicit worktree-path override of the generic brief.

Authority: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff and AUDIT FOCUS, `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` §D, and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:477–490`. This is unfrozen SO infrastructure, so the unrelated I/N/P theorem anchors and blueprints are not the statement authority. There is no local SO `statement.md`; the signed §D text is the applicable contract.

## Statement and proof review

The source prefix from `theorem HamExpr.jet_d3` through its conclusion (excluding `:=`) is character-for-character equal to signed §D, including the fully qualified namespace `KAM.Certificate`. A fresh declaration copied from that signed text, renamed `KAM.Certificate.auditSignedJetD3`, elaborates with body `by exact HamExpr.jet_d3 e hS hnv hz a b c`.

`SlpNode.Sound.d3` supplies the three ordered directional derivatives for every index below `2*n`. `slpTab3_spec` preserves prefixes and proves every entry; `slpFinish_sound` carries old table realizations through the appended third table. Constants/actions have zero third derivatives, characters have all three phase factors, products have eight terms, and exponential/inverse rules have the exact cross terms. Inverse coefficients are -6, +2, -1 with inverse powers 4, 3, 2. `slpInvPre_spec` constructs the inverse powers, rather than assuming them at the public expression theorem.

`iteratedFDeriv_three_eq_jetDeriv` differentiates evaluation of the second continuous multilinear derivative, using local C3 regularity on the open set. Its eventual-equality argument justifies differentiation locally and preserves direction order. `HamExpr.jet_d3` translates nested optional slots using the existing zero slot and identifies `dirVec` with `phaseBasis`. No positivity, dimensional lower bound, analyticity certificate, caller-supplied jet correctness, or extra domain premise is added. The `n=0` statement is vacuous in its phase indices, as signed.

The existing compiler induction and wrapper proofs elaborate against the strengthened invariant for all expression constructors: constants, π, actions, both mode trigonometric constructors, addition, multiplication, division, power, exp, sin, cos. B2 does not change compilation traversal: denominators inside zero products and exponent-zero operands remain compiled. The B1 mathematical surface is not re-audited here; its continued elaboration and axiom hygiene were checked.

## Declaration coverage

All declaration names below are relative to `KAM.Certificate`. The rows cover new declarations, moved calculus rules, and changed third-order portions of existing declarations. Existing B1 short-name reuse is outside scope; only the added d3 clause of `SlpNode.Sound.mono` is in scope.

| Node / locator | Lean declaration | Verdict | Reason |
|---|---|---|---|
| B2 / `Diff.lean:332` | `HamExpr.jet` | PASS | Maps all three folded-slot tables to zero-slot indices; retains the compiled program. |
| B2 / `Diff.lean:410` | `HamExpr.jet_d3` | PASS | Signed §D statement exactly; all ordered coordinate triples, no additional premise. |
| B2 / `DiffBuild.lean:315` | `slpTab3` | PASS | Threads the program through range (2*n) and nested slpTab2. |
| B2 / `DiffBuild.lean:319` | `slpTab3_spec` | PASS | Every in-range triple realizes its supplied function; prefix preserved. |
| B2 / `DiffCalculus3.lean:28` | `JetSmoothOn.jetNeg` | PASS | Approved rename of the moved negation closure; avoids short-name collision. |
| B2 / `DiffCalculus3.lean:31` | `jetDeriv_neg` | PASS | Moved second-order rule with unchanged mathematical statement and proof. |
| B2 / `DiffCalculus3.lean:41` | `jetDeriv2_mul` | PASS | Moved second-order rule with unchanged mathematical statement and proof. |
| B2 / `DiffCalculus3.lean:52` | `jetDeriv2_add` | PASS | Moved second-order rule with unchanged mathematical statement and proof. |
| B2 / `DiffCalculus3.lean:61` | `jetDeriv2_cexp` | PASS | Moved second-order rule with unchanged mathematical statement and proof. |
| B2 / `DiffCalculus3.lean:73` | `jetDeriv2_inv` | PASS | Moved second-order rule with unchanged mathematical statement and proof. |
| B2 / `DiffCalculus3.lean:95` | `jetDeriv_congr2` | PASS | Two local derivative congruences on an open set. |
| B2 / `DiffCalculus3.lean:100` | `jetDeriv_cmul` | PASS | Constant multiplication rule; derives differentiability from smoothness. |
| B2 / `DiffCalculus3.lean:108` | `jetDeriv3_add` | PASS | Third derivative distributes over addition. |
| B2 / `DiffCalculus3.lean:118` | `jetDeriv3_mul` | PASS | All eight ordered Leibniz terms, with correct derivative order. |
| B2 / `DiffCalculus3.lean:138` | `jetDeriv3_cexp` | PASS | Exponential times cubic first derivatives, three cross terms, and third derivative. |
| B2 / `DiffCalculus3.lean:154` | `jetDeriv_inv_sq` | PASS | Derivative of inverse square: -2 times inverse cube times first derivative. |
| B2 / `DiffCalculus3.lean:165` | `jetDeriv_inv_cube` | PASS | Derivative of inverse cube: -3 times inverse fourth power times first derivative. |
| B2 / `DiffCalculus3.lean:176` | `jetDeriv3_inv` | PASS | Coefficients -6, +2, -1 with inverse powers 4, 3, 2; nonzero premise only. |
| B2 / `DiffCalculus3.lean:211` | `iteratedFDeriv_three_eq_jetDeriv` | PASS | Local C3 regularity, continuous multilinear evaluation, eventual equality; correct order u,v,w. |
| B2 / `DiffNode.lean:86` | `jetDeriv3_char` | PASS | Three phase multipliers; includes (2π)^3 and i^3. |
| B2 / `DiffNode.lean:129` | `SlpNode` | PASS | Adds actual third-order slot data. |
| B2 / `DiffNode.lean:142` | `SlpNode.get3` | PASS | Total nested lookup; missing entries denote the zero folded slot. |
| B2 / `DiffNode.lean:146` | `SlpNode.Sound` | PASS | Adds in-range third-derivative invariant; proved by every constructor. |
| B2 / `DiffNode.lean:156` | `SlpNode.Sound.mono` | PASS | Only new d3 clause audited: prefix extension preserves realizations. |
| B2 / `DiffNode.lean:172` | `slpFinish` | PASS | Appends third-order table after first and second; preserves prior slots. |
| B2 / `DiffNode.lean:179` | `slpFinish_sound` | PASS | Derives all three tables; h3 is an explicit internal entry obligation discharged by callers. |
| B2 / `DiffNode.lean:206` | `slpConstNode` | PASS | Third table is correctly zero. |
| B2 / `DiffNode.lean:210` | `slpConstNode_sound` | PASS | Three derivatives of a constant vanish. |
| B2 / `DiffNode.lean:257` | `slpActionNode` | PASS | Third table is correctly zero; arbitrary natural action index remains total. |
| B2 / `DiffNode.lean:261` | `slpActionNode_sound` | PASS | Finite valid action coordinate; second and third derivatives vanish. |
| B2 / `DiffNode.lean:292` | `slpCharNode` | PASS | Third table uses -i times product of mode components times (2π)^3. |
| B2 / `DiffNode.lean:304` | `slpCharNode_sound` | PASS | Third phase formula and action-direction zeros proved. |
| B2 / `DiffNode.lean:370` | `slpCross` | PASS | Three second-times-first cross terms, with ordered indices. |
| B2 / `DiffNode.lean:375` | `slpCross_ent` | PASS | Derives entries from the operand invariant. |
| B2 / `DiffNode.lean:386` | `slpAddNode` | PASS | Adds corresponding third-order entries. |
| B2 / `DiffNode.lean:392` | `slpAddNode_sound` | PASS | New d3 clause follows third sum rule. |
| B2 / `DiffNode.lean:423` | `slpMulD3` | PASS | Exactly the eight terms of ordered product differentiation. |
| B2 / `DiffNode.lean:435` | `slpMulNode` | PASS | Passes slpMulD3 into the finalizer. |
| B2 / `DiffNode.lean:446` | `slpMulNode_sound` | PASS | Derives all eight third-order terms from operand invariants. |
| B2 / `DiffNode.lean:493` | `slpExpD3` | PASS | E times triple product plus three cross terms plus third derivative. |
| B2 / `DiffNode.lean:499` | `slpExpNode` | PASS | Passes slpExpD3 into the finalizer. |
| B2 / `DiffNode.lean:507` | `slpExpNode_sound` | PASS | New d3 clause follows exponential rule. |
| B2 / `DiffNode.lean:543` | `slpInvD3` | PASS | Correct inverse fourth/cube/square formula, coefficients -6,+2,-1. |
| B2 / `DiffNode.lean:550` | `slpInvTail` | PASS | Consumes certified inverse powers including the new fourth power. |
| B2 / `DiffNode.lean:563` | `slpInvTail_sound` | PASS | hw4 is internally generated by slpInvPre_spec; not an external theorem assumption. |
| B2 / `DiffNode.lean:618` | `slpInvPre` | PASS | Emits inverse and successive products through fourth power, without a nonzero fallback. |
| B2 / `DiffNode.lean:627` | `slpInvNode` | PASS | Uses the inverse slot at original program length and all three power slots. |
| B2 / `DiffNode.lean:631` | `slpInvPre_spec` | PASS | Proves prefix, valid inverse slot, global inverse value, and all power realizations. |
| B2 / `DiffNode.lean:659` | `slpInvNode_sound` | PASS | Discharges power obligations internally; retains only smoothness/nonvanishing and operand soundness. |

## Definition classification

Every new or changed data definition is an intended total program-building object: `slpTab3` is a three-dimensional threaded table; `SlpNode` contains its actual derivative-slot lists; `SlpNode.get3` is total lookup; `slpFinish` sequences all three table builders; the seven primitive node constructors append their operation and derivative tables. `slpCross`, `slpMulD3`, `slpExpD3`, `slpInvD3` encode exactly the formulas above. `slpInvPre` computes the inverse and its powers by ordinary SLP operations. `HamExpr.jet` maps folded optional entries to the prefixed zero slot.

`SlpNode.Sound` is an internal inductive correctness invariant, not a hypothesis smuggled into `HamExpr.jet_d3`: every constructor establishes it and `slpCompile_sound` derives it from `hS` and `hnv`. `slpFinish_sound` entry premises and `slpInvTail_sound` power premises are compositional internal interfaces, explicitly discharged by their callers. There are no new abbrevs, instances, conclusion-shaped source premises, or semantic fallbacks used to evade derivative correctness. Out-of-range list reads and arbitrary malformed nodes retain the existing total zero-slot convention; correctness is claimed and proved for valid compiled nodes and in-range phase indices.

## Verification receipts

All Lean-related commands are serialized, with `LEAN_NUM_THREADS=1`; builds use the prescribed compile gate. No overrides, clean/update/cache commands, or repository changes beyond this report were made. Probe files and logs were confined to `.lake/abi-scratch/` and removed after their relevant output was copied below.

Commands were run from `/root/code/KAM-inp-soexprc`.

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soexprc KAM.Certificate.Expr.Diff
```

Exit 0. Gate receipt: `[inp-gate] slot 1 acquired 14:56:26 for KAM.Certificate.Expr.Diff`.
Final output: `Build completed successfully (2902 jobs).` One replayed pre-existing warning in `Expr/Basic.lean:85:5`: `Variable name hS is not explicitly referenced.` No package error, sorry, or default-heartbeat failure.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOExprB2.lean
```

Exit 0. The probe imported `KAM.Certificate.Expr.Diff` and `Lean`, opened `KAM.Certificate`, and elaborated this fresh signed declaration:

```lean
namespace KAM.Certificate
theorem auditSignedJetD3 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b c : Fin n ⊕ Fin n) :
    e.jet.prog.val n z
        (((e.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0) =
      iteratedFDeriv ℂ 3 e.eval z ![phaseBasis a, phaseBasis b, phaseBasis c] := by
  exact HamExpr.jet_d3 e hS hnv hz a b c
end KAM.Certificate
```

It then ran `#print axioms` for every theorem declared in the four audited files (including unchanged B1 support declarations as extra dependency hygiene). Exact output:

```text
'KAM.Certificate.slpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpExpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCombine_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpPowNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_negKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.charFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigChar_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpDivNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cos_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sin_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jetSmoothOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.zero_slot_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpOv_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.list_getD_map' depends on axioms: [propext]
'KAM.Certificate.HamExpr.jet_v0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlotOk.mono' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.Realizes.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Realizes.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Realizes.none' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpEmit_prefix' does not depend on any axioms
'KAM.Certificate.slpEmit_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpAddO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpScaleO_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMapSt_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpEnt.scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTab1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTab2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTab3_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.jetNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_cexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_congr2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_cmul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_cexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_inv_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.iteratedFDeriv_three_eq_jetDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetSmoothOn_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_dirVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpNode.Sound.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SlpNode.Sound.realizes_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpFinish_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpConstNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dirVec_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpActionNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCharNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCross_ent' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpAddNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpExpNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpConstVal_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvTail_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial version additionally attempted an optional `run_cmd` whole-environment leaf-name scan; it was interrupted (exit 130) after excessive runtime. That interrupted run is not counted as a successful check. The clean signed/axiom probe above, without that scan, completed with exit 0. Name checks instead used a Python declaration inventory and global declaration-pattern scans of `KAM/**/*.lean` and `.lake/packages/mathlib/Mathlib`: each of the 22 new handwritten leaf names occurs only at its intended KAM declaration, and the Mathlib scan returned no matches. No new root declaration or `_root_` escape is introduced.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Diff KAM.Certificate.Expr.DiffNode KAM.Certificate.Expr.DiffBuild KAM.Certificate.Expr.DiffCalculus3
```

Exit 0. Exact output:

```text
replaying KAM.Certificate.Expr.DiffCalculus3
replaying KAM.Certificate.Expr.DiffBuild
replaying KAM.Certificate.Expr.DiffNode
replaying KAM.Certificate.Expr.Diff
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expressly permitted generated-root staleness. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1303 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen-anchor guard, and all 144 frozen declaration ABI hashes pass. This is PASS WITH NOTES under the audit brief; the generated root remains untouched.

Static scans: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option` in any changed file. Each file has copyright, `module`, public imports, module documentation, and `@[expose] public noncomputable section`.

| File | Physical lines | Maximum characters per line |
|---|---:|---:|
| `Expr/Diff.lean` | 445 | 100 |
| `Expr/DiffBuild.lean` | 343 | 100 |
| `Expr/DiffCalculus3.lean` | 236 | 99 |
| `Expr/DiffNode.lean` | 669 | 100 |

`git diff --check inp...HEAD` and `git diff --check`: exit 0, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty. The transitive KAM import closure has 38 modules, no providers, and no frozen theorem. Its 11 frozen definitions (`complexStrip`, `dotℂ`, `gramMatrix`, `hamiltonianVectorFieldℂ`, `invarianceError`, `IsPrimaryOnStrip`, `IsRealOnReals`, `normalFrame`, `omegaZero`, `torsion`, `torsionAverage`) were inspected and each is manifest-state `SEALED`.


## Source defects, deviations, and limits

No suspected mathematical source, blueprint, or frozen-definition defect was found in this slice. There is no new numerical constant dependence or norm substitution. The new calculus module moves second-order rules so the third-order rules can reuse them; `JetSmoothOn.neg` becomes the explicitly authorized `JetSmoothOn.jetNeg`. Editing B1 node/finalizer files is necessary to extend their invariant and does not alter a signed B1 statement. The handoff's approximate declaration count is not a signature contract; the table above enumerates the actual audited additions and changes. The 22 newly named handwritten declarations have unique leaf names across KAM and Mathlib. The generated projections `SlpNode.d3` and `SlpNode.Sound.d3` intentionally reuse the structural field name `HamJet.d3`, following the existing d1/d2 pattern; they are fully qualified, receiver-directed fields, not harmful root shadows. The name scan covers handwritten exports rather than autogenerated constructors, recursors, and projections; this distinction is explicit because the focus wording does not specify generated declarations.

This audit establishes the B2 theorem and its implementation hygiene, not the later ball-arithmetic checker, complete certificate soundness, lunar confinement theorem, or practical cubic-table replay performance. No evaluation benchmark was required or claimed. The generated root was not regenerated, as instructed. No production source, frozen file, manifest, README, generated root, or git state was edited by the auditor.

Final workspace check: only this new report and the pre-existing untracked handoff appear in `git status --short`. All auditor-owned scratch probes/logs were removed.
