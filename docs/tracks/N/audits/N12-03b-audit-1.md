# N12-03b independent audit 1

Verdict: **PASS WITH NOTES for PicardDerivatives and its two assigned mathematical nodes; FAIL for the submitted branch hygiene gate.** No frozen anchor is proved or seal-ready in this infrastructure package. The blocking branch defect is formatting in PicardFamilies, not a failed mathematical proof in PicardDerivatives.

## Scope and authority

Audited HEAD `6b0a10fa72ac1200e8c692d55ceaa3fdd0cf1849` in `/root/code/KAM-inp-n1203b`. Read AGENTS.md, PLAN, DECISIONS, the package audit brief and the supplied handoff. Followed the user's exact report destination rather than the generic brief's main-worktree destination. Read the N12 design, its two design audits, the delivered signatures at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`, Part 12's local-dependence blueprint and the track statement. The frozen averaging anchors were read for context; this module uses none of their definitions or theorem exports.

`git diff inp...HEAD` (inp at `4dad814dc58f7f254a380a342178c120e2d69be9`) reports multiple merge bases and chooses `ef8fc426c638557035e6101216aad4ef8b8a570e`. Its complete change inventory is PicardDerivatives (241 added lines) and PicardFamilies (332 added lines). The handoff's requested focused comparison `git diff inp-n1203a HEAD -- KAM/Nekhoroshev/Averaging` isolates PicardDerivatives plus three formatting changes to PicardFamilies. No mathematical re-audit of the inherited PicardFamilies package is claimed.

PicardDerivatives SHA-256: `01649fc206ad51c1788503d26337168bd992ade9487fbfb1488b76147273b58d`.

## Declaration ledger

Names below have prefix `KAM.Nekhoroshev`. The authoritative assignment is design row N12-03b at `docs/tracks/N/design/N12-LEAN-DESIGN.md:276`, with its proof plan at lines 314–330 and `blueprint-N/parts/p12-averaging.tex:37`. There are no frozen PicardDerivatives signatures: the delivered signatures specify only the eventual `ext_dep` interface.

| Node / role | Declaration (module line) | Verdict | Reason |
|---|---|---|---|
| ext-dep#parameter-integral | `hasFDerivAt_intervalIntegral_comp` (39) | PASS | Genuine parameter Fréchet derivative of the signed interval integral; exact chain-rule integrand, local uniform derivative bounds and time continuity. |
| linear integrand | `voltInt` (77) | PASS | Composition G ∘ Z, with time projection to the closed interval. |
| linear operator | `voltFun` (83) | PASS | Identity plus signed time integral. |
| integrand continuity | `continuous_voltInt` (87) | PASS | Joint continuity through continuous interval projection and CLM composition. |
| operator continuity | `continuous_voltFun` (95) | PASS | Parametric interval integration with variable endpoint. |
| integrand bound | `norm_voltInt_le` (104) | PASS | Operator norm ≤ Λ times bounded-family norm. |
| integral bound | `norm_integral_voltInt_le` (111) | PASS | Correct absolute time factor ≤ a, including negative time. |
| bounded-family operator | `voltMap` (124) | PASS | Packages voltFun using a proved diameter bound; no compactness assumption on E. |
| evaluation | `voltMap_apply` (135) | PASS | Definitional equality; no substituted object. |
| linear contraction | `contractingWith_voltMap` (139) | PASS | Contraction factor aΛ on the whole complete bounded-continuous-family space. |
| ext-dep#linear | `linear_family` (182) | PASS WITH NOTES | Continuous fixed family, exact Volterra identity and norm ≤ 1/(1−aΛ). Explicit nonnegative Λ is available from the design's norm bound. |

All public declarations are covered, including all three definitions and eight theorems. Generic real normed spaces strengthen the finite-dimensional application. Completeness is required for the fixed-family theorem as expected. These lemmas do not assert that the nonlinear Picard limit has this derivative.

## Statement fidelity and consumer applicability

The parameter lemma assumes derivative data for U and F at every time and nearby initial point; these are exactly the induction inputs in the design, rather than assumptions of the final local-dependence theorem. `B ∈ 𝓝 x` allows an open neighborhood inside the initial ball. The hDc continuity input is supplied by continuous DF and the jointly continuous derivative iterate. No C² or Lipschitz-DF input is imposed. Continuity inputs are weaker than the design's joint continuous bounded derivative data; uniform bounds have the intended operator norms and multiplication order. Time t is arbitrary, covering both signs and zero.

The linear theorem takes G continuous and uniformly bounded on the exact closed time/initial rectangle. For the planned consumer G(t,x)=DF(y(t,x)), the already-constructed continuous y and C¹ field supply this input. `0 ≤ a`, `0 ≤ Λ`, `aΛ < 1` are contraction data, not conclusion-shaped premises. On the design's nonempty ball and time interval, Λ≥0 follows by evaluating its norm bound at (0,x₀); alternatively choose a nonnegative bound initially. Thus the explicit hΛ does not strengthen the source theorem's hypotheses. General negative r produces an empty domain and harmless vacuity.

N12-03c still owes differentiation of each iterate, bounds on derivative iterates, uniform derivative convergence using the stated recurrence, identification Dₓy=Y, and the final `ext_dep` conclusion. Existence of the candidate Y alone does not discharge those nodes. No Lean consumer implementation was supplied in this package, so applicability is a comparison against the design and final signature, not an integration-build claim.

## Proof and definition audit

At PicardDerivatives:55–67 the Mathlib interval theorem `hasFDerivAt_integral_of_dominated_of_fderiv_le''` (ParametricIntegral:233–248) receives all six obligations explicitly:

1. Eventual time measurability near x from hFc on B and restriction from uIcc to uIoc.
2. Integrability at x from hFc and x∈B.
3. Derivative integrand measurability from hDc on the same restricted interval.
4. Almost-everywhere uniform bound ΛM via the operator-composition norm bound and hFb/hUb. Nonnegativity needed for multiplication follows from the actual norm bound.
5. Integrability of the constant majorant.
6. Almost-everywhere parameter derivative from the chain rule at every time and point in B.

No dominated-convergence obligation is assumed as a new standing axiom. The theorem is ordinary HasFDerivAt, not a within-derivative.

The Volterra contraction subtracts the two integrals using established interval integrability, rewrites G∘Z−G∘Z′ as G∘(Z−Z′), and uses |t|≤a. The fixed point exists on bounded continuous CLM families because E is complete. Its norm inequality N≤1+aΛN yields the exact advertised bound using 1−aΛ>0.

Definition classification: `voltInt` is a deliberate time-clamped integrand on its entire carrier; `voltFun` is exactly its identity-plus-integral operator; `voltMap` is the same function with continuity and boundedness certificates, with rfl evaluation. No new abbrev, structure, or instance is introduced. The local existential extension Y clamps time and is zero outside the initial closed ball; every conclusion is guarded by membership in the rectangle, where the proof replaces it by the actual fixed family. The outside-zero branch is never used to establish an unguarded differential or fixed-point claim. The parameter lemma omits completeness, as Mathlib does; the intended finite-dimensional complete application has genuine Bochner integrals.

Imports: PicardDerivatives directly imports PicardFamilies and Mathlib ParametricIntegral. PicardFamilies imports only four Mathlib modules. No project provider or frozen theorem is in this project import chain, so there is no DRAFT_SORRY or provider-quarantine dependency and no imported frozen state to approve. Provider/frozen type equivalence and seal-copy probes are inapplicable: there is no provider export or seal in this package.

## Findings

**H1 — branch hygiene failure; module mathematics unaffected.** Contrary to the handoff's “No other file touched”, comparison with `inp-n1203a` shows PicardFamilies changed. At lines 136 and 318, formerly split lines were joined to 102 and 101 Unicode characters. The file also gained a blank line at EOF (332). These are introduced differences relative to the named baseline, not merely an inherited clean baseline. The brief permits only the stale generated-root lint exception. Re-split these two lines and remove the added final blank line before the branch passes hygiene. No production correction was made by this auditor.

PicardDerivatives itself has 241 lines, no line over 100 characters, no trailing blank line, the required copyright/module/public imports/module docstring/public section, and exposed definition bodies. Its forbidden-token/resource-override scan has no matches. No heartbeat design signal was observed.

No suspected pinned-source or blueprint mathematical defect was found in the two audited obligations. No pinned-PDF re-audit is claimed. The handoff discrepancy and formatting deviations above are reported for correction; no frozen or source repair is proposed.

## Independent validation

Commands were serialized for Lean/Lake execution, with `LEAN_NUM_THREADS=1` and `nice -n 5`. An initial lint attempt was stopped during its static guard stage and restarted with those settings before its ABI Lean stage; it was not used as the final lint receipt.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1203b KAM.Nekhoroshev.Averaging.PicardDerivatives
[inp-gate] slot 1 acquired 08:12:16 for KAM.Nekhoroshev.Averaging.PicardDerivatives
Build completed successfully (2760 jobs).
```

Exit 0. No warning from PicardDerivatives. Replayed dependency warnings in PicardFamilies: unused section variables at lines 60, 82, 202 and 207, and a `haveI` style suggestion at 267. No override was applied.

Axiom probe (one `#print axioms` for each of the eight public theorems, importing only PicardDerivatives):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1203bAudit.lean
'KAM.Nekhoroshev.hasFDerivAt_intervalIntegral_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuous_voltInt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuous_voltFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.norm_voltInt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.norm_integral_voltInt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.voltMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.contractingWith_voltMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.linear_family' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0. No sorryAx or other additional axiom. Temporary probe removed after validation.

Full lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-n1203b/KAM/Nekhoroshev/Averaging/PicardFamilies.lean:136:102
/root/code/KAM-inp-n1203b/KAM/Nekhoroshev/Averaging/PicardFamilies.lean:318:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (468 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit 1. Only the stale root is an authorized exception; H1 accounts for the other failures. Root was not regenerated.

Protected-path command `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff, exit 0 (merge-base warning as recorded above). `git diff inp...HEAD --check`: exit 2, exact finding `KAM/Nekhoroshev/Averaging/PicardFamilies.lean:332: new blank line at EOF.` No other whitespace finding.

Kernel replay (all new lemma declarations are in this single module; there is no provider module):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.PicardDerivatives
replaying KAM.Nekhoroshev.Averaging.PicardDerivatives
```

Exit 0. This is an independent kernel replay, not the prover's receipt.

Closeout: only this report was written as a repository artifact; the pre-existing untracked handoff was preserved. No state-changing git command, production edit, frozen edit, dependency edit or generated-root edit was performed. Report whitespace validation (`git diff --no-index --check /dev/null docs/tracks/N/audits/N12-03b-audit-1.md`) passed with exit 0. The exact two mathematical obligations pass; H1 must be corrected for branch hygiene acceptance. No root theorem closure or frozen seal is asserted.

## Orchestrator addendum (2026-10-28)
The blocking hygiene defect is in the inherited `PicardFamilies.lean` (package N12-03a), not in PicardDerivatives. It was
fixed on inp-n1203a by the whitespace-only commit c893f18 (verified there: whitespace-stripped contents identical,
rebuild, leanchecker exit 0, `git diff --check` clean). inp-n1203a's fixed tip is now merged into this branch (f898724),
so the branch carries no line over 100 characters and no trailing blank line. PicardDerivatives itself passed: the
package verdict is **PASS WITH NOTES** after this merge.
