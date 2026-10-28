# B07 independent package audit 1

**Overall verdict: FAIL for the complete blueprint slice requested in AUDIT FOCUS.** The scalar implementation passes exact-signature and proof checks. The blocking issue is source/graph coverage, not an invalid Lean proof: the exported `free_radius` is strictly narrower than its named blueprint conclusion, and B06 initialization is not consumed to establish A7. No frozen anchor is supplied or sealed by B07; a seal-readiness verdict for a frozen theorem is not applicable.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11b-b07`. Audited HEAD: `9ddace1db6841cd47ad4d266f814bc33944fcc99`. Scope is **only** `KAM/Planetary/WeakKAM/Admissible.lean`; dependency reading is contextual and does not re-audit B02/B04/B06. Read AGENTS, PLAN, DECISIONS, the package brief, B07 handoff, P11B design/node table/proof plan, both P11B design audits, the live signature slice, Track P statement, and the relevant p11a1/3/4 blueprint statements. The user's exact worktree report path overrides the generic brief's main-worktree destination.

## Blocking coverage finding F1

**The named graph exports do not establish the full literal source conclusions.**

* `blueprint-P/parts/p11a3-iteration-selection.tex:215` includes A7: “ε₀=ε+N C₁ s₀²/2, |R₀|≤ε₀” on the initial domain. Line 222 explicitly invokes `initial` to obtain A7. Design `P11B-LEAN-DESIGN.md:71–74,233` assigns adm-choice and the B06 input to B07. In `Admissible.lean:255–280`, `adm_choice` instead returns positivity, scalar `SelectionAdmissibility`, and the ratio bound. The record at lines 68–81 omits A7 by explicit design. The module does not import `Initial`, apply `initial`, or expose a specialization to the selected radii. An independent B06 theorem is available (`Initial.lean:158`), but availability is not consumption. This is an unfulfilled blueprint attachment, not evidence that A7 is false. The algebraic ε₀ identity is definitional for the fixed schedule and proved for the adapted schedule; the analytic remainder assertion is the missing piece.
* `blueprint-P/parts/p11a4-limit-family.tex:39` says A1–A7 hold and that `inductive-lemma`, `parameter-selection`, and `exported-sums` “hold verbatim” with the adapted radius. Line 46, `fr-other`, explains that transfer. Design lines 116–119 map the parent and all three steps to `free_radius`. The actual export at `Admissible.lean:282–289` proves A1–A6, positive/smaller radius, balancing identity and ratio bounds only. It has no perturbation/Hamiltonian argument, A7 conclusion, iteration/selection witness, exported-sum conclusion, or transfer theorem. Its proof ends at line 322 without such a step. Therefore the scalar proof establishes `fr-small` and the scalar part of `fr-list`, but does not establish the full parent or `fr-other` as mapped.

These omissions are **inherited from the signature/design**, not unauthorized changes by the prover. All 15 signature declarations match. The canonical signature itself explicitly separates A7 (line 331) and has the narrower `free_radius` at lines 352–359; the prior design audits accepted this packaging. That acceptance does not discharge the current user's stronger requirement that an export under a node's own name have that node's literal conclusion and that every mapped node be established. The design's claimed coverage and scalar interface need reconciliation. A permissible repair needs an explicit B06 specialization and an appropriate generic adapted-radius consumer/transfer result, or an explicit authorized revision of the node mapping and exported parent contract. This report makes neither change and does not claim the later B10/B12/B13 results already exist.

The smaller omissions in scalar A1/A2/A3 (ϑ/√n≤1, 4λ≤a/8, s₀≤ϑ) follow from the standing n≥1, ϑ≤1 and the returned inequalities; they are not separate blocking findings. A7 and the downstream transfer are analytically different obligations.

## Declaration and node inventory

Names below are in `KAM.Planetary`. PASS means correct at the stated scalar/interface scope; it does not override F1.

| Node / role | Declaration (Admissible.lean line) | Verdict | Reason |
|---|---|---|---|
| sel-data, actual jet size | `selectionM₀` :27 | PASS | Actual diagonal vector-jet supremum, not an arbitrary supplied upper bound. |
| power-law scalar constant | `selectionChat` :30 | PASS | Exact explicit diameter, gap, M and lattice factors. |
| power-law scalar constant | `selectionCDio` :36 | PASS | β exponent −1−1/μ, as Csub contributes M/β. |
| loss-choice | `selectionGamma` :38 | PASS | Half the specified two-branch threshold. |
| adm-params | `selectionT₀` :42 | PASS | Exact logarithmic maximum. |
| adm-params | `selectiont₀` :45 | PASS | Exact two-branch collar. |
| adm-params | `selectionXi` :47 | PASS | All four terms and 2^(τ+1). |
| adm-params | `selectionThetaMax` :50 | PASS | ρ=1 branch; standing ρ∈{1,2} makes else the ρ=2 branch. |
| adm-params | `selectionLambdaMax` :53 | PASS | All three minimum branches, c-prime retained. |
| adm-params | `selectionAdmissible` :58 | PASS | λmax²/(2nC₁). |
| adm-params | `adm_params` :59 | PASS | Fixed radius and original Taylor remainder budget. |
| free-radius | `selectionAdapted` :63 | PASS | sqrt(2ε/(nC₁)), ε₀=2ε. |
| scalar A1–A6 | `SelectionAdmissibility` :68 | PASS WITH NOTES | Exact approved scalar predicate; excludes A7, hence not the full blueprint list. |
| positivity helper | `selectionCN_pos` :84 | PASS | n≥1 suffices. |
| seminorm helper | `selectionDGVector_nonneg` :89 | PASS | Nonnegativity of the real supremum; no boundedness claim is smuggled in. |
| jet-size helper | `selectionM₀_nonneg` :96 | PASS | Supremum of nonnegative jet sizes. |
| geometric helper | `selectionAdm_diam_pos` :102 | PASS | Positive volume rules out a subsingleton; compactness gives boundedness. |
| scalar helper | `selectionChat_pos` :110 | PASS | tau_gap supplies positive lattice gap; β≤M supplies M>0. |
| scalar helper | `selectionCDio_pos` :126 | PASS | Positive β and Chat. |
| scalar helper | `selectionGamma_pos` :132 | PASS | Both threshold branches positive. |
| cutoff helper | `selectionT₀_pos` :140 | PASS | Actual conclusion 1≤T₀, not merely positivity. |
| collar helper | `selectiont₀_pos` :142 | PASS | Both branches positive, C₁≥1. |
| weight helper | `selectionXi_pos` :153 | PASS | Positive collar/strip/cutoff. |
| closeness helper | `selectionThetaMax_pos` :160 | PASS | Nonnegative M₀ and β>0. |
| ratio helper | `selectionLambdaMax_pos` :168 | PASS | Uses B04 `selectionExtensionC_pos`; no assumed cutoff estimate. |
| threshold helper | `selectionAdmissible_pos` :186 | PASS | Positive ratio, n and C₁. |
| conditional scalar helper | `selectionAdmissibility_of_bounds` :195 | PASS | Distinct name, transparent ratio/radius premises; not presented as an unconditional source result. |
| adm-choice | `adm_choice` :255 | FAIL coverage | Exact signature and sound scalar proof; F1: A7 not attached. |
| ac-lam | local `hratio` :269 | PASS | Fixed-radius balancing gives λ₀≤λmax, explicitly returned. |
| ac-list | helper :195 and application :280 | PASS WITH NOTES | Establishes scalar list; full A7 attachment missing as above. |
| free-radius | `free_radius` :282 | FAIL coverage | Exact signature; source parent has additional conclusions, F1. |
| fr-small | locals :295–317 | PASS | Positive sqrt, smaller radius, balancing and λ bound. |
| fr-list | helper application :318 | FAIL full list | A1–A6 proved; A7 analytic bound not attached. |
| fr-other | no corresponding proof/conclusion | FAIL | No adapted-radius downstream transfer result in this module. |

## Definition classification and proof review

There are 12 new definitions and one Prop structure, with no new abbreviations. Every definition body and every record field matches `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean:291–359` after whitespace normalization, as do the two contracted theorem types, including binder order. Fresh copied definition bodies all proved equal by `rfl`; fresh theorem declarations using the canonical types applied the actual proofs successfully.

`selectionM₀` is an actual real supremum over finitely many derivative orders and the closed Euclidean thickening. On `SelectionData`, that thickening is compact and lies inside the open analytic collar of radius 2ϑ; the derivatives are continuous there and the unit Euclidean sphere is compact. Thus the intended supremum is bounded on this carrier. B07 only proves nonnegativity and does not export this regularity/boundedness bridge; later uses of `le_csSup` will still have to supply it. No proof here exploits a junk value from an unbounded supremum. The sphere seminorm itself is defined upstream, not newly invented by B07.

`selectionChat`, `selectionCDio`, and `selectionGamma` expand p11a1's Csub/CDio/gamma-star with m=n. Comparing `WeakMeasure/Basic.lean:85` and `WeakMeasure/PowerLaw.lean:26–32` gives the same constants (commuting scalar factors). The β exponent is correct, and the explicit gap is positive by `tau_gap`. This is a formula check; B07 does not itself prove a measure theorem or claim to consume `power_law` analytically.

The remaining scalar/schedule definitions are the literal formulas on their whole declared carriers. Real sqrt at ε≤0 and total division/powers are ordinary Lean total operations; the adapted theorem requires ε>0, while the fixed theorem allows ε=0. No theorem relies on the adapted zero radius. Every denominator relevant to the proofs is shown positive from standing inputs. `SelectionAdmissibility` is an output predicate with ten scalar fields. Its use in the conditional helper is a conclusion, never a bundled premise hiding the desired theorem.

The shared proof takes the three branches of λmax. It rewrites Q₀=(ε₀/s₀)/D with D>0, applies the minimum for quadratic and weighted bounds, and uses the third branch for closeness. Radius control comes from the first branch and C₁>0. `adm_choice` balances the two terms in ε₀/s₀; `free_radius` proves the sqrt square/product identities, radius comparison and exact ratio before invoking the same helper. No extra source premise, wider constant dependence, heartbeat override or assumed hard analytic step appears. B02 schedule constants, B03 varpi positivity and B04 c-prime positivity are used. `smooth_cutoff` itself need not be re-applied for these scalar estimates; its constant is consumed through `selectionExtensionC`. B06's missing attachment is F1.

## Independent checks

All Lean/Lake operations were sequential with `LEAN_NUM_THREADS=1` and niceness 5. No clean, update, cache retrieval, generated-file regeneration, source repair or state-changing git was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b07 KAM.Planetary.WeakKAM.Admissible
[inp-gate] slot 2 acquired 18:05:43 for KAM.Planetary.WeakKAM.Admissible
Build completed successfully (9104 jobs).
exit 0
```

A compile-slot wait preceded acquisition. The output said “Replayed” for the target and dependencies. No scratch/library rebuild was requested. B07's own replayed diagnostics were:

```text
warning: KAM/Planetary/WeakKAM/Admissible.lean:106:2: Try this:
  haveI̵
The goal is a proposition, so `have` is preferred over `haveI`.
warning: KAM/Planetary/WeakKAM/Admissible.lean:255:50: Variable name `he` is not explicitly referenced.
```

Other replayed warnings concern Schedule, CutoffTensor, CutoffScale, Cutoff and FourierCutoffTail/StripBudget. These are nonblocking hygiene notes outside the audited file. The handoff's claim of no warnings in B07 is inaccurate for this snapshot.

### Exact signatures, definition bodies and axioms

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B07Audit.lean
exit 0
```

The probe copied the 12 canonical definition bodies under fresh names and checked each equality by `rfl`. It copied both canonical theorem types with explicit applications to the package proofs, plus `type_of%` checks. The structure was compared field-for-field textually. No sorry or resource setting was introduced by the probe. Exact axiom output:

```text
'KAM.Planetary.selectionCN_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDGVector_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionM₀_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdm_diam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionChat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCDio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionGamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionT₀_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectiont₀_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionXi_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionThetaMax_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLambdaMax_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdmissible_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdmissibility_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.adm_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.free_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Admissible
replaying KAM.Planetary.WeakKAM.Admissible
exit 0
```

One invocation, using exactly the audited module. No provider exists in this package, so provider/frozen type and seal-body tests are not applicable; the canonical helper signature tests above are the relevant replacement.

### Import, naming, formatting and protected-path checks

A recursive source-import scan found 58 KAM modules, **no provider and no frozen theorem imports**. Frozen definition imports include the original frequency/phase/domain/symplectic objects; no DRAFT_SORRY theorem enters. The 16 new theorem short names have no other declaration under KAM; no `_root_` declaration or namespace shadow appears. All new declarations reside under `KAM.Planetary`. All definitions are in an exposed public noncomputable section. The module has copyright, `module`, public imports and docstring. It has 324 lines and maximum Unicode line width 97. The forbidden-token scan of this file returned no matches for sorry/admit/axiom/unsafe/opaque, set_option, EuclideanSpace or `_root_`.

```text
git diff inp...HEAD --check -- KAM/Planetary/WeakKAM/Admissible.lean
exit 0 (only the multiple-merge-base warning)
git diff --check
exit 0
git diff inp...HEAD --quiet -- KAM/Frozen manifest README.md
exit 0
git diff HEAD^ HEAD --quiet -- KAM/Frozen manifest KAM.lean README.md
exit 0
```

The broader required `git diff inp...HEAD` warns “multiple merge bases, using b322eb9fc48c5a2443ea35342817ad047322b08b”. At the inspected `inp` ref `e2088d57c609cc20f1033b70a41e064402222f53`, it includes many inherited packages and a **49-line addition to KAM.lean**. Thus the brief's full protected-path command is not literally empty: KAM.lean differs. Frozen files, manifest and README are empty in that triple-dot diff. `git show --stat HEAD` and the parent comparison isolate B07 to the single 324-line Admissible addition, with no protected-path edits. This is an inherited comparison-scope note, not a B07 mutation or permission to regenerate the root.

### Source lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (827 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Only the explicitly permitted stale `KAM.lean` exception fails lint; module, frozen-anchor and ABI checks pass. The root was left untouched.

## Uncertainties, errata and deliverables

No new suspected defect in a pinned Rus01/CP09 source was found. This audit checked the local blueprint's explicit formulas and cited source roles; it did not independently reread those external PDFs. F1 is a local blueprint/design/export coverage mismatch, including the prior design audits' acceptance of a narrower named export. It must remain visible rather than being counted as a proved full node. No mathematical counterexample to the scalar statements was found, and no heartbeat design failure occurred.

Only this report is the deliverable. The pre-existing untracked B07 handoff is preserved. Audit-created probes/logs under this worktree's `.lake/abi-scratch/` are deleted after validation. No production file, frozen file, manifest or generated root is edited. No commit is made.

Snapshot SHA256:

```text
Admissible.lean: 022d704cf6ab398af3b4cfa7c5bc818e7968d65114c17b1fed7b43ed06cdc607
P11BSignatures.lean: 6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596
```

