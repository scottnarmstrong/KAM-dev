# GAP-I3T independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gi3t`.
Audited HEAD: `2167804f73481a57309acd1da45f06287e5a648c`.
Comparison branch `inp`: `479ae87d47365eddc9db1abfdc46e44435f96bc9`.

## Verdict

**FAIL — `stepI:p3:tori-ig1` is not established by a literal export under its source hypotheses.**
The new lemmas are sound conditional consequences, and the real-analyticity and real-energy
helpers repair useful omissions in the available API. However, the purported node export
assumes `ToriSide`, an output bundle already containing the hard conclusions. The audit focus
explicitly says: “An export taking a proved dependency's OUTPUT as a premise is a FAIL.”
No frozen anchor is proved or modified by this package; seal readiness is not applicable.
Tracks N and P have no changed modules in this diff.

## Scope and authorities

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/I/audits/GAP-I3T-handoff.md`. The user's exact report destination overrides the
generic brief's main-worktree destination. Only `KAM/Iso/Charts/ToriIG1.lean` is audited as
changed code. Dependencies were inspected to determine the meaning of its premises and conclusions.

Controlling node contracts: `docs/graph/I/DEPGRAPH.md:6331–6371` (`bpI:p3:tori`) and
`:6434–6466` (`stepI:p3:tori-ig1`); blueprint
`blueprint-I/parts/p3-iso-local-charts.tex:371–405`, especially `:394–397`.
Also read the track-I statement, the relevant Part123 design/signature discussion, the
GAP-I3T section of `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md`, the frozen
I-G1 statement, and the relevant frozen definitions and real-restriction implementation.

The entire `git diff inp...HEAD` is one new 88-line file, `ToriIG1.lean`. The handoff was
already untracked at audit start. No production file, frozen file, manifest or generated root
was edited during this audit.

## Declaration ledger

Names below are fully qualified by their indicated namespace.

| Node / clause | Lean declaration | Verdict | Reason |
|---|---|---|---|
| T1 real-analytic restriction | `KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd` (line 33) | PASS as conditional helper | Positive `s₀` makes `rhoInf s₀` positive; holomorphy gives analyticity of the real restriction on all real angles. It assumes `TorusOutput`, so is not a source-level node theorem. |
| T3 real-point energy | `KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq` (line 42) | PASS as conditional helper | Every real angle lies in the positive strip; `T.real` identifies the complex torus with the inclusion of its real restriction; `T.energy` and real part give exactly `E`. |
| `stepI:p3:tori-ig1`, T1/T2/T3/T5 | `KAM.Iso.Charts.ToriSide.ig1_literal` (line 58) | FAIL as node export; sound conditional lemma | Assumes the output bundle `ToriSide` at line 62, rather than constructing the tori from the source hypotheses in source order. Most conjuncts are projections of that bundle. |
| `bpI:p3:tori`, missing real clauses | The three exports together with existing `tori` | PASS as derivable consequences; incomplete literal interface | The missing real clauses and nonzero frequency follow for the existing witnesses, but no new declaration combines them with `tori`'s quantified conclusion. Do not treat `ig1_literal` alone as the graph-node closure. |

All three new declarations are UNSIGNED. No new signed declaration or frozen provider export
requires a signature-equality/seal-body probe. Existing signatures were not changed.

## Refutation and completeness

### F1: output premise replaces the source application

`DEPGRAPH.md:6441–6443` fixes the Part 3 setting, the uniform constants before the perturbation,
then `f, ε, I₀, E`, with `0 ≤ ε < ε₁`, perturbation hypotheses, `I₀ ∈ closure B'`, and the energy
window. Its quantifiers are “as in the proposition.” The proposition's source order is explicit
at `:6338–6340` and blueprint `:372–374`: geometric data and finite patch/ray constants first,
then perturbation and initial data, then torus witnesses for both signs on the fixed rays.

In contrast, `ToriIG1.lean:58–62` universally binds an arbitrary `K, I, ωt` and assumes
`T : ToriSide ... K I ωt`. The definition at `KAM/Iso/Charts/Defs.lean:151–164` extends
`TorusOutput` and assumes a `ray` field containing the Diophantine direction, the frequency
ray identities and the final `C_K * ε` bound. `TorusOutput` at
`KAM/Iso/Confinement/Setting.lean:186–198` already assumes holomorphy, primaryness, reality,
invariance, energy and closeness. These are mathematical conclusions, not typing data.

The proof confirms the mismatch: line 73 destructures `T.ray`; lines 79–82 project
`T.holo`, `T.primary`, `T.real`, `T.invariant`, and `T.energy`. It does not call `apply`,
`toriSide_of_applyOut` or `tori`. This is legitimate proof reuse for a conditional lemma,
but fails the explicit output-premise restriction for a node export.

The conclusion also existentially rechooses `γ, ωs` instead of referring to the patch/ray
fixed before `f, ε, E, I₀`; its T2 and T5 conjuncts use separate existential witnesses.
The proof happens to choose the same witnesses, but that relationship is not exposed in the
statement. The whole T5 clause of the parent (blueprint `:380`) additionally includes the
base energy identity and exact norm identity; those are not stated by this conjunction.
The earlier base-point step can supply the base identity, but cannot cure the output-premise
or quantifier failure of the nominated node declaration.

### Parent over-claim and omitted optional bundle

The first helper supplies T1 real analyticity; the second supplies real-theta T3.
The last lemma correctly proves `ωs ≠ 0` by the Diophantine inequality at `Pi.single 0 1`,
then `ωt ≠ 0` using `st > 1`. Thus the omitted properties are available as consequences
for any witnesses of the existing `tori`, using `hd.hs` for the positive strip.

This supports a narrowly worded parent note: these properties are now derivable through
named lemmas. It does not justify saying a new source-ordered declaration states the full
node, nor that `ToriSide`'s fields themselves now contain the omitted clauses.

The offload plan at lines 311–314 prescribes output-taking helpers and calls a source-ordered
`tori_ig1` bundle optional. That prescription conflicts with the more specific AUDIT FOCUS's
output-premise prohibition and literal-node requirement. The implementation follows that
helper prescription, but the controlling audit condition still fails. Omitting the optional
bundle is therefore **not acceptable for the requested node closure** when no alternative
declaration states the node under the source hypotheses. A repair should construct the
witnesses using the proved dependencies inside a source-ordered theorem, retain the fixed
per-patch rays, and expose the strengthened clauses for both signs. The spelling `tori_ig1`
is not required; the statement and premise discipline are.

## Definitions and proof soundness

There are **no new `def`, `abbrev`, or `structure` declarations**. No junk-value or fallback
construction is introduced. Existing `realRestriction` is `Re ∘ K ∘ realInclusion` on its
whole carrier; with `IsRealOnReals` it agrees with the real-valued torus. The frozen
`realHamiltonian` is the real part of `h + f` evaluated at included real phase coordinates.
The real-energy proof uses their actual bodies and is valid at every real angle.

No mathematical proof defect was found in the three conditional lemmas. The failure is the
claimed graph contract and completeness, not Lean kernel soundness. No new constant choice
is made; the source's required independence is not proved by this conditional interface.

## Independent validation

All Lean/Lake checks were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override, clean, update, cache fetch, or package mutation was used.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi3t KAM.Iso.Charts.ToriIG1
[inp-gate] slot 1 acquired 05:14:42 for KAM.Iso.Charts.ToriIG1
Build completed successfully (3262 jobs).
exit 0
```

The build replayed an existing warning from `KAM/ODE/Exit.lean:36`: automatically included
`[NormedSpace ℝ E]` unused in `KAM.ODE.gen_exit`. No new-file warning was reported.

### Axioms and elaborated type

Temporary probe `.lake/abi-scratch/GAP_I3T_audit.lean` imported the audited module,
ran `#print axioms` for each new theorem and `#check @KAM.Iso.Charts.ToriSide.ig1_literal`.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_I3T_audit.lean
'KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Charts.ToriSide.ig1_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The elaborated type confirmed `0 < s₀ → ToriSide ... → ...`; no hidden discharge of the
output premise occurs. The probe was deleted after validation.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Charts.ToriIG1
replaying KAM.Iso.Charts.ToriIG1
exit 0
```

This package has one lemma module and no provider module.

### Imports and static hygiene

A recursive scan of project import lines found 105 reachable KAM modules, **no provider
modules and no frozen theorem modules**. Consequently there is no DRAFT_SORRY theorem
dependency to justify by manifest state. Definitions under `KAM/Frozen` are allowed.

The new file has 88 lines; maximum line width is 96 characters. It has copyright/authors,
`module`, public imports, module documentation, and `public section`. No new definitions
need exposure attributes. Forbidden-token/override scan was empty, and ambient spaces use
`Fin 2 → ℝ` / `Fin 2 → ℂ`. A repository declaration-name scan found each new theorem short
name only at its own declaration. The `_root_` declarations target the intended existing
`KAM.Iso.Confinement.TorusOutput` namespace; no harmful root shadow was found.

```text
git diff --check inp...HEAD
exit 0; no output
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only reported failure is the stale generated `KAM.lean`, explicitly permitted by the
audit brief. It was not regenerated. Module, frozen-anchor and ABI checks passed; no other
lint finding was printed. Hygiene is PASS WITH NOTES, independently of the node-contract FAIL.

## Errata, deviations, uncertainties

No suspected pinned-source mathematical erratum or frozen-statement defect was found.
The source blueprint's strengthened real clauses are mathematically justified by the new
helpers. The inconsistency is between the offload plan's optional source-level bundle and
the controlling audit's mandatory literal-node/output-premise condition, documented above.
The handoff's phrases “all unsigned, no new premises” and “exports 1-3 already carry the
node's literal conclusion” must not be read as source-level closure: the added declarations
have explicit output premises. The module documentation at `ToriIG1.lean:13–22,53–57`
likewise overstates node closure while accurately describing conditional real-form content.

Audit edits are limited to this report and the temporary scratch probe. No repair was made.
The graph node should remain open pending a source-ordered export satisfying the audit focus.
