# GAP-I3T independent audit 3

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gi3t`.
Audited HEAD: `9348636aefa83699abcfc5ebbd00c76425485d3a`.
Comparison `inp`: `74976f317ab6852d2a7222801accf8ce39ba0615`.

## Verdict

**PASS WITH NOTES for `stepI:p3:tori-ig1`.** The new `tori_ig1_full` states the
both-sign conclusion with fixed patch rays and common positive constants chosen
before `f, ε, I₀, E`. It constructs the tori internally. Audit 2's remaining
one-ray/interface failure is resolved. The original output-taking `ig1_literal`
is only a conditional helper and is not used as independent node closure.

The first two helpers also supply T1 real-analyticity and real-theta T3 for the
actual witnesses of the existing parent `tori`. That specific parent over-claim
can be cleared by citing these consequences. This audit does not independently
re-audit all of the parent's T4/T6/T7 proof or claim that the new theorem bundles
all seven parent clauses.

No frozen anchor is proved or changed by this package: seal-body matching and
seal readiness are not applicable. There are no changed track-N/P Lean modules.
The remaining notes concern generated-root lint and stale documentation.

## Authorities, scope and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff and audit 2.
The user's exact absolute report destination overrides the generic brief's
main-worktree destination. Production audit scope is exclusively
`KAM/Iso/Charts/ToriIG1.lean`; dependencies were inspected to interpret its types.

Controlling contracts: `docs/graph/I/DEPGRAPH.md:6331–6371` (parent),
`:6434–6466` (step), and `blueprint-I/parts/p3-iso-local-charts.tex:367–405`.
Also read the track-I statement, relevant frozen definitions and the I-G1 anchor,
`docs/tracks/I/design/PART123-LEAN-DESIGN.md` (node table, quarantine, D16–D18,
signatures and Part 5 consumers), and GAP-I3T in the offload plan at lines 306–314.

Inspected `git diff inp...HEAD`. It contains the new 281-line `ToriIG1.lean`,
two exposure annotations and wrapping in `Tori.lean`, the handoff and audits 1–2.
The latter `Tori.lean` changes preserve the binders and bodies of `ApplyOut` and
`ApplyLocal`; they add `@[expose]`. They are recorded as an additional package
change outside the handoff's named production scope. Protected paths have no diff.
Initial worktree status was clean. No state-changing git command was used.

There are no SIGNED declarations introduced in the audited module. Its six
public declarations are unsigned. The design's existing signed interfaces are
unchanged; no signature substitution is claimed. The offload plan maps exactly
one new graph node to this module. Its slice is complete via `tori_ig1_full`.

## Declaration ledger

| Node / clause | Lean declaration | Verdict | Reason |
|---|---|---|---|
| T1 real restriction | `KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd`, line 43 | PASS as helper | Positive strip width and holomorphy give real analyticity on all real angles. |
| T3 real energy | `KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq`, line 52 | PASS as helper | Reality identifies the complex torus with its real restriction; strip energy gives the real energy. |
| Conditional T1/T2/T3/T5 | `KAM.Iso.Charts.ToriSide.ig1_literal`, line 68 | PASS as conditional helper | Assumes `ToriSide`; explicitly identified as a helper. Does not count as node closure. |
| Fixed-ray predicate | `KAM.Iso.Charts.Ig1Clauses`, line 101 | PASS | Intended conjunction for the supplied ray and torus on its whole carrier. |
| One-ray application | `KAM.Iso.Charts.tori_ig1_node`, line 119 | PASS as local theorem | Constructs a torus from source data with local constants; is not alone the full node. |
| `stepI:p3:tori-ig1` | `KAM.Iso.Charts.tori_ig1_full`, line 188 | PASS | Both signs, common constants, patch selection, fixed rays and literal T1/T2/T3/T5 content. |
| Parent's omitted real clauses | First two helpers applied to existing `tori` witnesses | PASS as consequences | Preserve the actual parent witnesses and all real-angle quantifiers. |

## Statement fidelity and proof review

`DEPGRAPH.md:6442` requires “SOURCE_QUANTIFIERS: as in the proposition”.
The elaborated type of `tori_ig1_full` has the required shape:

```text
HeadData → B'.Nonempty → IG1Statement → G3Statement →
  ∃ patches γp γm ωsp ωsm ε₁ C_K,
    ChartCover … patches ∧ [fixed patch identities and both IsRay facts] ∧
    0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < C_K ∧
    ∀ f ε, PerturbData … → ε < ε₁ →
      ∀ I₀ ∈ closure B', ∀ E, |E - realPart h I₀| ≤ ε →
        ∃ p ∈ patches, [I₀ near p.c and slope bound] ∧
          (∃ Kp sp, Ig1Clauses … (γp p) (ωsp p) (p.Ψ (E,p.mPlus)) Kp sp) ∧
          (∃ Km sm, Ig1Clauses … (γm p) (ωsm p) (p.Ψ (E,p.mMinus)) Km sm)
```

Patches, both rays and their gamma functions precede the common thresholds and
all later data. The existential family is the D16 existence form used by the
parent. Constants depend only on the geometric data and the standing gates,
not on the perturbation, energy or initial point. The proof chooses per-ray
`C_i` before `uniform` at lines 218–253. Combining the initial existential
binders does not allow dependence on any later universal variable.

`HeadData` and `PerturbData` unpack exactly the source geometric and perturbation
premises (`Confinement/Setting.lean:79–100`). In particular `ε ≥ 0` is retained.
`IG1Statement` and `G3Statement` are the explicit design D18 quarantine convention
(§2.2, lines 133–138; D18 line 261), reproducing the prerequisite gate types.
They are not assumptions of the Part 3 torus output. No `ToriSide`, `ApplyOut`,
`ApplyLocal` or desired torus is an input to either construction theorem.

`Ig1Clauses` explicitly supplies holomorphy, primarity, reality, real analyticity,
invariance on the strip, the fixed ray's Diophantine condition, `1 < st < σ_ω`,
nonzero output frequency, complex and real energy, base energy, the positive
base-frequency scalar and both the exact frequency-distance identity and bound.
Positive gamma is retained by the outer `IsRay` facts. Nonresonance is encoded
by that positive Diophantine lower bound and positive scalar: for any nonzero
integer index the lower bound is positive, and scaling by `st > 1` preserves a
nonzero pairing. No separate nonresonance predicate is necessary here. T4/T6/T7
are other steps of the parent; the node under audit calls for T1/T2/T3/T5.

The one-ray proof first derives the patch energy window and the small margin,
then calls `applyLocal_exists` and its application to produce `Kinf, sinf`
(lines 134–150). It derives the base energy and frequency from `points`, proves
the ray nonzero, and pays the literal bound
`C₃ F₁ ε/(γ² ρ⁴) ≤ C_K ε` at lines 159–174. Positivity of the denominator and
`ε ≥ 0` justify each multiplication/division. The exact norm identity at
lines 180–181 follows by subtracting scalar multiples and `norm_smul`.

The full theorem obtains a finite cover and both rays, constructs local theorem
instances, and applies `uniform` over `Bool × P` (lines 208–253). The two
thresholds use the corresponding ray's constants. The resulting common bounds
are fed separately to both local constructions at lines 272–277. Both tori use
the same selected patch and common `ε₁, C_K`, with the previously fixed signed
rays. There is no selection depending on `f` before the universal quantifier.

The parent's existing witnesses already have `TorusOutput`; applying the first
two helpers with `hd.hs` proves their missing T1/T3 real clauses without changing
the witnesses or constants. The strengthened source-level export is now present
under the name `tori_ig1_full`; the exact optional name `tori_ig1` is immaterial.

## Definition classification

`Ig1Clauses` is the only new definition. It is an exposed Prop-valued conjunction
of the intended T1/T2/T3/T5 properties for all supplied arguments. It has no
fallback, junk value, hidden output hypothesis or altered carrier. It does not
assert positive gamma in isolation: the full theorem provides that through
`IsRay`. Existing `realRestriction` is `Re ∘ K ∘ realInclusion` on its whole
carrier (`KAM/Strip/RealRestriction.lean:80–86`). The real-energy helper unfolds
the frozen `realHamiltonian` and uses precisely this inclusion/restriction
identity. Ambient spaces and norms remain the max norm on `Fin 2 → ℝ/ℂ`.

## Independent validation

Every Lean/Lake operation was sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`, including lint. No clean, update, cache fetch or resource override.

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi3t KAM.Iso.Charts.ToriIG1
[inp-gate] slot 1 acquired 05:37:45 for KAM.Iso.Charts.ToriIG1
Build completed successfully (3264 jobs).
exit 0
```

Only the inherited `KAM/ODE/Exit.lean:36` unused `[NormedSpace ℝ E]` section-variable
warning was replayed. No audited-module warning.

Probe `.lake/abi-scratch/GAP_I3T_audit3.lean` imported the module, printed axioms
of all five public theorems, checked `@tori_ig1_full`, and printed `Ig1Clauses`.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_I3T_audit3.lean
'KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Charts.ToriSide.ig1_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Charts.tori_ig1_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Charts.tori_ig1_full' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Charts.ToriIG1
replaying KAM.Iso.Charts.ToriIG1
exit 0
```

The elaborated interface and predicate match the statement reviewed above.
The scratch probe was deleted after use. No provider belongs to this package;
provider/frozen type and explicit seal-body probes are inapplicable. A recursive
project import scan reached 106 modules, with no provider or frozen theorem
module. Thus no imported DRAFT_SORRY anchor. The contextual I-G1 and G3 anchors
are SEALED in the manifest; the audited module uses the D18 premises.

Static Python/`rg` scans: 281 lines; maximum width 100; no line exceeds 100.
All six new public short names occur at only one declaration each. Copyright,
`module`, public imports, module documentation and `public section` are present;
`Ig1Clauses` is exposed. No forbidden token, override or `EuclideanSpace` occurs.
The two `_root_` declarations intentionally extend `TorusOutput`; no harmful
root shadow was found.

```text
git diff --check inp...HEAD
exit 0; no output
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the stale generated root, expressly permitted by the
brief. It was not regenerated. Hygiene is PASS WITH NOTES. Final
`git diff --check` passed, HEAD remained the audited commit, and the only
remaining worktree change is this report.

## Source defects, deviations and remaining notes

No suspected pinned-source mathematical erratum or frozen-statement defect was
found. No Lean change was made by this audit. The proof follows the stated
blueprint application and uniformization; no additional mathematical deviation.

The handoff remains stale: its line 4 says “~100 lines” and “No landed file touched”,
and lines 18–19 say the optional source-level bundle is not done. Current HEAD
has 281 lines, the full bundle, and the exposure annotations in `Tori.lean`.
The module documentation at lines 25–27 still calls the local `tori_ig1_node`
“the node export”; only `tori_ig1_full` now meets the complete node contract.
These are documentation notes, not residual proof gaps. The graph's current
NOT_STARTED note at lines 6463–6465 is also superseded by this audit's evidence;
no graph/status edits were authorized or made.

The scope is package/node closure under the documented D18 convention, not a
new premise-free provider or revalidation of the complete confinement theorem.
