# E12Q independent package audit 1

**Verdict: PASS WITH NOTES for the authorized parametric E12/Q package.**
**Anchor `planetary.d25.planetaryExponentialSafety.v1`: PASS WITH NOTES, not yet seal-ready.**
The manifest remains `DRAFT_SORRY`; neither the unconditional library `expsafe` nor the unconditional provider `KAM.Provider.Planetary.planetaryExponentialSafety` is declared in this package. E11 and the two assembly declarations remain required. This report does not certify E11, the stopped theorem, or a seal.

Audited 2026-10-29 in `/root/code/KAM-inp-p14-e12`, HEAD `13513b23f9c40f85166a773eac5dfd6492e7b8f1`, comparison ref `inp` = `23a055ed6eaa23e4cc5d0d57c6f3c7c42cabdd32`. Read AGENTS.md, PLAN, DECISIONS, the package brief, handoff/AUDIT FOCUS, P14 design assembly and signatures, P14a expsafe proof, track P statement and frozen anchor/definitions. The explicit prompt controls the report destination over the generic brief's main-worktree destination.

## Scope and fidelity

Reviewed the entire `git diff inp...HEAD`: exactly Safety.lean (231 added lines), the provider (76 added lines, 91 total), and the handoff (134 added lines). Only the two requested Lean modules receive a proof audit. Protected paths have no comparison diff. Initial working tree was clean.

The authoritative signature is `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, SHA256 `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`; stopped is lines 363–369, expsafe 547–572.

**Literal-copy qualification:** hstop at Safety.lean:120–125 and hexpsafe at provider:36–61 have the signed propositions' exact line contents after stripping leading/trailing whitespace, with no token changes. Raw bytes differ because the nested hypotheses have different indentation. Thus a literal byte-for-byte claim is false as text, but there is no proposition/type change. Independent elaboration validates both telescopes. Universally quantified B and its admissibility implication replace the signature's explicit B,hB binders in the required way. There is no additional hypothesis beyond the two explicitly authorized predecessor propositions.

| Node / declaration | Verdict | Reason |
|---|---|---|
| exponent fact: `KAM.Planetary.safety_timeExponent_pos` (Safety:46) | PASS | Positive for every natural n, stronger than n≥2; quadratic denominator strictly positive. |
| exponent fact: `KAM.Planetary.safety_driftExponent_pos` (Safety:53) | PASS | Positive 3a/2 for every n; renamed names avoid E11 collision. |
| es-const: `KAM.Planetary.amdBox_exists_margin` (Safety:60) | PASS | Positive minimum of all inner gaps and AMD gap/n. n≥2 gives nonempty finite index and n>0. |
| elements / es-axis: `KAM.Planetary.keplerAxis_eq_action_div_sq` (Safety:86) | PASS | Positive mass/action force positive square root and positive axis; no reliance on sqrt fallback at negative arguments. |
| es-axis: `KAM.Planetary.keplerAxis_drift_le` (Safety:97) | PASS | Factors squared-action difference; positive mass, both actions in (0,u), and actual action drift are sufficient. No hard estimate assumed. |
| expsafe: `KAM.Planetary.expsafe_of_stopped` (Safety:119) | PASS WITH NOTES | Exact signed conclusion, conditional only on the authorized signed stopped proposition. Harmless constant/margin choices documented below. |
| es-par (inside expsafe, Safety:173–195) | PASS | ν=B0μ>0, ν<ν0≤1; power smallness and exact exponential identity give the signed stopped horizon. |
| es-stop (Safety:196–197) | PASS | Uses δ=ν^b/2, satisfying the stopped lower bound by equality; every z0 is covered. |
| es-amd (Safety:198–211) | PASS | Proves both strict action collars and strict AMD collar; applies the existing proved library amd with the literal target horizon. |
| es-assemble (Safety:212–227) | PASS | Preserves the entire frozen solution/uniqueness/Newton/geometric conjunction and adds uniform axis drift for all |t|≤T. |
| Q: `KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe` (provider:35) | PASS WITH NOTES | Exact frozen conclusion, conditional only on signed expsafe; applies hexpsafe B hB. No unconditional provider claimed. |

Quantifiers are `{n}, hn, hstop/hexpsafe, B, hB`, then `∃ muStar c C`, then every positive μ<muStar, then every inner datum z0. Constants are chosen before intro mu/z0. B0 and ν0 are chosen from hstop B hB, hence may depend on the fixed box and n, never on later μ/z0. The axis sum depends only on box data. Ambient phase spaces and body vectors retain the frozen Fin-function carriers.

## Definitions and proof review

There are **no new def, abbrev, structure, class or instance declarations** in either module. Local m0 and the existential constants denote genuine positive numbers, with no exceptional branch or fallback. Existing frozen AMDBox/Admissible, StoppedActionBound, LowAMDRegion, KeplerAction/Axis/Energy, exponents, moving/Newton solution and uniqueness predicates, actual masses, reconstruction, pair bounds, eccentricity and angular momentum retain their original meanings.

StoppedActionBound controls a curve only on intervals where it already stays in the outer region; it is not whole-horizon confinement. E12 obtains that confinement from the proved library `amd`, not by silently upgrading the stopped premise. It converts |t|≤T to Icc membership, obtains positive actions from the inner/outer regions, then uses |Λ²−Λ0²|=|Λ−Λ0|(Λ+Λ0) and Λ+Λ0≤2u. The factor 2 cancels δ's half, giving the stated μ^b drift.

Compared with blueprint-P/parts/p14a-amd-expsafe.tex:301–304 and design:439:

- C uses `B0^b * ∑ i, upper i / mass i^2`, rather than the maximum. Every summand is positive, every individual summand is bounded by the sum, and n≥2 makes the sum positive. The existential conclusion and constant dependence are unchanged.
- θ omits κ and ε_D, which belong to the preceding stopped construction. Once the exact stopped conclusion is available for all tested parameters, the remaining consumer needs only the action and AMD collars. This is a valid conditional implementation refinement.
- Helper action/axis lemmas work on all points satisfying their stated positive-action premises, a stronger domain than the blueprint's prograde elliptic subdomain.

No suspected mathematical blueprint/source defect was found in this slice. No pinned PDF/source theorem was independently re-audited, and no claim is made that E11 has discharged its source obligations. Handoff's old exponent names are corrected by its orchestrator note and current code.

## Independent checks

Every Lean/Lake invocation ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion or synthesis override was introduced. No source or protected file was changed.

1. Targeted build (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e12 KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
```

```text
[inp-gate] slot 1 acquired 15:37:26 for KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
Build completed successfully (9130 jobs).
```

Replayed inherited warnings only: AMD/Closure:125 unused hmargin, Kepler/Energy:106 unused hm/hκ, ODE/Exit:36 unused section instance. No warning originated in either audited module.

2. Independent signature/seal-body/axiom probe (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E12QAudit1.lean
```

The probe constructed SignedStopped and SignedExpsafe directly from the signed source telescopes, without admitted bodies. Checked `@expsafe_of_stopped` against `∀ {n} hn, SignedStopped n → SignedExpsafe n`, and the Q helper against `∀ {n} hn, SignedExpsafe n → SignedExpsafe n`. Checked a conditional Q assembly against `type_of% @KAM.Planetary.planetaryExponentialSafety`. Copied the complete frozen declaration telescope under fresh names, with signed predecessor premises explicitly bound, and elaborated the exact application bodies `expsafe_of_stopped hn hstop B hB` and `planetaryExponentialSafety_of_expsafe hn hexpsafe B hB`. All pass. This imports the frozen anchor for type comparison only; the probe uses no anchor proof to discharge a predecessor premise.

An initial audit-harness attempt omitted `include hstop` / `include hexpsafe` for section variables, causing two unknown-identifier errors. The corrected probe explicitly includes them and passes. Remaining probe diagnostics are only unused binder warnings on the type-comparison examples.

Exact `#print axioms` output (last list line-wrapped by Lean):

```text
'KAM.Planetary.safety_timeExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.safety_driftExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amdBox_exists_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerAxis_eq_action_div_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerAxis_drift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.expsafe_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

3. Kernel replay (one invocation, exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.PlanetaryExponentialSafety KAM.Planetary.Exponential.Safety
```

```text
replaying KAM.Planetary.Exponential.Safety
replaying KAM.Provider.Planetary.PlanetaryExponentialSafety
```

4. Lint (exit **1**, solely the explicitly permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1333 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was left untouched as required. No other lint failure occurred.

5. Names (exit **0**):

```sh
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-p14-e12 KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
```

```text
short-name check OK (no reused public short name)
```

6. Source and import checks: Safety has 231 lines (maximum width 96); provider has 91 (maximum width 98). Both have copyright, module, public imports, module docstring, and public noncomputable section. Full text scans found none of sorry/admit/axiom/unsafe/opaque/native_decide/EuclideanSpace or set_option. A recursive local-import walk from both modules visited 118 module names and found **zero frozen theorem imports**; the only provider visited was the audited provider itself. Thus no DRAFT_SORRY anchor or other provider occurs in their dependency closure. The only production importer of this provider is its own frozen anchor (line 31), as required.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, with empty output. Final report and scratch cleanup checks recorded below.

## Remaining work and disposition

Accept E12 and Q as audited conditional results. Before sealing, prove/import signed E11 stopped, assemble unconditional expsafe, add the unconditional provider with exactly hn B hB, and validate the resulting integration and seal. Regenerate KAM.lean through the orchestrator. Neither this audit nor the conditional Q helper closes the frozen anchor.

Final integrity: scratch probe and replay log deleted; `git diff --check` exits 0; `git status --short` lists only `?? docs/tracks/P/audits/E12Q-audit-1.md`. The report exists at the exact requested absolute path. No source, generated file, frozen file, manifest or git state was modified by the auditor.
