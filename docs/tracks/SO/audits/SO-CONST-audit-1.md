# SO-CONST independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-soconst`.
Audited HEAD: `3c5a747b7d020efd0073af8bdd2e5cb5d5f60816`.
Comparison ref at initial inspection: `inp` = `ae4969960eb8b30be03978dfe8fa11a178648b00`.
The shared `inp` ref advanced during the audit to `22a2bd62679248ea5072ac1f3f3d3531f288dbb6`;
final `git diff inp...HEAD` still contains exactly the same new 740-line module,
and the protected-path diff is still empty. Audited HEAD did not move.

## Verdict

**FAIL under the handoff's literal signed-API requirement (F1).** The mathematical
constant enclosures, entire requested slice, kernel proofs, pilot evaluations and
elaborated theorem types pass. The sole API failure is the explicit parameter rename
`hγbar` → `_hγbar` in `isoC1_le_isoC1Q`. This breaks named calls permitted by the
signed declaration. Restore that binder spelling before accepting the exact API.
No code was repaired during this read-only audit.

There are no frozen theorem anchors or provider exports in this package, so no
anchor is being sealed. Per signed result: `isoC1Q`, `isoC2Q`,
`isoC2_le_isoC2Q`: **PASS**; `isoC1_le_isoC1Q`: **FAIL (F1)** for API fidelity,
**PASS** for proof and elaborated type. The two additional signed declarations
`cRUpQ` and `cR_le_cRUpQ` also pass. Hygiene is **PASS WITH NOTES** solely for the
explicitly permitted generated-root exception.

## Scope, authority and method

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/SO/audits/SO-CONST-handoff.md`. The user's exact report destination
overrides the generic brief's main-worktree destination. Reviewed all of
`git diff inp...HEAD`: exactly one new source file, 740 added lines,
`KAM/Certificate/Constants.lean`. Audited only that implementation, using its
imports as reference definitions.

Compared all six signed headers with
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean:593-615`; compared the formulas
with `KAM/Apost/Constants.lean`, `KAM/Strip/CohomologicalDefs.lean`,
`KAM/Iso/Apost/Defs.lean:91-126,208-215`, and
`blueprint-I/parts/p2-iso-iteration.tex:67-90,330-344`. Also read the track-I
statement and SO project plan and feasibility report in `/root/code/KAM`.
The source-level blueprint formula comparison introduces no new HL19 transcription
claim: the existing real formulas are the target of this package.

## F1: literal signature mismatch with an observable named-call failure

At `KAM/Certificate/Constants.lean:667` the exported binder is
`(_hγbar : 0 < γbar)`. The signed file at line 605 has
`(hγbar : 0 < γbar)`. All other tokens in the six declaration headers match,
including implicit/explicit binder order, parameter carriers, premises and conclusions.

The unused positivity premise is logically harmless: it remains present, and
α-equivalence allows both `type_of%` checks and positional application of the signed
declaration. It is not harmless for the *literal API* contract. A fresh copy of
the signed declaration, with this body,

```lean
  exact isoC1_le_isoC1Q (hγbar := hγbar)
    hn hτ hρinf hρ hM hσK hσB hσT hμ hν
```

fails with:

```text
.lake/abi-scratch/SOConstNamedArg.lean:8:24: error: Invalid argument name `hγbar` for function `isoC1_le_isoC1Q`
```

Lean's suggestions include `_hγbar`. This is a compatibility defect, not a false
inequality, missing premise or untrusted proof. The `_hP` names belong to unsigned
helpers and introduce no corresponding mismatch. They are harmless unused premises.

## Mathematical review and consumer direction

`cRUpQ` substitutes `3141592/1000000 < π` and `2718/1000 < exp 1` in
positive denominators. Thus `(2π)⁻¹`, `τ/(eπ)` and `8n/π` all increase;
nonnegative products, natural powers and `max 1` preserve the upper direction.
`cR_le_cRUpQ` proves this for every natural n and τ, including zero exponents,
without Params. No upper π/e estimate is mistakenly used in a denominator.

Every rational chain formula has the same dependence and operations as its real
counterpart, replacing only cR and real powers with the specified rational
counterparts. Its comparison theorem proves real ≤ cast rational. Nonnegativity
comes from existing `one_le_*` lemmas and Params, not a conclusion-shaped field.
`Params` has only n ≥ 2, τ ≥ n−1 and positivity of M, σK, σB, σT.
`params_of_rat` obtains exactly these from signed premises, correctly accounting
for natural subtraction. The final comparisons add no assumptions.

`aExp_cast` proves a = 2(τ+n)+2. Therefore 2a = 4(τ+n)+4. `hatcStarQ_ge`
converts 2^(2a) exactly; `delta0_cast` is equality; `delta0_rpow_neg` uses
δ₀ > 0 from ρinf < ρ before converting negative real powers to inverse natural
powers. The ρ powers become 4τ and 2τ. μ,ν > 0 are explicit in the only
comparison requiring these divisors. The unused γbar positivity proof removes
no hypothesis and changes no mathematics.

For e ≥ 0, γ > 0 and ρ > 0, multiplying isoC1 ≤ C₁Q by
e/(γ⁴ρ^(4τ)) preserves order. Consequently the rational checked smallness
inequality implies the real one. The upper isoC2 bound similarly yields a
conservative displacement bound. No reverse comparison is needed or claimed.
No norms, domains or analytic inputs are changed in this scalar arithmetic slice.

## Declaration-by-declaration review

Names below are in `KAM.Certificate`; line numbers refer to the audited source.
Each definition's body was compared with the reference real formula. Each theorem
was inspected for premise fidelity and included in the axiom probe.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| SO-CONST / signature | `cRUpQ` (L44, def) | PASS | Rational upper enclosure, using positive lower endpoints for π and e. |
| SO-CONST / signature | `cR_le_cRUpQ` (L48, theorem) | PASS | All denominators use lower endpoints; reciprocal and power monotonicity give the required upper direction for all natural n, τ. |
| SO-CONST / constants | `mSizeQ` (L77, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `ThetaQ` (L78, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CXQ` (L79, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CTQ` (L80, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `COmegaQ` (L81, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CsymQ` (L82, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CredQ` (L83, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `Cxi0Q` (L84, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CGQ` (L86, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CBQ` (L87, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CDNQ` (L88, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CDXQ` (L89, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CDTQ` (L91, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CYQ` (L96, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CDTbordQ` (L97, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCSQ` (L99, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCxiNQ` (L101, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCgQ` (L102, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCxiQ` (L105, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCDKQ` (L107, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCDeltaQ` (L108, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `CPQ` (L110, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCpartialQ` (L111, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatClinQ` (L113, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCE1Q` (L116, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCE2Q` (L120, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatCEQ` (L123, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatcStepQ` (L124, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatcSumQ` (L126, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `hatcStarQ` (L128, def) | PASS | Rational polynomial/max mirror of the corresponding real constant; same parameter dependence. |
| SO-CONST / constants | `delta0Q` (L136, def) | PASS | Exact rational formula min 1 ((ρ−ρinf)/8); no case fallback. |
| SO-CONST / signature | `isoC1Q` (L140, def) | PASS | Signed header exact; rational formula mirrors isoC1 with exponent 2a = 4(τ+n)+4. |
| SO-CONST / signature | `isoC2Q` (L145, def) | PASS | Signed header exact; rational formula mirrors isoC2 with exponent a = 2(τ+n)+2. |
| SO-CONST / constants | `aExp_cast` (L156, theorem) | PASS | Exact equality a = 2(τ+n)+2; no premises. |
| SO-CONST / constants | `mSizeQ_ge` (L161, theorem) | PASS | Exact cast identity presented as ≤; holds for every rational input, without Params. |
| SO-CONST / constants | `ThetaQ_ge` (L167, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CXQ_ge` (L175, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CTQ_ge` (L183, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `COmegaQ_ge` (L194, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CsymQ_ge` (L205, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CredQ_ge` (L216, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `Cxi0Q_ge` (L225, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CGQ_ge` (L242, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CBQ_ge` (L250, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CDNQ_ge` (L261, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CDXQ_ge` (L272, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CDTQ_ge` (L286, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CYQ_ge` (L303, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CDTbordQ_ge` (L314, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCSQ_ge` (L324, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCxiNQ_ge` (L342, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCgQ_ge` (L357, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCxiQ_ge` (L381, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCDKQ_ge` (L402, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCDeltaQ_ge` (L417, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `CPQ_ge` (L438, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCpartialQ_ge` (L453, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatClinQ_ge` (L477, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCE1Q_ge` (L510, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCE2Q_ge` (L537, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatcStepQ_ge` (L561, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatcSumQ_ge` (L585, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatCEQ_ge` (L609, theorem) | PASS | Upper comparison of the corresponding real constant from Params only; monotone operations and proved nonnegativity. |
| SO-CONST / constants | `hatcStarQ_ge` (L617, theorem) | PASS | Upper comparison from Params and μ,ν > 0; exact 2a conversion; positive divisors preserve direction. |
| SO-CONST / constants | `params_of_rat` (L643, theorem) | PASS | Constructs exactly Params from the signed dimension, exponent and positivity premises; natural subtraction handled using hn. |
| SO-CONST / constants | `delta0_cast` (L652, theorem) | PASS | Exact cast equality with track K delta0; no premises. |
| SO-CONST / constants | `delta0_rpow_neg` (L657, theorem) | PASS | Uses only ρinf < ρ to ensure δ₀ > 0; converts −ma to the inverse natural power m(2(τ+n)+2). |
| SO-CONST / signature | `isoC1_le_isoC1Q` (L665, theorem) | FAIL (F1) | FAIL literal signed API: hγbar renamed _hγbar (F1). Elaborated type, positional application, upper inequality and proof all pass. |
| SO-CONST / signature | `isoC2_le_isoC2Q` (L684, theorem) | PASS | Signed header exact; upper comparison under exactly the signed premises; no added assumptions. |
| SO-CONST / pilot | `isoPilotThreshold` (L712, def) | PASS | Exact rational γ⁴ρ⁴/C₁Q for the stated pilot, hence a sufficient residual threshold. |
| SO-CONST / pilot | `isoC1Q_pilot` (L716, theorem) | PASS | Exact pilot equality proved by decide +kernel; independently re-elaborated. |
| SO-CONST / pilot | `isoC2Q_pilot` (L720, theorem) | PASS | Exact pilot equality proved by decide +kernel; independently re-elaborated. |
| SO-CONST / pilot | `hatcStarQ_pilot` (L724, theorem) | PASS | Exact pilot equality proved by decide +kernel; independently re-elaborated. |
| SO-CONST / pilot | `hatCDeltaQ_pilot` (L728, theorem) | PASS | Exact pilot equality proved by decide +kernel; independently re-elaborated. |
| SO-CONST / pilot | `cRUpQ_pilot` (L731, theorem) | PASS | Exact pilot equality proved by decide +kernel; independently re-elaborated. |
| SO-CONST / pilot | `isoPilotThreshold_enclosure` (L735, theorem) | PASS | Fresh decide +kernel proof passes; factor-two enclosure of 1.3366e−100. |

## Definition classification and completeness

All 35 new definitions are total computable ℚ expressions; there are no new
structures, instances, selectors or abbreviations. `cRUpQ` is an enclosure rather
than an identity; the 30 chain definitions from `mSizeQ` through `hatcStarQ`
are arithmetic mirrors; `delta0Q` is an exact rational minimum;
`isoC1Q` and `isoC2Q` are the signed final mirrors; `isoPilotThreshold` is the
stated exact quotient. All use ordinary rational arithmetic on their entire
carrier. Division/inversion at zero has the standard total-field meaning,
matching the real formula; every comparison using positive denominators proves
the positivity it needs. No fallback or junk branch supports a theorem.

The slice is complete: six signed declarations plus every chain comparison,
exponent/cast/parameter conversion and the six pilot theorems. No signature file
is imported into production. No conclusion-shaped premise or assumed comparison
was found. The import closure contains 19 frozen definition modules, all manifest
state SEALED; it contains no frozen theorem and no provider. No package theorem
uses a draft frozen theorem. The generic frozen-provider type and sealing-body
checks are inapplicable; fresh signed-statement application probes were used instead.

## Independent pilot checks

All six pilot proofs were copied under fresh names and re-elaborated using
`decide +kernel`. No `native_decide`, floating evaluator or numerical oracle was
used. The additional exact-threshold equality was proved by `decide +kernel` too.

| Quantity | Kernel-checked value |
|---|---|
| cRUpQ 2 1 | 1 |
| hatCDeltaQ | 3525311976177664 |
| hatcStarQ | 19888413388084648309626446997880832000 |
| isoC2Q | 1938060754672665339606597632000000000000 |
| isoC1Q | 1502726028501549837873490441646465003847653084860516401152000000000000000000000000000 |
| isoPilotThreshold | 1/7481642515174653798898541941295261706580362741677007109438518067200000000000000000000000000000000000 |

Parameters are n=2, τ=1, ρ=1/200, ρinf=1/400,
M=σK=σB=σT=4, μ=1/1000, ν=1/4, γbar=1/42.
The threshold enclosure is `[ (13366/10^104)/2, 2*(13366/10^104) ]`.
These agree with the feasibility report §3, in particular its exact ĈΔ and ĉ*
at lines 117 and 121 and its approximate 1.3366048938742373e−100 threshold
at line 129. The module's kernel theorem states a factor-two enclosure, not
all the decimal digits of that approximation. No lunar candidate or residual
certificate is validated by this constants-only package.

## Exact checks and outputs

All deliberate build, probe and replay invocations were serialized and used
`LEAN_NUM_THREADS=1` and `nice -n 5`. The first lint invocation was inadvertently
plain `sh scripts/lint_sources.sh`; its internal ABI tool invokes Lean, so this
was an audit-execution deviation from the requested environment/priority wrapper.
It was repeated with the correct wrapper after all other Lean checks finished.
There was no intentional parallel Lean job in this audit; unrelated jobs in other
worktrees were left untouched. No state-changing git command was run.

```text
$ LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soconst KAM.Certificate.Constants
[inp-gate] slot 1 acquired 11:28:34 for KAM.Certificate.Constants
Build completed successfully (3193 jobs).
exit 0

$ LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOConstAudit.lean
exit 0
```

The successful probe contained fresh copies of the three signed theorem statements
with bodies applying the existing exports to every explicit binder in order;
`example : type_of% @audit_<name> := @<name>` for these and the three definitions;
fresh copies of all six kernel pilot proofs; the exact-threshold equality; and
`#print axioms` for each of the 43 public theorems. There were no warnings or errors.
Exact axiom output:

```text
'KAM.Certificate.cR_le_cRUpQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.aExp_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mSizeQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ThetaQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CXQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CTQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.COmegaQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CsymQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CredQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Cxi0Q_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CGQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CBQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CDNQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CDXQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CDTQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CYQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CDTbordQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCSQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCxiNQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCgQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCxiQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCDKQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCDeltaQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CPQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCpartialQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatClinQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCE1Q_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCE2Q_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatcStepQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatcSumQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCEQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatcStarQ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.params_of_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.delta0_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.delta0_rpow_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isoC1_le_isoC1Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isoC2_le_isoC2Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isoC1Q_pilot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isoC2Q_pilot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatcStarQ_pilot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hatCDeltaQ_pilot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cRUpQ_pilot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isoPilotThreshold_enclosure' depends on axioms: [propext, Classical.choice, Quot.sound]

```

```text
$ LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOConstNamedArg.lean
.lake/abi-scratch/SOConstNamedArg.lean:8:24: error: Invalid argument name `hγbar` for function `isoC1_le_isoC1Q`
[argument-name suggestions omitted]
exit 1 (expected negative compatibility test; F1)

$ LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Constants
replaying KAM.Certificate.Constants
exit 0
```

One module was passed in one replay invocation: there is no separate provider or
lemma module in the diff. All 43 axiom lists contain exactly
`[propext, Classical.choice, Quot.sound]`; no sorryAx or new axiom occurs.

```text
$ LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1283 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1 (only the permitted stale generated-root error)
```

Static source checks: 740 lines, maximum line length 99 characters; correct
copyright/module/import/docstring/public-section framing and exposed definitions.
No sorry, admit, axiom, unsafe, opaque, resource override, native_decide or
EuclideanSpace token occurs in the audited file. A scan of declaration short names
across the other `KAM/**/*.lean` files found zero matches for any of the 78 new
names. All declarations are inside `namespace KAM.Certificate`; no root shadow.
The corresponding real definitions keep their own KAM.Apost/KAM.Iso.Apost names.

```text
$ git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
[empty]
$ git diff --check inp...HEAD
[empty; exit 0]
$ git diff --check
[empty; exit 0]
```

## Source defects, deviations and remaining action

No new suspected pinned-source or blueprint defect was found. F1 is an introduced
Lean API deviation, with exact source/signature locations and a refuting client
above. The stale generated root is the expressly authorized lint exception;
it was not regenerated. The initial lint wrapper omission is recorded above.
The imported track-I statement document still labels itself Phase 0 draft; current
manifest/owner rulings and actual audited constants, rather than that status prose,
control the current scope.

Required package action: restore the signed `hγbar` parameter spelling, then rerun
the named-call check and applicable package checks. The unused premise itself may
remain unused. This audit changes only this report; its probe/log files under
`.lake/abi-scratch/` are removed after reporting. The pre-existing untracked prover
handoff is left intact. No theorem closure or downstream certificate acceptance is
claimed beyond the audited scalar constant bounds.
