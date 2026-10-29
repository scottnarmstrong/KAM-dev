# SO-CONST independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-soconst`.
Audited HEAD: `4921a7072211ebc150e3c7200976ffe64aeedb85`.
Comparison ref `inp`: `be9aaad9157c8f4e4e65654dd71083c64242cefc`.

## Verdict

**PASS WITH NOTES** for SO-CONST. All six signed declarations pass, including
`isoC1_le_isoC1Q` with the restored `hγbar` binder. Audit-1 F1 is resolved by
commit `4921a707`; its former failing named-argument client now elaborates.
Every audited declaration passes mathematical and API review. The only check
exception is the explicitly permitted stale generated `KAM.lean`.

No frozen theorem anchor or provider belongs to this package, so anchor sealing
is inapplicable. These are acceptance results for the scalar constant package;
no lunar certificate, Hamiltonian residual, invariant torus or confinement result
is established by this audit.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the current local handoff
(including its uncommitted orchestrator-fix addendum), and audit 1. The user's
exact absolute destination overrides the generic brief's main-worktree path.
Implementation scope is only `KAM/Certificate/Constants.lean`.

Reviewed `git diff inp...HEAD`: the new 742-line implementation, the prior
362-line audit and the 48-line committed handoff. Protected-path diff is empty.
Compared the entire module against its real definitions in
`KAM/Apost/Constants.lean:58`, `KAM/Strip/CohomologicalDefs.lean:31`,
`KAM/Iso/Apost/Defs.lean:78` and `:208`, the track-I statement,
`blueprint-I/parts/p2-iso-iteration.tex:67` and `:330`, and the current six signed
headers in `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:788-808`.
Also read the SO plan and feasibility report §3 under `/root/code/KAM`.
No draft signature file was imported into the probes or production.

All six headers match token-for-token after whitespace normalization, including
binder spelling/order, implicitness, carrier, premises and conclusion. Fresh
copies of the three signed theorem headers were proved by applying their exports
to every explicit binder in order. Fresh signed definition headers forward to the
three exported definitions. Each fresh declaration was checked with
`example : type_of% @audit2_<name> := @<name>`.
The repaired client uses this exact body against the signed isoC1 comparison:

```lean
  exact isoC1_le_isoC1Q (hγbar := hγbar)
    hn hτ hρinf hρ hM hσK hσB hσT hμ hν
```

It exits 0. The only implementation change since the previously audited
`3c5a747b` is `_hγbar` → `hγbar` plus a comment and `have _ := hγbar`.
This preserves the mathematical proof and repairs literal named-call compatibility.

## Mathematical review

`cR_le_cRUpQ` uses `3141592/1000000 < pi` and `2718/1000 < exp 1`, with
positive rational denominators. Replacing pi and e by lower bounds increases
`(2*pi)^(-1)`, `tau/(e*pi)` and `8*n/pi`. Natural powers, nonnegative
multiplication and max preserve the upper direction. `Real.rpow_natCast` is
applied to the natural exponent tau, including tau=0. The theorem has no Params
or hidden positivity assumption on n or tau.

All 30 chain mirrors from `mSizeQ` to `hatcStarQ` have the intended formulas
and parameter dependence. Each comparison proves **real ≤ cast rational**.
Monotonicity is justified by existing `one_le_*` facts under Params, rather than
by any assumed enclosure. Params contains exactly n≥2, tau≥n−1 and positivity
of M, sigmaK, sigmaB, sigmaT. `params_of_rat` obtains these from signed premises,
correctly translating natural subtraction using hn. The unsigned `_hP` binders
retain harmless source premises; none assumes a hard conclusion. Only
`hatcStarQ_ge` adds mu,nu>0, exactly where division requires it and exactly as
provided by the final signed theorem.

`aExp_cast` proves a=2(tau+n)+2. Thus 2a=4(tau+n)+4; `hatcStarQ_ge` converts
2^(2a) exactly. `delta0_cast` is equality. `delta0_rpow_neg` derives delta0>0
from rhoinf<rho, then rewrites its negative real powers to inverse natural powers
m(2(tau+n)+2). The final theorems use m=2 and m=1 respectively. Their outer rho
powers become natural exponents 4tau and 2tau. No sign or exponent is lost.
The positivity assumptions in the signed API suffice for every denominator.
The hγbar premise remains present; `have _ := hγbar` merely references it.

For nonnegative residual e and positive gamma,rho, the bound isoC1≤C1Q gives
isoC1*e/(gamma^4*rho^(4tau)) ≤ C1Q*e/(gamma^4*rho^(4tau)). Hence a checked
smallness inequality using C1Q implies the real inequality. Likewise isoC2Q
provides an upper bound for the displacement coefficient. These directions serve
the intended consumer; consumer attachment itself is outside this slice.

## Declaration-by-declaration results

All names below are in `KAM.Certificate`. Line numbers refer to the audited module.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| SO-CONST / signed | `cRUpQ` (def, L44) | PASS | Total rational upper enclosure, using positive lower bounds for pi and exp(1). |
| SO-CONST / signed | `cR_le_cRUpQ` (theorem, L48) | PASS | Real cR ≤ rational enclosure for all natural n, tau; no Params needed. |
| bpI:p2:constants / rational comparison | `mSizeQ` (def, L77) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `ThetaQ` (def, L78) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CXQ` (def, L79) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CTQ` (def, L80) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `COmegaQ` (def, L81) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CsymQ` (def, L82) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CredQ` (def, L83) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `Cxi0Q` (def, L84) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CGQ` (def, L86) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CBQ` (def, L87) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CDNQ` (def, L88) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CDXQ` (def, L89) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CDTQ` (def, L91) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CYQ` (def, L96) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CDTbordQ` (def, L97) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCSQ` (def, L99) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCxiNQ` (def, L101) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCgQ` (def, L102) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCxiQ` (def, L105) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCDKQ` (def, L107) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCDeltaQ` (def, L108) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `CPQ` (def, L110) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCpartialQ` (def, L111) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatClinQ` (def, L113) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCE1Q` (def, L116) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCE2Q` (def, L120) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatCEQ` (def, L123) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatcStepQ` (def, L124) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatcSumQ` (def, L126) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `hatcStarQ` (def, L128) | PASS | Arithmetic mirror of the corresponding real constant; same parameter dependence. |
| bpI:p2:constants / rational comparison | `delta0Q` (def, L136) | PASS | Exact min(1,(rho-rhoinf)/8), total on all rational inputs. |
| SO-CONST / signed | `isoC1Q` (def, L140) | PASS | Signed header exact; rational mirror with exponent 2a = 4(tau+n)+4. |
| SO-CONST / signed | `isoC2Q` (def, L145) | PASS | Signed header exact; rational mirror with exponent a = 2(tau+n)+2. |
| bpI:p2:constants / rational comparison | `aExp_cast` (theorem, L156) | PASS | Exact a = 2(tau+n)+2; no assumptions. |
| bpI:p2:constants / rational comparison | `mSizeQ_ge` (theorem, L161) | PASS | Exact cast identity, stated as upper comparison; arbitrary rational inputs. |
| bpI:p2:constants / rational comparison | `ThetaQ_ge` (theorem, L167) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CXQ_ge` (theorem, L175) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CTQ_ge` (theorem, L183) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `COmegaQ_ge` (theorem, L194) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CsymQ_ge` (theorem, L205) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CredQ_ge` (theorem, L216) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `Cxi0Q_ge` (theorem, L225) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CGQ_ge` (theorem, L242) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CBQ_ge` (theorem, L250) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CDNQ_ge` (theorem, L261) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CDXQ_ge` (theorem, L272) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CDTQ_ge` (theorem, L286) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CYQ_ge` (theorem, L303) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CDTbordQ_ge` (theorem, L314) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCSQ_ge` (theorem, L324) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCxiNQ_ge` (theorem, L342) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCgQ_ge` (theorem, L357) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCxiQ_ge` (theorem, L381) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCDKQ_ge` (theorem, L402) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCDeltaQ_ge` (theorem, L417) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `CPQ_ge` (theorem, L438) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCpartialQ_ge` (theorem, L453) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatClinQ_ge` (theorem, L477) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCE1Q_ge` (theorem, L510) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCE2Q_ge` (theorem, L537) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatcStepQ_ge` (theorem, L561) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatcSumQ_ge` (theorem, L585) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatCEQ_ge` (theorem, L609) | PASS | Real constant ≤ cast rational mirror; Params only, with proved nonnegative factors. |
| bpI:p2:constants / rational comparison | `hatcStarQ_ge` (theorem, L617) | PASS | Upper comparison from Params and explicit mu,nu positivity; exact 2a conversion. |
| bpI:p2:constants / rational comparison | `params_of_rat` (theorem, L643) | PASS | Constructs precisely Params from signed source premises; natural subtraction justified by hn. |
| bpI:p2:constants / rational comparison | `delta0_cast` (theorem, L652) | PASS | Exact rational-to-real minimum identity; no assumptions. |
| bpI:p2:constants / rational comparison | `delta0_rpow_neg` (theorem, L657) | PASS | rhoinf < rho gives positive delta0; exact inverse natural power for any multiplier m. |
| SO-CONST / signed | `isoC1_le_isoC1Q` (theorem, L665) | PASS | Signed header and hγbar spelling exact; full application and repaired named call pass. |
| SO-CONST / signed | `isoC2_le_isoC2Q` (theorem, L686) | PASS | Signed header exact; upper comparison from exactly the signed premises. |
| SO-CONST / pilot | `isoPilotThreshold` (def, L714) | PASS | Exact rational gamma^4 rho^(4tau)/C1Q for the documented pilot. |
| SO-CONST / pilot | `isoC1Q_pilot` (theorem, L718) | PASS | Exact pilot equality independently re-elaborated with decide +kernel. |
| SO-CONST / pilot | `isoC2Q_pilot` (theorem, L722) | PASS | Exact pilot equality independently re-elaborated with decide +kernel. |
| SO-CONST / pilot | `hatcStarQ_pilot` (theorem, L726) | PASS | Exact pilot equality independently re-elaborated with decide +kernel. |
| SO-CONST / pilot | `hatCDeltaQ_pilot` (theorem, L730) | PASS | Exact pilot equality independently re-elaborated with decide +kernel. |
| SO-CONST / pilot | `cRUpQ_pilot` (theorem, L733) | PASS | Exact pilot equality independently re-elaborated with decide +kernel. |
| SO-CONST / pilot | `isoPilotThreshold_enclosure` (theorem, L737) | PASS | Fresh decide +kernel proves factor-two enclosure of 1.3366e-100. |

## Definition classification and completeness

There are 35 new definitions and 43 public theorems, all enumerated above.
There are no structures, instances, abbreviations, selectors or root declarations.
`cRUpQ` is an enclosure; the 30 chain definitions are arithmetic mirrors;
`delta0Q` is an exact rational minimum; `isoC1Q` and `isoC2Q` are the final
signed mirrors; `isoPilotThreshold` is the pilot quotient.

All definitions are total computable rational expressions on their entire carrier.
Rational inversion at zero has ordinary total-field semantics, matching the real
arithmetic convention; comparison proofs establish needed positivity explicitly.
There are no junk/fallback branches. The slice includes all signed constants,
chain bounds, cast/exponent conversions, parameter conversion and six pilot proofs.
No added premise or weakened conclusion was found.

The recursively inspected source import closure has 55 KAM modules, including
19 frozen definition modules, each manifest state SEALED. Their contents were read.
It contains no frozen theorem, DRAFT_SORRY anchor or provider. No package export
uses a quarantined result. Provider/frozen type and seal-body tests are therefore
inapplicable; the signed-statement probes described above serve this package's API.

## Independent pilot evaluation

Fresh copies of all six pilot theorem statements were proved by `decide +kernel`,
without invoking the existing pilot theorems. A further fresh `decide +kernel`
proof established the exact threshold fraction below. No native_decide,
floating-point evaluator or numerical oracle was used in these proofs.

Parameters: n=2, tau=1, rho=1/200, rhoinf=1/400, M=sigmaK=sigmaB=sigmaT=4,
mu=1/1000, nu=1/4, gammabar=1/42.

| Quantity | Independently kernel-checked value |
|---|---|
| cRUpQ | 1 |
| hatCDeltaQ | 3525311976177664 |
| hatcStarQ | 19888413388084648309626446997880832000 |
| isoC2Q | 1938060754672665339606597632000000000000 |
| isoC1Q | 1502726028501549837873490441646465003847653084860516401152000000000000000000000000000 |
| isoPilotThreshold | 1/7481642515174653798898541941295261706580362741677007109438518067200000000000000000000000000000000000 |

The threshold lies between `(13366/10^104)/2` and `2*(13366/10^104)`.
This matches the feasibility report §3's exact hatCDelta and hatcStar values
(lines 117 and 121) and its approximate threshold `1.3366048938742373e-100`
(line 129). The enclosure theorem certifies a factor-two range, not that entire
decimal expansion. Pilot arithmetic alone does not verify a lunar residual.

## Exact hygiene checks

All Lean/Lake/replay invocations were serialized with LEAN_NUM_THREADS=1 and
nice -n 5, including the lint script's internal ABI elaboration. No heartbeat,
recursion-depth or synthesis-heartbeat override was used. No state-changing git
command, generated-root repair or source edit was made.

```text
$ LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soconst KAM.Certificate.Constants
[inp-gate] slot 1 acquired 11:36:44 for KAM.Certificate.Constants
Build completed successfully (3193 jobs).
exit 0

$ LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOConstAudit2.lean
exit 0
```

The probe emitted exactly these axiom lists, with no errors or warnings:

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

All 43 lists are exactly `[propext, Classical.choice, Quot.sound]`.

```text
$ LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Constants
replaying KAM.Certificate.Constants
exit 0
```

The replay used one invocation with the only implementation module in the diff.

```text
$ LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1283 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1 (only the permitted stale generated-root error)
```

Static checks: 742 lines; maximum line length 99 Unicode characters; correct
copyright, module, public imports, module docstring, exposed public section and
namespace. No forbidden proof escape, resource override, native_decide or
EuclideanSpace token. All 78 short names were checked against declarations in
other KAM sources; zero clashes. No harmful root shadowing occurs.

```text
$ git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
[empty; exit 0]
$ git diff --check inp...HEAD
[empty; exit 0]
$ git diff --check
[empty; exit 0]
```

## Source defects, deviations and limitations

No suspected mathematical pinned-source or blueprint defect was found within this
constants-only scope. The real formulas and blueprint agree; this audit makes no
new claim to independently rederive HL19's analytic estimates.

Documentation notes: the original handoff says `740 lines` and `named _hγbar`
(lines 5 and 20); those describe the pre-fix version and are superseded by its
orchestrator addendum and the current 742-line source. Its signature locator
`595-615` (line 46) has drifted: the current controlling declarations are at
788-808. Audit 1 retains its historical FAIL correctly. The track-I statement's
Phase-0 status prose is older than the current owner/manifest state and is not
used as authority to change any declaration. None of these notes changes a
mathematical hypothesis or the package verdict.

The stale generated root is an explicitly permitted lint exception and was left
for the orchestrator. No additional audit-execution deviation occurred.
The only repository file written by this audit is this report. The pre-existing
uncommitted handoff addendum is preserved. All audit-2 scratch probes and logs are
removed after their receipts are copied into this report.
