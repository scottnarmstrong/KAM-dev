Audited HEAD: `0b979a014ed3ade7a7918455e7bb1f1e4b9020b2`; package commit: `c2a92e9d1a00b5eda686e5e9345ac737d17c6329`; SHA256: `KAM/EffectiveStability/Tube/Check/Bracket.lean` = `93991e0e4a3d21e39e8f53666cebc91d2066a23afc6df8f0adf9cf60e997b549`; `KAM/EffectiveStability/Tube/Check/Confine.lean` = `d7ba18137d2cb9b19c7a6434ca53eb78dcc314b099731c1eb57a875270260026`; `KAM/EffectiveStability/Tube/Check/Deriv.lean` = `0e3bafe15e15c1b12e802756630550190f3d7efa22029e751f3dea2902409bd3`; `KAM/EffectiveStability/Tube/Check/Domain.lean` = `1d05366f37c8fa0cd7308404d9ed80c2a724bd2c609053777e65ab4029f54c64`; `KAM/EffectiveStability/Tube/Check/Gamma.lean` = `4793699372fc2601f2b03381433f82aa1f439cee2712108613037d35bcf2f83e`; `KAM/EffectiveStability/Tube/Check/Lip.lean` = `702030dc347262f25fe522d627f757e604f22f6d8cfb252b4b850962a43cb1dc`; `KAM/EffectiveStability/Tube/Check/Solution.lean` = `b877632bc5effb9d4e72539d05b797da7e7ad15985261b7b19a4e00486339ad9`; `KAM/EffectiveStability/Tube/Check/TubeChart.lean` = `af55d1c0fdb90b3db6fac64dcd8a602463802c41090c1c3ea89d250927945dda`.

# N5b-Assembly phase A — audit 1

**Verdict: PASS WITH NOTES.** No blocking mathematical, hypothesis, or implementation finding in the eight
modules of `KAM/EffectiveStability/Tube/Check/`. N1 below concerns documentation only. This accepts the generic
assembly at the package commit, not the uncompleted literal SJSU instance or the T2-CONF headline.

The eight audited package files and the phase-A handoff are byte-identical to `c2a92e9d1`. HEAD advanced during this audit
through other workers' N6 commits; the first line records HEAD when this report was written. No source was edited.
Only this report and the expressly authorized audit scratch/log files were written by this auditor.
An untracked `KAM/EffectiveStability/Tube/Check/Center.lean` appeared during validation; it is not part of
the committed eight-file package and is excluded from this audit.

Read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`,
`.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N5b-Assembly.md`, the phase-A handoff, the route and phase-1
SR-4/SR-7 gates, and the draft-v2 target. Reviewed the whole package against the literal consumer in
`KAM/Application/Confinement/ApproxIntegral.lean`, with targeted inspection of the chart and ODE interfaces.
N6 was inspected only for the shape of its enclosure interface; its certificates are outside this audit.

## Finding

**N1 — low, documentation: `polarInvD` is a local-inverse derivative, not a global derivative of the chosen arg lift.**

Location: `KAM/EffectiveStability/Tube/Check/Deriv.lean:35-39`:

> The derivative of `polarInv` at `w` in the direction `dw`

`polarInv` uses `Complex.arg (p - i q)`. At a nonzero mode with `q = 0`, `p < 0`, this lift is discontinuous;
for example `arg (-1 - i q)` approaches `-π` from `q > 0`, while its value at `q = 0` is `π`.
Consequently it has no derivative there. The formula in `polarInvD` is instead the derivative of a smooth
local inverse of `polar` through the specified lift. The actual theorems correctly prove precisely that:
`fderiv_localInverse_eq` (line 83) and `fderiv_comp_tubeChart_apply` (line 108) use a local inverse and periodic
observables. No proof differentiates the discontinuous arg lift.

Suggested fix: say “the inverse of the polar derivative at `polarInv w`, equivalently the derivative of a
smooth local inverse through that lift, for nonzero modes.” No theorem or hypothesis needs changing.
This is an introduced documentation imprecision, not an erratum in a pinned mathematical source.

## Main statement and hypothesis audit

`tubeChart_confinement` (`TubeChart.lean:96-136`) has exactly the advertised parameterized phase-A conclusion:
for every `z₀` in the sup-norm closed ball, an actual Hamiltonian solution exists on `(-T₁,T₁)` with `T < T₁`,
agrees on the overlap with every solution on every order-connected interval through zero, and satisfies the
chosen planet-action predicate for every `|t| ≤ T`. The state is `(η,ξ)` and the conclusion uses
`oscillatorAction x.2 x.1`. `mem_closedBall_iff_coords` (line 88) matches the draft's ξ-first box clause.
There is no restriction of competing solutions to the polar domain.

Every hypothesis of the main theorem was checked:

| Hypotheses | Static obligation and use |
|---|---|
| `hV` | Exact orthogonality, giving the inverse rotation and canonical transport. |
| `hBper`, `hB`, `hρ`, `hBmin`, `hBmax`, `hβ`, `hsym` | Periodicity, differentiability, value/derivative bounds, positive action margin, and the explicit derivative symmetry of the shift. These are structural identities or inequalities on `B`, not assumptions that a chart transport theorem holds. |
| `hH`, `hHh`, `hhd` | Global C² of the Cartesian Hamiltonian, the exact pullback identity on positive actions, and joint differentiability of the exact reduced Hamiltonian on the box. The stronger global Cartesian premise is usable for the intended polynomial and supports unrestricted uniqueness. |
| `hfper`, `hfd` | Periodicity and differentiability of the literal observables; polynomial/trigonometric observables can supply these globally. |
| `hη`, `hT`, `hTη` | A pointwise reduced-bracket bound on the static box, nonnegative time, and a strict scalar time margin. No orbit, flow, or drift estimate is assumed. |
| `hface`, `hc`, `hερ` | Static bounds on `f_j - ct_j - u_j`, on the exact centre relative to `ct_j`, and their numerical margin. The centre is exactly `f_j(tubeChart z)`; it is not replaced by a rounded literal. |
| `hN`, `hAb`, `ha`, `hab` | Matrix column-sum and per-mode bounds on the Cartesian ball. These are explicit inequalities; `modeBounds_of_mem_closedBall` reduces the latter to centre calculations. |
| `hμ`, `hμρ`, `hFu`, `hFφ`, `hLF` | Centre action bounds, coordinate partial bounds on the static box, and scalar Lipschitz margins. The theorem derives both ball inclusions rather than assuming `Q ⊆ D`. |
| `hG` | An enclosure of the explicit algebraic/trigonometric `chartGamma` on the static action tube, independent of any trajectory. For T2-CONF, `Pγ` is the two numerical eccentricity inequalities supplied by N6. This is a pointwise enclosure input to a transfer theorem, not a hypothesis of confinement or existence. |
| `hz₀` | Initial-state membership in the explicit ball. |

No conclusion-shaped hypothesis was found. The intermediate abstract lemmas explicitly accept compactness,
frontier/face data, or a property on `K`; the main theorem discharges their geometric premises from the above
static data. Its generic `Pγ` parameter deliberately leaves the enclosure predicate to the instance.
Phase B must choose the literal numerical predicate, not hide a dynamical assertion inside it.

No hidden sign/positivity assumption is needed: nonempty `Q` implies `r ≥ 0`; the mode, column-sum and derivative
bounds imply nonnegative majorants; the centre and `hμρ` imply `ρ > 0`; a point of `Q ⊆ K` makes `η_j ≥ 0`,
so `Tη_j < δ/2` gives `δ > 0`. Negative radius is excluded by `hz₀`, and radius zero and `T = 0` are legitimate.
The positive mode margin excludes the polar singularity wherever derivatives are used.

## Proof obligations independently checked

**Compactness and closure inside W — PASS.** `Domain.lean:98-157` first constructs the closed set
`S = {x : 2(bmin_j - ρ) ≤ modeSq_j(x) ∀ j}`, which lies strictly inside `W` by `ρ < bmin_j`.
It proves `K = S ∩ tubeU⁻¹({v : |v_j| ≤ ρ ∀ j})`. Continuity of `tubeU` on `S` follows from periodic-observable
regularity on `W`; it does not assume global continuity of `arg`. Thus `K` is closed in the whole Cartesian
space. Upper action bounds put `Vᵀx` in a finite sup-norm ball, and the inverse rotation puts `K` in its compact
image. `Confine.lean:130-144` then proves `D ⊆ K`, `closure D ⊆ K ⊆ W`, compactness of `closure D`, and the
bracket bound on that closure. In particular, relative closedness in the open `W` alone is never used as compactness.

**Frontier separation — PASS.** `Confine.lean:88-107` uses openness of `D`, then the already closed `K` to put each
frontier point in `W`. Continuity gives `|u_j| ≤ ρ` there. If all observable inequalities were strict, some tube
inequality would have to be an equality. On such a face,
`|F_j-c_j| ≥ ρ-(ε_j+γ_j) > δ`, contradicting the hypothesized strict observable inequalities.
Thus some `|F_j-c_j| ≥ δ`; closure continuity also bounds it above by `δ`. At lines 148-154,
`Tη_j < δ/2` produces exactly the consumer's strict alternative
`F_j < c_j-δ/2-Tη_j` or `c_j+δ/2+Tη_j < F_j`. No frontier separation is assumed by the main theorem.

**Chart derivative and Lipschitz bound on Q — PASS.** Independently differentiating
`q=-√(2I)sin θ`, `p=√(2I)cos θ` gives
`dI=q dq+p dp` and `dθ=(q dp-p dq)/(q²+p²)`, with the displayed sign and no missing factor of two.
`Deriv.lean:83-136` identifies this with the smooth local inverse derivative and transports periodic observables
across arg cuts. `Lip.lean:115-186` uses the correct column sums for `Vᵀ` and the product sup norm, giving
`|dφ_b| ≤ (A_b/a_b+A_2/a_2)‖dw‖`,
`|du_l| ≤ (A_l+β_l(Θ₀+Θ₁))‖dw‖`, and exactly the stated `chartLip`.
The convex closed-ball mean-value argument is at lines 190-201.
`TubeChart.lean:155-180` first applies it to the coordinate observables to prove `|u_j| < ρ` throughout Q;
only then does it use the box partial bounds for `f_j` to prove `|F_j-F_j(z)| ≤ δ/2`. There is no circular
use of the box hypotheses to establish the box inclusion.

**Bracket and action conventions — PASS.** In canonical `(I,θ)` coordinates the field is
`(h_θ,-h_I)`, so `df(X_h)=f_I h_θ-f_θ h_I`. For `f=u₀`, `h=sin φ₀`, the reduced bracket is `cos φ₀`;
for `f=φ₀`, `h=u₀`, the local differential expression is `-1`. These hand computations agree with the
transport and slice formulas. `Bracket.lean:54-61` requires joint differentiability explicitly;
`TubeClose`'s separate slice regularity is not silently upgraded. Its perturbation estimate uses the angle
error `e₁` and two action errors `2e₂` in the correct slots.
`Gamma.lean:56-81` cancels the common phase and the `√2`/oscillator-action factor correctly, including zero
modes for this algebraic identity. Its `chartGamma` body agrees with N6's `Tube/Ecc/Defs.lean:51` after casting
the rational matrix to reals; the generic core does not import the SJSU application.

**Existence and unrestricted uniqueness — PASS.** `Solution.lean:46-66` chooses finite real interior endpoints
from the extended-real maximal interval and takes `T₁ = min(r,-q) > T`. A separately constructed whole-space
maximal solution exists because `H` is globally C². Both the W-solution and every competing Cartesian solution
agree with this whole-space solution by maximality, hence with each other on the required overlap.
It never applies W-maximality to a competitor not known to stay in W. Endpoint and `|t| ≤ T` quantifiers match
the consumer and the draft-v2 target.

## Validation

All eight modules were built once, serially, through the mandated wrapper. Each command is
`.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Check.<Module>`:

| Module | Exact success output |
|---|---|
| `Solution` | `Build completed successfully (2863 jobs).` |
| `Confine` | `Build completed successfully (9076 jobs).` |
| `Domain` | `Build completed successfully (2787 jobs).` |
| `Gamma` | `Build completed successfully (2790 jobs).` |
| `Deriv` | `Build completed successfully (2788 jobs).` |
| `Lip` | `Build completed successfully (2789 jobs).` |
| `TubeChart` | `Build completed successfully (9092 jobs).` |
| `Bracket` | `Build completed successfully (2764 jobs).` |

No warnings originate in the package. Replayed dependency warnings concern an unused section variable in
`KAM/ODE/Exit.lean:36` and a deprecated import in `Tube/Algebra/Bounds.lean:8`.

A single scratch module, `.drafts/g2/scratch/audit/N5b-1-Axioms.lean`, imports `TubeChart` and `Bracket` and
runs `#print axioms` for **all 41 public theorems**, including every main result and geometric/derivative helper:

```text
.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N5b-1-Axioms.lean
exit 0
```

Every theorem reports exactly `[propext, Classical.choice, Quot.sound]`; no unexpected axioms or `sorryAx`.
Full output: `.drafts/g2/scratch/audit/N5b-1-axioms.log`.

Module headers, public imports/sections, exposed definitions and ambient Fin-function types pass inspection.
The forbidden-pattern scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, any `set_option`,
`EuclideanSpace`, `native_decide`, and `sorryAx` has no hits in the eight audited files. Line counts are Bracket 96, Confine 185,
Deriv 140, Domain 161, Gamma 97, Lip 250, Solution 70, TubeChart 205: total 1,204, maximum 250.
`git diff c2a92e9d1 -- KAM/EffectiveStability/Tube/Check/` is empty.

The prescribed `.drafts/g2/lint_noabi.sh` was run once and completed with **exit 1**. Full output is
`.drafts/g2/scratch/audit/N5b-1-lint.log`. `abi_hashes` was skipped as instructed by the worker rules.
The observed output includes:

```text
Lean lines over 100 characters: [30 locations outside the eight audited files]
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (18407 Lean files, 0 comparator configurations)
Ran 29 tests in 4.450s
OK
Ran 8 tests in 0.008s
OK
FileNotFoundError: [Errno 2] No such file or directory: '/mnt/HC_Volume_106379410/kam-sjsu-g2/KAM/EffectiveStability/SJSU/Ham/Hw/D3P0.lean'
```

The width findings concern `SJSU/Ham/{Center,Hw,IntModel,Rate}.lean`,
`SJSU/Model/SJSU18O2Part{0,1,2,3,4,5}.lean`, `Tube/Engine/{Lit,Spread,Step}.lean`, and
`Tube/Poly/{Compose,Dense,Polar,Sparse}.lean`. There is no diagnostic in the audited eight files.
The final `check_frozen_anchors.py` scan did **not** finish: it attempted to read the above external file,
which disappeared during the shared-tree run. Thus this audit does not claim `FROZEN-ANCHOR GUARD OK` or a
green repository lint. The 29 guard unit tests passed; the final repository guard is an outstanding
repository-wide validation limitation. No generated root, frozen file, or another worker's file was repaired.


## Scope, remaining obligations, errata

The handoff's phase-A completeness claim matches the proved generic assembly. The change from unit-complex
observables to `polarInv` plus periodicity is justified by the local-inverse transport. The free tube radius
`ρ`, the centre-error budget `ε+γ`, and the per-action enclosure predicate are faithful generalizations.

Phase B still has to attach the literal V/B/H/f data and prove all numerical bounds, exact pullback equality
`hHh`, and joint reduced-Hamiltonian regularity `hhd`. In particular, a truncated model with `TubeClose` errors
cannot replace the exact `h` in `hHh`; model errors belong in the bracket bound. No claim is made here that
these instance premises have been discharged, or that `sjsu_secular_confinement_proof` has been proved.
No suspected pinned-source erratum or mathematical deviation was found. N1 is the sole documentation finding.

READY g2-audit-n5b-1
