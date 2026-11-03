# Independent audit: B5-CHART, round 1

Verdict: **PASS WITH NOTES** for the generic chart package and its main export
`KAM.EffectiveStability.torusChart_isCanonical`. No frozen anchor is present or sealed;
“seal-ready” is inapplicable. All five requirements of the package brief are met.
The design's converse symplecticity assertion is not exported (note N1 below).

## Scope and authority

Audited worktree `/root/code/KAM-inp-b5chart`, HEAD
`4070d877707e1d53794303543af0a0c4141d8094`, with `inp` at
`a362154c24ec6fc4797d55c8a6a08a5eb29d5995`; merge base
`673036c7c1136ca7e6142d13e25793b53c9c410e`.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief,
B5-CHART and B1-common briefs, SPEC.md, B5-DESIGN.md, OD-B13, the handoff AUDIT FOCUS,
and source plan §3.4, lines 426–457. The user's exact report destination overrides the
older audit brief's main-worktree destination.

`git diff inp...HEAD` adds exactly seven Lean modules (753 lines) and the 98-line handoff.
The complete changed Lean bodies were inspected. Frozen/provider type-equality and seal-body
probes are N/A: this is unfrozen Track B real-analysis infrastructure, not an I/N/P provider.
Its relevant frozen definition `KAM.symplecticForm` was inspected against the sign convention
in SPEC.md. No new module imports a provider or frozen theorem anchor.

## Mathematical findings

* **Hypotheses:** TorusBaseData contains only C³ regularity, κ < 1, and the global
  operator norm bound on Du. Nonnegativity of κ is derived at φ = 0, including n = 0.
  TorusChartData adds lattice periodicity, C² regularity of v, and the literal entrywise
  symmetry of Dxᵀ Dv. None of bijectivity, canonicality, inverse regularity, or chart
  symplecticity is assumed. The Lagrangian premise is appropriate for this generic theorem;
  deriving it from CertifiedTorus remains B5-LAG's job under OD-B13.
* **Inverse:** Inverse.lean:47–91 derives a global Lipschitz bound, a lower distance bound,
  injectivity, and surjectivity via the fixed point of φ ↦ y − u φ on the complete whole
  space. Lines 93–112 prove invFun is a two-sided inverse and continuous. Lines 138–175
  give a genuine derivative equivalence and the exact 1/(1−κ) operator norm bound.
  Lines 178–195 identify the global inverse locally with the inverse-function theorem's
  local inverse, proving C³. Shift equivariance uses injectivity and periodicity.
* **Explicit map:** Matrix.lean:30–35 and Map.lean:29–38 have exactly the requested
  Jacobian, inverse transpose, chart and inverse formulas, in the prescribed sup-norm
  carrier. Matrix determinant nonvanishing is proved from the derivative lower bound.
  Map.lean:93–104 uses both matrix inverse identities and both base inverse identities;
  there is no point/domain restriction on either inverse composition.
* **Regularity and shifts:** C³ u gives C² Dx; Cramer's formula and determinant nonvanishing
  give C² inverse-transpose entries. Together with C² v this proves C² Ψ. Jacobian lattice
  invariance follows by differentiating x(φ+k)=x(φ)+k, then yields Ψ equivariance.
* **Essential symplectic calculation:** set A=Dx and B=A^{-T}. Deriv.lean:40–82 proves
  DΨ(a)=(Aa₁, Dv a₁+B a₂+dB[a₁]J). Symplectic.lean:65–87 differentiates BᵀA=1,
  obtaining dB[a]ᵀA+BᵀdA[a]=0. Its lines 45–62 identify dA with D²x;
  lines 99–108 use symmetry of D²x to cancel the J terms. The remaining Dv terms cancel
  only through `torusChart_lagrangian_vec`, proved at lines 29–42 from h.lagrangian.
  Algebra.lean:34–60 uses hsymV explicitly in its final rewrite. Thus the proof has not
  silently dropped the essential Lagrangian premise. All signs match the frozen
  form p·q′−q·p′.
* **Consumer:** TorusChart.lean:35–38 directly fills all five actual fields of
  ChartChain.IsCanonicalChart (ChartChain.lean:30–39) on univ. Global C², symplecticity,
  and left inverse restrict to the B1-T cylinder. Mapping that cylinder into a particular
  Hamiltonian domain V still requires a separate domain estimate; mapsTo_univ does not
  supply it. No certificate-to-confinement closure is claimed here.

## Notes, scope limits and errata

N1. `docs/tracks/B/B5-DESIGN.md:29`, Mathematics item 2 says “symplectic **iff**
`Dxᵀ Dv` is symmetric”; the package split at line 47 also says “symplecticity ⇔ symmetric”.
The package exports only sufficiency, as explicitly required by brief-B5-CHART item 4
and the audit focus. The converse is absent. This is a design-versus-export coverage
note, not a false theorem or a blocker for either named consumer. Do not cite this
package as a proved Lean equivalence.

N2. Requiring only C² v is a strictly stronger theorem than the C³-v request;
C³ u is retained. κ is hypothesis data, not part of the chart's value. These are
benign, explicitly disclosed differences. Some technical helpers use the full data
bundle when fewer fields suffice; these do not replace a source result with extra premises.

No suspected mathematical source defect, frozen-statement defect, heartbeat design
signal, or proof escape was found. No production source was edited by this audit.

## Declaration-by-declaration review

All names below are in `KAM.EffectiveStability`. Technical helpers refine the indicated
B5 brief item; there are no corresponding I/N/P blueprint nodes for this Track B package.
Generated structure projections/recursors have their ordinary Lean meanings.

| Node / module | Public declaration | Verdict | Reason |
|---|---|---|---|
| 1 / Inverse | `torusChartX` | PASS | Definition classified below; literal intended data/object. |
| 1 / Inverse | `torusChartXinv` | PASS | Definition classified below; literal intended data/object. |
| 1 / Inverse | `TorusBaseData` | PASS | Definition classified below; literal intended data/object. |
| 1 / Inverse | `torusChartX_lipschitz_u` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_kappa_nonneg` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_dist_lower` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_injective` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_surjective` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_left` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_right` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_lipschitz` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_continuous` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `TorusPeriodic` | PASS | Definition classified below; literal intended data/object. |
| 1 / Inverse | `torusChartX_shift` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_shift` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_contDiff` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartX_fderiv` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartDx_lower` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartDxEquiv` | PASS | Definition classified below; literal intended data/object. |
| 1 / Inverse | `torusChartDxEquiv_coe` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartDxEquiv_symm_norm` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1 / Inverse | `torusChartXinv_contDiff` | PASS | Global contraction / derivative lower bound; no periodicity needed except shift lemmas. |
| 1–3 / Matrix | `torusChartJac` | PASS | Definition classified below; literal intended data/object. |
| 1–3 / Matrix | `torusChartInvT` | PASS | Definition classified below; literal intended data/object. |
| 1–3 / Matrix | `clm_apply_eq_mulVec` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartJac_mulVec` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartJac_det_ne` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartJac_isUnit` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartInvT_det_isUnit` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartInvT_entry` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartJacT_invT_mulVec` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartInvT_jacT_mulVec` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `contDiff_matrix_det` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `contDiff_matrix_inv_entry` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartJac_contDiff` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 1–3 / Matrix | `torusChartInvT_contDiff` | PASS | Standard-basis matrix identity or smooth determinant/inverse with proved nonzero determinant. |
| 4 / Algebra | `symplecticForm_eq_dot` | PASS | Frozen form convention; conditional algebra helper with explicit matrix identities, discharged downstream. |
| 4 / Algebra | `torusChart_symplectic_algebra` | PASS | Frozen form convention; conditional algebra helper with explicit matrix identities, discharged downstream. |
| 2–3 / Map | `torusChartMap` | PASS | Definition classified below; literal intended data/object. |
| 2–3 / Map | `torusChartInvMap` | PASS | Definition classified below; literal intended data/object. |
| 2–3 / Map | `TorusChartData` | PASS | Definition classified below; literal intended data/object. |
| 2–3 / Map | `torusChartMap_contDiff` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartMap_zero` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartJac_shift` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartInvT_shift` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartMap_shift` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartInvMap_map` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 2–3 / Map | `torusChartMap_invMap` | PASS | Literal chart formula; global inverse compositions / periodic derivative / C² product rule. |
| 4 / Deriv | `torusChartDInvT` | PASS | Definition classified below; literal intended data/object. |
| 4 / Deriv | `torusChartDJac` | PASS | Definition classified below; literal intended data/object. |
| 4 / Deriv | `torusChartMap_differentiable` | PASS | Entrywise directional derivatives; genuine chain and product rules under proved differentiability. |
| 4 / Deriv | `torusChartMap_fderiv_fst` | PASS | Entrywise directional derivatives; genuine chain and product rules under proved differentiability. |
| 4 / Deriv | `torusChartMap_fderiv_snd` | PASS | Entrywise directional derivatives; genuine chain and product rules under proved differentiability. |
| 4 / Symplectic | `torusChart_lagrangian_vec` | PASS | Lagrangian vector identity, differentiated inverse identity and symmetric second derivative. |
| 4 / Symplectic | `torusChartDJac_mulVec` | PASS | Lagrangian vector identity, differentiated inverse identity and symmetric second derivative. |
| 4 / Symplectic | `torusChart_diff_identity` | PASS | Lagrangian vector identity, differentiated inverse identity and symmetric second derivative. |
| 4 / Symplectic | `torusChartMap_symplectic` | PASS | Lagrangian vector identity, differentiated inverse identity and symmetric second derivative. |
| 5 / TorusChart | `torusChart_isCanonical` | PASS | Direct assembly into existing B1 bundle or zero-data smoke test. |
| 5 / TorusChart | `torusChartData_zero` | PASS | Direct assembly into existing B1 bundle or zero-data smoke test. |
| 5 / TorusChart | `torusChartMap_zero_data` | PASS | Direct assembly into existing B1 bundle or zero-data smoke test. |

## Definition classification

| Definition | Classification and whole-carrier behavior |
|---|---|
| torusChartX | Literal φ+uφ, all u and φ. |
| torusChartXinv | Standard total Function.invFun; arbitrary choice outside the bijective regime is explicit. Every inverse/regularity claim proves and uses the contraction regime, so no fallback is exploited. |
| TorusBaseData | Source-premise Prop bundle only. |
| TorusPeriodic | Literal integer lattice periodicity, period 1. |
| torusChartDxEquiv | Genuine continuous linear equivalence on its entire hypothesis-indexed carrier; injectivity proved before construction, finite-dimensional surjectivity supplied by the library. |
| torusChartJac | Standard-basis matrix of the total fderiv of x. Genuine derivative under the standing regularity premise. |
| torusChartInvT | Standard totalized Mathlib matrix inverse of Dxᵀ; inverse claims and smoothness are restricted to the proved nonsingular regime. No singular fallback used. |
| torusChartMap | Literal global formula (xφ,vφ+BφJ), total for all inputs; canonicality requires the stated data. |
| torusChartInvMap | Literal formula (xinv y,Dx(xinv y)ᵀ(p−v(xinv y))); inverse identities proved globally under data. |
| TorusChartData | Source regularity, periodicity and Lagrangian-symmetry bundle; no chart conclusion. |
| torusChartDInvT | Literal entrywise total fderiv in a direction; derivative identities proved only under regularity. |
| torusChartDJac | Literal entrywise total fderiv of Dx; identified with D²x under the standing regularity. |

## Independent checks

All deliberately launched build, probe and kernel commands used a 4 GB/no-swap scope,
nice priority 10 and LEAN_NUM_THREADS=1. Lean/Lake work was serial.
The initial plain lint was stopped before its Lean ABI phase, then restarted under the
same cap (the lint contains an internal lake env lean call).

Build command (compile gate retained):
```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  env LEAN_NUM_THREADS=1 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b5chart KAM.EffectiveStability.TorusChart
```
Output: `[inp-gate] slot 1 acquired 04:16:25 for KAM.EffectiveStability.TorusChart`
and `Build completed successfully (2890 jobs).` Exit 0; no warnings.
The facade imports all six lemma modules. No library/root rebuild was requested.

Axiom probe: generated one `#print axioms KAM.EffectiveStability.<name>` for each of
all 48 public theorems listed above, importing the facade. Command:
```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  .lake/abi-scratch/B5ChartAudit.lean
```
Exit 0. Complete output:
```text
'KAM.EffectiveStability.torusChart_isCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartData_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_zero_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.symplecticForm_eq_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChart_symplectic_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_fderiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_fderiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_lipschitz_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_kappa_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_dist_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartDx_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartDxEquiv_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartDxEquiv_symm_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartXinv_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJac_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvT_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvMap_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_invMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.clm_apply_eq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJac_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJac_det_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJac_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvT_det_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvT_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJacT_invT_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvT_jacT_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiff_matrix_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiff_matrix_inv_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartJac_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInvT_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChart_lagrangian_vec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartDJac_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChart_diff_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay command (one invocation):
```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  env LEAN_NUM_THREADS=1 lake env leanchecker --verbose \
  KAM.EffectiveStability.TorusChart.Inverse KAM.EffectiveStability.TorusChart.Matrix \
  KAM.EffectiveStability.TorusChart.Algebra KAM.EffectiveStability.TorusChart.Map \
  KAM.EffectiveStability.TorusChart.Deriv KAM.EffectiveStability.TorusChart.Symplectic \
  KAM.EffectiveStability.TorusChart
```
Exit 0. Complete output:
```text
replaying KAM.EffectiveStability.TorusChart
replaying KAM.EffectiveStability.TorusChart.Symplectic
replaying KAM.EffectiveStability.TorusChart.Deriv
replaying KAM.EffectiveStability.TorusChart.Map
replaying KAM.EffectiveStability.TorusChart.Algebra
replaying KAM.EffectiveStability.TorusChart.Matrix
replaying KAM.EffectiveStability.TorusChart.Inverse
```

Short-name command:
```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-b5chart KAM.EffectiveStability.TorusChart.Inverse \
  KAM.EffectiveStability.TorusChart.Matrix KAM.EffectiveStability.TorusChart.Algebra \
  KAM.EffectiveStability.TorusChart.Map KAM.EffectiveStability.TorusChart.Deriv \
  KAM.EffectiveStability.TorusChart.Symplectic KAM.EffectiveStability.TorusChart
```
Exit 0: `short-name check OK (no reused public short name)`.

A Python source scan of these seven explicit files counted lines, checked every line's
Unicode length against 100, and searched for
`\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace|set_option)\b`.
Output: `width violations: []`, `forbidden tokens: []`.
Line counts: facade 62; Algebra 62; Deriv 84; Inverse 197; Map 106; Matrix 132;
Symplectic 110. Every file has copyright, `module`, public imports, module documentation,
and `@[expose] public noncomputable section`. No global Phase abbreviation is introduced.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and
`git diff --check` both produced no output, exit 0. No generated or protected source changed.

Full lint command:
```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
```
Exit **1**, solely the audit brief's explicitly permitted stale generated-root exception.
Complete output:
```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4552 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.903s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```
The stale generated part is KAM/Root/EffectiveStability.lean; it was not regenerated.
The lunar-band file-hash-only qualification is the lint's own existing scope, not a
kernel replay claim for those unrelated application theorems.

## Final handoff

Owned report: `/root/code/KAM-inp-b5chart/docs/tracks/B/audits/B5-CHART-audit-1.md`.
All temporary audit probes and captured logs under `.lake/abi-scratch/B5ChartAudit*`
were removed after their outputs were incorporated here. The repository status was
checked to contain only this new report; HEAD and inp remained at the revisions above.
No source fixes, freezes, commits, generated-root edits or certificate application
builds were performed. Uncertainties are limited to the explicitly recorded converse
coverage and the downstream certificate/domain work outside B5-CHART.
