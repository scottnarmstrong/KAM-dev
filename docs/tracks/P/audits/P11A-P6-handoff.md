# P11A-P6 prover handoff (branch inp-p11ap6, d5326c4; contains inp-p11ap0 (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new; all committed on inp-p11ap6)
- `KAM/Planetary/Preparation/PolarAverage.lean` (330 lines): the six signature declarations, copied verbatim
  (statement text compared mechanically with `.drafts/design/P11ASignatures.lean`: identical), plus small helpers.
- `KAM/Planetary/Preparation/PolarAverage/ParamIntegral.lean` (98): `p11_differentiableOn_paramIntegral`
  (holomorphic dependence of `∫ a in K, f (q, γ a)`; differentiation under the integral, bound from continuity of `fderiv`).
- `.../EvenDescent.lean` (169): `p11_even_descent` (even holomorphic `h(s,p)` on `D(0,R)×Ω` gives `(u,p) ↦ h(√u,p)`
  holomorphic on `D(0,R²)×Ω`; parameter Cauchy integral + partial fractions).
- `.../Torus.lean` (219): `p11PolarW` (torus average in the radial variable), holomorphy in `(J,w)`, evenness in each `w_j`
  (torus shift invariance `p11_torusAverage_shift`).
- `.../Iterate.lean` (194): coordinatewise descent, `p11PolarW_sqrt_differentiableOn`.
- `.../Order.lean` (137): `p11_vanish_of_decay` (decay `C√t^k` gives vanishing derivatives of order `j`, `2j<k`),
  `p11_radial_schwarz_gen` (radial Schwarz on any finite-dim space; P0's `p11_radial_schwarz` is only for `ℂⁿ`).
No existing file edited (KAM.lean, Frozen, manifest, other packages untouched).

## Declarations proved (signature names)
`e5`, `p11PolarAverage` (def), `polar_avg`, `polar_average_linear`, `polar_average_normalization`, `polar_extension_unique`.

## Approach (differs from the design's local Taylor/series plan; same statements)
No multi-index series. `p11PolarAverage G (J,ρ) = p11PolarW G (J, √(ρ/π))`. `p11PolarW` is holomorphic in `(J,w)` (parameter integral
over the real torus, integrand holomorphic in the complexified angle) and even in each `w_j` (shift `θ_j ↦ θ_j+1/2`).
Descent through the principal square root coordinate by coordinate (`p11_even_descent`) shows `p11PolarAverage G` itself is
holomorphic on `D × B(0, π r²)`; so `AG := p11PolarAverage G`, and clause (b) is `rfl` (no `Re ρ>0` needed).
(a): norm of a torus mean of values of `G` on `B(0,r)` (`≤ S ≤ 2^{2n} S`). (c): radial Schwarz bounds the integrand by
`S(‖(x,y)‖/r)^k`; along real rays `‖AG(J,tρ)‖ ≤ C√t^k`, hence order `⌈k/2⌉=(k+1)/2` (`p11_vanish_of_decay`), then P0's
`p11_schwarz_one` on `λ ↦ AG(J,λρ)` on `D(0,(πr²/4)/‖ρ‖)` with sup bound `2^{2n}S` gives the exact stated bound (`ρ=0` separately).
`polar_extension_unique`: identity theorem (`KAM.analyticOnNhd_of_differentiableOn`, `eqOn_of_preconnected_of_eventuallyEq`) on each fibre.
`e5`: reflection `t↦1-t` (odd a) / `t↦1/2-t` (odd b) plus periodicity. Local steps `pa_taylor/pa_mono/pa_series` are therefore not
separate declarations.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-p11ap6 KAM.Planetary.Preparation.PolarAverage` -> `Build completed successfully (9091 jobs)`;
  only unused-variable warnings (`hr1` in `polar_avg`, `hD` in `polar_average_linear`/`polar_extension_unique`: kept, signatures verbatim).
- No `sorry`, `axiom`, `maxHeartbeats`, longest file 330 lines.
- `scripts/lint_sources.sh`: all checks PASS (long lines fixed, module check 662 files, frozen guard OK, ABI hashes OK) except the
  line `KAM.lean is out of date; run scripts/gen_root_imports.py` (exit 1): KAM.lean is generated and I must not edit it; the orchestrator
  must regenerate it to import the six new modules.
- `#print axioms` of e5, polar_avg, polar_average_linear, polar_average_normalization, polar_extension_unique: each
  `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / deviations / errata
- Statement-level: none false or under-hypothesised. `hr1 : r ≤ 1` and `hD` are not needed by my proofs (kept; signatures verbatim).
  Clause (b) holds for all `z` (stronger than stated), because the principal-root average is even in each radial variable.
- Design note: blueprint `bpP:p11:e5` (L438) also claims `|∫ sin^a cos^b| ≤ 1`; the signature `e5` only states the vanishing, which is what was proved.
- No heartbeat design signals; no suspected errata in pinned sources.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P6 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) the six signature declarations = signature file exactly (polar_avg, linear, normalization, unique, e5, ...); (2) proofs sound (Taylor coefficients and termwise integration; P0 AnalyticExtension and Schwarz, C3 consumed as designed); no added premises; (3) hygiene (facade + 5 modules; no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Preparation/PolarAverage.lean and PolarAverage/*.lean.
