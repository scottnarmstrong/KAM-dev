# P11A-P2d prover handoff (branch inp-p11ap2d, 57550759; offloaded package run by the main orchestrator)


Hard rules observed: no `set_option maxHeartbeats`/overrides, file 503 lines (<1500), no
sorry/axiom/admit/unsafe/opaque, no `EuclideanSpace`, no frozen/manifest/KAM.lean/README edits, no
provider import, lines <= 100. No signature touched (no signed declaration in scope; helpers only,
all short names checked unused elsewhere in KAM).

## File (new, committed)
`KAM/Planetary/Preparation/HoloChart.lean` (503 lines). Imports HoloLift (P2b), SecularSpectrum.Transport,
Newtonian.Tube, Poincare.Product.
* `p11FastScale` (CLM, `p11FastScaleL`): `T1 z = assemble (J/2pi) (2 pi theta) (slow z.2) (slow z.1)`;
  `p11FastScale_symplectic`, `_isSymplecticOn`, `_injective`, `_shift`
  (`T1 (theta+k, .) = T1 + fastShift k`), `fast_snd_p11FastScale`.
* `p11RealDom J0 r rz` (real working domain), `p11_preimage_workingDom` (equals
  `realInclusion₂ ⁻¹' p11WorkingDom n J0 s r rz` for `0 < s`), `p11RealDom_shift`.
* `P11HoloData.fast_close` (rescaled action in the `rC/pi`, `t2`, `t1` balls),
  `chartInput_eq'`/`chartInput_eq` (`p11ChartInput C z = liftInv d.R (T1 z)`, from P2b),
  `R_row_bound`, `R_mulVec_bound`, `fast_chartInput`.
* Membership (step hc-id): `chartInput_mem` (chart input in `poincareProdDom` and Poincare image in the
  `p11Zeta` circular tube, via `forward_tube`, patch clause `|J/2pi - action| < delta/8` at `J0 in K`,
  `rC <= pi delta/8`, and `(B_rho r_z)^2 <= delta`); `p11_noCollision_of_circularTube` (tube radius
  `p11Zeta` => `NoCollision`, via `axisData_canonical`, `circularTube_pair_bounds`).
* `frameBall`, `liftInv_facts` (`SecularSpectrum.lift` on the frame ball), `chart_eventuallyEq`,
  `chart_analyticAt`, `chart_symplectic` (`IsSymplecticOn.comp` x2: T1, liftInv, poincareProd_symplectic).
* hc-lat: `chart_lattice` (`poincareProd_lattice`, `liftInv_add_fastShift`, `p11FastScale_shift`),
  `chart_injective` (`poincareProd_eq_iff`, `liftInv_injOn`, `p11FastScale_injective`).
* Energy: `chart_energy`: `fixedHamiltonian eps (chart z) = Re (p11WorkingH C eps z)` via
  `fixedHamiltonian_poincareProd` (hProd + eps fFix), `h_re` of the interface.
* **`P11HoloData.chart_spec`**: the last conjunct of `P11SecularSpec` verbatim (the `let O := ...`
  block), for any `C : P11SecularData n` with `C.J0 = d.J0`, `C.rC = d.rC`, `C.rho = d.rho`, `C.h = d.h`,
  `0 < C.sigma`, `(d.Brho * C.rz)^2 <= p11PhysicalDelta D`, `hch : C.chart = poincareProd .. (p11ChartInput C z)`
  and `hF` (below). P2f: `exact d.chart_spec C hJ0 hrC hrho hh hsig hrz hch hF`.

## How P2f uses it / hypotheses to discharge
* `hch`: choose `chart := fun z => poincareProd D.m (D.G*D.m0) (p11ChartInput C z)`.
* `hrz`: `(Brho*rz)^2 <= p11PhysicalDelta D` (implied by `rz <= min{1, delta/(8 Brho)}`; the design's
  `rho_*` is this forward-tube delta). Needs `d.rC <= pi delta/8` which is the interface field.
* `hF` (F is a PARAMETER): `forall z in O, (C.F (realInclusion₂ z)).re = fFix D.G D.m
  (poincareProd D.m (D.G*D.m0) (p11ChartInput C z))`. This is the real-point identification
  "hat f_fix o Phi_rho^{-1} o T1 = f_fix o Psi^(n) o (chart input)" (the part of hc-id tying P2c's
  `p11hsF`/`p11hsFHat` — NOT on my branch, so not importable — to `fFix`). It is NOT proved here; P2f (or a
  small P2c follow-up) must show `p11hsFHat (realInclusion₂ w)` is `-pairPotential` of the Poincare planets
  (separation formula) at real points of `poincareProdDom`. Also real-ness `Im F = 0` is P2c's.

## Checks
* Gate: `inp_lake_build.sh /root/code/KAM-inp-p11ap2d KAM.Planetary.Preparation.HoloChart` ->
  "Build completed successfully (9281 jobs)"; no warnings in my file (earlier build also built HoloLift).
* `#print axioms` of `chart_spec`, `chart_energy`, `chart_injective`, `chartInput_mem`,
  `p11FastScale_shift`: all `[propext, Classical.choice, Quot.sound]`.
* `scripts/lint_sources.sh`: only "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated,
  not edited — orchestrator must regenerate); `check_lean_modules: PASS`, FROZEN-ANCHOR GUARD OK,
  ABI HASHES OK. grep: no `sorry`, `maxHeartbeats`, `EuclideanSpace`; lines <= 100.

## Uncertainties / errata / deviations
No errata, no deviation, no design signal (all proofs at default heartbeats). Note for P2f: the
smallness hypothesis is stated as `(B_rho r_z)^2 <= delta` (not `rz <= rho_*/(8 B_rho)`) because
`poincareGamma <= delta` needs the square; both design bounds imply it when `B_rho r_z <= min(1, delta/8)`.

ORCHESTRATOR RULING (OVERNIGHT 20:40): P11A-P2 is split; P2d owns item 4 (hc-id, hc-lat: the chart, its analyticity/symplecticity, lattice, domain membership). The energy identity fixedHamiltonian = Re(h + eps F) needs P2c's F, which was not on P2d's branch: it moves to P2f and is NOT a finding here.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (holo_chart and steps stepP:p11:hc-id, hc-lat) and its node table; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (the chart clauses of P11SecularSpec). Consumes P2b's P11HoloData. P2b files (HoloFrame, HoloScalar, HoloData, HoloLift) passed their own audit. Audit ONLY KAM/Planetary/Preparation/HoloChart.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
