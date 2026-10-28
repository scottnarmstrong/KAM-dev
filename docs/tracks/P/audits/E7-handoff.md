# E7 prover handoff (branch inp-p14-e7, bd819d08; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Exponential/Perturbation.lean` (~320 lines). No other file touched (KAM.lean not regenerated, per rules).

## Declarations (signature-file ones verbatim)
- `chart_perturbation_analytic` (verbatim): `analyticOnNhd_fMov_poincareProd` at G = m0 = 1, `mul_one` normalisation.
- `perturbation` (verbatim): proves graph nodes pt-input, pt-rho, pt-def, pt-p12, pt-p3, pt-p4, pt-neg and (ii).
- Helpers (all unique names, grepped): `perturbationCore` (K_*: fast angles in [0,2π] ∩ `enlargedCylinder`), `perturbationCore_subset`,
  `isClosed_perturbationCore`, `isCompact_perturbationCore` (pt-input compactness / x-top), `exists_shift_mem_core` (pt-rho geometry: every
  z in the partial complex tube lies within ρ of a lattice translate of K_*), `fastShift_neg_add`, `fastShift_zero_eq`,
  `isPartialPerturbation_neg_of` (pt-neg), `chartSafe_shift_iff`, `fMov_poincareProd_shift` (Ch3 periodicity), `mem_periodicOrbitSet_self`.

## Approach (graph steps)
- pt-input: K_* ⊆ enlargedCylinder ⊆ chartSafe (E3 `real_domain`); `tube` (E6) with W = chartSafe, f = fMov∘poincareProd (analytic by
  `chart_perturbation_analytic`; periodic by `poincareProd_lattice`) gives r, fc.
- pt-rho: ρ = min κ (r/2); C = image of K_* × closedBall 0 ρ under (x,v) ↦ cx x + v is compact and ⊆ tube; fc bounded by B' on C; B0 = max 1 B'.
  For z in F_ρ, `exists_shift_mem_core` gives k with z − cx(fastShift k) ∈ C, so z ∈ tube and |fc z| = |fc(z − cx shift)| ≤ B0 by tube periodicity.
  (F_ρ ⊆ tube and its τ-invariance are not needed separately: P4 uses tube invariance directly.)
- pt-def: P = fc/B0 on the tube, 0 elsewhere. pt-p12/p3/p4: the four clauses of `IsPartialPerturbation`. pt-neg: `isPartialPerturbation_neg_of`.
- (ii): for w in `workingCylinder`, cx w ∈ F_ρ (uses κ>0 for fastBox κ ⊆ fastBox 2κ), hence in tube, `tube` real-trace clause gives fc(cx w) = f w.

## Checks
- Gate build `KAM.Planetary.Exponential.Perturbation`: "Build completed successfully", no warnings in my file; no sorry.
- `#print axioms` (temporary, removed): `chart_perturbation_analytic` and `perturbation`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: line-length offenders fixed; remaining message "KAM.lean is out of date" is expected (KAM.lean is generated, not edited by me). See final status line below.
- grep: no maxHeartbeats, EuclideanSpace, sorry, axiom in the file. No heartbeat design signals.

## Uncertainties / issues for the orchestrator
- **SHORT-NAME CLASH (blocker for the audit launcher):** the signature-mandated name `perturbation` is already a short name in
  `KAM/Apost/PerturbationTorsion.lean:325` (theorem) and `KAM/Planetary/SecularForm/Basic.lean:52` (def). `main_shortname_check.py` exits 7 on it.
  Fully qualified it is `KAM.Planetary.perturbation`, distinct. I did NOT rename (signature must be verbatim); needs an owner/orchestrator ruling
  (rename in the signature/graph, or exempt it).
- All 7 pt-* steps and both declarations assigned to E7 are in this module; nothing belonged to another package.

## Suspected errata / deviations
- None found in the source. Deviation (benign): K_* is taken as `enlargedCylinder`-bounds with κ (closed ±2κ), which contains closure of G' = fastBox B (2κ); the source's Γ ≤ A⁺ is `chartAMD ≤ A`.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row E7 (chart_perturbation_analytic, perturbation) and its node table/proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean lines ~301, ~322. The handoff records a deviation: K_* taken as the enlargedCylinder bounds with kappa (closed +-2 kappa) containing the closure of G' = fastBox B (2 kappa), and the source's Gamma <= A+ read as chartAMD <= A: decide whether this is faithful to the blueprint and the signed statement, not a strengthened premise. Audit ONLY KAM/Planetary/Exponential/Perturbation.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public short name, no root shadow, lines <= 100.
