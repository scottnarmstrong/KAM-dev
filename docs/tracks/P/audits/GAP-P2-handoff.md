# GAP-P2 prover handoff (branch inp-gp2r, 58568c65; off inp; graph-gap programme package run by the main orchestrator)


Branch inp-gp2r. New file (only): `KAM/Planetary/Averaging/OscillatorNodes.lean` (331 lines, lines <= 100 cols).
No landed file edited; KAM.lean not edited (lint prints the expected "KAM.lean is out of date" note).

## Node -> declaration (all in namespace KAM.Planetary, unsigned)
- stepP:p2:oi-ratio -> `p2_oi_ratio` (θ_φ = e b η identity with b=1+m, η=2Φ/δ_ν; e²bη/4 ≤ ebη;
  ∀ h, |ad^h u|/h! ≤ θ_φ^h A in class at two losses; u∘X¹ class + bound (1-θ_φ)⁻¹A) and
  `p2_oi_ratio_integral` (integral remainder, same factor). Helper `OscComposeData.ofDeltaBound`
  builds the landed `OscComposeData` from the source premises (|φ| ≤ δ/ᾱ, δ ≤ ᾱ δ_ν/(16b)); the
  smallness is derived, not assumed as a bundled field.
- stepP:p2:oi-range -> `p2_oi_range` (θ_φ ≤ 2ebδ/(ᾱδ_ν) ≤ e/8 < 0.34; (16/9)θ_φ < 0.61 < 1; Lie
  series = composition on the two-loss domain) and `p2_oi_range_ab` ((a) displacement bounds and
  (b) remainder bound with factor (1-2ebδ/(ᾱ d))⁻¹, ᾱ=2πα, projected from `osc_iter`; all
  osc_iter source hypotheses, nothing derived taken as premise).
- stepP:p2:ar-apply -> `p2_ar_apply` (∃ Ψ g fs: map data, g real/θ-independent, H∘Ψ = H₀+g+f_* on
  V, and f̂₀ = μ⟨P⟩ as `coeff (μ•P) = μ * coeff P`). Premises are the source ones (holo/real h,
  P class/bound 1/real, (R1) as DivisorBound with K = (15/(π s₀)) log(1/ε), (R2)); the landed
  `OscHyp` is built inside (private `ar_hyp`).
- stepP:p2:ar-collect -> `p2_ar_collect` (P̃ = g - μ⟨P⟩ + f_* has class and bound
  400bμ²/(ᾱ d) + e^{-κ/6}μ, and e^{-κ/6}μ = με⁵; κ=2πK s₀ with K as above). Private
  `ar_exp_kappa` re-proves e^{-κ/6}=ε⁵.
- Already closed / out of scope: ob-prod, oi-disp, oa-first, oa-iter, oa-concl (ruling (b));
  oi-transfer (meta step, with Part 11).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gp2r KAM.Planetary.Averaging.OscillatorNodes`: success, no
  warnings in the new file (only pre-existing unused-variable warnings in OscillatorFinite:159,161:
  `hμ`, `hP` of `averaged_remainder`).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK.
- `#print axioms` of all six theorems: [propext, Classical.choice, Quot.sound].

## Notes / uncertainties
- oi-range: "(a),(b) as in N iterative" is exported as the projection of `osc_iter` (separate theorem);
  the series = composition clause is for a generic φ with the oscillator class/bound premises, not
  only the generator `oscGen`.
- ar-apply: the conclusion states H∘Ψ for f = μ•P; real inclusion clause of the map is omitted.
- No suspected errata. No deviations. No heartbeat design signals.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 02:15): graph-gap programme for the landed parts. This package appends UNSIGNED exports stating the LITERAL conclusion of each listed graph node, built from landed declarations. Restricted scope: only stepP:p2:oi-ratio, oi-range, ar-apply, ar-collect (the other GAP-P2 nodes were closed earlier; oi-transfer is out of scope). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/Averaging/OscillatorNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
