# P12-C prover handoff (branch inp-p12c, d775cfa3; contains T21, T20, T16, T19 and GAP-D round 1 (all now passed and landed); offloaded package run by the main orchestrator)


## Files (new)
- KAM/Planetary/PlanarAssembly/ChartData.lean: `total_chart`, `perturbation`, `chart_of_birkhoff`,
  `chart_hamiltonian_of_preserves_fast` (verbatim signatures).
- KAM/Planetary/PlanarAssembly/SlowSmall.lean: `p12c_flow_zero`, `p12c_slow_T`, `p12c_slow_small`
  (helpers: slow part of T depends only on (I, slow); vanishes at slow = 0; uniform smallness by
  compactness).
- KAM/Planetary/PlanarAssembly/DataBox.lean: `p12c_actions_sq`, `p12c_actions_nonneg`, `p12c_box`
  (action box inside actions '' closedBall a0 r).
- KAM/Planetary/PlanarAssembly/Data.lean: `PlanarAssembly.pg_hypotheses` (verbatim signature, one
  joint construction).
`birkhoff_mono_radius`, `kepler_h`, `collar`, `fast_diffeo`, `product_chart`, `forward_tube` already
existed (P12-B/A) and are imported, not redefined. Merged inp-gapd (not needed: clause (a) is
derived from PlanarBirkhoffResult + product chart directly).

## Approach
p := ⟨G,m0,m⟩; ζ = tubeRadius η (axisGap a) (axisData_canonical); `forward_tube` gives δft; continuity
of actions gives η1; `patch p hp a _ η1` gives a0, r, B and PlanarBirkhoffResult (T16/T21; the SAME
T, O', chi, jets). V = ∏(lo,hi) (open box of actions, closure inside actions '' closedBall a0 r ⊆ O'),
W = ∏(lo/2, 2hi) for fast_diffeo, O = p11c_tube O' rS, r0 = min(rS/2, ρ), δ = 1 (the MapsTo clause
holds for all r ≤ r0, so any positive δ is valid). Tube clause: forward_tube + p12c_slow_small
(Γ_i(T z) ≤ δft). BNF: upstream clause at mu0=1, r0 ≤ rS/√2, restricted to V ⊆ interior. B bound and
symmetry from patch.

## Checks
- `lake build` (via gate) of ChartData, SlowSmall, DataBox, Data: success, no sorry, no errors,
  no warnings in my files (one earlier unused simp arg fixed? check log: only upstream warnings).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK;
  it prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file; orchestrator
  to regenerate after landing).
- `#print axioms` of pg_hypotheses, chart_of_birkhoff, chart_hamiltonian_of_preserves_fast:
  [propext, Classical.choice, Quot.sound] each.

## Delivery gates / notes
- Same T and jets as T16 (`P0 I = p11c_secular fhat I 0`, Ω = 2σ, β = p11c_beta p (axes I)), on the
  patch cube; but the joint existential of the signed statement hides P0/Ω/β, so the certificates
  P0mov = C0+δS, P0fix = C0 (`p11cB_secular_mov` etc.) are NOT exposed by pg_hypotheses; they are
  upstream facts about the same P0 (PlanarBirkhoffResult clause `P0 I = p11c_secular fhat I 0`).
  Fixed-Sun clause (P13-A) can reuse the same patch/T via `patch` (fixed branch of hf).
- Upstream gap noted: PlanarBirkhoffResult does not expose a slow-smallness bound for T; I derived it
  (flow(0)=0 + uniform continuity) rather than change upstream.
- Source gaps (analytic eigenframe, real-flow existence, real Lie/Taylor): discharged only through
  the audited upstream exports used (patch/birkhoff_form, p11c_frame explicit frame); no new premise.
- 100-column limit respected; no heartbeat overrides; files < 300 lines.
- Suspected errata: none. Deviations: δ := 1 (design suggested δ tied to r; weaker constraint only).

AUDIT FOCUS: design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-C and its node table (bpP:p12:data, data#pg-data, perturbation, ...) and, IN FULL, its section 'Characterization and delivery gates (P12-C / P13-A)' and the SOURCE_GAP rows; P1213 design audits; signatures /root/code/KAM-inp/.drafts/design/P1213Signatures.lean (PlanarAssembly.pg_hypotheses, total_chart, perturbation, chart_of_birkhoff, chart_hamiltonian_of_preserves_fast). Gate checks (required): the exact owner declarations for the axis cube, C0, deltaS, sigma, beta-hat and the Birkhoff map are the actual T21/T16/T13 objects; the certificates P0mov = C0 + deltaS, P0fix = C0, Omega = 2 sigma, beta = beta-hat hold on that same cube and domain (proved, not assumed; say where); every applicable SOURCE_GAP row (analytic eigenframe, uniform real-flow existence, real-vs-holomorphic Lie/Taylor/symplectic applicability) is discharged from delivered exports; no import of the frozen properlyDegenerateKAM theorem. pg_hypotheses must be ONE joint construction with the same T, O', chi, jets. Audit ONLY KAM/Planetary/PlanarAssembly/{ChartData,SlowSmall,DataBox,Data}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
