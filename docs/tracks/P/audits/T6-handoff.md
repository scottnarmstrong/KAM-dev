# T6 prover handoff (branch inp-p11c-t6, 7a890020; offloaded package run by the main orchestrator)


Branch `inp-p11c-t6`. All work committed. No `maxHeartbeats` override anywhere; no file above 300 lines.

## Files (new)
- `KAM/Planetary/PlanarTorsion/Quartic.lean` (facade + final theorem `quartic_explicit`, line-derivative and moving/fixed steps)
- `Quartic/Defs.lean`: `p11c_coeffs` (verbatim from the signature file)
- `Quartic/Jet.lean`: `qeJet_*`: an analytic O(‖z‖^N) function has vanishing diagonal jets below N, and conversely
- `Quartic/Reduce.lean`: `qeV`, `qe_secular_eq` (secular fix average = pref * pairAverage α (qeV I u))
- `Quartic/Algebra.lean`: `qe_alg` (exact conversion remainder ≤ (Σ|co|)·(a0+a1)^3)
- `Quartic/Compose.lean`: `qe_pairJet_qeV`, `qe_quartic_coeffs` (identification of the six c_ν with the displayed algebra, rpow → sqrt)
- `Quartic/Bounds.lean`: `qe_gap_bound`, `qe_remainder_bound` (qeS − qePoly = O(‖u‖^6), analytic)

## Declarations / graph nodes
- `quartic_explicit` (bpP:p11b:quartic-explicit; steps qe-conv, qe-an) and `p11c_coeffs`: signature verbatim (only line breaks differ).
- `qe-c12` (c1,c2 vs. Part-8 diagonal formula): not a separate export; c1, c2 are covered because the whole
  degree-four part is identified through `pair_jet` (T5), which already contains the diagonal case. No unsigned export.
- `p11c_homogeneousPart`, `p11c_quartic`, `p11c_hatFix/Mov`, `p11c_secular`: reused from `Setting` (T1).

## Approach
Fixed secular average at u = (ξ,η) equals pref·pairAverage(α, V(u)), V_i = √((1-Γ_i/2I_i)/I_i)(ξ_i,η_i),
via `poincareProd_block`, `orbit_poincare_bridge`, axis scaling. `pair_jet` (T5) gives jet 5 of pairAverage;
`pairJet∘V` equals a polynomial of degree ≤4 in u up to an explicit O(‖u‖^6) error (`qe_alg`); so
S − qePoly is analytic and O(‖u‖^6) and its 4th diagonal derivative vanishes; the 4th derivative of qePoly is
read along lines. Moving model: `same_jets` (Part 8, ModelTransfer) gives equal 4th jets. Analyticity:
`pair_series.1` composed with a0/a1 and sqrt/rpow analyticity at positive actions.

## Checks
- gate build: `inp_lake_build.sh /root/code/KAM-inp-p11c-t6 KAM.Planetary.PlanarTorsion.Quartic` → "Build completed successfully (9225 jobs)"; no `sorry` warnings in my files.
- `#print axioms KAM.Planetary.quartic_explicit`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS (976 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144);
  prints only "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new modules; I did not edit KAM.lean).
- Lines ≤ 100 columns checked by awk.
- Short-name clash check: none of the 62 new declaration names exists elsewhere in KAM.

## Uncertainties / notes
- `Quartic.lean` imports `SpectralAdapter` (T12) for `p11cSecularData` and `p11c_axes_mem` (needed for `same_jets`). No cycle (T12 does not import T6); if the orchestrator prefers T6 not to depend on T12, those two can be moved to Setting.
- Heartbeat design signal: the first draft of `qe_alg` used large `nlinarith` calls that timed out at default heartbeats; refactored into explicit factorisations + linear steps (no override).
- `Quartic.lean` also gate-built `PairJet`, `SpectralAdapter` deps (olean snapshot lacked them).

## Errata / deviations
None found. Design audit N2 noted (homogeneousPart already in Setting).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T6 (c1..6 and quartic_explicit; T5, U8b exact eccentric conversion, evenness/same_jets) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/PlanarTorsion/Quartic.lean and Quartic/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
