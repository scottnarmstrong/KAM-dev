# P4-RB prover handoff (branch inp-p4rb, be13c58; contains inp-p4s, inp-p4lt (audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch inp-p4rb. All committed. Build: gate build of `KAM.Planetary.PGMeasure.ResonanceLarge` OK, no warnings.
Lint (`scripts/lint_sources.sh`): all checks pass except "KAM.lean is out of date" (generated; I may not edit it —
orchestrator must run scripts/gen_root_imports.py). `#print axioms` of `large_modes_measure_le`,
`large_mode_structure`, `volume_largeSection_le`: propext, Classical.choice, Quot.sound only.
No maxHeartbeats overrides (one timeout during development in a summability step was fixed by splitting the lemma out;
design signal: unifying `Summable.comp_injective` with a subtype-of-subtype inside a 100-line proof was expensive).

## Files (all < 270 lines; facade is the main module)
- ResonanceLarge.lean (facade + final statements), ResonanceLarge/{LineSlice,Structure,Frequency,Measurable,Sections}.lean

## Helpers (no signed declaration touched; no premises added; all internal, no source-facing restatement).
Blueprint: blueprint-P/parts/p4-pg-measure.tex, proof of Prop two-scale-diophantine-measure.
- `volume_le_of_line_diam` (LineSlice): coordinate form of Tonelli on short sections (`stepP:p4:ext-tonelli`, used in dm-A/dm-B).
- `large_mode_structure`, `largeModes`, `kFast/kSlow/l1` (Structure): `stepP:p4:dm-Bstruct` (i),(ii), consequences.
- `freqCore, fastPart, pullFreq, resonanceSet, pullFreq_eq, freqCore_spec, fast_lip_y/xi, slow_lip_y, beta_lip_y` (Frequency): `stepP:p4:dm-y` (N1,N2 in frequency coordinates y=omega_H0(I), I=g y).
- `sliceDomain, continuousOn_*, measurableSet_sliceDomain, colCoeff` (Measurable): Borelness of R_k (proof header of the proposition: "Borel: F_k continuous by (N1)-(N2) and lip-inverse").
- `largeSection, measurableSet_largeSection, largeSection_line_diam, volume_largeSection_le` (Sections): `stepP:p4:dm-B`.
- `resonanceSet_subset_largeSection` (N3 cover by j), `volume_resonanceSet_large_le`, `summable_latticeWeight_tail`, `large_modes_measure_le` (ResonanceLarge): `stepP:p4:dm-B` summation + `lattice-tail`(b).

## Interface for P4-M (important)
Everything is in the flat frequency coordinates z=(y,xi), y=fastFrequency H0 I:
`resonanceSet d mu Q k alpha` = {z | blockFast z ∈ fastFrequency '' core ∧ blockSlow z ∈ Q ∧ |k·freq(g y, xi)| < alpha}.
`large_modes_measure_le`: volume ⋃_{k ∈ largeModes a b mu LN Lg} resonanceSet d mu Q k (alpha1 / l1 k ^ tau)
 ≤ ofReal(4 b² LB (2Ry)^a (2·3^(n-1)/(τ+1-n)) (4 LN Lg)^(τ+1-n) α1 mu^(τ-n)/λ · (2λ)^b), n=a+b,
 for mu ∈ Ioc 0 mu1, 0<λ≤λ0, Q measurable ⊆ actionShell b (-λ) λ, 0<α1.
P4-M must still: (1) show resonanceBad∩(k1≠0, k ∉ K_A) pulled by Φ(I,ξ)=(ωH0 I, ξ) lies in this union (Φ-image,
Lipschitz-image bound factor Lg^(a+b), vol core and Borelness of the image are P4-RA's/P4-M's); `largeModes` is
exactly the complement of K_A within k1≠0 (mu·LN·Lg·|k|_1 > ‖k1‖/2); note `l1 k = ∑|(k i:ℝ)|` is the sum in `resonanceBad`;
(2) include the constant c1's Lg^n/vol(core) factor. My bound is the 2nd entry of c1's max without those factors.

## Suspected errata / deviations
None found. Deviation: blueprint's `k ∈ 𝒦_A` uses |k_1|_∞ (max norm); implemented as `‖kFast k‖` (Pi norm of real cast) — same.
Blueprint step (ii) uses mu ≤ mu1 with M = 2bLN·LB, matching MeasureData.small exactly.
The set R'_k is defined with y ∈ ω(core) (not "g y ∈ core"); equivalent via hinv.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md rows P4-RB and P4-M and the P4-M proof plan; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean; blueprint-P p4 two-scale-diophantine-measure): the P4-RB outputs (large-mode structure, slow sections, tail) are INTERNAL helpers under the orchestrator ruling (distinct names, blueprint-node citations, shaped for P4-M's two_scale_diophantine_measure): check each helper is mathematically correct, faithful to its cited blueprint step, carries no conclusion-shaped or unjustified hypothesis, does not restate or weaken any signed declaration, and is usable by P4-M; proofs sound; hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/ResonanceLarge*.lean.
