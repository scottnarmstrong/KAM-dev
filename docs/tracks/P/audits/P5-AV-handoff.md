# P5-AV prover handoff (branch inp-p5av, 4fbe4652; off inp-p5th; offloaded package run by the main orchestrator; one session was interrupted by the orchestrator by mistake and a second finished it, including the previously untracked AveragingHamil.lean)


## Files (all KAM/Planetary/PGAssembly/)
Averaging{Defs,Facts,Norm,Dom,Map,Bound,Div,Small,Hyp,Rem,Fourier,Real,Conj,Hamil,Disp}.lean and the
top module Averaging.lean (imports the chain; each file < 300 lines). New this session:
AveragingHamil (avg_hamil, from the interrupted session's untracked file; built and committed),
AveragingDisp (avg_rem_diff, avg_chart via hol_chart, avg_disp: 12/18 displacement bounds from the
P2 estimates 3μ', 9μ'), Averaging (avg, pgAvg). Long lines (>100) wrapped in place in the
Averaging*.lean files (whitespace only).

## Declarations
Signature-file declarations: PGAveraging, averagingDomain, realAverageMap, AveragingSpec,
pgOscNormalize/Unnormalize, pgOscP/H/E/Epsilon/Width/Alpha, pg_osc_hyp, pg_osc_bound,
pg_osc_positive, pg_osc_zero, pg_osc_normalization, pg_osc_domain, avg, pgAvg (verbatim, in
AveragingDefs and the proof modules).

## Approach
avg: `averaged_remainder` applied to pg_osc_hyp/pg_osc_bound gives (Ψ, R); the record is
⟨avgPsi Ψ, avgRem R⟩ = (T∘Ψ∘T⁻¹, 2π·R∘T⁻¹). Clauses: diff/inj/maps/periodic/real by conjugation
lemmas; Hamiltonian identity by avg_hamil (pg_osc_zero + pgRemainder definition); remainder
bounds via 2π·avgB ≤ 2 LP μ r^5 (two_pi_avgB_le) and Fourier mode transport; chart by hol_chart
with avg_sympl (symplectic factor 2π cancels); displacement via avg_disp.

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-p5av KAM.Planetary.PGAssembly.Averaging`:
  "Build completed successfully (9240 jobs)", no sorry in the files; no maxHeartbeats.
- scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no
  long-line reports. Only message: "KAM.lean is out of date" (generated; not edited, per rules).
- #print axioms of avg, pgAvg, pg_osc_hyp, pg_osc_bound, pg_osc_zero, pg_osc_normalization,
  pg_osc_domain, pg_osc_positive: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
None found. No signature changed. Note avg's displacement constants are 6 and 18 sharp-vs-12/18
(fast bound proved with factor-2 slack). KAM.lean needs regeneration by the orchestrator.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md (incl. Revision 4) row P5-AV and its proof plan; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean): (00) the orchestrator also renamed six unsigned helpers whose short names already existed in KAM (commit a05a4da2: blockFast_append/blockSlow_append clashed in the root build with PGMeasure/ResonanceSlow; avgB, avgPsi, norm_dotC_le, strip_mono reused names from other namespaces) to pgAv-prefixed names: check the diff is purely that rename; (0) the signed theorem avg was renamed pg_avg by the orchestrator (commit above; it clashed with the P2/P3 KAM.Planetary.avg in Averaging/Finite); the signature file line ~1062 now says pg_avg: check the rename is exactly that and nothing else; (1) every declaration the handoff lists (PGAveraging, averagingDomain, realAverageMap, AveragingSpec, pgOscNormalize/Unnormalize, pgOscP/H/E/Epsilon/Width/Alpha, pg_osc_*, pg_avg, pgAvg) = signature file EXACTLY, and the P5-AV slice COMPLETE (read the design row and proof plan line by line); definitions mean the source objects on their whole carriers; (2) proof soundness: the averaging conjugation and Hamiltonian identity (avg_hamil), the displacement bounds (handoff: 6 and 18 proved versus the signed 12/18, i.e. a stronger fast bound: confirm the SIGNED constants are what is stated), the Fourier/pointwise remainder bounds; no added premises; (3) because two sessions wrote this package, check consistency across the files (no duplicate or orphaned helpers); (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY the KAM/Planetary/PGAssembly/Averaging*.lean files.
