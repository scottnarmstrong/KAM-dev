# P5-CH prover handoff (branch inp-p5ch, 9d4eef24; contains inp-p5av incl. the pg_avg rename and the pgAv helper renames; P5-AV is in audit; offloaded package run by the main orchestrator)


## Files (new)
- `KAM/Planetary/PGAssembly/ChartDefs.lean` (phi, phiDomain, oscillatorPolarComplex, oscillatorPolarComplex_real)
- `KAM/Planetary/PGAssembly/ChartMem.lean` (chart_dyn, chart_rK_lt_half, params_l2_eq, isOpen_phiDomain, phiDomain_slow(_pos), phiDomain_fullShift, oscillatorPolar_fullShift, polar_mem_averagingDomain, realAverageMap_add_fastShift)
- `KAM/Planetary/PGAssembly/ChartLoc.lean` (chart_disc_aux, chart_radial_margin, mem_of_dist_lt_innerCore)
- `KAM/Planetary/PGAssembly/Chart.lean` (phi_chart, location); imports the others (facade for the package path).
All files < 160 lines. Declarations copied verbatim from P45Signatures.lean (only line wraps in `def phi`/`phiDomain`).
Merged inp-p5av (pg_avg rename, pgAv* helper renames) as instructed; Chart uses `pg_avg`.

## Approach
- phi_chart: IsChart = `disc_measure_chart.1` (mono to slow>0) `.comp` the `AveragingSpec` chart component, maps via `polar_mem_averagingDomain` (slow action < r^2, r < pgOscRadius/4). Lattice equivariance from `AveragingSpec` periodic + real components and `oscillatorPolar_fullShift`. Injectivity mod lattice: shift z by `fullShift (append k 0)`, AveragingSpec InjOn, then `oscillatorPolar_lattice`.
- location: fast part via `rK < l1/2`, `rK < rhoBar/2` (from `r_k` and `rstar` dynamic facts, `chart_dyn`); cylinder: fast action stays in V by inner-core margin (`mem_of_dist_lt_innerCore`, rK + disp1 < sqrt r); oscillator radius via displacement bound and `chart_radial_margin` (sqrt(2I)+k1 r^{3/2} < r, using l1 = k1 r^{5/2}).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p5ch KAM.Planetary.PGAssembly.Chart`: Build completed successfully, no sorry/warnings in my files (after final merge too).
- `scripts/lint_sources.sh`: no over-long lines; PASS on modules, frozen guard, ABI hashes; only message "KAM.lean is out of date" (generated; not edited, per rules).
- `#print axioms` phi_chart, location, oscillatorPolarComplex_real: [propext, Classical.choice, Quot.sound].
- grep: no duplicate declaration names in KAM; no EuclideanSpace / maxHeartbeats.

## Notes
- `oscillatorPolarComplex` and `oscillatorPolarComplex_real` are listed under P5-CH in the design table (row bpP:p5:phi) but belong to the "kam-hyp / polar bridge" in the signatures; I implemented them here. P5-KH should import them from Chart, not redefine.
- No errata or deviations found; no heartbeat issues.
- Uncertainty: `r_k` gives `rK < rhoHat/(256*(a+b))`; the a+b=0 case is handled (division by zero gives rK<0, so rK < l1/2 holds via contradiction with the positivity of rK from hypothesis).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md (incl. Revision 4 and the pg_avg rename note) row P5-CH and its node table/proof plan; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean): (1) phi_chart, location, phi, phiDomain = signature file EXACTLY, and the P5-CH slice COMPLETE (every graph proof step the node table maps to Chart; siblings failed audit for unexported graph cuts); definitions mean the source objects on their whole carriers; (2) proof soundness: consumption of pg_avg/pgAvg (P5-AV) and P4-POL, P1 IsChart.comp and hol_chart; no added premises; (3) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/PGAssembly/Chart{,Defs,Loc,Mem}.lean.
