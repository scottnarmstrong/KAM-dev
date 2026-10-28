# P5-KH prover handoff (branch inp-p5kh, 966e014f; offloaded package run by the main orchestrator)


## Files
- `KAMInputsBase.lean` (git mv of the round-1 file; content unchanged except module docstring): kamH, pgKamScale, helpers
  mu_lt_one_of_admissible, pgKamScale_L / _cutoff / _rhoHat / _eHat.
- `KAMInputsFreq.lean` (145 lines): fderiv_complex_realSlice, realInclusion_mem_actionNbhd, complexFast_realSlice,
  jpGrad_realSlice, **complexFrequency_realSlice** (the design's missing `complexFrequency_real`; hypotheses mu in Icc 0 mu0,
  blockFast J in V only).
- `KAMInputsKamH.lean` (220): kamH_eq_smul, fderiv_kamH, freq_kamH, realFreq_kamH, kh_dyn (rstar facts), mu_mem_Icc,
  actionNbhd_sub_analytic, kamH_differentiableOn, kamH_injOn (freq_inj), kamH_hessian (kam_c1 >= 2 pi pgCU), pgCU_pos.
- `KAMInputsF.lean` (360): kamF (verbatim), kamPolarPt, kamPolar_mem, kamF_eq (averaging identity), kamF_sup,
  kamF_differentiableOn.
- `KAMInputsPer.lean` (268): kamF_periodic, jetPolynomial_realSlice, kamH_real, kamF_real.
- `KAMInputs.lean` (208, facade): kam_hyp, pg_kam_hyp, pg_kam_dictionary (all four clauses), kamF_inClass.
All signatures verbatim from P45Signatures.lean. Merged inp-p5ch (round 2, phi_comp_hamiltonian); not needed by this module.

## Approach
- InClass/WBound: wbound_of_sup_bound with s = sigma = pgWidth/(24 pi) (so strip pgWidth/(12 pi) = averaging strip w/6 after
  the 2 pi scaling); sup bound from kamF = (mu pgRemainder + A.remainder)/(2 pi) on the polar point (norm <= 2r < r1, <= osc/2),
  coth(w/24)^(a+b) absorbed by kam_c1.
- Reality: oscillatorPolarComplex_real, real trace of Psi (AveragingSpec), ext_P_real, h0real, jet *_real; fast action in V
  via mem_of_dist_lt_innerCore (rho = l1/2 <= r^2/24 < sqrt r, from ell >= r^2/4).
- Domain inclusion: rho <= rhoBar/2, rhoBar <= pgAnalytic.rho, slow part < r^2/2 + l1/2 < 1.

## Checks
- `inp_lake_build.sh ... KAM.Planetary.PGAssembly.KAMInputs`: Build completed successfully (9305 jobs), after the merge.
- `scripts/lint_sources.sh`: PASS except "KAM.lean is out of date" (generated; not edited; the five new modules need
  `gen_root_imports.py`), check_lean_modules PASS, frozen guard OK, ABI OK.
- `#print axioms` of kamH, kamF, kam_hyp, pg_kam_hyp, pg_kam_dictionary, complexFrequency_realSlice, pgKamScale:
  [propext, Classical.choice, Quot.sound] each.
- No sorry, no maxHeartbeats, all files < 1500 lines. All new public names grepped: no clash in KAM.

## Uncertainties / errata / deviations
- No errata. Deviation: round-1 file moved to KAMInputsBase (facade now KAMInputs.lean imports all five).
- Design signal: pg_kam_hyp's strip width forces the sup bound on width pgWidth/(12 pi) which uses the full averaging strip w/6
  (no slack); fine here but tight.

AUDIT FOCUS: design docs/tracks/P/design/P45-LEAN-DESIGN.md (incl. Revision 4 and the pg_avg rename note) row P5-KH (kamH, kamF, kam_hyp, pgKamScale, pg_kam_hyp, pg_kam_dictionary) and its node table; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean. Two rounds by the prover (round 1 blocked on P5-CH's oscillatorPolarComplex, then merged); the orchestrator wrapped four long lines. The handoff proves the design's missing complexFrequency_real bridge as complexFrequency_realSlice: check it is exactly what the design means. Design signal: pg_kam_hyp's strip width uses the full averaging strip w/6 with no slack: confirm the bound is still correct. Audit ONLY KAM/Planetary/PGAssembly/KAMInputs*.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name (signed names follow the signature file), no harmful root shadow, lines <= 100.
