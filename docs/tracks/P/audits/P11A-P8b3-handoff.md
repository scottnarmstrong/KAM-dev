# P11A-P8b3 prover handoff (branch inp-p11ap8b3, 2526f740; contains inp-p11ap8b2 (pr-b, pr-c; audited separately) merged; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Preparation/PreparedM.lean` (~730 lines; imports PreparedFreq, WeakMeasure.Stability).
  No other file edited (KAM.lean, Frozen, manifest, PreparedOps/Dev/Num/Resc/Freq untouched; pr-c untouched).

## Mapping
- `stepP:p11:pr-d` -> `KAM.Planetary.p11_pr_d`, conclusion exactly the three scalar/diagonal clauses of
  `P11PreparedSpec`/`P11PreparedFullSpec` for `p11PreparedFreqR Q` on `p11thick (p11PreparedBox n) (1/4)`:
  (i) p11op (p11scalar 2 freqR d) j y <= 2^(mu+1)(2L+1)^2 for 1<=j<=mu+1;
  (ii) p11JetBound true mu thick freqR (p11M0 n mu L) (M0*);
  (iii) the order-zero scalar bound <= 2^(mu+1)(2L+1)^2.
  Form: `exists K > 0, forall {Fast eps c A Q}, ...` like `p11_pr_b`. Premises: 0<eps, eps*MF<=exp(-1), 0<=c,
  `K(1+c) eps l^Qe <= 1`, `3 pi eps <= pi rz^2/16`, `5 eps <= s2`, `P11FastSpec`, `P11SlowSpecOf`, the identity
  `Q.N = (h0+g2)(rescale)/eps` on `actionNbhd box 1`. Standing hypothesis `P11SecularFullSpec D C` (needs its Euclidean
  `euclid_le`; `P11SecularSpec` alone does not carry it) and `1 <= nu`. No proved dependency's output is a premise.

## Approach
- M_1 <= 2L+1: order 0 is Euclidean: freq = main (omega, eps*Omega/2pi) + deviation; main has Euclid length <= L
  (`euclid_le`, eps<=1), deviation per coordinate <= K1(1+c)eps l^Qe (`p11_pd_dev_pure/rho/dev0`, from
  `p11_dev_J_bound`, `p11_dev_rho_bound` + PreparedNum), combined by `p11_pd_euclid_add` (Minkowski-type bound).
  Orders >=1: `p11op_re_le` with `p11_freq_partial` (eps L + small), numerics in `p11_pd_num`.
- Then `M_bound` (WeakMeasure) on V = real slice of `actionNbhd box 1` (`p11_pd_contdiff`, `p11_pd_freq_diff`);
  2^j M^2 <= 2^(mu+1)M^2. Diagonal: `p11dg_le_p11op` and 1 <= (2n+1)^(mu+1). Order-0 scalar via `abs_p11dot_le`.
- Declarations (all `p11_pd_*`, unique short names; grep-checked): euclid_add, omega_partial, dev_pure, dev_rho, dev0,
  point, freq_diff, thick_mem, euclid_mono, single_cast, single_nat, zero, prem, num, ord, contdiff, jet; export `p11_pr_d`.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-p11ap8b3 KAM.Planetary.Preparation.PreparedM` -> Built, no warnings in my file.
- `#print axioms KAM.Planetary.p11_pr_d`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: module check PASS, frozen guard OK, ABI OK; "KAM.lean is out of date" (generated; new
  module needs root import by orchestrator). It also reports >100-column lines in OTHER files from P8b2
  (PreparedNum.lean:25, PreparedResc.lean:16,214,226) — not mine, not edited. My file: 0 lines >100, no sorry/maxHeartbeats/EuclideanSpace.
- Design signal (resolved by refactor, no overrides): a first monolithic `p11_pr_d` timed out at default heartbeats;
  split into `p11_pd_ord`, `p11_pd_zero`, `p11_pd_jet`, `p11_pd_num`.

## Uncertainties / errata / deviations
- Need `P11SecularFullSpec` (not just `P11SecularSpec`) — matches the design (prepared uses the full spec).
- Smallness uses the same Qe exponent as `p11_pr_b`; K depends on n, mu, L, K0 (pr-b constant), K1. 
- No source defect found. Blueprint's "max-norm operator norm" is read in the Euclidean `p11op` gauge as the signatures define it;
  order 0 genuinely needs the Euclidean bound L on the main term (hence FullSpec).

ORCHESTRATOR RULINGS: (02:35) step pr-d was split from P11A-P8b2 into this parallel package; pr-b/pr-c and the P8b2 modules are audited separately and are NOT in scope. (01:45, AMEND P-A002) constants may depend on n, tau, the fixed data and the derivative orders, fixed before eps. The signed prepared/amount are assembled later by P8e.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (prepared, step pr-d) and NODE: stepP:p11:pr-d in docs/graph/P/DEPGRAPH.md. Check that the export states pr-d's literal conclusion (the 2^k M1^2 bound, M*, M0*) with eps-smallness only as explicit numeric premises, no proved dependency's output as a premise, and in the shape P11PreparedFullSpec's corresponding clause needs (signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean). Audit ONLY KAM/Planetary/Preparation/PreparedM.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
