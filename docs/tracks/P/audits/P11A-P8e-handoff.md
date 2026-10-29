# P11A-P8e prover handoff (branch inp-p11ap8e, bbf064fa; built on P8b/P8b2/P8b3 (passed) and inp (P8, P8a, P8c landed), with P8D (data_star_of_amount, passed) merged; offloaded package run by the main orchestrator)


## Files (all new, KAM/Planetary/Preparation/, no sorry, lines <= 100, no heartbeat overrides)
- PreparedSmall.lean: `p11_prep_five_eventually` (5 eps <= s2), `p11_prep_small` (for eps <= e0: eps MF <= e^-1,
  3 pi eps <= pi rz^2/16, 5 eps <= s2, `P11FastSpec` of `p11FastData`, `P11SlowSpec` of `p11SlowData`, 1 <= c2),
  `p11_prep_eventually_le` (M eps l^q <= 1 for small eps).
- PreparedChoice.lean: `p11PrepChk` (checkW = derivative of h0+g2 at the rescaled point, tail / eps),
  `p11PrepQ = p11PreparedCore D nu eps p11PrepChk`, `p11_prep_chk_eq` (clause 2), `p11_prep_freqR_eq` (clause 11),
  `p11_prep_ball_mem`, `p11_prep_pt`, `p11_fderiv_pi_one`.
- Prepared.lean: `prepared` (signature verbatim).
- AmountSetup.lean: compactness jet bound `p11_amt_jet_bound`, `p11HalfCube` geometry.
- Amount.lean: `p11_amt_chk_contDiff` (checkW smooth on ball 5/4, from the spec alone), `amount` (signature verbatim).
- Not edited: KAM.lean, Frozen, manifest, other pieces. New modules need root import by the orchestrator.

## prepared: clause discharge (Q = p11PrepQ D nu eps, c3 = max (max 1 c2) (Kc (1+c2)))
- eps3 = min e0 (min eb e1): e0 from p11_prep_small, eb from p11_prepared_basic_dom, e1 from eventual M eps l^Qe <= 1
  with M = (Kb+Kd)(1+c2)+c3 (Kb, Kc, Kd the constants of p11_pr_b/c/d).
- 5 eps <= s2: p11_prep_small. c3 eps l^Qe <= 1: eventual bound.
- Spec clauses formulas/chain, N/P holomorphy, periodicity, reality, N real, sup P, Hamiltonian identity: `p11_prepared_basic_dom` (c3 >= c2).
- smallV bound and fderiv bound: `p11_pr_b` (hN is rfl for the core). The signed Hessian bound is 2L+1 (as ruled).
- freqR = diag(1,eps) checkW on ||y|| <= 5/4: `p11_prep_freqR_eq` (via p11_freq_partial_eq with alpha = 0).
- Jet closeness (spec and full clause 3): `p11_pr_c`, premise hcheck from `p11_prep_chk_eq`.
- Full clause 2: `p11_prep_chk_eq`. Scalar bounds j>=1, vector jet through order mu, order-zero scalar: `p11_pr_d`.

## amount
Uses `prepared`; the chosen Q = p11PreparedData satisfies FullSpec by choose_spec. Then `amount_transfer` with
U = ball 0 (5/4), W = checkW (smooth by p11_amt_chk_contDiff), R = Rho = [-1/2,1/2]^n, Vn = patch V,
varpi analytic on V, L1 = compactness bound on patch K, theta = c3 eps l^Qe from FullSpec clause 3 (mono to J0+eps R),
betaJ = patch beta (beta <= index varpi K <= index varpi (J0+eps R) via index_def_anti). Extra smallness: eps <= r0
(ball J0 r0 in K, J0 in interior K) and 2^mu theta (2 L1+theta) <= beta/2. Finally index_def_congr replaces
diag(eps) checkW by p11PreparedFreqR Q on the box (clause 11).

## Checks
- Gate builds: PreparedSmall, PreparedChoice, Prepared, AmountSetup, Amount: success.
- scripts/lint_sources.sh: only "KAM.lean is out of date" (generated); module check, frozen guard, ABI PASS; no long lines in my files.
- `#print axioms prepared` and `#print axioms amount`: [propext, Classical.choice, Quot.sound].
- Short names of new public declarations grepped: unique.

## Uncertainties / errata / deviations
None found; no signed statement changed. Design signal: none (default heartbeats).

ORCHESTRATOR ADDITION (03:40): after the prover finished, the orchestrator added the SIGNED data_star to Preparation/Datum.lean, verbatim from the signature file, with body data_star_of_amount D (fun _nu hnu => amount D hnu) (parametric ruling OVERNIGHT 03:25; data_star_of_amount passed its own audit P11A-P8D-audit-1).

AUDIT FOCUS: this package proves three SIGNED theorems: prepared (Preparation/Prepared.lean), amount (Preparation/Amount.lean) and data_star (Preparation/Datum.lean), plus the signed def p11PreparedData if defined here. (1) Each signed declaration equals /root/code/KAM-inp/.drafts/design/P11ASignatures.lean EXACTLY (~1124-1141 and ~1282-1300): binders, statement, let-bindings; run the exact-type probe example : type_of% @KAM.Planetary.prepared := @<signature copy> style comparisons in a scratch file if needed. (2) Every clause of P11PreparedFullSpec is discharged from the landed/passed pieces (PreparedBasic pr-basic/pr-a, PreparedJets/G0 pr-in, PreparedFreq pr-b, PreparedClose pr-c, PreparedM pr-d, AmountCore amount steps) with no added premise and no conclusion-shaped hypothesis; the bridge modules PreparedSmall, PreparedChoice, AmountSetup are sound. (3) #print axioms of prepared, amount, data_star: only propext, Classical.choice, Quot.sound. (4) graph nodes bpP:p11:prepared, bpP:p11:amount, bpP:p11:data-star (design node table). Audit KAM/Planetary/Preparation/Prepared.lean, PreparedSmall.lean, PreparedChoice.lean, Amount.lean, AmountSetup.lean and the data_star theorem in Datum.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
