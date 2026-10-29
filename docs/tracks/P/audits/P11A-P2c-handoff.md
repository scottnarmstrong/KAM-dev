# P11A-P2c prover handoff (branch inp-p11ap2c, 02ca2bb0; offloaded package run by the main orchestrator)


## Files (new, all under KAM/Planetary/Preparation/; 1030 lines total, each < 340)
- HoloStripGeometry.lean (288): `p11hsBlock/Planet/Sep` (complex-angle separation), `p11hs_poincareC_shift`,
  `p11hsSep_shift`, `p11hs_strip` (uniform Re s_ij >= (a_j-a_i)^2/4 for |Im lam| <= 2 pi sigma', via compactness of
  [0,2pi]^n x closedBall (`IsCompact.eventually_forall_of_forall_eventually`) and 2pi-periodicity; sigma' <= 1/4, 2 pi sigma' <= 1/8).
- HoloStripBound.lean (212): `p11hsFHat` (= -G sum m_i m_j s_ij^{-1/2}, principal root), `p11hsGood`, explicit sup bound
  `p11hsMInf = G sum m_i m_j 2/(a_j-a_i)` (`p11hsFHat_norm_le`), holomorphy, shift-periodicity, realness at real points.
- HoloStripInput.lean (337): `p11hsInput rho` (complex lift, same formula as `p11ChartInput` without Re), `P11HsHyp`
  (parametric rho hypotheses: holomorphic entries, row-sum bounds B,B', real on reals, r_z/sigma smallness, strip data),
  bounds |rho x|<=B|x|, |H|<=nB'|x||y|, `p11hsInput_mem_good`, `p11hsInput_differentiableOn`, `p11hs_fderiv_im`.
- HoloStrip.lean (193): `p11hs_strip_data` (exists r', sigma'), `p11hsF D rho = f_hat o input`, `p11hsF_differentiableOn`,
  `p11hsF_norm_le`, `p11hsF_bound_weighted` (MF/coth(pi sigma)^n for MF >= coth^n * MInf), `p11hsF_shift`, `p11hsF_real`,
  and `p11hs_F` packaging the four holo_chart F-clauses (holomorphic, bound, periodic, real) on `p11WorkingDom n J0 (2 sigma) (2 rC) rz`.
Uses `SecularForm.Data` (convert via `p11PhysicalData D`), `a := D.a`.

## Checks
- Gate build of KAM.Planetary.Preparation.HoloStrip: success. `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated, not edited); all other guards OK.
- `#print axioms` p11hs_F, p11hs_strip_data, p11hsInput_mem_good: propext, Classical.choice, Quot.sound only. No sorry, no heartbeat overrides.

## For P2f (assembly)
1. Get (r', sigma') from `p11hs_strip_data`; pick rC, rz, sigma (sigma <= sigma'/4), B, B' from p11_rotation_bounds with
   `rz*B < r'`, `n*B'*rz^2 <= pi sigma'/2`, and `L` in the rotation ball within r' of `action D a` (`center` field).
   NOTE: r' comes from the strip lemma and may be smaller than the forward_tube delta; rC / J0 must be chosen to satisfy `center`
   (J0/(2 pi) close to the actual action within r'), which the patch data (delta/8) does not automatically give -> P2f/P2b must shrink.
2. Fill `P11HsHyp`, apply `p11hs_F` with MF >= coth(pi sigma)^n * p11hsMInf (e.g. max 1 ...).
3. Remaining (not mine): F = f_hat∘Phi_rho^{-1}∘T1 identification with fFix∘poincareProd∘p11ChartInput on reals (hc-id), hc-mean.

## Uncertainties / errata / deviations
- Deviation: the strip lemma is stated with extra 2 pi sigma' <= 1/8 so blocks stay in poincareNbhd (|Im lam|<1/4); sigma' <= 1/4 still holds.
- Sup bound is the explicit M_infty above, not an abstract sup. `P11HsHyp` smallness fields mirror hc-lift (r_z bounds) as source-level premises.
- No errata found.

ORCHESTRATOR RULING (OVERNIGHT 20:40): P11A-P2 is split; P2c owns item 3 of the P2 handoff map (hc-strip, hc-F), stated PARAMETRIC in a rotation family rho with the hc-rot bounds; P2f assembles holo_chart. holo_chart itself, hc-lift (P2b), hc-id/hc-lat (P2d) and hc-mean (P2e) are not findings here.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (holo_chart and steps stepP:p11:hc-strip, hc-F) and its node table; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (P11SecularSpec's F clauses: holomorphic, bound MF/coth(pi sigma)^n, periodic, real). Check p11hs_F's four clauses match those conjuncts verbatim on p11WorkingDom, that P11HsHyp assumes nothing the assembly cannot discharge from p11_rotation_complex/p11_rotation_bounds (or P2b's P11HoloData), and the uniform separation strip. Audit ONLY KAM/Planetary/Preparation/HoloStrip*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
