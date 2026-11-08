# GLOBAL recheck of b:4#HH closure (sonnet-global-B-hh), HEAD 8b82920e2

VERDICT: ACCEPT WITH FINDINGS

Read: DEPGRAPH.md (L1-14, L525-921), plan L341-424, the coverage diff, plus the earlier sources. LEAN_* ignored.
Counts re-checked: 29 nodes listed in the dashboard, 76 EDGE lines (grep), queue of 11 PROPOSED nodes agrees with the list.

## Status of my earlier findings
* F1 (no w0 with Psi w0 = z0): RESOLVED. b:4#inverse-chart (L702-728) concludes w0 = Psiinv z0 in the chart domain, Psi w0 = z0, |I(w0)-I(z0)| <= d; initial-inclusion (L730) and HH (EDGE L838) consume it; source plan L153-155.
* F2 (soundness black box, §3.2 outside corpus): LARGELY RESOLVED. Corpus now covers L341-424; soundness (L632) depends on B1-E, chart-composition, lie-identity, oscillator-drift; Lie (L346-354), composition (L355-356, L398-402) and oscillator bracket/tails (L373-385, L387-402) are nodes; the torus-only Fourier block (L358-371) and §3.3 divisors/units (L408-424) are excluded with reasons that are correct for HH (divisors are producer-side; no rescaling). Residual: R2 below.
* F3 (model identification): RESOLVED (L647-673; HH EDGE L837, certificate-accepted DEPS it).
* F4: PARTLY. certificate->soundness edge removed (direction fixed). initial-inclusion dependency: see R1.
* F5 (certificate source proof): RESOLVED as a declared computational leaf (L675-700, PROOF_SOURCE L338-340 = untrusted producer/replay; CL20 L560-566 excluded, coverage L-item b:4#cl20-computation). I accept this as the honest representation of the source: the plan itself gives only a target.
* F6 (domains): MOSTLY. transfer (L765) fixes forward domain = closed E_b; inverse-chart fixes the physical disc; certificate-accepted still says "required domains (per j)" (L684) and physical-bounds hypothesis (L793) says only "forward action displacement <= d_j". Cosmetic (R3).
* F7 (transfer/coverage): RESOLVED. b:2.3#transfer is a node (L758-784, PROOF_SOURCE plan L143-150 which is the B1-T form; the oscillator statement is L201, both cited), coverage items updated; physical-bounds follows the plan chain I(z) <= I(w)+d < b+d <= 1.01e-8 (L788, L795) and 2d + eta T (L805). Arithmetic re-verified: b+d = 1.01e-8 = 101/10^10 (strict via I(w) <= a+eta T = 7.561e-9 < b); 2d+eta T = 1.2e-9 = 12/10^10; initial 6.4e-9+1e-10 = 6.5e-9 < 6.561e-9.
* F8 (edge cite): OPEN, trivial (HH EDGE L841 still cites L21 only for "premise and conclusion").

## Re-examination of the revised closure (new attempts to refute)
Root identity, statement, model, quantifier order, coordinates and constants: unchanged and still correct (frozen statement byte-identical to FREEZE-PROPOSAL-HH L20-36, diffed previously; HH SOURCE_CONCLUSION L826 matches).
AND/OR: all DEPS conjunctive, no ROUTES; no cycles seen (soundness -> {B1-E, chart-composition, lie-identity, oscillator-drift}; HH -> inverse-chart -> {chart-composition, certificate-accepted}; physical-bounds -> {soundness, transfer, initial-inclusion, certificate-accepted}). B1-E premises at the consumer: (a) H C^2/V open: model-identification (L656); (b),(c),(d) Psi C^2, symplectic, left inverse: chart-composition (L568); (f) H o Psi = N o I + R: lie-identity (L540); (g) bracket bound eta: oscillator-drift (L597); eps>0, N and R definitions are inside the accepted data of soundness (L624). a+T eta<b: certificate literals (L677). w0 with I(w0) <= a: initial-inclusion. Each premise now has a discharging node.
Forward vs inverse: forward displacement used twice in physical-bounds/transfer (z0 = Psi w0), inverse only for existence/inclusion; the nodes say exactly this (L784, L815). Good.
OD-B18 NOTE (inverse-chart L728, initial-inclusion L756): still a Lean-route deviation only; the source statement (displacement d on the physical disc) stays the node statement. Accepted.

## Remaining findings

### R1 (MEDIUM) inverse-chart and initial-inclusion do not depend on checker-soundness
inverse-chart DEPS = chart-composition, certificate-accepted (L717). Its hypothesis "inverse displacement bound from the certificate" (L709) and conclusion |I(w0)-I(z0)| <= d_j (L711) are statements about the *actual* chart. certificate-accepted is only the Boolean checkNormalForm = true (L684); converting acceptance into the inequality on the real chart is soundness (soundness' data list includes "forward/inverse displacement bounds, initial-set inclusions", L624, plan L321). chart-composition only says displacement bounds "compose" (L568, plan L401-402) and has no base case. physical-bounds correctly depends on soundness (L801); inverse-chart should too, which also makes the soundness node's "initial-set inclusions" content visibly consumed.
Fix: add EDGE b:4#inverse-chart -> b:3.1#checker-soundness (soundness yields the bounds and inclusion for every z0 in c.initialRegion); optionally state the base-case displacement bound of a single time-one flow inside chart-composition.

### R2 (LOW-MEDIUM) Cauchy-type estimate is a hidden analytic input
oscillator-drift SOURCE_CONCLUSION (L597) uses "tail E on Cartesian complex discs with margins contributes w_j E(1/dq_j + 1/dp_j)" (plan L382-384) i.e. a Cauchy estimate for a holomorphic function, and the change of variables z=(q+ip)/sqrt2 on the real slice with |z_j| <= rho_j (plan L373-375). EXTERNAL_POLICY (L8) lists only ODE inputs; ext nodes are only ODE; "Explicit source gaps: 0" stands. Plan states it without proof.
Fix: record a leaf ext:analysis#cauchy-estimate (or state in the node NOTE that it is a standard analytic input, not derived in the plan) and update EXTERNAL_POLICY; the same for complex-flow existence if distinct from the real ODE ext node (L550, L579 reuse ext:ode#local for complex data, which needs the C^n = R^2n remark).

### R3 (LOW) Domains still unnamed in certificate-accepted and physical-bounds
State "forward displacement on closed E_b; inverse on the physical disc" in certificate-accepted SOURCE_CONCLUSION (L684) and physical-bounds hypotheses (L793); consumers currently carry it only in transfer (L765) and inverse-chart (L710).

### R4 (LOW) HH edge L841 cite L21 only; add L33-36 for the conclusion uses.

## Recommendation
ACCEPT WITH FINDINGS. Structure now exposes every premise of B1-E and the b:3.1 soundness inputs; fix R1 (one edge) and record R2 before marking b:4#HH and its new nodes REVIEWED. No blocking defect found.
