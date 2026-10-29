# DEFS-P2: definitions audit for six definition nodes in parts p3, p7, p10, p12 (main orchestrator; no new Lean)

Not a package audit of new code: the worktree is a clean copy of inp. Definition-node policy (OVERNIGHT 02:30, for
owner review): a pure definition node closes by naming the Lean definitions that ARE the source's objects, plus a
definitions-audit row classifying each. The survey (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md,
section "p0-p10 leftovers", and the p11b/p12 section) lists candidate Lean definitions.

Nodes (read each NODE record in docs/graph/P/DEPGRAPH.md, its STATEMENT_SOURCE lines and LEAN_NOTE):
1. bpP:p3:conv#data: Part-3 conventions (realFreq, dioBase, omegaSet, KamHyp in KAM/Planetary/TwoScale/Setting.lean
   :29-66; geometricWidth in Averaging/Setting).
2. bpP:p3:limitmap#data: S, |.|_*, G-check, L_*, D_j (limitmap_data, unsc, sc in TwoScale/LimitMapScale.lean:30-42;
   psiR, phaseTube in TwoScale/LimitMapPsi.lean:32-36); the survey says G-check and L_* are not located.
3. bpP:p7:conv#data: J0, R(g), e_g, cr, Omega_chart, Gamma, Q^I symplectic (rot, ex in KAM/Kepler/Basic.lean:55-59;
   frozen quarterTurn, planeCross, symplecticForm; poincareGamma in Poincare/Chart.lean:34; delaunay in
   KAM/Kepler/Orbit.lean:45, delaunay_symplectic).
4. bpP:p7:sec-product#data: w = ((lambda,xi),(Lambda,eta)) via assemble; q^(i) = body(q,i) (frozen assemble,
   bodyVector; poincareProd, poincareProdDom in Poincare/Product.lean:45-51).
5. bpP:p10:conv#data: A_n, Lambda(a), nu, sigma, U_n, G_n (open), norms (axes, action, axis, actionDomain, nu in
   SecularForm/Basic.lean:47-51; sigma in SecularForm/Coefficients.lean:121; goodAxes, simpleAxes in
   SecularSpectrum/GoodPolynomial.lean:49-50; action_diffeomorphism).
6. bpP:p12:sec-set#data: its definitions (its asserted cylinder-norm property is exported by cylnorm, GAP-PX).

AUDIT FOCUS: for EVERY source object, one row: source object | Lean declaration (file:line) | FAITHFUL /
FAITHFUL-WITH-NOTE / NOT FAITHFUL / MISSING | reason (body equals the source formula on the whole public carrier;
no fallback branch, no arbitrary witness, no off-source behaviour). Then per node: CLOSABLE (list the LEAN_REF) or
NOT CLOSABLE (exactly what is missing). A property the node asserts (e.g. "G_n open") needs a named lemma: give it
or say it is missing. Do not edit any file other than your report docs/tracks/P/audits/DEFS-P2-audit-1.md.
