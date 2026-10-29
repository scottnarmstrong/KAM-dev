# LREF-P: LEAN_REF audit for nine p1/p6 step nodes (main orchestrator; no new Lean)

Not a package audit of new code: the worktree is a clean copy of inp. For each step node below, the survey
(/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md, section "p0-p10 leftovers") names landed
declarations that should already state the node's literal conclusion. Your job: confirm or refute, node by node.
A node is closable by LEAN_REF only when ONE named declaration (or one conjunct of one, as the PROVED precedent
cu-c / cu-b cites a p11_cutoff conjunct) states the node's literal SOURCE_CONCLUSION under only its
SOURCE_HYPOTHESES, with quantifiers in the source's order and no proved dependency's output taken as a premise.

Nodes (read each NODE record in docs/graph/P/DEPGRAPH.md and the blueprint lines it cites):
1. stepP:p1:pc-c: analyticOnNhd_periodOne_iff (KAM/Planetary/Hamiltonian/Transport.lean:174), fderiv_periodOne
   :188, periodOne_lattice_iff :212, periodOne_injMod_iff :224, periodOne_hasDerivAt_iff :239.
2. stepP:p6:pl-a: KAM/Kepler/Plane.lean :45/:51/:54/:65/:72/:78, abs_planeDot_le :89, planeLength_add_le :95.
3. stepP:p6:pl-b: norm_le_planeLength (Plane.lean:117), planeLength_le_sqrt_two_mul_norm :125.
4. stepP:p6:pl-c: analyticAt_planeLength (Plane.lean:240), analyticAt_inv_planeLength :252,
   hasFDerivAt_planeLength :262, hasFDerivAt_inv_planeLength :286.
5. stepP:p6:dom-open: isOpen_collisionFreeDomain (KAM/Planetary/Newtonian/Models.lean:258).
6. stepP:p6:dom-smooth: analyticOnNhd_movingHamiltonian (Models.lean:319), analyticOnNhd_fixedHamiltonian :327.
7. stepP:p6:he-fix: hamiltonianVectorField_fixed (Models.lean:556); fixedField_blocks
   (KAM/Planetary/Newtonian/HamiltonNodes.lean:54); fderiv_fixedHamiltonian_partials :167.
8. stepP:p6:rc-pack: reconstruction (KAM/Planetary/Newtonian/Reconstruction.lean:233), reconstruction_all_time :246.
9. stepP:p6:ot-apply: orbit_transfer_moving (Reconstruction.lean:304), orbit_transfer_fixed :315.

AUDIT FOCUS: per node, verdict CLOSABLE (give the exact LEAN_REF: declaration, or declaration + conjunct) or NEEDS
BUNDLE (the content is proved but split across several declarations or stated with an extra premise: give the
exact one-line bundle lemma statement that would close it) or NOT CLOSABLE (say exactly what is missing). Check
the source hypotheses and quantifier order literally (e.g. dom-smooth says C^infinity: analytic implies it, say
whether the analytic form is accepted as the node's literal content or a ContDiff corollary is needed). Do not
edit any file other than your report docs/tracks/P/audits/LREF-P-audit-1.md.
