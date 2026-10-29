# P11A-P1 prover handoff (branch inp-p11ap1, 9a2d476a; offloaded package run by the main orchestrator)


Branch inp-p11ap1. Commits: 27daf6f4 plus a line-length reformat commit.

## Files
- KAM/Planetary/Preparation/Basic.lean — import facade (sec-conv#data introduces no new definition).
- KAM/Planetary/Preparation/Working.lean — P11Physical, p11Zeta, p11_zeta_pos (proved), forward_tube and
  p11PhysicalDelta (one-line wrappers over forward_tube_core), p11SecularMatrix, P11PatchData, P11PatchSpec
  (all VERBATIM), norm_dict (+ stepP:p11:nd as local obligations: nd_scalar_eq, nd_p11dg_smul, nd_rnd,
  inline scaling), proved via chart_scaling_jets (W8) and index_def machinery (W0/W1).
- Not delivered: Preparation/BasePoint.lean, p11_patch, p11PatchData, select (sel-hyp/sel-gam/sel-int).

## Blocker (design signal, not a heartbeat issue)
p11_patch (Part 10 port) needs the clause `charpoly (p11SecularMatrix D (J/2π)) = ∏ (X - sigma J i)`,
i.e. the literal Hessian of the frozen secularAverage of fFix∘poincareProd equals Part 8's `coeffs`
(Part 10's `sigma` = sorted spectrum of `coeffs`). On inp only `cross_hessian` (off-diagonal) is present;
`quadratic_form` / qf-diag2 (S8-Q) exist only on branch inp-s8q, not on inp. I may not merge it.
p11PatchData (:= choose of p11_patch) and `select` (statement uses p11PatchData) depend on it. No sorry
was used. select's planned route once p11_patch exists: P11DioHyp with wt k := w (close trivial), power_law
with tau = max(n mu,2n) > 2n mu/2 - 1, eps = vol K/2, gamma small, boundary null => good set meets int K,
fast/slow Diophantine from integer vectors (k,0), (0,k).

## Checks
- Gate builds: Preparation.Basic OK; Preparation.Working OK (rebuilt after reformat: OK).
- `#print axioms` norm_dict, forward_tube, p11_zeta_pos: propext, Classical.choice, Quot.sound.
- lint_sources.sh: all pass except "KAM.lean is out of date" (generated; not edited, per rule).

## Deviations / notes
- `forward_tube` short name also exists as KAM.Planetary.PlanarAssembly.forward_tube (different
  namespace); signature name kept verbatim as mandated by the brief.
- norm_dict's RND conclusion is derived from the amount hypothesis (nd_rnd: zero index forces
  nondegeneracy), since the signature has no RND hypothesis.
- No errata found.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P1 (Preparation/Basic, Working, BasePoint; P10 exact physical-frequency interface; norm_dict, select) and its node table; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean. NOTE: the handoff's header 'PARTIAL (blocked on S8-Q)' is STALE: after S8-Q landed the orchestrator merged inp and a second round added Preparation/Patch.lean (p11_patch, p11PatchData), PatchHessian.lean and BasePoint.lean (select); audit the current files. Also: the deferred one-line wrappers forward_tube and p11PhysicalDelta over forward_tube_core (orchestrator ruling 15:16) must be present and exact. Audit ONLY the KAM/Planetary/Preparation/{Basic,Working,Patch,PatchHessian,BasePoint}.lean files. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
