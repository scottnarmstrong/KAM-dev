# T3 prover handoff (P11C; branch inp-p11c-t3, 6a35ee34; off inp; offloaded package run by the main orchestrator; prover on claude-10, completed in a second session T3b after the orchestrator's brief had omitted one declaration)


**Files:** new `KAM/Planetary/PlanarTorsion/LaplaceReduction.lean` (363 lines). No other file touched.

**Proved (signatures verbatim, incl. `def p11c_laplace`):** `laplace_red`, `laplace_up`, `laplace_rational_reduction`
(namespace `KAM.Planetary`). Public helpers (all new names, grep-checked): `p11cKer`, `p11cKer_pos`, `p11cKer_contDiff`,
`p11c_cont_div`, `p11cI`, `p11c_laplace_eq`, `p11cI_cont`, `p11cI_red1`, `p11cI_red2`, `p11c_laplace_red1/2/3`,
`p11cEv`, `p11cRep`, `p11cRep_comb/zero/one/base/all`, `p11c_one_sub_sq_ne`, `p11c_laplace_step`.
Also proved (T3b): `laplace_reduction_denominator` (signature verbatim), helpers `p11cRepD`, `p11cRepD_mono`, `p11cRepD_base`, `p11cRepD_all`.

**Approach:** kernel f=1+a²-2a cos t >0. Recurrence 1: pointwise identity cos(kt)/f^(s-1)=cos(kt)·f/f^s plus
product-to-sum, integrated. Recurrence 2: FTC on sin(kt)·f^(1-s) over [0,2π] (boundary terms vanish, sin(2πk)=0, valid also k=0);
recurrence 3 is algebra from 1,2 (holds for all integer k, not only k≥1). laplace_up: apply red1/2 at s+1 (+ symmetry
L(s,-1)=L(s,1)), eliminate L(s+1,2) by linear_combination. Rational reduction: closure lemma `p11cRep_comb`
(polynomial combination of two represented functions over a pole-free denominator), induction on j for k=0,1 via laplace_up,
then on k via red3 (denominator (j-1/2-k)·a, nonzero since half-integer).
Does not import U8a `laplace_def`; the bridge to it is left to the later bridge (design: "identified by a bridge").
Imports only Mathlib. No frozen/provider imports.

**Checks:** gate build `inp_lake_build.sh /root/code/KAM-inp-p11c-t3 KAM.Planetary.PlanarTorsion.LaplaceReduction`: success, no warnings
after cleanup (final minor line-wrap edits re-checked with `lake env lean`, clean). `#print axioms` (temporary, removed) for
laplace_red, laplace_up, laplace_rational_reduction: [propext, Classical.choice, Quot.sound].
`scripts/lint_sources.sh`: PASS except the expected "KAM.lean is out of date" (not edited by instruction).

**Uncertainties:** none on statements; no heartbeat issues; no maxHeartbeats. **Errata/deviations:** none.
`p11cKer_contDiff` is a slight misnomer (it states Continuous).

AUDIT FOCUS (design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T3 and Appendix; audit DESIGN-P11C-design-audit-1.md; signatures .drafts/design/P11CSignatures.lean incl. ~L794): (1) p11c_laplace, laplace_red, laplace_up, laplace_rational_reduction, laplace_reduction_denominator = signature file exactly, and the T3 slice is COMPLETE; (2) proofs sound (U8a laplace_def, integration by parts; the explicit a^k (1-a^2)^(2j) denominator envelope); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM: many p11cKer / p11cI / p11cRep* helpers). Audit ONLY KAM/Planetary/PlanarTorsion/LaplaceReduction.lean.
