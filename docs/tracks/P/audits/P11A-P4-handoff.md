# P11A-P4 prover handoff (branch inp-p11ap4, 9c065f8e; contains inp-p11ac6 and inp-p11ap3 (audited) and the p11Affine port; offloaded package run by the main orchestrator; prover on claude-12)


**Files (new):** KAM/Planetary/Preparation/RectangularAverage.lean (128 lines, `aniso_avg`),
RectangularAverageCore.lean (435), RectangularAverageDomain.lean (96), RectangularAverageEps.lean (197).
All well under 1500 lines; no heartbeat options; no EuclideanSpace; no sorry/axiom.

**Proved:** `aniso_avg` (bpP:p11:aniso-avg; aa-same, aa-quad as local steps), signature verbatim except
line breaks inserted in four >100-column lines (whitespace only, for lint).

**Approach:** NOT a re-proof of the iteration. Key observation: p11Box c r1 r2 = r_*-neighbourhood
(r_* = min r1 r2) of the closed polydisc `p11AvgBase` (radii r_j - r_*), so the existing isotropic finite
iteration (Averaging/FiniteStep..Gen, `IterSetup`, stated for an arbitrary complex base set Dc) applies with
the single radius r_*. Only the wrapper layers (`AvgHyp`, `goodSched_*`, `setup_of_avg`, `nfb_core`) were tied
to real D (realBase), which cannot represent a complex centre c; I re-did them for complex Dc
(`P11AvgHyp`, `p11_goodSched_single/multi`, `p11_nfb_core`; copies of the P23 proofs, distinct names).
The quadratic bound (aa-quad) needed a new remainder sequence `p11Eps` (eps_1 = 2(E/Q)E <= 3E/(4kappa))
and a first-step lemma `p11_step_first_quad`; everything else compares with the old `multiEps` sequence.
Quadratic constant obtained is 128 (<= 130 claimed). Widths: Weighted widths are already geometric, so
nfb is used with sbar=0 and kappa = 2 pi T s directly (not `avg`, whose hstrict premise is not implied).
Existing Averaging files were not edited.

**Checks:** gate build `inp_lake_build.sh ... KAM.Planetary.Preparation.RectangularAverage`: success, no
warnings in my files. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK;
only message: "KAM.lean is out of date" (generated, not mine to edit). 
`#print axioms KAM.Planetary.aniso_avg`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none beyond the whitespace line breaks. Note for orchestrator: root
file needs regeneration for the new modules. p11Affine not used (merged branch note acknowledged).
Design note: the design's "P2 direct/split/nfb adaptation" needed no change of isotropic N6/7; the only
real obstruction was complex (non-real) centre, handled by the Dc-general copies.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P4 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) aniso_avg and any other P11A-P4 signature declarations = signature file exactly; (2) proofs sound (P2 direct/split/nfb adaptation, N6/7 exact gauge adapters; P3 RectangularBracket and C6 AffineFlow consumed as designed; the quadratic first-step epsilon sequence and finite iteration core proved, not assumed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM; p11Affine imported from MaximalStep/Affine, not redefined). Audit ONLY KAM/Planetary/Preparation/RectangularAverage*.lean.
