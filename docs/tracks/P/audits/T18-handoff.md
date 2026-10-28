# T18 prover handoff (branch inp-p11c-t18, 0b7c10a7; contains T13, T6 round 1 (T6 round 2 passed later); offloaded package run by the main orchestrator)


## Files (all new, under KAM/Planetary/PlanarTorsion/)
Facade `AsymptoticEntries.lean`; `AsymptoticEntries/{Pair,Calculus,Leading,CoeffEq,EntryBounds,Inputs,
Projector,Coeffs,Entries}.lean` (each < 250 lines, lines <= 100 cols). No Frozen/manifest/KAM.lean edits.

## Declarations (graph nodes; the signature file has no T18 declarations, so statements are mine,
each the literal node conclusion at a = ![alpha,1], alpha -> 0+ (nhdsWithin 0 (Ioi 0)), in absolute
`leading + O(alpha^(lead exponent + 2))` form)
- `as_in` (stepP:p11b:as-in, Inputs): Q11 = -(3 G m2/(8 sqrt kappa)) a^(3/2) + O(a^(7/2));
  Q22 = -(3 G m1/(8 sqrt kappa)) a^2 + O(a^4); Q12 = O(a^(11/4)); Delta_Q < 0 eventually;
  Delta_Q/Q11 - 1 = O(a^(1/2)).
- `as_pi` (as-pi, Projector): eventually |pi12| <= |Q12|/|Delta|, 0 <= pi22 <= Q12^2/Delta^2,
  pi11 = 1 - pi22; pi12 = O(a^(5/4)), pi22 = O(a^(5/2)). Helper `p11cAe_delta_lower`.
- `as_c` (as-c, Coeffs): c1..c6 (Lean idx 0..5): c1 = (3 m2/(32 m0 m1)) a + O(a^3),
  c2 = -(3 m1/(8 m0 m2)) a^2 + O(a^4), c3 = -(9/(16 m0)) a^(3/2) + O(a^(7/2)), c4 = O(a^(7/2)),
  c5 = O(a^(9/4)), c6 = O(a^(11/4)) (m1,m2 = p.m 0, p.m 1; m0 = p.m0).
- `as_ent` (as-ent, Entries): beta00 - 8c1, beta01 - 4c3 = O(a^(7/2)), beta11 - 8c2 = O(a^4), and the
  three entry limits beta00 = (3 m2/(4 m0 m1)) a + O(a^3), beta01 = -(9/(4 m0)) a^(3/2) + O(a^(7/2)),
  beta11 = -(3 m1/(m0 m2)) a^2 + O(a^4) (matches asymptotics' targets). `as-det` is T19's.
All hypotheses: only `p : PlanarData`, `hp : p.Valid`.

## Approach
Pair coefficients: `p11c_comp_vanishes` (T4) gives pairCoeffs - jet = a^ord * analytic, so O(a^7).
Q entries via exact formulas for p11c_Q at ![a,1] and pair_quadratic_consistency (b_{3/2}^{(1,2)});
projector via exact closed form in Q (R = sqrt(D^2+4Q12^2)), inv_rev for 1/Delta; coefficients via exact
actions Lambda; entries via beta_def (T13) with u = 1 - v and abstract monomial bounds (EntryBounds).

## Checks
- `inp_lake_build.sh $PWD KAM.Planetary.PlanarTorsion.AsymptoticEntries`: Build completed successfully
  (9259 jobs); no sorry/maxHeartbeats in my files.
- `scripts/lint_sources.sh`: PASS except "KAM.lean is out of date; run gen_root_imports.py" (new
  module not in KAM.lean; orchestrator regenerates); check_lean_modules PASS, frozen guard OK.
- `#print axioms` as_in, as_pi, as_c, as_ent: [propext, Classical.choice, Quot.sound].

## Uncertainties / notes
- O-constants depend on p (not on the mass ratio only): uniformity (asymptotics_uniform_ratio) must be
  obtained in T19 by scaling/normalisation; these lemmas give no explicit constants.
- Relative errors kept as absolute errors; the blueprint's O(alpha^(5/2)) relative error of `a` is
  stated as absolute O(a^(7/2)).
- Public helper names all prefixed `p11cAe_` (grep-checked unique); no signature declarations changed.
- No errata found in the pinned source for these steps (blueprint's pi22 bound and c-sizes check out;
  blueprint numbering c1..c6 = Lean indices 0..5, A,B,p1..p6 = indices 0..7).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T18 (as_in/as_pi/as_c/as_ent; T4/T6/T12/T13) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean (no T18 signed declarations: each export must state its graph node's literal conclusion; check the asymptotic forms, exponents and the alpha -> 0+ filter against the SOURCE_CONCLUSION of each node in docs/graph/P/DEPGRAPH.md and the blueprint). Audit ONLY KAM/Planetary/PlanarTorsion/AsymptoticEntries.lean and AsymptoticEntries/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
