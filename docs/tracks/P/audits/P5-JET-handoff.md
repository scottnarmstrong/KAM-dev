# P5-JET prover handoff (branch inp-p5jet, ab33230; contains inp-p5ex (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all new, under KAM/Planetary/PGAssembly/)
Facade `Jets.lean` (102 lines): `birkhoff_ext`, `birkhoff_ext_parameter_regularity` (statements copied
verbatim from P45Signatures.lean), torsion-on-closure lemmas. Supporting modules (each <= 260 lines):
- `JetsPolar` (local chain rule `iteratedFDeriv_comp_clm_of_isOpen`; polarization `eq_zero_of_diag_of_symm`;
  `hasDerivAt_diag_line`)
- `JetsFourth` (`fourth_jet_unique` verbatim, from `fourth_jet_unique_gen` on a real normed space;
  one-variable step via `analyticOrderAt`)
- `JetsFamily` (iterated derivatives of a holomorphic family in a compact real parameter are jointly continuous)
- `JetsParam` (`holomorphic_parametric_integral_gen`: N `holomorphic_parametric_integral` transported along a CLE to a
  general finite-dim domain; it USES the N lemma)
- `JetsAverage` (`avgDom`, `avgFun`; holomorphy and joint (mu,I,x)-continuity of `complexAverage`)
- `JetsSlice` (partial jets of a jointly holomorphic function: holomorphic / continuous in I)
- `JetsDefs` (`jetP0`, `jetOmega`, `jetBeta`, `jetPolynomial`, `pgRemainder` as in the signature; only line-wrapped)
- `JetsReal` (complex jets at real vectors = real jets; complex multilinear map zero on real tuples is zero)
- `JetsPoly` (jets of the oscillator polynomial; mixed 4th entry via diagonal derivative trick)
- `JetsIdent` (on V: jets = P0/Omega/beta via HasSecularBirkhoffForm + fourth_jet_unique + hsymm)
- `JetsVanish` (remainder jets vanish for real I in V), `JetsRegular` (differentiability, joint continuity,
  symmetry of jetBeta, remainder jets vanish on the whole tube by `real_slice_identity` + `connected_complex_tube`).

## Nodes proved
- `fourth_jet_unique` (bpP:p5:be-coef): `KAM.Planetary.fourth_jet_unique` (JetsFourth).
- `jetP0/jetOmega/jetBeta/jetPolynomial`, `pgRemainder`: defs in JetsDefs.
- `birkhoff_ext` (bpP:p5:birkhoff-ext, steps be-coef/be-an/be-jet/be-det) and
  `birkhoff_ext_parameter_regularity` (F2): Jets.lean.

## Approach (brief)
Holomorphy/continuity of A(mu,I,x)=complexAverage: parametric integral + dominated convergence (bound MP).
Jets are slice derivatives at x=0; holomorphic in I (partial iterated derivative = iteratedFDeriv of F composed
with `inr`), jointly continuous in (mu,I) by a Cauchy-estimate family lemma. On V: real restriction of the
average is `secularAverage`; remainder is analytic and o(|y|^4) so real jets equal those of the Birkhoff
polynomial (fourth_jet_unique); diagonal jets by one-variable computation, the mixed beta_ij entry by
symmetry of the 4th jet and a second-derivative-along-a-line argument (uses hsymm). Complex jets at real
vectors = real jets; complex multilinear maps are determined by real tuples, so `iteratedFDeriv k pgRemainder = 0`
on V; identity theorem extends to the connected tube. beta symmetric on the tube by permutation symmetry
of the 4th derivative of the (complex-analytic) average. det bound on closure(V) by continuity.

## Checks
- Gate build: `inp_lake_build.sh /root/code/KAM-inp-p5jet KAM.Planetary.PGAssembly.Jets` -> "Build completed
  successfully (9112 jobs)"; no sorry/error; only linter warnings (unused simp args, unused binder names in the
  verbatim statements).
- `sh scripts/lint_sources.sh`: no forbidden patterns, 0 lines over 100 chars, check_lean_modules PASS,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only message is "KAM.lean is out of date; run
  scripts/gen_root_imports.py" (expected: new modules; KAM.lean not edited by me - orchestrator to regenerate).
- `#print axioms` of `birkhoff_ext`, `birkhoff_ext_parameter_regularity`, `fourth_jet_unique`:
  `[propext, Classical.choice, Quot.sound]`.
- No set_option maxHeartbeats / heartbeat overrides anywhere; all files < 270 lines.

## Uncertainties / deviations
- `jetBeta` and the verbatim defs were only wrapped over two lines (100-char lint); semantics unchanged.
- `JetsParam` re-applies the N lemma through a continuous linear equivalence rather than assuming `Fin q → ℂ`.
- The statement `birkhoff_ext` clause 4 (torsion on closure V) is proved by continuity, as designed.
- No suspected errata in pinned sources; design points confirmed: hBNF/hsymm needed exactly as designed
  (hsymm only for the mixed beta_ij entries; beta symmetry on the complex tube follows without it).
- No design signals (no heartbeat issues).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-JET, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements/definitions = design signatures (fourth_jet_unique, jetP0/Omega/Beta/Polynomial, birkhoff_ext, birkhoff_ext_parameter_regularity) with hBNF/hsymm exactly as designed; (2) proofs sound (N holomorphic_parametric_integral, P5-EX and P5-ID consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/Jets*.lean (compare with branch inp-p5ex).
