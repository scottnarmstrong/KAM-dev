# S8-W independent audit 1

Overall verdict: **PASS WITH NOTES**. The three source-facing results pass statement fidelity and proof review. The note is a literal module-style omission in the empty facade (N1 below), plus the explicit package/consumer boundary. No mathematical or axiom-closure defect was found.

Audited worktree: `/root/code/KAM-inp-s8w`; HEAD `59925ecc9f65bb05f02ab19e7a2da8d9ce70df52`; comparison `inp` = `31f0bfbf70c07b1eefd006237f331c00e003a0e5`; additional scoped comparison `inp-s8b` = `326288529ed59457294068ad2b05b5b9295b3099`. Date: 2026-10-28 UTC.

The user-specified report location overrides the generic brief's main-worktree destination. Only this report is changed by the auditor; transient probes and logs are confined to `.lake/abi-scratch/` and removed after recording evidence. No git mutation or production repair was performed.

## Authority, scope and verdicts

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the S8-W handoff, track-P statement, P810 design revision 2 and both design audits. Reconstructed the source contracts from `blueprint-P/parts/p8-secular-form.tex:29,160,231`, the design S8-W row at line 429, and its Appendix A. The untracked signature file is absent in this worktree; read the original `/root/code/KAM-inp/.drafts/design/P810Signatures.lean:609–616` and compared its theorem text with the production declaration. No draft was imported.

`git diff inp...HEAD` adds exactly the seven scoped Lean files (883 lines). `git diff inp-s8b...HEAD` globally includes unrelated upstream changes; restricting both comparisons to the seven assigned files produces byte-identical diffs. Those unrelated changes and S8-B are not audited again here.

| Source obligation | Export | Verdict | Boundary |
|---|---|---|---|
| bpP:p8:e-weyl | `KAM.Planetary.SecularForm.e_weyl` | PASS | Exact design signature; full O(2), all n including zero. |
| Quadratic invariant reduction within stepP:p8:qf-pair | `KAM.Planetary.SecularForm.Weyl.quadratic_invariant` | PASS | Three scalar invariants, homogeneous degree two, no additional hypothesis. |
| Six quartic invariant reduction within stepP:p8:q4-str | `KAM.Planetary.SecularForm.Weyl.quartic_invariant` | PASS | Six scalar invariants, homogeneous degree four, exact monomial order. |
| Homogeneous strengthening of e-weyl | `KAM.Planetary.SecularForm.Weyl.exists_homogeneous_dot_poly` | PASS | Produces a degree-k dot polynomial from degree-2k scaling. |

There is no provider or frozen theorem anchor in this package: provider/frozen type-equality and seal-body checks are N/A. This audit certifies infrastructure, not a frozen seal. Pair decomposition of the physical secular average, analyticity of coefficients, Taylor extraction, quantitative remainders and the full `quadratic_form`/`quartic` conclusions remain S8-Q/S8-4 work. Neither complete proof cut is closed just by its algebraic invariant reduction. The design specifies no separate exact quadratic/quartic helper signatures; their mathematical source clauses above are the fidelity authority.

## Binder and scope audit

All input aliases were expanded. `planeDot v w = ∑ k, v k*w k` and `planeSq v = ∑ k, v k^2` are the SEALED anchors `planetary.planeDot.v1` and `planetary.planeSq.v1`; current whole-file hashes match the manifest. No new instances, structures, bundled result assumptions or ambient norm changes occur.

| Export | Binder (outer to inner) | Bin | Authority |
|---|---|---|---|
| e_weyl | implicit n : ℕ | TYPING | Number of vectors, p8:29; exact signature. |
| e_weyl | P : MvPolynomial (Fin n × Fin 2) ℝ | TYPING | Real polynomial on all planar configurations. |
| e_weyl | hInv | SOURCE | p8:29 simultaneous O(2) invariance. |
| exists_homogeneous_dot_poly | implicit n : ℕ | TYPING | General finite number of vectors. |
| exists_homogeneous_dot_poly | P : MvPolynomial (Fin n × Fin 2) ℝ | TYPING | Same polynomial carrier. |
| exists_homogeneous_dot_poly | k : ℕ | TYPING | Homogeneous degree parameter. |
| exists_homogeneous_dot_poly | hInv | SOURCE | p8:29 invariant-theory premise. |
| exists_homogeneous_dot_poly | hscale | SOURCE | p8:231 homogeneous degree 2k; function-level formulation. |
| quadratic_invariant | P : MvPolynomial (Fin 2 × Fin 2) ℝ | TYPING | p8:160 pair of planar vectors. |
| quadratic_invariant | hP : P.IsHomogeneous 2 | SOURCE | p8:160 degree-two part. |
| quadratic_invariant | hInv | SOURCE | p8:160 O(2) invariant quadratic part. |
| quartic_invariant | P : MvPolynomial (Fin 2 × Fin 2) ℝ | TYPING | p8:231 pair of planar vectors. |
| quartic_invariant | hP : P.IsHomogeneous 4 | SOURCE | p8:231 degree-four part. |
| quartic_invariant | hInv | SOURCE | p8:231 O(2) invariant quartic part. |

Counts across these four exports: TYPING 7, SOURCE 7, STANDING 0, RULED 0, EXCESS 0. Each hInv expands to `∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose*R=1 → ∀ u, eval (R·u) P=eval u P`: R and u are universally quantified test data; orthogonality guards the tested action, not an extra assumption on P. hscale expands to `∀ r u, eval (r*u) P = r^(2*k)*eval u P`; r and u are universal test data. Homogeneity is Mathlib's actual supported-monomial degree predicate, with its scaling law proved by `eval_smul_of_isHomogeneous`.

The witnesses Q and c precede `∀ u`: one polynomial/coefficient vector works on the entire real configuration carrier. No positivity, distinctness, linear independence, nonzero-vector, dimension bound or preexisting dot representation is assumed. The generic scaling version permits even the zero polynomial and k=0 and is stronger than requiring syntactic homogeneous degree 2k. Internal helper premises describe their explicit algebraic subclaims (membership, balance, reflection or degree); the public e_weyl proof constructs each premise. They do not leak into the source theorem.

## Proof review

1. Coordinates: inverse complex substitution is proved by polynomial induction. Unit complex multiplication gives a real orthogonal matrix. Clearing Laurent powers is performed only at norm-one, hence nonzero, t. An infinite set of roots gives a polynomial identity; all exponents are bounded by 2N, so summing noncentral coefficient identities removes the entire unbalanced contribution. This needs only equality of evaluated sums at real configurations, which is exactly what the later proof uses; it does not assert unsupported coefficientwise cancellation of individual monomials.
2. Balanced generators: simultaneous induction on equal z/w degree removes two distinct Boolean-tagged coordinates, with truncation justified by positive exponents. Every balanced monomial belongs to the algebra generated by z_j w_k. Complex constant coefficients are handled in the real/imaginary adjoin induction.
3. Reflection: Binet–Cauchy puts products of cross terms in the dot algebra. Thus real parts lie in sums of an even dot-algebra term and a finite dot-linear cross combination. Reflection fixes the first, negates the second, and full O(2) invariance forces the second to vanish over ℝ. This proves dot-algebra membership before extracting the existential Q by the range-of-aeval theorem.
4. Homogeneity: decompose an arbitrary Q0 into homogeneous components, apply the source scaling to r*u, and compare the r^(2k) coefficient of a univariate polynomial identity. The branch k>totalDegree proves both sides vanish; it does not silently replace P by a zero object.
5. Two vectors: the four ordered dot variables become |u|², |v|² and two equal off-diagonal values. Support degree is a+d+e. Enumeration of the three degree-one and six degree-two triples proves span membership. The finite-span theorem yields coefficients independent of u. No unsupported uniqueness of a dot representation is needed or claimed.

## Declaration ledger

All exports below are under `KAM.Planetary.SecularForm`; prefix `Weyl.` applies except to `e_weyl`. Locators abbreviate `KAM/Planetary/SecularForm/InvariantPolynomial/`. Every row is a separately inspected public declaration (44 theorems and 21 literal definitions/abbreviations); helper rows implement cuts within e-weyl unless marked quadratic/quartic.

| Node | Declaration and locator | Verdict | Reason / definition classification |
|---|---|---|---|
| bpP:p8:e-weyl / helper | `Weyl.degT` (Balanced.lean:28) | PASS | Literal sum of true-tag exponents (z-degree). |
| bpP:p8:e-weyl / helper | `Weyl.degF` (Balanced.lean:31) | PASS | Literal sum of false-tag exponents (w-degree). |
| bpP:p8:e-weyl / helper | `Weyl.balancedPart` (Balanced.lean:34) | PASS | Literal finite sum of equal-degree monomials; genuine projection, not a fallback. |
| bpP:p8:e-weyl / helper | `Weyl.degT_add_degF` (Balanced.lean:37) | PASS | Total exponent count split over the two Boolean tags. |
| bpP:p8:e-weyl / helper | `Weyl.zwScale` (Balanced.lean:42) | PASS | Literal (tz,t⁻¹w) substitution; globally defined, used on units for rotations. |
| bpP:p8:e-weyl / helper | `Weyl.prod_zwScale` (Balanced.lean:45) | PASS | Finite-product factorization for every t, including zero; no cancellation assumed. |
| bpP:p8:e-weyl / helper | `Weyl.zw_rot_eq` (Balanced.lean:58) | PASS | Unit norm proves conjugate t equals t⁻¹. |
| bpP:p8:e-weyl / helper | `Weyl.eval_zwScale` (Balanced.lean:66) | PASS | Evaluation expands into the literal finite Laurent-type sum. |
| bpP:p8:e-weyl / helper | `Weyl.eval_zwScale_one` (Balanced.lean:73) | PASS | Unscaled evaluation expansion. |
| bpP:p8:e-weyl / helper | `Weyl.eval_balancedPart` (Balanced.lean:77) | PASS | Evaluation of the actual filtered monomial sum. |
| bpP:p8:e-weyl / helper | `Weyl.eval_balancedPart_toZW` (Balanced.lean:85) | PASS | Orthogonal invariance supplies rotations; infinite-root lemma removes the unbalanced sum at every real point. |
| bpP:p8:e-weyl / helper | `Weyl.infinite_unit_circle` (Coordinates.lean:29) | PASS | Injective arc of the unit circle from the nonempty real interval (0,1). |
| bpP:p8:e-weyl / helper | `Weyl.sum_unbalanced_eq_zero` (Coordinates.lean:44) | PASS | Clear negative powers at units, polynomial infinite-root identity, compare all noncentral coefficients. |
| bpP:p8:e-weyl / helper | `Weyl.zw` (Coordinates.lean:102) | PASS | Literal x+iy and x−iy; Boolean branches exhaust exactly the two intended coordinates. |
| bpP:p8:e-weyl / helper | `Weyl.toZW` (Coordinates.lean:106) | PASS | Literal inverse substitution x=(z+w)/2, y=−i(z−w)/2; finite coordinate carrier exhausts 0,1. |
| bpP:p8:e-weyl / helper | `Weyl.eval_toZW` (Coordinates.lean:111) | PASS | Polynomial induction proves exact inverse-substitution evaluation. |
| bpP:p8:e-weyl / helper | `Weyl.rotMat` (Coordinates.lean:125) | PASS | Literal real complex-multiplication matrix, defined for all complex t. |
| bpP:p8:e-weyl / helper | `Weyl.rotMat_orth` (Coordinates.lean:127) | PASS | Unit norm gives the sum-of-squares identity needed for orthogonality. |
| bpP:p8:e-weyl / helper | `Weyl.zw_rot` (Coordinates.lean:135) | PASS | Direct complex coordinate computation; no unit premise needed. |
| bpP:p8:e-weyl / helper | `Weyl.Pt` (Generators.lean:30) | PASS | Transparent type alias Fin n → Fin 2 → ℝ; no altered norm or carrier. |
| bpP:p8:e-weyl / helper | `Weyl.dotFn` (Generators.lean:33) | PASS | Literal frozen planeDot evaluated at the indexed vectors. |
| bpP:p8:e-weyl / helper | `Weyl.crossFn` (Generators.lean:36) | PASS | Literal signed determinant y_j x_k−x_j y_k; sign is consistent throughout. |
| bpP:p8:e-weyl / helper | `Weyl.mFn` (Generators.lean:39) | PASS | Literal z_j w_k. |
| bpP:p8:e-weyl / helper | `Weyl.mFn_re` (Generators.lean:41) | PASS | Real part equals the dot product. |
| bpP:p8:e-weyl / helper | `Weyl.mFn_im` (Generators.lean:44) | PASS | Imaginary part equals the chosen signed cross product. |
| bpP:p8:e-weyl / helper | `Weyl.cross_mul_cross` (Generators.lean:47) | PASS | Binet–Cauchy polynomial identity verified by ring. |
| bpP:p8:e-weyl / helper | `Weyl.cAlg` (Generators.lean:54) | PASS | Literal complex algebra adjoined from all z_j w_k functions. |
| bpP:p8:e-weyl / helper | `Weyl.balanced_mem` (Generators.lean:57) | PASS | Induction removes one z and one w exponent; handles N=0 and empty n without nonemptiness assumptions. |
| bpP:p8:e-weyl / helper | `Weyl.balancedPart_mem` (Generators.lean:117) | PASS | Finite linear combination of balanced monomials, using balanced_mem. |
| bpP:p8:e-weyl / helper | `Weyl.dAlg` (Generators.lean:133) | PASS | Literal real algebra adjoined from all dot-product functions. |
| bpP:p8:e-weyl / helper | `Weyl.IsOdd` (Generators.lean:137) | PASS | Literal finite dAlg-linear span of signed cross products; auxiliary predicate, not a source premise. |
| bpP:p8:e-weyl / helper | `Weyl.isOdd_zero` (Generators.lean:141) | PASS | Zero coefficients construct the zero span element. |
| bpP:p8:e-weyl / helper | `Weyl.IsOdd.add` (Generators.lean:144) | PASS | Add actual coefficient families. |
| bpP:p8:e-weyl / helper | `Weyl.IsOdd.mul_left` (Generators.lean:150) | PASS | Multiply actual coefficient families by a dot-algebra element. |
| bpP:p8:e-weyl / helper | `Weyl.isOdd_cross` (Generators.lean:155) | PASS | Kronecker coefficient family represents a single cross product. |
| bpP:p8:e-weyl / helper | `Weyl.IsOdd.mul_odd` (Generators.lean:169) | PASS | Expand both finite sums and use Binet–Cauchy to return to dAlg. |
| bpP:p8:e-weyl / helper | `Weyl.sAlg` (Generators.lean:184) | PASS | Literal sums e+v with e∈dAlg and v in the cross-product span; algebra laws proved in its body. |
| bpP:p8:e-weyl / helper | `Weyl.dAlg_le_sAlg` (Generators.lean:195) | PASS | Construct odd component zero. |
| bpP:p8:e-weyl / helper | `Weyl.dotFn_mem_sAlg` (Generators.lean:197) | PASS | Adjoined dot generator included via dAlg_le_sAlg. |
| bpP:p8:e-weyl / helper | `Weyl.crossFn_mem_sAlg` (Generators.lean:200) | PASS | Construct even component zero and explicit odd generator. |
| bpP:p8:e-weyl / helper | `Weyl.re_im_mem_sAlg` (Generators.lean:204) | PASS | Adjoin induction handles complex constants, sums and products without real-coefficient restrictions. |
| homogeneous strengthening | `Weyl.eval_smul_of_isHomogeneous` (Homogeneous.lean:28) | PASS | Each supported monomial has exactly the declared total degree. |
| homogeneous strengthening | `Weyl.exists_homogeneous_dot_poly` (Homogeneous.lean:43) | PASS | Project any dot representation to degree k and compare r^(2k) coefficients; also treats k above totalDegree. |
| qf-pair / q4-str algebra | `Weyl.quadraticTerms` (TwoVectors.lean:27) | PASS | Literal ordered three-vector (|u|², |v|², u·v). |
| qf-pair / q4-str algebra | `Weyl.quarticTerms` (TwoVectors.lean:31) | PASS | Literal six-vector in the exact design quarticMonomials order; rfl probe passed. |
| qf-pair / q4-str algebra | `Weyl.planeDot_self` (TwoVectors.lean:35) | PASS | Frozen scalar-product and squared-length formulas agree on the diagonal. |
| qf-pair / q4-str algebra | `Weyl.planeDot_comm` (TwoVectors.lean:38) | PASS | Symmetry of the literal scalar-product formula. |
| qf-pair / q4-str algebra | `Weyl.eval_dots_eq` (TwoVectors.lean:42) | PASS | Evaluate all four ordered dot variables, combine the equal off-diagonal terms. |
| qf-pair / q4-str algebra | `Weyl.sum_degree_eq` (TwoVectors.lean:54) | PASS | Homogeneous support degree becomes a+d+e=D after combining off-diagonal exponents. |
| qf-pair / q4-str algebra | `Weyl.quadraticSpan` (TwoVectors.lean:64) | PASS | Literal real linear span of the three quadratic functions. |
| qf-pair / q4-str algebra | `Weyl.quarticSpan` (TwoVectors.lean:69) | PASS | Literal real linear span of the six quartic functions. |
| qf-pair / q4-str algebra | `Weyl.quadratic_monomial_mem` (TwoVectors.lean:73) | PASS | Exhaust all three nonnegative triples summing to one. |
| qf-pair / q4-str algebra | `Weyl.quartic_monomial_mem` (TwoVectors.lean:82) | PASS | Exhaust all six nonnegative triples summing to two. |
| qf-pair / q4-str algebra | `Weyl.quadratic_invariant` (TwoVectors.lean:98) | PASS | Exactly invariant homogeneous quadratics; coefficients chosen before all configurations, no extra premise. |
| qf-pair / q4-str algebra | `Weyl.quartic_invariant` (TwoVectors.lean:126) | PASS | Exactly invariant homogeneous quartics; all six terms, coefficients chosen before all configurations. |
| bpP:p8:e-weyl / helper | `Weyl.refl` (Weyl.lean:30) | PASS | Literal diag(1,−1). |
| bpP:p8:e-weyl / helper | `Weyl.refl_orth` (Weyl.lean:32) | PASS | Direct verification of RᵀR=1. |
| bpP:p8:e-weyl / helper | `Weyl.reflPt` (Weyl.lean:37) | PASS | Literal blockwise reflection on the full configuration carrier. |
| bpP:p8:e-weyl / helper | `Weyl.dot_reflPt` (Weyl.lean:39) | PASS | Reflection fixes every dot generator. |
| bpP:p8:e-weyl / helper | `Weyl.cross_reflPt` (Weyl.lean:42) | PASS | Reflection negates every signed cross generator. |
| bpP:p8:e-weyl / helper | `Weyl.reflPt_dAlg` (Weyl.lean:45) | PASS | Adjoin induction extends invariance from generators to all dot-algebra elements. |
| bpP:p8:e-weyl / helper | `Weyl.reflPt_odd` (Weyl.lean:52) | PASS | The explicit coefficient representation is odd under reflection. |
| bpP:p8:e-weyl / helper | `Weyl.mem_dAlg_of_refl` (Weyl.lean:57) | PASS | Reflect decomposition, derive odd component zero over ℝ, retain the actual even component. |
| bpP:p8:e-weyl / helper | `Weyl.aeval_apply_pi` (Weyl.lean:69) | PASS | Polynomial induction identifies algebra-map evaluation with pointwise real evaluation. |
| bpP:p8:e-weyl | `e_weyl` (Weyl.lean:82) | PASS | Exact original design signature, text equality and fresh exact-type probe; representation proved, never assumed. |

For each of the 21 definition/abbreviation rows independently: BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS. No new structure is declared. Subalgebra/submodule constructions and span predicates are literal auxiliary objects, not selected canonical witnesses. No new definition uses Classical.choose or an unproved existence premise. The if-branches in zw, toZW and zwScale implement exhaustive coordinate tags; they are not off-domain replacements. Complex inversion at zero is ordinary total field arithmetic in zwScale and is never used as a rotation inverse at zero.

## Independent checks

All auditor-controlled Lean/Lake/replay processes were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. Lint was run after replay because its ABI check itself invokes Lean. The compile gate waited for a free slot normally.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8w KAM.Planetary.SecularForm.InvariantPolynomial
   [inp-gate] slot 2 acquired 12:49:23 for KAM.Planetary.SecularForm.InvariantPolynomial
   Build completed successfully (9058 jobs).
   exit 0
   ```

2. Fresh probe `.lake/abi-scratch/S8WAudit.lean`:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8WAudit.lean
   exit 0; no errors or warnings
   44 #print axioms outputs; every row: [propext, Classical.choice, Quot.sound]
   ```

   The probe copies the exact original e_weyl statement under a fresh name and applies `SecularForm.e_weyl P hInv`; its type text is independently identical to production. It checks `designQuartic u v = Weyl.quarticTerms u v` by `rfl`, using the literal design formula, and composes `quadratic_invariant P hP hInv` into the explicit three-term scalar formula with `Fin.sum_univ_three`. Thus the facade exports the actual results and the coefficient conventions are consumable. All 44 theorem names in the ledger were included in the axiom probe, not only the four principal exports. Exact output follows:

```text
'KAM.Planetary.SecularForm.Weyl.degT_add_degF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.prod_zwScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.zw_rot_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_zwScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_zwScale_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_balancedPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_balancedPart_toZW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.infinite_unit_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.sum_unbalanced_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_toZW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.rotMat_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.zw_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.mFn_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.mFn_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.cross_mul_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.balanced_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.balancedPart_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.isOdd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.IsOdd.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.IsOdd.mul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.isOdd_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.IsOdd.mul_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.dAlg_le_sAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.dotFn_mem_sAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.crossFn_mem_sAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.re_im_mem_sAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_smul_of_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.exists_homogeneous_dot_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.planeDot_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.planeDot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.eval_dots_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.sum_degree_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.quadratic_monomial_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.quartic_monomial_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.quadratic_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.quartic_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.refl_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.dot_reflPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.cross_reflPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.reflPt_dAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.reflPt_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.mem_dAlg_of_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Weyl.aeval_apply_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.e_weyl' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

   ```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.InvariantPolynomial KAM.Planetary.SecularForm.InvariantPolynomial.Coordinates KAM.Planetary.SecularForm.InvariantPolynomial.Balanced KAM.Planetary.SecularForm.InvariantPolynomial.Generators KAM.Planetary.SecularForm.InvariantPolynomial.Weyl KAM.Planetary.SecularForm.InvariantPolynomial.Homogeneous KAM.Planetary.SecularForm.InvariantPolynomial.TwoVectors
replaying KAM.Planetary.SecularForm.InvariantPolynomial.TwoVectors
replaying KAM.Planetary.SecularForm.InvariantPolynomial.Weyl
replaying KAM.Planetary.SecularForm.InvariantPolynomial.Generators
replaying KAM.Planetary.SecularForm.InvariantPolynomial.Homogeneous
replaying KAM.Planetary.SecularForm.InvariantPolynomial.Coordinates
replaying KAM.Planetary.SecularForm.InvariantPolynomial.Balanced
replaying KAM.Planetary.SecularForm.InvariantPolynomial
   exit 0
   ```

   One invocation replayed all seven assigned modules.

4. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (558 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failing condition is the stale generated `KAM.lean`, explicitly permitted by the assigned audit brief. Module checking, frozen-anchor guard and all 144 elaborated ABI hashes pass. The generated root was not edited or regenerated. N1 is a separate manual style finding that this lint does not detect.

5. Static checks:

   ```text
   git diff --check inp...HEAD
   exit 0; no output
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   exit 0; empty (0 bytes)
   rg -n '\b(sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace)\b' KAM/Planetary/SecularForm/InvariantPolynomial.lean KAM/Planetary/SecularForm/InvariantPolynomial
   exit 1; no matches
   ```

   Source line totals: facade 17; Coordinates 145; Balanced 116; Generators 231; Weyl 109; Homogeneous 111; TwoVectors 154; total 883. No size cap is approached. All seven have copyright, module, public imports and module documentation; the six declaration-bearing modules have `@[expose] public noncomputable section`. The facade omission is separately recorded below. No provider or frozen theorem imports occur, directly or through the project import closure; project dependencies terminate in frozen Defs, whose relevant states/hashes were verified.

## Findings, errata and remaining scope

**N1 — low, literal style deviation.** `KAM/Planetary/SecularForm/InvariantPolynomial.lean:6–17` contains `module`, its public import and module documentation, but no `public section`. AGENTS.md rule 3 says “Every `.lean` file is a Lean module: copyright comment, `module`, imports (`public import` for the interface), module docstring, `public section`.” The facade contains no declarations, so this omission has no export or proof effect; module lint checks module headers and does not enforce this part of the literal rule. Suggested owner-side cleanup: append an empty `public section` after the docstring. This auditor did not edit production code. The package receives PASS WITH NOTES rather than an unqualified hygiene PASS.

**N2 — scope note.** S8-W supplies the invariant reductions, not pair decomposition, analytic coefficient extraction or all of the surrounding source proof cuts. No downstream implementation or frozen-root closure is asserted. The design's S8-B input is unnecessary for this proof: the package imports only Mathlib and the original frozen scalar-product/length definitions. This is a dependency reduction, not a substituted object.

**Source errata:** no new suspected blueprint or pinned-source defect was found in the assigned algebraic statements. The broader CP11 coefficient errata mentioned elsewhere in p8 are outside this audit; they are neither repaired nor revalidated here. No mathematical deviation was introduced. Existing untracked `docs/tracks/P/audits/S8-W-handoff.md` was present at audit start and preserved.

Final report validation: all 65 declaration rows and all 44 exact axiom receipts present; no pending checks or trailing whitespace. Auditor scratch files removed. Only this report is newly written; the preexisting handoff is preserved.
