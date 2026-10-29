# T7 independent package audit 1

Audit date: 2026-10-28. **Overall verdict: PASS WITH NOTES.** All four signed exports and all assigned T7 graph obligations pass. Notes are limited to non-fatal build warnings and the explicitly permitted stale generated root in lint; no blocking finding was confirmed.

Scope is exactly `KAM/Planetary/PlanarTorsion/Characters.lean` and `Characters/*.lean` in
`/root/code/KAM-inp-p11c-t7`. The explicit user report destination overrides the generic brief's
main-worktree destination. Only this report is a lasting auditor edit; temporary probes/logs are
under this worktree's `.lake/abi-scratch/` and are removed after their receipts are copied below.
No source repairs, git mutations, generated-root refresh, frozen edits, or manifest edits were made.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief, T7-handoff.md including
AUDIT FOCUS, P11C-LEAN-DESIGN.md, DESIGN-P11C-design-audit-1.md, P11CSignatures.lean,
blueprint-P/parts/p11b-planar-torsion.tex, the relevant P-p11b graph records and consumers, the
track-P statement, and the actual frozen Phase/oscillatorAction/hamiltonianVectorField definitions.

Inspected HEAD: `a7c0963c945c6fee75ed7a7f0a3dc7e46cbd190f`.
Comparison `inp` at inspection: `b6dab3a6fc8453330a4abaa465a782e1aa713798`;
merge base: `d9183adae208ecf2e726620694b69c8168e33006`.
`git diff inp...HEAD` contains precisely nine added modules, 1,203 lines. No other package is audited.

Input SHA-256 values:

| Input | SHA-256 |
|---|---|
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| /root/code/KAM-inp/.drafts/design/P11CSignatures.lean | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| blueprint-P/parts/p11b-planar-torsion.tex | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |

## Frozen-anchor boundary and signed exports

There is **no frozen anchor or provider in T7**. Thus provider/frozen type equality and a proposed
frozen seal-body probe are not applicable; this audit gives no frozen-seal or campaign-theorem
closure. The four signed helper exports, rather than frozen theorems, are the package's targets.
All nine signed definitions/structures have the exact original signature bodies after whitespace
normalization. The four theorem headers likewise match exactly, including binder order,
quantifiers, carriers and conclusions. A fresh Lean probe copies each literal signed statement
under `example` and closes it with the corresponding production theorem:

```lean
-- Each full header/conclusion was copied literally from P11CSignatures.lean.
-- The four corresponding bodies are:
by exact char F
by exact character_polynomial F k
by exact character_bracket F freq I k z
by exact average_action_polynomial F
```

That probe elaborated at default heartbeats, exit 0, with no warnings/errors. None of the
signature file's `sorry` bodies was imported or copied into a proof. All new public theorems
and lemmas were separately queried for axioms in the same probe.

| Signed target | Verdict | Assessment |
|---|---|---|
| KAM.Planetary.char | PASS | Covariance, l1 support, HasSum reconstruction, reality: exact signed four clauses. |
| KAM.Planetary.character_polynomial | PASS | Analytic dependence, concrete polynomial of degree ≤4, homogeneity, real quartic average witness: exact. |
| KAM.Planetary.character_bracket | PASS | Exact derivative along the frozen vector field, with positive i(k·Ω). |
| KAM.Planetary.average_action_polynomial | PASS | Exact existential analytic real action coefficients on O. |

## Graph completeness, proof review and consumer applicability

The design node table at lines 87 and 108–111 assigns five records at least partly to T7.
Every assigned obligation is accounted for; no unsigned export masquerades as a literal graph
node while assuming its conclusion.

| Node | Establishing declarations / proof fragments | Verdict | Reason |
|---|---|---|---|
| bpP:p11b:e-ca (shared T2/T4/T7) | charAlg1/2, charQc_eval, charG_expand, charQcoef and quartic_of_actions | PASS for T7 | Exact finite ring/degree computations; this is a proof method, not an assumed CAS certificate. The other packages' orbital/physical identities remain outside this audit. |
| bpP:p11b:sec-bnf#data (T1/T7) | QuarticFamily, eval, p11c_rotation/NR4/n0/bracket; hamiltonian_n0, rotation_hasDerivAt | PASS | All T7 data present here, including NR4/n0/bracket absent from Setting; actual frozen action and vector-field conventions. |
| bpP:p11b:char | char, character_polynomial, character_bracket, average_action_polynomial | PASS | Together they establish every clause at blueprint lines 126–128 and the action-polynomial consequence used at line 157. |
| stepP:p11b:ch-mon | charG_expand, charInt_ne/zero, charFc_eq, charBox, character_eq_sum, charFc_sum, character_support/covariance | PASS | Explicit polynomial factorization proves the monomial/orthogonality/support/reconstruction/covariance step, without assuming a Fourier theorem or coefficient formula. |
| stepP:p11b:ch-bra | char's conjugation clause; character_differentiable, hamiltonian_n0, rotation_hasDerivAt, character_bracket | PASS | Conjugation of the actual integral and chain rule along explicit rotations; differentiability is proved from the constructed polynomial. |

Per plane, Q(E)=charUP^p charVP^q and E^(p+q)G=Q(E) give mode n-(p+q);
0≤n≤2(p+q) forces |k|≤p+q. The two plane degrees sum to four, giving the required l1 bound,
not merely a coordinatewise box bound. Compact-box continuity justifies exchanging the finite
sum with the original integral; the restricted Pi measure proves factorization. Reconstruction
sums a finite box containing the support and evaluates the one-plane polynomial at E=1.
This realizes the labelled proof fragment via an explicit coefficient construction rather than
introducing a new unsigned statement under a graph-node name.

The rotation is (cos θ x+sin θ y, -sin θ x+cos θ y); its derivative is (Ω y,-Ω x).
The negative Fourier exponent therefore yields positive character covariance and the signed
+i(k·Ω) bracket. The frequency need not be analytic or nonresonant for this pointwise bracket
identity: dropping those unused standing premises strengthens it, exactly as approved in the
signatures. Openness of O is likewise unnecessary for these coefficientwise statements.

The polynomial witness is in the four real coordinates complexified; these coordinates are
linear combinations of z and conjugate z, so the carrier matches the blueprint polynomial claim.
Its coefficients are finite linear combinations of analytic F.coeff with parameter-independent
complex constants. `character_polynomial` proves the exact approved interface, while the explicit
construction in character_mv/charFcPoly supplies the coefficient dependence. The zero mode is
real by reality at k=0 and is rotation-invariant; odd plane degree vanishes, and the remaining
plane degrees are 4+0, 2+2, 0+4. Factors four and the 1/4,1/2 coefficients in charQcoef account
for frozen R=(x²+y²)/2. The real quartic average witness is constructed, not assumed.

Consumers checked: blueprint homological steps ho-def/ho-eq (lines 135–141), the averaged-action
use in lie (line 157), and the beta-formula averaging use (lines 195–202), together with the
corresponding design/signature interfaces. They receive finite support, reality, covariance,
analytic quartic structure, the bracket identity and the action-polynomial average they need.
No chart, physical jet identification, homological solution, nonresonance proof, or flow theorem
owned by another package is claimed to follow from T7.

## Definition classification

There are 25 explicit definitions and one structure (no new abbrev). All bodies are concrete on
their whole declared carrier; there is no choice-of-solution fallback or junk-value branch.

- Signed source data: p11c_monomial, QuarticFamily and QuarticFamily.eval; only genuine coefficient
  functions and their source analyticity are bundled. The unused exponent coefficients are harmless:
  eval uses all and only degree-four exponent vectors, bounded by four in every coordinate.
- Signed canonical/integral adapters: p11c_rotation, p11c_character, p11c_average, p11c_NR4,
  p11c_n0, p11c_bracket. General Bochner integrals and fderiv are total Lean operations, but the
  character identities here prove the required continuity/integrability/differentiability for the
  actual quartic family; they do not exploit an undefined-integral or nonsmooth fallback.
- Exact auxiliary algebra: charG, charW, charWb, charUP, charVP, charQ, charQc, charIdx,
  CoeffDeg, charFcPoly. These are finite polynomials, their actual evaluations, the original finite
  exponent set, or an explicit degree predicate.
- Auxiliary integral/average coefficients: charFc, charK, charLam, charAvgA/B/C and charQcoef.
  The parity and exponent-selector branches are literal exact coefficients; zero branches reflect
  proved vanishing modes or absent monomials, not discarded physical data.

The next table includes every explicit new public declaration (88 rows). Structure-generated
constructor/projections are covered with QuarticFamily. Namespace-qualified CoeffDeg.one/mul
are predicate lemmas; they introduce no global instances and do not shadow root declarations.
Node labels abbreviate bpP:p11b or stepP:p11b as appropriate.

| Node | Lean declaration and locator under Characters/ | Verdict | Reason / definition classification |
|---|---|---|---|
| char (polynomial/average) | `KAM.Planetary.PlanarCharacters.charK` (Average.lean:27) | PASS | Concrete unit-axis zero mode, all natural exponents. |
| char (polynomial/average) | `KAM.Planetary.PlanarCharacters.charFc_zero_radial` (Average.lean:29) | PASS | Rotation covariance and homogeneity; includes the zero vector. |
| char (polynomial/average) | `KAM.Planetary.PlanarCharacters.charK_odd` (Average.lean:49) | PASS | Half-turn and odd parity force the zero mode to vanish. |
| char (polynomial/average) | `KAM.Planetary.PlanarCharacters.charFc_zero_odd` (Average.lean:61) | PASS | Odd-degree radial zero mode is zero. |
| char (polynomial/average) | `KAM.Planetary.PlanarCharacters.charFc_zero_even` (Average.lean:64) | PASS | Even-degree radial zero mode equals the stated power of x²+y². |
| char (polynomial/average) | `KAM.Planetary.charLam` (Average.lean:78) | PASS | Parity-guarded real product of the two unit-axis zero modes. |
| char (polynomial/average) | `KAM.Planetary.charAvg_term` (Average.lean:83) | PASS | Exhausts plane degrees 4,2,0; uses frozen half-square actions. |
| char (polynomial/average) | `KAM.Planetary.charAvgA` (Average.lean:116) | PASS | Finite coefficient sum of J0², with the factor four. |
| char (polynomial/average) | `KAM.Planetary.charAvgB` (Average.lean:121) | PASS | Finite coefficient sum of J0 J1, with the factor four. |
| char (polynomial/average) | `KAM.Planetary.charAvgC` (Average.lean:126) | PASS | Finite coefficient sum of J1², with the factor four. |
| char (polynomial/average) | `KAM.Planetary.charIte_analytic` (Average.lean:130) | PASS | Parameter-independent branch; scalar multiple of the source analytic function. |
| char (polynomial/average) | `KAM.Planetary.charAvgA_analytic` (Average.lean:136) | PASS | Finite sum of analytic source coefficients. |
| char (polynomial/average) | `KAM.Planetary.charAvgB_analytic` (Average.lean:140) | PASS | Finite sum of analytic source coefficients. |
| char (polynomial/average) | `KAM.Planetary.charAvgC_analytic` (Average.lean:144) | PASS | Finite sum of analytic source coefficients. |
| char (polynomial/average) | `KAM.Planetary.average_formula` (Average.lean:149) | PASS | Explicit action-polynomial identity holds for every I, including outside O. |
| char (polynomial/average) | `KAM.Planetary.average_action_polynomial` (Average.lean:163) | PASS | Signed statement exactly; analytic real coefficients on O. |
| ch-mon / char | `KAM.Planetary.charIdx_sum` (Basic.lean:27) | PASS | Degree-four membership gives the exact sum of plane degrees. |
| ch-mon / char | `KAM.Planetary.sum_piFinset_two` (Basic.lean:32) | PASS | General finite product-sum identity, with no analytic premise. |
| ch-mon / char | `KAM.Planetary.character_support` (Basic.lean:38) | PASS | Exact l1 support bound four, on the original character integral. |
| ch-mon / char | `KAM.Planetary.character_covariance` (Basic.lean:53) | PASS | Positive exponential sign matches the negative-angle rotation. |
| ch-mon / char | `KAM.Planetary.char` (Basic.lean:67) | PASS | All four signed clauses exactly, without openness or NR4 premises. |
| ch-bra / char | `KAM.Planetary.mv_eval_differentiable` (Bracket.lean:28) | PASS | Polynomial induction proves real differentiability on the whole phase carrier. |
| ch-bra / char | `KAM.Planetary.character_differentiable` (Bracket.lean:48) | PASS | Concrete polynomial representation supplies differentiability; none assumed. |
| ch-bra / char | `KAM.Planetary.n0_fderiv_apply` (Bracket.lean:56) | PASS | Derivative of the frozen half-square action; no factor two lost. |
| ch-bra / char | `KAM.Planetary.hamiltonian_n0` (Bracket.lean:77) | PASS | Frozen vector field gives (Ω y, -Ω x). |
| ch-bra / char | `KAM.Planetary.rotation_hasDerivAt` (Bracket.lean:89) | PASS | Derivative of the explicit rotation at zero, used by the chain rule. |
| ch-bra / char | `KAM.Planetary.character_bracket` (Bracket.lean:106) | PASS | Signed statement exactly; +i(k·Ω) and arbitrary parameter frequency. |
| char (polynomial/average) | `KAM.Planetary.charIdx_single` (CharPoly.lean:29) | PASS | Injectivity of bounded exponent vectors justifies finite coefficient selection. |
| char (polynomial/average) | `KAM.Planetary.charQcoef` (CharPoly.lean:42) | PASS | Ten explicit quartic monomials of a J0²+b J0 J1+c J1². |
| char (polynomial/average) | `KAM.Planetary.charQcoef_analytic` (CharPoly.lean:49) | PASS | Finite parameter-independent coefficient selectors preserve analyticity. |
| char (polynomial/average) | `KAM.Planetary.charIdx_mem` (CharPoly.lean:65) | PASS | Concrete degree sum implies membership in the original exponent set. |
| char (polynomial/average) | `KAM.Planetary.quartic_of_actions` (CharPoly.lean:70) | PASS | Constructs an actual QuarticFamily witness, valid for all I and z. |
| char (polynomial/average) | `KAM.Planetary.character_mv` (CharPoly.lean:107) | PASS | Constructs an actual four-variable polynomial and proves degree ≤4. |
| char (polynomial/average) | `KAM.Planetary.character_homog` (CharPoly.lean:136) | PASS | Degree exactly four in the scaling identity, including t=0. |
| char (polynomial/average) | `KAM.Planetary.character_polynomial` (CharPoly.lean:151) | PASS | All four signed clauses exactly; real quartic average witness constructed. |
| sec-bnf#data / char | `KAM.Planetary.p11c_monomial` (Defs.lean:31) | PASS | Exact signed real monomial in (x0,y0,x1,y1). |
| sec-bnf#data / char | `KAM.Planetary.QuarticFamily` (Defs.lean:34) | PASS | Exact signed source coefficient data and analyticity; no output fields. |
| sec-bnf#data / char | `KAM.Planetary.QuarticFamily.eval` (Defs.lean:38) | PASS | Exact signed finite sum of all degree-four monomials. |
| sec-bnf#data / char | `KAM.Planetary.p11c_rotation` (Defs.lean:43) | PASS | Exact signed negative-angle rotations on each canonical plane. |
| sec-bnf#data / char | `KAM.Planetary.p11c_character` (Defs.lean:46) | PASS | Exact signed normalized box integral and negative Fourier exponent. |
| sec-bnf#data / char | `KAM.Planetary.p11c_average` (Defs.lean:50) | PASS | Exact signed real part of the zero character. |
| sec-bnf#data / char | `KAM.Planetary.p11c_NR4` (Defs.lean:53) | PASS | Exact signed nonzero divisors for all nonzero l1 modes ≤4. |
| sec-bnf#data / char | `KAM.Planetary.p11c_n0` (Defs.lean:56) | PASS | Exact signed sum of frequencies times frozen oscillator actions. |
| sec-bnf#data / char | `KAM.Planetary.p11c_bracket` (Defs.lean:59) | PASS | Exact signed derivative in the frozen Hamiltonian vector field. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc_eq_zero_of_lt` (Factor.lean:26) | PASS | One-plane support bounded by p+q, with no restriction on x,y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG_zero` (Factor.lean:35) | PASS | Rotated monomial at angle zero recovers x^p y^q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc_sum` (Factor.lean:39) | PASS | Finite reconstruction in any box D≥p+q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG_rot` (Factor.lean:57) | PASS | Explicit rotation composition via sine/cosine addition. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG_smul` (Factor.lean:63) | PASS | Exact degree p+q homogeneity, all real t. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG_period` (Factor.lean:70) | PASS | Full 2π periodicity of the rotated monomial. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc_smul` (Factor.lean:74) | PASS | Exact homogeneity passes through the original Fourier integral. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc_rot` (Factor.lean:85) | PASS | Periodic integral shift proves covariance; no chosen angle restriction. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charBox_integral` (Factor.lean:115) | PASS | Pi restricted measure and finite product integral; no assumed Fubini result. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charBox` (Factor.lean:125) | PASS | Normalized two-plane monomial integral factors into one-plane coefficients. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charMono_continuous` (Factor.lean:149) | PASS | Polynomial/trigonometric continuity supplies compact-box integrability. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charIdx` (Factor.lean:155) | PASS | Same bounded degree-four exponent filter as QuarticFamily.eval. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.character_eq_sum` (Factor.lean:159) | PASS | Proves the finite factorized formula for the original box integral. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.CoeffDeg` (Poly.lean:27) | PASS | Coefficientwise total-degree bound on polynomials over complex polynomials. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.CoeffDeg.mono` (Poly.lean:30) | PASS | Monotonicity of that concrete degree bound. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.CoeffDeg.mul` (Poly.lean:33) | PASS | Coefficient convolution and totalDegree_mul bound. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.CoeffDeg.one` (Poly.lean:40) | PASS | Degree bound for every coefficient of one. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.CoeffDeg.pow` (Poly.lean:45) | PASS | Degree bound for powers from a degree-one coefficient bound. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charW_deg` (Poly.lean:51) | PASS | Total-degree bound for x+i y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charWb_deg` (Poly.lean:58) | PASS | Total-degree bound for x-i y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.coeff_deg_aux` (Poly.lean:65) | PASS | Multiplication by a scalar constant preserves degree ≤1. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charUP_deg` (Poly.lean:69) | PASS | Both nonzero coefficient polynomials have degree ≤1. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charVP_deg` (Poly.lean:78) | PASS | Both nonzero coefficient polynomials have degree ≤1. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQ_deg` (Poly.lean:87) | PASS | All expansion coefficients have degree ≤p+q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFcPoly` (Poly.lean:91) | PASS | Exact finite coefficient selector for Fourier mode k. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFcPoly_deg` (Poly.lean:95) | PASS | Selected polynomial has total degree ≤p+q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFcPoly_eval` (Poly.lean:101) | PASS | Evaluation equals the integral-defined one-plane coefficient. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG` (Trig.lean:28) | PASS | Actual rotated real monomial for arbitrary p,q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charW` (Trig.lean:32) | PASS | Concrete coordinate polynomial x+i y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charWb` (Trig.lean:35) | PASS | Concrete coordinate polynomial x-i y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charUP` (Trig.lean:39) | PASS | Explicit polynomial E times the first rotated coordinate. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charVP` (Trig.lean:44) | PASS | Explicit polynomial E times the second rotated coordinate. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQ` (Trig.lean:49) | PASS | Finite product charUP^p charVP^q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQc` (Trig.lean:52) | PASS | Actual evaluation map of polynomial coefficients at real x,y. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQc_def` (Trig.lean:55) | PASS | Specialized polynomial identity, by ring-homomorphism evaluation. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQc_natDegree` (Trig.lean:78) | PASS | Explicit degree bound 2(p+q). |
| e-ca / ch-mon | `KAM.Planetary.PlanarCharacters.charAlg1` (Trig.lean:89) | PASS | Conditional algebra identity; circle and imaginary-unit identities are typing inputs. |
| e-ca / ch-mon | `KAM.Planetary.PlanarCharacters.charAlg2` (Trig.lean:94) | PASS | Conditional algebra identity; its scalar inputs are discharged at use. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charQc_eval` (Trig.lean:101) | PASS | Proves E^(p+q) G=Q(E) for E=exp(iθ). |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charG_expand` (Trig.lean:118) | PASS | Finite exact expansion with exponent n-(p+q), all p,q. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charInt_ne` (Trig.lean:138) | PASS | Nonzero integer Fourier mode integrates to zero over [0,2π]. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charInt_zero` (Trig.lean:150) | PASS | Zero mode integral is exactly 2π. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc` (Trig.lean:155) | PASS | Actual normalized interval Fourier integral, all integer modes. |
| ch-mon / char | `KAM.Planetary.PlanarCharacters.charFc_eq` (Trig.lean:159) | PASS | Orthogonality proves finite coefficient-selection formula. |

## Hygiene and exact validation receipts

All Lean/Lake executions were serial with LEAN_NUM_THREADS=1 and inherited niceness 5.
Builds used the requested compile gate; its slot wait was allowed to finish. No heartbeat,
recursion-depth or synthesis-heartbeat override was added or used.

Targeted command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t7 KAM.Planetary.PlanarTorsion.Characters
```

Exit 0. Terminal output:

```text
[inp-gate] slot 1 acquired 19:21:02 for KAM.Planetary.PlanarTorsion.Characters
Build completed successfully (9118 jobs).
```

Replayed upstream unused-variable warnings are in Kepler/Energy.lean:106,
Planetary/Poincare/Chart.lean:212,247, Kepler/Mass.lean:147,157,500,524. Scoped warnings:
Factor.lean:31,55 deprecated if_neg/if_pos; Factor.lean:185 deprecated integral_finset_sum;
Basic.lean:82 deprecated push_neg; Basic.lean:116 unused simp argument map_sum;
Average.lean:96,112 deprecated if_pos/if_neg (three occurrences on line 112).
These are maintenance notes, not holes or elaboration failures; no options were used to hide them.

Probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T7AuditProbe.lean
```

Exit 0; exactly 62 axiom-query output lines, no diagnostics. Complete output:

```text
'KAM.Planetary.PlanarCharacters.charFc_zero_radial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charK_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_zero_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_zero_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charAvg_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charIte_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charAvgA_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charAvgB_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charAvgC_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.average_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.average_action_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charIdx_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_piFinset_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_covariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mv_eval_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.n0_fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonian_n0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rotation_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charIdx_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charQcoef_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.charIdx_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quartic_of_actions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_mv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_homog' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.character_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charG_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charG_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charG_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charG_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charBox_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charMono_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.character_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.CoeffDeg.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.CoeffDeg.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.CoeffDeg.one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.CoeffDeg.pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charW_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charWb_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.coeff_deg_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charUP_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charVP_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charQ_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFcPoly_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFcPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charQc_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charQc_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charAlg1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charAlg2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charQc_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charG_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charInt_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charInt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarCharacters.charFc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay command (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Characters KAM.Planetary.PlanarTorsion.Characters.Defs KAM.Planetary.PlanarTorsion.Characters.Trig KAM.Planetary.PlanarTorsion.Characters.Factor KAM.Planetary.PlanarTorsion.Characters.Basic KAM.Planetary.PlanarTorsion.Characters.Poly KAM.Planetary.PlanarTorsion.Characters.Average KAM.Planetary.PlanarTorsion.Characters.CharPoly KAM.Planetary.PlanarTorsion.Characters.Bracket
```

Exit 0; complete verbose output:

```text
replaying KAM.Planetary.PlanarTorsion.Characters.Defs
replaying KAM.Planetary.PlanarTorsion.Characters.CharPoly
replaying KAM.Planetary.PlanarTorsion.Characters.Trig
replaying KAM.Planetary.PlanarTorsion.Characters.Factor
replaying KAM.Planetary.PlanarTorsion.Characters.Bracket
replaying KAM.Planetary.PlanarTorsion.Characters.Average
replaying KAM.Planetary.PlanarTorsion.Characters.Poly
replaying KAM.Planetary.PlanarTorsion.Characters.Basic
replaying KAM.Planetary.PlanarTorsion.Characters
```

Source lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 **solely for the expected generated-root exception allowed by the brief**; complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (830 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module-system, frozen-anchor and elaborated ABI checks all passed. No generated file was
regenerated or repaired. The ABI probe inherits LEAN_NUM_THREADS=1 and niceness 5 from the shell;
it ran only after the kernel checker had exited. Build/probe/checker receipts above are independent
reruns by this auditor, rather than the prover's handoff receipts. The targeted build reused the
worktree's existing build snapshot; kernel replay independently validated all nine compiled modules.


## File and namespace hygiene

| File | Lines | Maximum Unicode line width |
|---|---|---|
| Characters.lean (facade) | 24 | 99 |
| Characters/Defs.lean | 64 | 100 |
| Characters/Trig.lean | 189 | 100 |
| Characters/Factor.lean | 202 | 100 |
| Characters/Basic.lean | 121 | 99 |
| Characters/Poly.lean | 111 | 98 |
| Characters/Average.lean | 174 | 100 |
| Characters/CharPoly.lean | 175 | 100 |
| Characters/Bracket.lean | 143 | 100 |

Every implementation file has the copyright comment, module, public imports, module docstring,
and exposed public noncomputable section. The facade contains imports/docstring only; module lint
accepts this declaration-free facade. No file approaches the 1,500-line cap. No scoped occurrence
of sorry/admit/axiom/unsafe/opaque/EuclideanSpace or set_option was found.

All explicit declarations live in KAM.Planetary or KAM.Planetary.PlanarCharacters; there is no
root declaration or new global instance. Full-name source collision search found none. The bare
suffixes one and mul also occur upstream, but the added names are under
KAM.Planetary.PlanarCharacters.CoeffDeg, so no public helper is reused or root name shadowed.

Source-level transitive KAM import traversal found 70 modules, no provider and no frozen theorem
module at all; frozen imports are definitions only. Thus no DRAFT_SORRY theorem can leak through
the import closure. The all-theorem axiom receipt independently excludes sorryAx.

The final commit a7c0963c versus its parent 84136a0d is whitespace-only in all nine files:
whole-text whitespace-stripped equality passed, and comment-masked lexical token comparison
using check_lean_modules.code_mask plus word/symbol tokens also passed. The 31 wrapped long
lines changed no Lean code token. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty; `git diff --check inp...HEAD` exits 0 with no output.

## Uncertainties, defects and deviations

No new suspected pinned-source or blueprint mathematical defect was found in the audited slice.
No changed premise, weakened conclusion, changed normalizer, or wider constant dependence was
found. No pinned-paper PDF claim was newly verified: this is the requested blueprint/design/
signature/Lean package audit. Existing design-audit N1/N2 concern provenance and the broader
execution DAG, not a missing T7 proof; the current design/signature/blueprint hashes match that
audit's recorded hashes. The split into eight focused modules and an import facade is a harmless
implementation refinement; the alternative explicit polynomial proof discharges ch-mon locally.
The shared e-ca node is accounted for only as used in T7, with no claim about T2/T4's physical jets.

Final validation: the report contains 88 explicit declaration rows, five scoped graph rows and
all 62 public-theorem/lemma axiom receipts. No receipt is pending. Report whitespace validation,
`git diff --check inp...HEAD` and `git diff --no-index --check /dev/null docs/tracks/P/audits/T7-audit-1.md`
pass. Auditor scratch files were removed after copying the complete probe/kernel/lint outputs.
Final status contains only the pre-existing untracked T7-handoff.md and this new report; no tracked
file is modified. The live inp ref advanced during the audit to `f5376c6dffbc49d970aeb4f9b37796a46f764133`; the merge base
and nine-file `git diff inp...HEAD` audit slice remained unchanged. HEAD stayed at the hash above.
