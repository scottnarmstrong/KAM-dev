# Delta design audit 2: N Parts 6–7, Revision 2

**Overall verdict: PASS WITH NOTES.** Audit-1 findings **F1, F2 and F3 are closed at the design/signature level**. Notes N1–N5 have been addressed. Two minor documentation/API notes remain below; neither changes a theorem target or prevents the advertised consumers from supplying its premises. This approves the revised design interfaces, not theorem bodies: all 43 draft theorem obligations still use `sorry`.

## Scope and snapshot

Independent refute-first delta review of `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, its Revision 2 section, the supplied signatures, and `.drafts/handoff-DESIGN-N67b.md`, under the original audit brief and repository rules. Compared the full revision against audit-1 design commit `949524142150f68a0c11bb04d589d89ef83ac945`; re-read the touched blueprint/packet contracts and Part 11 consumer. No delegation or state-changing git operation. Only this report is retained as a new change; auditor-created scratch is removed. Designer-owned scratch is preserved.

| Input | Revision / SHA-256 |
|---|---|
| Worktree HEAD / last commit | `bcf3267b154db286850517732eab17b94aaf91e5` — `Handoff DESIGN-N67b` |
| Design revision commit | `6e78b50` — `Design N67 Revision 2: fix audit F1-F3 and notes N1-N5` |
| Revised design | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Original supplied signatures | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| Designer's revision handoff | `71b2905ac4391b1f12603330742ac927636eb74e92fd9ad8db8d5b8b7ccb159a` |
| Part 11 homological consumer, `p11b-partial-nf.tex` | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| Existing square-only `Canonical/Setting.lean` | `49a4a9eb675de5a375ff138568f5bce11617db7dfaaeb55657cfc1fca68ebd10` |

The p6/p7 blueprint and packet SHA-256 hashes are unchanged from audit 1 (freshly recomputed). Appendix A is byte-identical to the 854-line signature file. Mechanical declaration comparison finds exactly **seven new declarations and two changed declarations** (`IsActionNorm`, `normal_form`); every other original declaration is unchanged. Inventory: **37 definitions, 5 structures, 43 theorem obligations = 85 declarations**. All signature line references below refer to this hashed v2 file.

The user-requested checker resolves imports against the shared `/root/code/KAM-inp` build, not a newly rebuilt worktree library. Shared source HEAD observed during validation: `f21b16ab24a1722cd8341a595173c311cdfe9357`. This is an elaboration receipt against that shared environment, not certification of newly landed upstream implementations.

## Disposition of every previous finding

| Audit-1 item | Severity then | Delta verdict | Evidence and refutation result |
|---|---|---|---|
| F1: incomplete norm / false exit | BLOCKING | CLOSED | `IsActionNorm` L598–604 adds `map_zero` and `smul`; the shifted norm fails the zero field. Actual norm examples remain admissible. `exit_ball` L649–654 is unchanged except for the meaning of its structure premise. |
| F2: missing exact normal-form cases | MAJOR | CLOSED | `normal_form` L422–425 explicitly adds the disjunction and `EqOn` equality on `Dom n D (r/2) (s/6)`, retaining every prior conjunct and hypothesis. |
| F3: Part 11 parameter carrier | MAJOR | CLOSED | L147–198 adds independent `m`, arbitrary holomorphic `ω : ℂᵐ→ℂⁿ`, a directional identity, rectangular reality and three specialization bridges. N6-2 owns the new core; Part 11 owns its coordinate-projection/bracket bridge. |
| N1: P's q=1 | LOW | CLOSED | §8 documents `p=2`, `α_design=2α/q₀`, preserving α/q and q/α; generator/map do not depend on α,p. The new homological core also permits q=1 directly. |
| N2: premature facade / schedule | MEDIUM | CLOSED, minor estimate note N7 | N6-5 owns `IterativeMap` and the source wrapper; N6-6 imports that module; N6-7 creates the facade after its imports. S7-6 now depends on S7-3. Six waves stated. |
| N3: claimed current I/12 and energy consumers | LOW | CLOSED | §§0.1/8 mark I reuse prospective and Part 12 as having no direct p6/p7 consumer. Part 11 explicitly does not apply canonical `energy_core`; its argument is repeated separately. |
| N4: telescoping openness | LOW | CLOSED as consumer convention | Revision 2 states the open-domain convention; every actual normal-form Uᵢ is an open `Dom`. No new consumer hypothesis is required. |
| N5: sum and division Mathlib citations | MEDIUM | CLOSED | N6-4 now uses a local finite-sum induction on `map_add_le_add`; N6-2 uses general `DifferentiableOn.mul` plus `.inv`, with nonvanishing already supplied by the divisor bound. |

### F1 refutation re-check

`map_zero : N 0 = 0` supplies exactly the missing initial strict inequality `N(I(0)−I(0))=0<ϱ`. Continuity on the compact real time segment then gives an attained first boundary time and the preceding closed-ball bound. Symmetry handles either sign of time. The stronger structure really represents a norm: `norm_le` supplies nonnegativity and definiteness; `smul` supplies absolute homogeneity; `add_le` supplies triangle. Both the Pi max norm and `euclid` satisfy these fields. No conclusion-shaped field or global function-type instance was introduced. Thus the previous constant-curve counterexample is excluded for the correct source reason, and no estimate/conclusion was weakened to avoid it. `transfer` and `stopped_extension` now take an actual source norm, with all other premises and conclusions unchanged.

### F2 fidelity and branching re-check

Blueprint p6 L167 and packet `bpN:p6:normal-form` L890 require equality when N=0 or the second first-step case applies. The new clause uses `nfSteps K s=0` and exactly Step 0's threshold

`iterU α p ε (r/8) (s/6) < exp(−(2πKs)/6)`.

This is y₀<exp(−κ/6), not a threshold at the later losses or at the doubled Case B losses. Equality is on the intended function domain, so arbitrary off-domain total-function values are unconstrained. The quantified Ψ,g,f_* witnesses simultaneously satisfy this equality, the old quadratic correction estimate, remainder bound, map/displacement and reality conclusions. No old conjunction was removed.

At the sharp norm instance the condition is the blueprint's case verbatim. With a carried upper bound ε, the construction may use ε to choose its first-step branch and has exactly the smallness estimates stated: this is a valid bound-predicate formulation, not an inference from a mere quadratic error bound. N=0 remains independent of ε=0. Consumers needing only the old conjuncts project past the additional conjunct; N6-8 must actually prove both equality cases when constructing its witness. This is an unproved implementation obligation, not a remaining statement gap.

### F3 definitions, reality and consumer re-check

`homGenParam` and `homResParam` use the same Fourier lattice `Fin n→ℤ`, but the action/parameter input is `Fin m→ℂ`. No dummy angles or change of norm/lattice occurs. All coefficients depend on the full parameter vector; only the denominator uses the supplied ω. The core retains α/q as the divisor, qδ/(2πα) as generator bound, the full finite-mode support and resonant projection identities, and conditional reality with a real frequency at real parameter points. No higher-derivative bound, frequency Lipschitz bound, or stronger smallness premise was introduced. Holomorphy of ω follows from source holomorphy of h and composition with the fast projection; it is not an extra independent hypothesis for that consumer.

The new `RealOnParam` is needed because existing `KAM.Canonical.RealOn` is square-only (Setting.lean L143–145). It says that the imaginary part vanishes at **every** pair of real angle/parameter vectors whose complex inclusion belongs to U. It is not restricted to a smaller subset or endowed with a hidden analyticity assumption. At m=n its pair inclusion is definitionally `realInclusion₂ n`; the new equivalence and generator/resonant bridges are exact total-definition identities. An independent scratch probe proved these three bridges by `rfl`/`Iff.rfl`, without using draft theorem obligations.

For `bpN:p11:hom` (p11b L117–123), take m=n+2k, the extended base set, and `ω(y)=freq h (fastProjection y)`. Then the consumer supplies precisely `hf`, the finite weighted bound, holomorphy of the projected frequency, α/q nonresonance and the stated real-frequency premise. Since h depends on neither angle nor slow pair, its slow bracket terms vanish; its extended bracket with φ is the core's directional expression. The Part 11 package is explicitly assigned that coordinate/domain/holomorphy and bracket-identification bridge. This is ordinary specialization work with source premises, not an assumed conclusion or an incompatible canonical-orbit application. The m=n wrapper retains the exact old canonical statements, and both generator definitions agree globally.

## New nonblocking notes

### N6 — LOW: replace the new `DifferentiableOn.fderiv` spelling

Design §7.1 N6-2 L278 names `DifferentiableOn.fderiv`. No declaration with that exact qualified name was found in the pinned Mathlib calculus sources. The proposed fact is correct here and already available: use

```lean
(KAM.differentiableOn_fderiv_of_isOpen (KAM.Weighted.isOpen_polyNbhd D r) hh)
```

or the first conjunct of `KAM.holomorphic_regularity` on that open set. The correct derivative-regularity theorem was checked in a probe. Applying the resulting derivative to each coordinate basis vector gives holomorphy of `freq h`, without extra assumptions. This is a proof-plan citation correction; `homological_param` and its canonical wrappers have the required source hypotheses already.

### N7 — LOW: package-size arithmetic is still inconsistent

The package rows now sum to **7,600** estimated lines, not the stated **7,050**. N6-2 is listed as a 700-line single `Homological` module, while §0.9 says all packages except N6-8 have at most 650 lines and §7 says no file above 600 is planned; N6-6 also lists 650 lines for `IterativeRemainder`. Correct these summaries, or explicitly split/re-estimate those modules. All stated estimates remain below the actual 1500-line hard cap, so this is not a package dependency or target-validity blocker. The facade order and S7-6 prerequisite omission themselves are fixed.

## Signature ledger

Every declaration is included for traceability. “Unchanged” inherits its source/packet comparison from audit 1 and is backed by the mechanical declaration diff; it is not a fresh proof-body audit. The seven additions and two changed declarations were audited in full, and the norm-taking downstream signatures were rechecked with the stronger structure. No failing signature remains at this design level.

| Lean name (v2 line) | Blueprint label | Verdict | Delta evidence |
|---|---|---|---|
| `projMode` (L51) | `bpN:p4:projections` | PASS | Unchanged; Verbatim generalized upstream stubs; remove on landing. |
| `truncate` (L56) | `bpN:p4:projections` | PASS | Unchanged; Verbatim generalized upstream stubs; remove on landing. |
| `zBall` (L72) | `bpN:p6#data` | PASS | Unchanged; Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `freq` (L75) | `bpN:p6#data` | PASS | Unchanged; Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `dotC` (L78) | `bpN:p6#data` | PASS | Unchanged; Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `conjExp` (L81) | `bpN:p6#data` | PASS | Unchanged; Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `IsNonresonant` (L84) | `bpN:p6:setting / iterative-direct` | PASS | Unchanged; Correct point sets, max norms and divisor threshold. |
| `FreqLipschitz` (L88) | `bpN:p6:setting / iterative-direct` | PASS | Unchanged; Correct point sets, max norms and divisor threshold. |
| `DivisorBound` (L92) | `bpN:p6:setting / iterative-direct` | PASS | Unchanged; Correct point sets, max norms and divisor threshold. |
| `IsDecomp` (L98) | `bpN:p6:setting` | PASS | Unchanged; Finite decomposition and explicit weighted bound; no hidden proof field. |
| `starNorm` (L107) | `bpN:p6:setting` | PASS | Unchanged; Finite decomposition and explicit weighted bound; no hidden proof field. |
| `lipschitz` (L111) | `bpN:p6:lipschitz` | PASS | Unchanged; Holomorphy of h supplies regularity of freq; operator/entry constants preserved. |
| `lipschitz_entries` (L116) | `bpN:p6:lipschitz` | PASS | Unchanged; Holomorphy of h supplies regularity of freq; operator/entry constants preserved. |
| `divisor` (L123) | `bpN:p6:divisor` | PASS | Unchanged; Both thresholds retained; nonnegative K,L and p>1 are source data. |
| `homGen` (L132) | `bpN:p6:homological` | PASS | Unchanged; Explicit finite-mode constructions on the guarded locus; 2π and sign correct. |
| `homRes` (L138) | `bpN:p6:homological` | PASS | Unchanged; Explicit finite-mode constructions on the guarded locus; 2π and sign correct. |
| `homGenParam` (L148) | `bpN:p11:hom / bpN:p6:homological` | PASS | New: same generator with independent parameter dimension; positive divisors guard use. |
| `homResParam` (L154) | `bpN:p11:hom / bpN:p6:homological` | PASS | New: exact parameter-capable PΛ TK f using generalized upstream projections. |
| `RealOnParam` (L159) | `bpN:p11:hom / bpN:p6:homological (reality)` | PASS | New: reality at every real point of the rectangular carrier, with a square-carrier bridge. |
| `realOnParam_iff_realOn` (L165) | `bpN:p6:homological (reality bridge)` | PASS | New: definitionally the existing RealOn at m=n; independently checked with Iff.rfl. |
| `homological_param` (L170) | `bpN:p11:hom / bpN:p6:homological` | PASS | New: source divisor, holomorphy, support, directional identity, bounds and reality all preserved. |
| `homGen_eq_homGenParam` (L193) | `bpN:p6:homological (specialization bridge)` | PASS | New: exact equality of the total generator definitions, independently checked by rfl. |
| `homRes_eq_homResParam` (L197) | `bpN:p6:homological (specialization bridge)` | PASS | New: exact equality of the total resonant-part definitions, independently checked by rfl. |
| `homological_direct` (L201) | `bpN:p6:homological / iterative-direct` | PASS | F3 closed via the separate rectangular core and explicit specialization bridges. |
| `homological` (L225) | `bpN:p6:homological` | PASS | Unchanged; Source-form divisor premises, support, identity, estimates and conditional reality retained. |
| `bracket_g` (L245) | `bpN:p6:bracket-g` | PASS | Unchanged; Correct 2/e factor and decomposition weights; monotone replacement by bounds is valid. |
| `iterMap` (L259) | `bpN:p6:iterative` | PASS | Unchanged; Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `iterG` (L264) | `bpN:p6:iterative` | PASS | Unchanged; Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `iterF` (L269) | `bpN:p6:iterative` | PASS | Unchanged; Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `IterHyp` (L276) | `bpN:p6:iterative-direct` | PASS | Unchanged; Source divisor premise and smallness only; correct dimensionless ratio. |
| `iterU` (L296) | `bpN:p6:iterative-direct` | PASS | Unchanged; Source divisor premise and smallness only; correct dimensionless ratio. |
| `iterative_direct_a` (L306) | `bpN:p6:iterative / iterative-direct (a)` | PASS | Unchanged; Widths, symplecticity, integer translations, injectivity and left inverse match. |
| `iterative_direct_b` (L322) | `bpN:p6:iterative / iterative-direct (b)` | PASS | Unchanged; Both displacements, scaled bound and derivative estimate match. |
| `iterative_direct_c` (L334) | `bpN:p6:iterative / iterative-direct (c)` | PASS | Unchanged; Identity is definitional; resonant increment and remainder class retained. |
| `iterative_direct_d` (L342) | `bpN:p6:iterative / iterative-direct (d)` | PASS | Unchanged; Denominator, 2/e, tail exponential and all parameter dependences match. |
| `iterative_direct_e` (L349) | `bpN:p6:iterative / iterative-direct (e)` | PASS | Unchanged; Reality on the correct domains; symmetry of Λ required conditionally. |
| `iterHyp_of_source` (L361) | `bpN:p6:iterative` | PASS | Unchanged; Derives direct premises from N1,N2; not a conclusion-shaped assumption. |
| `chain` (L374) | `bpN:p6:telescope` | PASS | Unchanged; Correct composition order, any-bound displacement, chain rule and injectivity; see N4 for open sets. |
| `telescope` (L378) | `bpN:p6:telescope` | PASS | Unchanged; Correct composition order, any-bound displacement, chain rule and injectivity; see N4 for open sets. |
| `nfSteps` (L397) | `bpN:p6:normal-form#data` | PASS | Unchanged; Correct nonnegative floor; step states deliberately private future proof obligations. |
| `normal_form` (L400) | `bpN:p6:normal-form` | PASS | F2 closed: exact EqOn correction in the zero-step and Case B branches added. |
| `nonresonant_case` (L438) | `bpN:p6:nonresonant-case` | PASS | Unchanged; True stronger bound-predicate statement; id/zero clauses follow definitionally. |
| `cpx` (L456) | `bpN:p7:setting` | PASS | Unchanged; Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realNbhd` (L459) | `bpN:p7:setting` | PASS | Unchanged; Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realStrip` (L462) | `bpN:p7:setting` | PASS | Unchanged; Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realH` (L466) | `bpN:p7:setting` | PASS | Unchanged; Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `IsOrbit` (L470) | `bpN:p7:setting` | PASS | Unchanged; Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `reMap` (L475) | `bpN:p7:setting` | PASS | Unchanged; Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `thetaGradR` (L480) | `bpN:p7:setting` | PASS | Unchanged; Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `hessR` (L484) | `bpN:p7:setting` | PASS | Unchanged; Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `isOpen_realNbhd` (L486) | `bpN:p7:setting` | PASS | Unchanged; Elementary neighborhood facts; positive strip required exactly where needed. |
| `realNbhd_mono` (L488) | `bpN:p7:setting` | PASS | Unchanged; Elementary neighborhood facts; positive strip required exactly where needed. |
| `realInclusion₂_mem_Dom_iff` (L492) | `bpN:p7:setting` | PASS | Unchanged; Elementary neighborhood facts; positive strip required exactly where needed. |
| `realHamiltonian_eq_realH` (L497) | `bpN:p7:setting / p10:hypotheses-check` | PASS | Unchanged; Explicit bridges to frozen objects; no parallel frequency or Hamiltonian assumed equal. |
| `freq_realInclusion` (L501) | `bpN:p7:setting / p10:hypotheses-check` | PASS | Unchanged; Explicit bridges to frozen objects; no parallel frequency or Hamiltonian assumed equal. |
| `real_system` (L509) | `bpN:p7:real-system` | PASS | Unchanged; Smoothness, field identification, periodicity and energy retained; Part 3 supplies existence/uniqueness. |
| `theta_derivative` (L529) | `bpN:p7:theta-derivative` | PASS | Unchanged; Pointwise-in-action sum, Euclidean consequence and value bound correct. |
| `resSpan` (L538) | `bpN:p7:resonant-gradient` | PASS | Unchanged; Arbitrary Λ; coefficient support gives membership in real span. |
| `resonant_gradient` (L543) | `bpN:p7:resonant-gradient` | PASS | Unchanged; Arbitrary Λ; coefficient support gives membership in real span. |
| `conjugation` (L553) | `bpN:p7:conjugation` | PASS | Unchanged; Holomorphic real symplectic map, mapping and conjugacy; genuine orbit conclusion. |
| `preimage` (L568) | `bpN:p7:preimage` | PASS | Unchanged; All displacement, reality and contraction-radius premises retained; positive r′,s′ implied. |
| `preimage_nfl` (L584) | `bpN:p7:preimage-nfl` | PASS | Unchanged; Correct witness-level form; action displacement and r/128 conclusion retained. |
| `IsActionNorm` (L598) | `bpN:p7:transfer / exit-ball` | PASS | F1 closed: zero and absolute real homogeneity restore the documented norm. |
| `isActionNorm_norm` (L606) | `bpN:p7:transfer / exit-ball` | PASS | Unchanged theorem statement; the intended norm satisfies every corrected structure field. |
| `isActionNorm_euclid` (L608) | `bpN:p7:transfer / exit-ball` | PASS | Unchanged theorem statement; the intended norm satisfies every corrected structure field. |
| `transfer` (L612) | `bpN:p7:transfer` | PASS | Unchanged theorem statement; T1–T3 and admissibility retained, now with an actual source norm. |
| `stopped_extension` (L637) | `bpN:p7:stopped-extension` | PASS | Unchanged theorem statement; valid source-norm specialization, with no added global regularity premise. |
| `exit_ball` (L649) | `bpN:p7:exit-ball` | PASS | F1 closed through the corrected structure; curve/radius conclusion unchanged. |
| `nonresonant` (L659) | `bpN:p7:nonresonant` | PASS | Unchanged; Source N1,N2, smallness, stopped orbit and sr exp(κ/6)/(5ε) preserved. |
| `IsOrthProj` (L679) | `bpN:p7:ext-linalg / resonance-data` | PASS | Unchanged; Idempotent self-adjoint linear projection; existence onto prescribed subspace. |
| `exists_orthProj` (L685) | `bpN:p7:ext-linalg / resonance-data` | PASS | Unchanged; Idempotent self-adjoint linear projection; existence onto prescribed subspace. |
| `resSpace` (L689) | `bpN:p7:resonance-data` | PASS | Unchanged; Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsCloseToRes` (L692) | `bpN:p7:resonance-data` | PASS | Unchanged; Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsMConvex` (L696) | `bpN:p7:resonance-data` | PASS | Unchanged; Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsQuasiConvex` (L700) | `bpN:p7:resonance-data` | PASS | Unchanged; Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `HessBound` (L705) | `bpN:p7:resonance-data` | PASS | Unchanged; Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `energy_core` (L710) | `bpN:p7:energy-core` | PASS | Unchanged; All four conclusions, C²/C¹ local regularity, projection condition and segment preserved. |
| `ResSetting` (L743) | `bpN:p7:s-energy#rs` | PASS | Unchanged; Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `resRho` (L768) | `bpN:p7:s-energy#rs` | PASS | Unchanged; Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `IsAdmissible` (L771) | `bpN:p7:s-energy#rs` | PASS | Unchanged; Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `admissible` (L780) | `bpN:p7:admissible` | PASS | Unchanged; Ball inclusion, 5δ/4+M distance bound and initial bound retained. |
| `no_exit` (L790) | `bpN:p7:no-exit` | PASS | Unchanged; All three exit/curvature/time premises retained literally. |
| `resonant_lemma1` (L803) | `bpN:p7:resonant-lemma1 (off graph)` | PASS | Unchanged; Convex stopped estimate and zero-denominator infinite-time case retained. |
| `resonant_lemma2` (L811) | `bpN:p7:resonant-lemma2` | PASS | Unchanged; Both R conditions retained; any Ω bound legitimately replaces maximum. |
| `resonant_prop2` (L827) | `bpN:p7:resonant-prop2` | PASS | Unchanged; Complex Euclidean Hessian, √n, added Mr bound, r/2 and all-time Λ=univ preserved. |

## Layer verdicts and proof limits

- **Fidelity: PASS.** F2 restores the lost source clause. The parameter core is a genuine generalization of the homological source, with its old scalar/canonical surface retained. The extra norm fields are properties of the source norm, not new restrictions on its theorem.
- **Consumers: PASS at the designed interfaces.** Part 7 and N Parts 8–10 retain their quantitative contracts and frozen-solution bridges. P's q=1 specialization is explicit; the two-scale/oscillator variants remain P's own work. The Part 11 homological interface now has the correct carrier and reality premise; its fast-coordinate and weighted-bracket identification is explicitly owned there. Canonical iteration, preimage, conjugation, and energy arguments used only as patterns in the extended setting remain separate Part 11 variants. No direct canonical theorem application on the extended weighted symplectic carrier has been certified. I reuse is prospective; Part 12 has no new direct consumer.
- **Frozen objects: PASS, unchanged.** No frozen definition, theorem or manifest was edited. The existing `hamiltonianVectorField`, complex field, real Hamiltonian, frequency map, real inclusion and generic ODE predicate remain the referenced objects. Revision 2 adds a rectangular reality predicate with an explicit definitional bridge to the existing square one; it does not replace a frozen solution predicate or assume a parallel Hamiltonian/frequency definition equal.
- **Definitions/structures: PASS.** Norm zero/homogeneity close the actual defect. New Fourier constructions have real bodies, finite selected support under the source cutoff, and guarded nonzero denominators. No new global instance, junk-value inference, axiom or conclusion-shaped premise was added.
- **Packages: PASS WITH NOTES.** The facade dependency order is executable after N2's changes; the new core and specialization bridges have an owner. The hard file limit remains satisfied by every estimate; N7 concerns inaccurate summaries and the softer 600-line target.
- **Mathlib/API: PASS WITH N6 citation correction.** The two previous helper issues are fixed and checked; the newly cited derivative fact already has a project theorem providing the exact required type. No new mathematical proof ingredient or stronger hypothesis is needed to repair that spelling.

The point of closure is design readiness of the revised declarations. Neither successful elaboration of signatures nor an independently proved definitional bridge proves the main homological, iterative, normal-form or stability results. The frozen/source root statuses and unfinished upstream proof obligations are not upgraded by this report.

## Fresh verification receipts

The unmodified v2 signature copy was elaborated **once**, using exactly the requested checker:

```text
/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-n67 .drafts/scratch/NPart67Signatures.audit2.lean
[sig-gate] slot 3 acquired 05:08:48
exit 0
43 diagnostics, all: warning: declaration uses `sorry`
No errors, no other warnings.
```

The checker waited for a shared signature slot as expected and ran `LEAN_NUM_THREADS=1 nice -n 5 lake env lean` against the shared build. The source signature and Appendix A hashes match. The probe was compiled only after this run completed:

```text
/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-n67 .lake/abi-scratch/N67DeltaProbe.lean
[sig-gate] slot 3 acquired 05:12:48
final run exit 0; no warnings/errors
```

The independent probe copied the actual generator/resonant/reality definitions and proved the three specialization bridges with `rfl`/`Iff.rfl`. It also instantiated the generator on one angle and three parameter coordinates, and checked `KAM.differentiableOn_fderiv_of_isOpen`, `KAM.holomorphic_regularity`, `DifferentiableOn.mul`, `DifferentiableOn.inv` and `map_add_le_add`. A first auxiliary run had an auditor-only missing `KAM.` qualifier and an unclosed unnamed section; the final corrected probe above passed. Neither auxiliary attempt changed the supplied signatures or design.

```text
'N67DeltaProbe.generator_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'N67DeltaProbe.resonant_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'N67DeltaProbe.reality_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The 43 main draft theorem bodies remain `sorry`; no axiom-clean claim is made for those results. No heartbeat, synthesis-heartbeat or recursion-depth override was used. No library rebuild, cache operation or frozen edit was performed. All auditor-started Lean work was serialized; unrelated sessions were left untouched.

Source lint was rerun after the auxiliary probe completed. Its `lake env lean` ABI subprocess was routed through the same user-supplied signature checker by an auditor-only temporary PATH wrapper, so it respected the compile gate, one-thread setting and nice 5:

```text
env PATH="<auditor temporary lake wrapper>:$PATH" LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (401 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Final checks: all 85 declaration rows present exactly once; balanced code fences; no trailing whitespace; original signature/design hashes unchanged; auditor scratch removed; `git status --short --untracked-files=all` shows only the new audit-2 report. Designer-owned scratch files were not removed.

## Closeout

F1–F3 close as design defects; N1–N5 close with the documented interface and scheduling changes. N6–N7 are nonblocking proof-plan/estimate corrections with concrete replacements above. No new suspected pinned-source erratum was found. The declared rectangular-reality predicate and carried-bound Case B formulation have been checked rather than silently treated as literal unchanged source text. No frozen statement or source was repaired, and no manuscript/proof/root completion claim is made.

Only `docs/tracks/N/design/DESIGN-N67-design-audit-2.md` is the auditor's persistent deliverable. The original supplied signature file, canonical design, prior report, handoffs, frozen files, manifest, README and generated root are unchanged by this delta audit. All 85 declarations have a ledger row; all revised contracts and their immediate consumer consequences have been classified. The two notes require no corrected theorem signature because no theorem target fails.
