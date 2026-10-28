# Independent design audit 1: N Parts 8–9

**Overall verdict: FAIL.** The proposed main stability statements survive this audit, but the design is not ready for exact-signature dispatch: F1 narrows a source interface, and F2 makes the declared package waves/import graph inconsistent. These findings concern source coverage and implementation dependencies; no counterexample to `thm1` was found.

Audit target: branch `inp-design-n89`, HEAD `f57cd820d7d1827c08573c50fbbe9e86371044ca`. `git diff inp...HEAD` adds only the 980-line design document. Read the audit brief, AGENTS.md, PLAN.md, DECISIONS.md, designer handoff, both source blueprints, applicable graph packets and consumers, upstream signatures, and frozen definitions directly. No source PDF was re-audited.

The supplied signatures have SHA-256 `ad4f6dff495383a78c6f46031a3c8db43eba559e16298cea1dbb8f5a0acc9f5e`; Appendix A matches byte for byte. Both blueprint hashes and the upstream Part-6/7 hash match the design snapshot. All **82/82 graph nodes** have exactly one inventory row, including the four extra claim nodes. Graph coverage alone does not establish fidelity (F1).

## Findings and exact fixes

### F1 — MAJOR: the real-matrix projection formula has been specialized to integer bases

Locators: signatures L157–159; design Appendix A and §4 row `bpN:p8:projection`; blueprint `p8-resonance-geometry.tex:53–66`; graph `N-p8.nodes.md:328` (`bpN:p8:projection`) and `:360` (`stepN:p8:pr-alg`).

The source begins “Let A ∈ R^{n×d} … have independent columns” and identifies the projector with `A (Aᵀ A)⁻¹ Aᵀ`. The only signature identifying the chosen projector with that matrix is:

```lean
theorem projection_matrix {d : ℕ} {Λ : Lattice n}
    (b : Basis (Fin d) ℤ Λ) :
    let A := (basisMatrix b).map (Int.castRingHom ℝ)
    ∀ v, proj (lattice Λ) v =
      (A * (A.transpose * A)⁻¹ * A.transpose).mulVec v
```

This theorem is true, but does not represent the general source interface. The arbitrary-subspace `projection` signature supplies algebraic properties of the chosen map, not its identification with a matrix for arbitrary real columns. For example the line spanned by `(1, sqrt 2)` has no nonzero integer vector, so no integer lattice basis can instantiate the missing case. `projection_distance` also exports only the lattice specialization of the source's arbitrary-subspace distance assertion. This is a coverage narrowing, not evidence that the lattice specialization itself is false. Existing lattice consumers can use that specialization.

Proposed fix: generalize the matrix theorem, then retain the present lattice formula as a separately named corollary. The corrected type is:

```lean
theorem projection_matrix {d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : LinearIndependent ℝ (fun j => fun i => A i j)) :
    ∀ v : Fin n → ℝ,
      proj (Submodule.span ℝ (Set.range (fun j => fun i => A i j))) v =
        (A * (A.transpose * A)⁻¹ * A.transpose).mulVec v
```

For full source coverage, also export the general distance component (the existing lattice theorem follows using `lattice_resonance`):

```lean
theorem projection_distance_subspace
    (V : Submodule ℝ (Fin n → ℝ)) (w : Fin n → ℝ) :
    (∀ v ∈ V, v ⬝ᵥ compProj V w = 0) ∧
    euclid (w - compProj V w) = euclid (proj V w) ∧
    (∀ u : Fin n → ℝ, (∀ v ∈ V, v ⬝ᵥ u = 0) →
      euclid (proj V w) ≤ euclid (w - u))
```

No new source assumption is needed. Prove these in G2 from the unique-projector characterization and the real Gram inverse. Rank zero remains a valid stronger extension.

### F2 — MAJOR: wave-1 elementary data depend on wave-7 declarations

Locators: design §6 L308–310 and L324–327; signatures L247–277 (`CoverParams`, `CoverParams.Valid`), L333–334 (`theoremCover`), L348–359 (`elementary`).

G7 owns `CoverParams` in `ResonanceGeometry/Covering.lean`, wave 7. P1 owns the constants and `elementary`, wave 1, and its DAG allows only `Poschel.Setting` as an import of `Poschel.Elementary`. However `theoremCover` returns `CoverParams n`, and the final conjunct of `elementary` is `(theoremCover ...).Valid`. Thus the exact P1 declarations cannot be elaborated through the advertised imports/wave order. The all-in-one scratch file hides this dependency. This is not a theorem falsehood or an unavoidable mathematical cycle.

Proposed fix preserving **all existing theorem signatures**: give the raw parameter record and source-validity predicate an early, dependency-light owner, for example `KAM/Nekhoroshev/Interfaces/CoverParams.lean`, available before P1. Move precisely these signatures there:

```lean
structure CoverParams (n : ℕ) where
  p : ℝ
  b : ℝ
  r0 : ℝ
  M : ℝ
  m : ℝ
  K : ℝ
  A : ℝ

structure CoverParams.Valid (c : CoverParams n) : Prop where
  hn : 1 ≤ n
  hp : 0 < c.p
  hb : 0 < c.b
  hr0 : 0 < c.r0
  hM : 0 < c.M
  hm : 0 < c.m
  hK : 1 ≤ c.K
  hA : c.p * c.M / (c.b * c.m) + Real.sqrt 2 ≤ c.A
```

Have both P1 and G7 import that module; keep `lam`, `radius`, `alpha`, `delta`, `actionBlock`, covering and cutoff theorems in their geometry owners. Assign `theoremCover` explicitly to P1's elementary module. Update the package ownership table, inputs and waves together. No signature weakening is required for F2, so the correction is an ownership/import change rather than a replacement theorem statement.

### N1 — LOW: document all dropped premises of `m_le_M`

Locators: design §5 comparison row “Other premises remain explicit”; signatures L341–346; blueprint `bpN:p9:m-le-M`.

Besides weakening positive ell to nonnegative ell, the signature omits the source's `0 < m` and `0 < M`. This is a true stronger lemma: a nonzero transverse vector gives `m * ‖ξ‖₂² ≤ Q[ξ,ξ] ≤ M * ‖ξ‖₂²` without either positivity assumption. Proposed fix: list both omissions explicitly and remove “Other premises remain explicit”. No signature change is needed.

## Per-signature audit

One row per declaration in the supplied file, including all 15 upstream excerpts (86 declarations total, 33 theorem bodies). Line numbers refer to the original signatures file. PASS concerns the stated component; package failures are recorded separately in F2.

| Lean name and signature line | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `KAM.NormalForm.zBall` (L29) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.freq` (L31) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.dotC` (L33) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.IsNonresonant` (L35) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.FreqLipschitz` (L38) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.cpx` (L46) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realNbhd` (L48) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realStrip` (L50) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realH` (L53) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.hessR` (L56) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.resSpan` (L58) | `bpN:p7:gradient` | PASS | Literal upstream real-span interface. |
| `KAM.Stability.IsOrthProj` (L61) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.resSpace` (L65) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.IsCloseToRes` (L67) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.IsQuasiConvex` (L70) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Nekhoroshev.Lattice` (L81) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.lattice` (L82) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.latticeDim` (L83) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.integerReal` (L84) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.eBall` (L85) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.resonance` (L86) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.basisMatrix` (L87) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis` (L90) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.integer_independent_real` (L97) | `bpN:p8:ext-indep` | PASS | Explicit new scalar-extension obligation; no assumed external closure. |
| `KAM.Nekhoroshev.lattice_resonance` (L100) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.latticeBasis` (L104) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis_change` (L107) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis_sub` (L114) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.gram` (L119) | `bpN:p8:volume-def` | PASS | Integer Gram determinant square root, empty determinant 1; basis choice auxiliary. |
| `KAM.Nekhoroshev.volume_def` (L122) | `bpN:p8:volume-def` | PASS | Integer Gram determinant square root, empty determinant 1; basis choice auxiliary. |
| `KAM.Nekhoroshev.projection_exists_unique` (L126) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.proj` (L130) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.compProj` (L133) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.projection` (L135) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.projection_zero` (L145) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.resonanceDistance` (L147) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.projection_distance` (L150) | `bpN:p8:projection` | PASS | Correct abstract projector/lattice-distance component; see F1 for missing general coverage. |
| `KAM.Nekhoroshev.projection_matrix` (L157) | `bpN:p8:projection` | FAIL | F1: restricts the real-matrix formula to integer lattice bases. |
| `KAM.Nekhoroshev.addVector` (L161) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume` (L164) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_index` (L177) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_cyclic` (L182) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_hadamard` (L185) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.klattice` (L189) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.maximalK` (L192) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.maximal` (L196) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.zone` (L212) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.zoneStratum` (L215) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.blocks` (L218) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.blocks_cover` (L221) | `bpN:p8:blocks-cover` | PASS | Finite family and covering for arbitrary frequency; n=0 extension is true. |
| `KAM.Nekhoroshev.sqrt` (L226) | `bpN:p8:sqrt` | PASS | Both inequalities retained; positivity follows from lower bound 1. |
| `KAM.Nekhoroshev.geom_formula` (L229) | `bpN:p8:geom-formula` | PASS | Stronger arbitrary-real-subspace formulation; all projection identities retained. |
| `KAM.Nekhoroshev.geometric` (L237) | `bpN:p8:geometric` | PASS | Exact positive parameters, ratio range, two nonresonance conclusions. |
| `KAM.Nekhoroshev.CoverParams` (L247) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.lam` (L256) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.radius` (L259) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.alpha` (L262) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.delta` (L264) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.actionBlock` (L266) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.Valid` (L269) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.covering` (L279) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.cutoffs` (L295) | `bpN:p8:cutoffs` | PASS | Correct inclusions and Kg >= sqrt(n) Ka direction; zero-rank closeness true. |
| `KAM.Nekhoroshev.Theorem1Setting` (L308) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.setting` (L327) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.thmA` (L329) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.thmEps0` (L330) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.thmK` (L331) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.theoremCover` (L333) | `bpN:p9:setting / s-blocks#data` | PASS | Exact S1-S4 and constants; see F2 for definition ownership. |
| `KAM.Nekhoroshev.m_le_M` (L341) | `bpN:p9:m-le-M` | PASS | True strengthened transverse-vector lemma; omitted positivity premises noted in N1. |
| `KAM.Nekhoroshev.elementary` (L348) | `bpN:p9:elementary` | PASS | All source arithmetic retained; added Valid conjunct is true but causes F2. |
| `KAM.Nekhoroshev.local_real_regularity` (L362) | `stepN:p9:om-max#local-real-regularity` | PASS | Actual frozen realPart/frequencyMap; correct real restriction of Hessian. |
| `KAM.Nekhoroshev.FrequencyBall` (L371) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.FrequencyBall.points` (L378) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.FrequencyBall.maximum` (L381) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.frequency_maximum` (L384) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0_radius` (L391) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0Ball` (L394) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0` (L398) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.full_rank_zone` (L407) | `stepN:p9:t1-b#full-rank-zone` | PASS | Correct top-lattice identity and strict frequency threshold equivalence. |
| `KAM.Nekhoroshev.block_hyp` (L416) | `bpN:p9:block-hyp` | PASS | Exact singleton restrictions and every Part-7 numerical premise; no orbit conclusion assumed. |
| `KAM.Nekhoroshev.block_frequency_radius` (L447) | `bpN:p9:block-stab#frequency-size` | PASS | Exact rLambda/2 ball; strict guard follows from rLambda <= r0 and r0 > 0. |
| `KAM.Nekhoroshev.blockBall` (L453) | `bpN:p9:block-stab#frequency-size` | PASS | Exact rLambda/2 ball; strict guard follows from rLambda <= r0 and r0 > 0. |
| `KAM.Nekhoroshev.blockAdm` (L462) | `bpN:p9:block-stab` | PASS | Exact stopped statement; max/Euclidean distinction, full rank and Omega=0 handled. |
| `KAM.Nekhoroshev.local_field` (L468) | `bpN:p9:block-stab#local-field` | PASS | Open singleton tube; indicator and total Hamiltonian fields agree locally. |
| `KAM.Nekhoroshev.block_stab` (L478) | `bpN:p9:block-stab` | PASS | Exact stopped statement; max/Euclidean distinction, full rank and Omega=0 handled. |
| `KAM.Nekhoroshev.thm1` (L494) | `bpN:p9:thm1` | PASS | Joint branches and constants retained; hI supplies nonempty P; no containment assumed. |

## Consumer verdict

**PASS for the current mathematical uses; package dispatch blocked by F2.** Literal cross-track searches for `\Nref{bpN:p8:` and `\Nref{bpN:p9:` in I/P find no direct theorem applications. Their `bpN:p3:*` references use the earlier ODE layer, outside this design; they are not additional consumers of a Part-8/9 signature. The Part-8 prose advertises future Track-P reuse, and its action covering accepts arbitrary carriers and maps without Hamiltonian premises.

- **N Part 7:** it supplies the stability interfaces used here. Read exact `nonresonant`, `resonant_prop2` and `stopped_extension` types in `NPart67Signatures.lean` (L637, L659, L827), including the complex Hessian formula, subgroup carrier, every radius inequality and the time predicate. `block_hyp` supplies their source premises; `block_stab` proves the contained-orbit intermediate estimate before invoking `stopped_extension`. No orbit containment or stability conclusion is assumed in `Theorem1Setting`, `block_hyp`, `block_stab` or `thm1`. Singleton membership is supplied by equality with the initial action. `conjExp (9/8) = 9` supplies the numerical substitution.
- **N Part 10:** `hypotheses-check`, `confinement-estimate`, and `stepN:p10:cf-orbit/cf-branch` can instantiate `thm1` with the frozen real field, `Fin n → ℝ` action carrier, arbitrary connected interval and two-sided `HasDerivAt`. `n ≥ 3` supplies `n ≥ 2`. Actual initial membership supplies nonempty P. The original period-one h,f at width s/2 give the exact exponent and radius after canceling the paired 2π factors. There is no newly imposed frequency lower bound in Part 9; the caller already supplies its nonexceptional-frequency estimate.
- **N Part 11:** `p11c-partial-stability.tex:146–151` uses `covering` and `cutoffs` with b=1/32, A=40M1/m1, and the map at a singleton initial action. `CoverParams.Valid` imposes neither m≤M nor a Hamiltonian, so this substitution is available once the caller proves its displayed numerical inequality. The radius and nonresonance conclusions have the required carriers. The separate extended dynamics are re-derived there; Part 9's orbit theorem does not pretend to cover the slow-variable product carrier. The general arbitrary-subspace `geom_formula` remains available for real vectors.
- **N Part 12:** no direct `bpN:p8:*`/`bpN:p9:*` use found. Earlier-layer ODE/averaging references do not add a new Part-8/9 consumer obligation.

## Frozen-object verdict

**PASS.** Read the actual frozen `FrequencyMap`, `HamiltonianVectorField`, `RealHamiltonian`, Nekhoroshev `RealPart` and `IsSolutionOn` definitions. The signatures use `KAM.frequencyMap`, `KAM.hamiltonianVectorField` and `KAM.Nekhoroshev.realPart` themselves. The upstream `realHamiltonian_eq_realH` is a stated bridge to the frozen `realHamiltonian`; its equality follows by unfolding the two real restrictions. The two-sided derivative clause of `IsSolutionOn` supplies exactly the arbitrary-orbit derivative used by Part 10; membership and differentiability need not be added as assumptions to Part 9. Local indicator-field agreement is addressed by `local_field`, using openness rather than global equality of total extensions. There is no replacement Newton/restricted predicate and no provider import or frozen theorem closure.

## Definition and totality verdict

**PASS.** All 15 upstream excerpts match the owning signatures literally. AddSubgroup lattices do not assume saturation. No global instance changes the max norm of bare function or matrix types. Euclidean norms and integer cutoffs are explicit. The rank-zero Gram determinant gives volume 1, basis independence and positivity are explicit proof obligations, and the projection is chosen from a unique characterization. None is accepted as proved by the scratch elaboration.

`zone` treats the zero lattice separately, and `zoneStratum` makes dimensions outside 1…n empty. `lam 0` is not used to justify a zero-rank zone. `FrequencyBall` supplies center membership, nonnegative radius and strict radius < r0; `frequency_maximum` asserts nonemptiness, compactness, attainment and the exact M-radius bound, so sSup junk values are not used. Empty P is permitted in pure setting/arithmetic lemmas, while orbit/maximizer users supply initial membership. `thmK` is used with positive eps and eps0. `blockAdm` uses multiplication, with explicit full-rank all-time and zero-Omega behavior. The shared constants depend only on the source-listed data; proof arguments and unused setting parameters in a maximum's type do not change its unfolded value.

Allowed strengthening checked: `geom_formula` accepts every real subspace; several algebraic helpers and `blocks_cover` also hold at n=0; `m_le_M` has the true premise drops in N1; `thm1` drops an independently stated nonempty-P premise already implied by hI. The strict exceptional threshold, one-half radius, sqrt(n) cutoff factor and strengthened r0≤ell/(2M) are existing blueprint choices, not silent changes introduced by these signatures.

## Package verdict

**FAIL (F2).** The 12 advertised packages / 13 proposed files all have estimates ≤650 lines, below the 1500-line cap. G1–G7 have a sensible lattice → projection → volume → maximality → blocks → geometry → covering order. P3–P5 follow upstream stability and stopped extension. The explicit restriction preventing upstream projection/energy modules from importing the new Part-8 projection module prevents a real import cycle. The remaining concrete dependency defect is P1's early use of G7-owned raw records. Fix ownership before dispatch. Default-heartbeat failures must still cause proof splitting; no budget override is authorized.

## Validation and limitations

All checks below were rerun independently for this audit, sequentially, with `LEAN_NUM_THREADS=1`. The existing design gate invokes `nice -n 5 lake env lean` against `/root/code/KAM-inp`'s shared build; no worktree rebuild was attempted.

1. **Original signatures, one targeted invocation:**

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n89 .drafts/scratch/N89Signatures.lean
   ```

   Exit **0**; exactly **33** “declaration uses `sorry`” warnings, no errors or other Lean diagnostics. The original and user-requested scratch copy have the same SHA-256 recorded above.

2. **Mathlib/API and axiom probe:** same gate with `.lake/abi-scratch/N89AuditProbe.lean`, exit **0**. This separate probe used the signature declarations plus `#check`/`#print axioms` commands; it was not a production implementation. All **22** checked declarations resolved with compatible types. Mathlib names checked were `Submodule.basisOfPid`, `Pi.basisFun`, `AddSubgroup.toIntSubmodule`, `Matrix.PosDef.conjTranspose_mul_self`, `Matrix.PosDef.det_pos`, `Matrix.det_mul`, `Matrix.det_transpose`, `Matrix.det_fromBlocks₁₁`, `Matrix.isUnit_iff_isUnit_det`, `Int.isUnit_iff`, `Module.Basis.invertibleToMatrix`, `LinearIndependent.iff_fractionRing`, `Matrix.rank_eq_finrank_span_cols`, `IsCompact.exists_isMaxOn`, `Real.rpow_natCast`, and `Real.rpow_mul`. Also checked the existing KAM holomorphic-regularity theorem, all three norm/cutoff interfaces, `HeadParams.expo`, and `WBound.mono`.

   In particular the Schur API requires an invertible leading block, and `iff_fractionRing` requires a fraction-field action/scalar tower on its ambient module; neither alone proves integer-to-real independence. The design explicitly leaves that proof to `integer_independent_real`, so this is not an unpaid premise disguised as a library theorem. The F1 generalized matrix type was separately checked as a well-formed proposition; no proof of the proposed repair is claimed.

   `#print axioms` for `projection_matrix`, `geometric`, `covering`, `block_hyp`, `block_stab`, and `thm1` each returned exactly:

   ```text
   [propext, sorryAx, choice, Quot.sound]
   ```

   Therefore these remain draft statements, not independently established results. The temporary probe was deleted after the run.

3. **Repository lint:** reused the designer's existing, unmodified PATH adapter to route the linter's internal ABI elaboration through the same gate:

   ```sh
   LEAN_NUM_THREADS=1 PATH="$PWD/.drafts/scratch/gated-bin:$PATH" scripts/lint_sources.sh
   ```

   Exit **0**, with exact output:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

4. **Read-only inventory/hygiene:** 82 unique design rows = 82 graph nodes; 15/15 literal upstream excerpts; 86 per-declaration audit rows; Appendix/signatures equality; original/scratch checksum equality. `git diff --check` and `git diff --no-index --check /dev/null <this-report>` both exit **0**. `git status --short` lists only this untracked report. No heartbeat, recursion-depth or synthesis-budget override was used.

**Validation verdict: syntax/API/lint PASS; overall design FAIL for F1/F2.** No new production module exists to target with `lake build`; the brief's signature elaboration is the applicable targeted Lean check.

The only persistent audit deliverable is this report. The original signatures, design, blueprints, graph, frozen files, manifest and generated files were not edited. The user-requested scratch copy was refreshed from the original; temporary audit probes are deleted after checking. No git state-changing command, production build, cache fetch or library rebuild was run.

## Suspected errata and deviations

No newly verified defect in Pos93 is asserted: this is a blueprint/signature audit, not an independent PDF audit. Inherited source issues remain as documented in design §5: p.200 maximality ambiguity; pp.202–204 omitted dimension/volume/maximum-comparison arguments; the strengthened radius repair to the printed “r0≤4ell/m”; the sqrt(n) norm adaptation; and the strict exceptional branch improving the printed “except when ‖omega(I0)‖≤mr0/8”. These have quoted locations and explanations in the design and blueprint; they must remain in prover handoffs. No source repair, owner ruling or frozen change was made by this audit. F1/F2 are design deviations, and N1 is an incomplete description of a valid strengthening.
