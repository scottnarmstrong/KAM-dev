# W0-NORMAL independent audit 2 — tight delta

**Verdict: PASS WITH NOTES for the finite-mode Qdef/resavg/AB repair. F1 is resolved on the declared finite polar carrier. Full source-node AB/avgG completion remains FAIL / PARTIAL because F2 is unresolved.** No provider or manifest-bound theorem is offered for sealing; seal readiness is N/A. No unchanged result is re-audited or promoted by this report.

## Scope and identity

Audit date: 2026-10-30. Worktree: `/root/code/KAM-inp-wpc`. Audited HEAD: `498f0f8361589e65305889c2860f30240b05d02d`; comparison `inp`: `1bf1f17e58b446e605ea638600114cc8a7de8560`; Round-1 baseline: `836404bdcde3ae89b4e1c0a856bfdb74969f7f38`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, Round-1 report, handoff including AUDIT FOCUS and Round 2, `docs/tracks/W/W-STATEMENTS.md`, relevant W0 source and adopted errata, and W3/W7 consumption statements. Applied the lean-statement-audit workflow to the new infrastructure contracts; there is no frozen AB anchor. The user's exact report path overrides the generic brief's main-worktree destination. Initial status contained only the pre-existing untracked Round-1 report, which was preserved.

Inspected `git diff inp...HEAD` and `git diff 836404bd HEAD -- KAM/Wave/Normal`. The tight Normal delta is exactly four files: ActionCoeff (docstrings only), Nonresonance (generic `signSide` only), ResonantBalance (new, 123 lines), ResonantPart (new, 367 lines), 499 insertions and 4 deletions. The other five original Normal files are byte-unchanged against Round 1. Build/replay of Nondegeneracy below is a mechanical compatibility check of a consumer of the generalized definition, not a fresh mathematical audit. The merged source has unrelated W0 gradient/convolution edits; Qdef/AB/resavg formulas at W0:260–307 are unchanged. No review of those unrelated edits is claimed.

Snapshot SHA256:

| File | SHA256 |
|---|---|
| `KAM/Wave/Normal/ResonantBalance.lean` | `3c2d6c597c23284dc3a542116c865c7c602a9246e39664724bc7a2a2ad7ae313` |
| `KAM/Wave/Normal/ResonantPart.lean` | `b0a71837d418b2fdb35c528818589e7659ffcb4e578aeed5a350e6c7a9a504a2` |
| `blueprint-W/parts/w0-normalization.tex` | `83f7f2ebcbf97613e30433401435e374f2731749fd9ef8b44ba2ac9b7697505b` |

Direct frozen definitions remain `wave.lam.v1` and `wave.sineMode.v1`, SEALED under D41. Their manifest/file hashes agree: Lam `097b70740bbedd0463d2e0ffb98e99bf508f81207b8370ac05ddc91aa3e05f81`; SineMode `708e6e5d2d878d13e87acb6f2e2b4a057be17a33f9999b417cbaf75bac555263`. No provider or DRAFT_SORRY import enters the new modules.

## Findings and adversarial disposition

**F1: finite repair accepted.** W0:272–275 defines “the sum of the resonant monomials of G^tan (with their coefficients)”. `ResonantPart.lean:108–112` now defines exactly this finite object with `S = tangentialQuarticTuple`: corrected prefactor 1/16, all ordered positive-mode quadruples, all 16 sign patterns, coefficient g divided by four square roots of frequencies, and an actual zero-divisor filter. It is not defined by the desired A/B formula or by an angle average. `quarticG_eq_complex` (:325) connects the unfiltered expansion to the original finite `quarticG(q)` for arbitrary real q,p using z=(q+ip)/√2. Positivity of the frequencies makes the four-root denominator equivalent to the source sqrt(product).

The previously missing nonresonance consumption is explicit: `signBalanced_of_resonant` (Balance:59–72) applies `quartic_nonresonance` after the injective mode shift. `signBalanced_sum_zero` proves the reverse implication by taking f=λ, and cancellation of phases by taking f=φ. The g=0 branch in `resonantQuartic_term_eq` discards only zero-coefficient terms; it does not incorrectly claim all unsupported resonances are balanced. `signBalanced_iff` and `_count` retain repeated-index multiplicities: the diagonal has six balanced patterns; a fixed two-pair tuple has four. Ordered mode tuples then give the source's diagonal/off-diagonal constants.

`resonantQuarticPart_polar` (:143), `resonantQuarticReal_all` (:202), and the old `avgG_eq` compose to the full finite resonant=average identity. `_split` and `_normal` select tangential terms by zeroing tangential amplitudes; `_tangential_eq` (:271–305) composes these with `partial_avgG_eq`. The audit probe independently elaborates full and tangential resonant=average equalities and the supported divisor-zero iff balanced statement. Thus a separate theorem integrating each individual complex monomial is unnecessary for this finite equality; the valid counting/moment proof establishes the same conclusion.

Adversarial checks: looked for a missing reverse implication, loss of g=0 support, incorrect diagonal multiplicity, a filter on only the first tuple position, wrong phase sign, and cancellation hiding nonresonant terms. None survives inspection. Tuple predicates inspect all four entries; `true` selects z with +λ, giving exp(-iλt) as prescribed. All 16 choices have the same coefficient for a fixed tuple; grouping duplicate monomials preserves both the divisor and tangential membership. No conclusion-shaped premise has replaced the missing bridge. ActionCoeff's changed docstrings correctly describe its older theorem as a helper.

**F2: retained, not repaired.** Source W0:293–296 says the average is “computed on finitely supported q and extended by the absolutely convergent formula”. Every new sum still ranges over `Fin N`. No theorem here identifies an infinite weighted-space Hamiltonian/resonant projection with these truncations or justifies the limiting passage. `resonantQuarticPart_tangential_eq` also takes nonnegative real actions and polar values z=√I exp(-iφ); conjugates are dependent coordinates. W3 `quartic-ident` (`w3-birkhoff.tex:282–291`) requires all w in its two-sided complex space with I_j=w_j w_{-j}; its two coordinates are independent. Free real phases do not supply that complexification. Even the finite independent-complex identity remains unstated in this package. These are scope gaps, not counterexamples to the finite theorem. No explicit arbitrary-z polar-surjectivity corollary is exported either; the accepted contract here is the actual polar theorem.

Downstream: finite polar consumers can now rewrite the genuine resonant sum to A/B or to the tangential average. W3's infinite complex identity, W5's analytic normal-form attachment, and identification of W7's abstract affine frequencies with the wave Hamiltonian still need F2 and their own bridges. No consumer closure is inferred from imports, coefficient agreement, or compilation.

**H1: discharged by current authorization.** The user explicitly authorizes regenerated `KAM.lean` / `KAM/Root`. The current `inp...HEAD` diff has nine generated imports in `KAM/Root/Wave.lean`; `KAM.lean` itself has no delta against current inp. This authorized root delta is not a Round-2 failure. The auditor did not regenerate or edit roots.

The handoff's normal-part wording needs care: `normalQuarticTuple` is an all-normal *predicate*. Applying `resonantQuarticPart` to it still imposes resonance, and `resonantQuarticReal normalQuarticTuple` is also a resonant object. Neither is the full unfiltered G^nor of Qdef. There is no separately named unfiltered normal functional here. This causes no defect in AB, whose subtraction uses the normal part of the average/resonant sum. Construction of the full partial normal-form Hamiltonian is outside this delta.

## Declaration ledger

Names below are in `KAM.Wave`. PASS means the declared finite/helper contract, never full source closure.

| Node | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| sign encoding | `unitOfBool_val` (Balance:35) | PASS | Units agree with Bool signs. |
| resavg helper | `signSide_count` (Balance:38) | PASS | Equal multisets imply zero signed counts; generic carrier and DecidableEq are typing. |
| resavg | `signBalanced_of_resonant` (Balance:59) | PASS | Consumes nonresonance with exactly g≠0 and divisor=0. |
| pair classification | `signBalanced_iff` (Balance:86) | PASS | Exhaustive 16-pattern pairing equivalence. |
| multiplicity | `signBalanced_count` (Balance:98) | PASS | 4(P1+P2+P3)−6P4, including repeated indices. |
| reverse/phase | `signBalanced_sum_zero` (Balance:106) | PASS | Any real f; yields both required cancellations. |
| polar helper | `conjSelect_polar` (Part:60) | PASS | Correct conjugate and minus-phase convention for all real r,φ. |
| resavg helper | `quarticMonomial_polar` (Part:67) | PASS | Balanced phases cancel; h is a conditional helper premise. |
| resavg | `resonantQuartic_term_eq` (Part:87) | PASS | Supported resonance iff balance; zero coefficients handled. |
| resavg | `resonantQuartic_term_sum_eq` (Part:122) | PASS | Correct signed-pattern sum and cast. |
| resavg | `resonantQuarticPart_polar` (Part:143) | PASS | Genuine projection is phase independent for arbitrary finite tuple selector S. |
| tangential split | `resonantQuarticReal_split` (Part:179) | PASS | Complementary tuple restrictions. |
| avgG bridge | `resonantQuarticReal_all` (Part:202) | PASS | Correct full finite action polynomial, all real amplitudes. |
| normal restriction | `resonantQuarticReal_normal` (Part:249) | PASS | Zeroing first two amplitudes selects all-normal resonant terms. |
| AB | `resonantQuarticPart_tangential_eq` (Part:271) | PASS WITH NOTES | Genuine finite polar Qdef left side; correct A/B; F2 retained. |
| Gz expansion | `sum_quarticMonomial` (Part:314) | PASS | Exact 16-term expansion for arbitrary finite complex z. |
| Gz attachment | `quarticG_eq_complex` (Part:325) | PASS | Finite quarticG(q), real q,p, corrected 1/16. |
| avgG / AB helpers | `avgG_eq`, `partial_avgG_eq` (ActionCoeff docstrings only) | Unchanged | Formula/body not re-audited; finite scope retained. |
| full AB / avgG source nodes | no infinite/independent-complex export | FAIL completion | F2 remains; no seal claimed. |

## Definitions and carriers

Every changed/new definition is literal and total on its declared finite carrier. For each row: BODY_MATCH=OK, PUBLIC_CARRIER=OK for that finite/helper object, WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS. This does not identify its carrier with the infinite source carrier. The `if` branches select source-defined signs, tuple support, or resonance; none is an invented off-domain fallback. Positive m is required wherever frequencies occur. There are no new choice-selected mathematical objects.

| Definition | Body classification |
|---|---|
| `signSide` (Nonresonance:30, changed) | Same multiset sum, generalized from ℕ+ to arbitrary α; specialization to old positive modes is unchanged. |
| `unitOfBool` (Balance:33) | Literal ±1 integer unit coding. |
| `signBalanced` (Balance:55) | Zero signed count at every mode; literal equality of exponent vectors. |
| `signBalancedCond` (Balance:76) | Six 2+2 patterns with pair equalities; other patterns False; equivalence proved. |
| `conjSelect` (Part:45) | z or its conjugate, for all complex z. |
| `quarticMonomial` (Part:47) | Product of four selected factors. |
| `quarticDivisor` (Part:51) | Signed frequency sum; no absolute value or altered zero locus. |
| `normQuarticCoeff` (Part:56) | g divided by four positive frequency square roots. |
| `resonantQuarticPart` (Part:108) | Literal finite resonant projection of the corrected expansion, restricted by S. |
| `resonantQuarticReal` (Part:115) | Explicit balanced-pattern amplitude sum; identified with projection by `_polar`. |
| `allQuarticTuples` (Part:166) | True selector, including empty finite carriers harmlessly. |
| `isTangentialMode` (Part:169) | Zero-based index <2, i.e. physical modes 1,2. |
| `tangentialQuarticTuple` (Part:172) | At least one of four modes tangential. |
| `normalQuarticTuple` (Part:176) | All four modes normal; predicate, not an unfiltered G^nor functional. |
| `quarticGComplex` (Part:310) | Unfiltered finite 1/16 expansion; `_eq_complex` supplies its original-q attachment. |

## Binder audit

Expanded principal contracts, one row per binder (no bundled assumptions). Source locators are in `blueprint-W/parts/w0-normalization.tex`, except mass standing assumption in its opening and the referenced W0 complex-coordinate convention.

| Contract | Binder | Bin | Source/meaning |
|---|---|---|---|
| AB | `{n : ℕ}` | TYPING | Finite specialization, two tangential plus n normal modes. |
| AB | `m : ℝ` | TYPING | AB:278 mass parameter. |
| AB | `hm : 0 < m` | STANDING | W0:3 and AB:278. |
| AB | `I : Fin 2 → ℝ` | TYPING | Tangential actions, AB:278. |
| AB | `Z : Fin n → ℝ` | TYPING | Finite normal actions, AB:278. |
| AB | `hI : ∀ i, 0 ≤ I i` | SOURCE | I_i=abs(z_i)²; polar reconstruction, resavg:294. |
| AB | `hZ : ∀ j, 0 ≤ Z j` | SOURCE | Same for normal modes. |
| AB | `φ : Fin (2+n) → ℝ` | TYPING | Arbitrary independent angles, resavg:294–295. |
| Gz | `{N : ℕ}` | TYPING | Finite restriction of Gz sum. |
| Gz | `m : ℝ` | TYPING | Mass parameter. |
| Gz | `hm : 0 < m` | STANDING | W0:3. |
| Gz | `q : Fin N → ℝ` | TYPING | Real q coordinates, Gz:260–265. |
| Gz | `p : Fin N → ℝ` | TYPING | Real p coordinates, W0:z. |
| polar projection | `{N : ℕ}` | TYPING | Finite restriction. |
| polar projection | `S : Fin N → Fin N → Fin N → Fin N → Prop` | TYPING | Arbitrary selector generalizes tangential/full sums. |
| polar projection | `m : ℝ` | TYPING | Mass parameter. |
| polar projection | `hm : 0 < m` | STANDING | W0:3. |
| polar projection | `r : Fin N → ℝ` | TYPING | Real amplitudes; arbitrary signs strengthen sqrt-action case. |
| polar projection | `φ : Fin N → ℝ` | TYPING | All real phases, resavg:294–295. |
| supported resonance | `{N : ℕ}` | TYPING | Finite modes. |
| supported resonance | `m : ℝ` | TYPING | Mass parameter. |
| supported resonance | `hm : 0 < m` | STANDING | W0:3. |
| supported resonance | `e : Bool × Bool × Bool × Bool` | TYPING | Four signs of Gz expansion. |
| supported resonance | `i : Fin N` | TYPING | First mode. |
| supported resonance | `j : Fin N` | TYPING | Second mode. |
| supported resonance | `k : Fin N` | TYPING | Third mode. |
| supported resonance | `l : Fin N` | TYPING | Fourth mode. |
| supported resonance | `hg : gN i j k l ≠ 0` | SOURCE | resavg:293, nonzero coefficient. |
| supported resonance | `hdiv : Σ signed λ = 0` | SOURCE | resavg:294, resonance premise. |

Counts (SOURCE, STANDING, TYPING, RULED, EXCESS): AB=(2,1,5,0,0); Gz=(0,1,4,0,0); polar projection=(0,1,5,0,0); supported resonance=(2,1,7,0,0). The remaining helpers have only their displayed typing data and mass positivity where present, except `signSide_count`'s multiset equality and `quarticMonomial_polar` / `signBalanced_sum_zero`'s balance premise. Those are honest named conditional helpers, supplied by proved producers in the main results, not source-node substitutes. No extra instance or bundled field hides a proof obligation.

## Verification

All audit-owned Lean/Lake commands were serial, with `LEAN_NUM_THREADS=1` and nice priority 5. Other worktrees' unrelated processes were not started or altered by this audit. No clean/rebuild-from-scratch, cache operation, package mutation, or heartbeat override was performed.

Targeted build, exit 0:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpc KAM.Wave.Normal.ResonantBalance KAM.Wave.Normal.ResonantPart KAM.Wave.Normal.Nondegeneracy
```

```text
[inp-gate] slot 3 acquired 18:20:49 for KAM.Wave.Normal.ResonantBalance KAM.Wave.Normal.ResonantPart KAM.Wave.Normal.Nondegeneracy
Build completed successfully (2845 jobs).
```

Kernel replay, exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Normal.ResonantBalance KAM.Wave.Normal.ResonantPart KAM.Wave.Normal.Nondegeneracy
```

```text
replaying KAM.Wave.Normal.Nondegeneracy
replaying KAM.Wave.Normal.ResonantPart
replaying KAM.Wave.Normal.ResonantBalance
```

Probe command, final exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W0Audit2.lean > .lake/abi-scratch/W0Audit2.log 2>&1
```

All 17 theorem names were obtained by `^theorem (\w+)` over the two new files, exactly the 17 new theorem rows above. Output: `unitOfBool_val` uses `[propext]`; each of the other 16 uses `[propext, choice, Quot.sound]` (`choice` prints unqualified because the probe opens Classical, i.e. `Classical.choice`). No sorryAx or unexpected axiom. The six additional examples produced no output. The first probe attempt exited 1 solely because the audit's explicitly expanded `if S ...` lacked a classical decidability context; adding `open Classical` and `noncomputable section` to the scratch file fixed it. No package source was changed.

Reproducible complete probe:

```lean
import KAM.Wave.Normal.ResonantPart
open KAM.Wave Classical
noncomputable section
open scoped BigOperators
#print axioms KAM.Wave.unitOfBool_val
#print axioms KAM.Wave.signSide_count
#print axioms KAM.Wave.signBalanced_of_resonant
#print axioms KAM.Wave.signBalanced_iff
#print axioms KAM.Wave.signBalanced_count
#print axioms KAM.Wave.signBalanced_sum_zero
#print axioms KAM.Wave.conjSelect_polar
#print axioms KAM.Wave.quarticMonomial_polar
#print axioms KAM.Wave.resonantQuartic_term_eq
#print axioms KAM.Wave.resonantQuartic_term_sum_eq
#print axioms KAM.Wave.resonantQuarticPart_polar
#print axioms KAM.Wave.resonantQuarticReal_split
#print axioms KAM.Wave.resonantQuarticReal_all
#print axioms KAM.Wave.resonantQuarticReal_normal
#print axioms KAM.Wave.resonantQuarticPart_tangential_eq
#print axioms KAM.Wave.sum_quarticMonomial
#print axioms KAM.Wave.quarticG_eq_complex

-- Explicit finite AB consumer, including the complex-valued left side.
example {n : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin 2 → ℝ) (Z : Fin n → ℝ)
    (hI : ∀ i, 0 ≤ I i) (hZ : ∀ j, 0 ≤ Z j) (φ : Fin (2+n) → ℝ) :
    resonantQuarticPart tangentialQuarticTuple m hm
      (fun t => (Real.sqrt (Fin.append I Z t) : ℂ) * Complex.exp (-(Complex.I * φ t))) =
      (((1 / 2 : ℝ) * ∑ i, ∑ j, actionA m hm i j * I i * I j +
        ∑ j, ∑ i, actionB m hm j i * I i * Z j : ℝ) : ℂ) :=
  resonantQuarticPart_tangential_eq m hm I Z hI hZ φ
-- Term-level resavg bridge, not merely an import or matching closed forms.
example {N : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin N → ℝ)
    (hI : ∀ j, 0 ≤ I j) (φ : Fin N → ℝ) :
    resonantQuarticPart allQuarticTuples m hm
      (fun j => (Real.sqrt (I j) : ℂ) * Complex.exp (-(Complex.I * φ j))) =
      (avgG m hm I : ℂ) := by
  rw [resonantQuarticPart_polar, resonantQuarticReal_all, avgG_eq m hm I hI]
  simp only [Real.sq_sqrt (hI _)]
-- Both directions of the supported resonance characterization.
example {N : ℕ} (m : ℝ) (hm : 0 < m) (e : Bool × Bool × Bool × Bool)
    (i j k l : Fin N) (hg : gN i j k l ≠ 0) :
    quarticDivisor m hm e i j k l = 0 ↔ signBalanced e i j k l := by
  constructor
  · exact signBalanced_of_resonant m hm e i j k l hg
  · intro h
    exact signBalanced_sum_zero e i j k l h (lamMode m hm)
-- The defining equation retains the divisor filter and corrected prefactor.
example {N : ℕ} (S : Fin N → Fin N → Fin N → Fin N → Prop)
    (m : ℝ) (hm : 0 < m) (z : Fin N → ℂ) :
    resonantQuarticPart S m hm z =
      (1 / 16 : ℂ) * ∑ i, ∑ j, ∑ k, ∑ l,
        if S i j k l then (normQuarticCoeff m hm i j k l : ℂ) *
          ∑ e : Bool × Bool × Bool × Bool,
            (if quarticDivisor m hm e i j k l = 0 then quarticMonomial z e i j k l else 0)
        else 0 := rfl
example {N : ℕ} (m : ℝ) (hm : 0 < m) (q p : Fin N → ℝ) :
    (quarticG m hm q : ℂ) = quarticGComplex m hm
      (fun j => ((q j : ℂ) + Complex.I * (p j : ℂ)) / (Real.sqrt 2 : ℂ)) :=
  quarticG_eq_complex m hm q p

example {n : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin 2 → ℝ) (Z : Fin n → ℝ)
    (hI : ∀ i, 0 ≤ I i) (hZ : ∀ j, 0 ≤ Z j) (φ : Fin (2+n) → ℝ) :
    resonantQuarticPart tangentialQuarticTuple m hm
      (fun t => (Real.sqrt (Fin.append I Z t) : ℂ) * Complex.exp (-(Complex.I * φ t))) =
      ((avgG m hm (Fin.append I Z) - avgG m hm (Fin.append (0 : Fin 2 → ℝ) Z) : ℝ) : ℂ) := by
  rw [resonantQuarticPart_tangential_eq m hm I Z hI hZ φ,
      partial_avgG_eq m hm I Z hI hZ]
```

Mandated slim lint (runs `scripts/lint_sources.sh` with the slim artifact overlay), exit 0:

```sh
LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpc > .lake/abi-scratch/W0Audit2-lint.log 2>&1
```

```text
check_lean_modules: PASS (1657 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No stale-root or forbidden-token warning. Frozen-anchor and ABI validation passed.

Static checks: `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option|Provider|DRAFT_SORRY' KAM/Wave/Normal` had no matches. New files satisfy copyright/module/public-import/docstring/exposed-public-section requirements. The changed original files have 290 and 162 lines, new files 123 and 367; all Normal files remain below 1500. `git diff inp...HEAD --check` and working-tree `git diff --check` exit 0 with no output. Both `git diff inp...HEAD -- KAM/Frozen manifest README.md` and the same protected-path diff against `836404bd` are empty. Authorized generated-root imports are accounted for above.

## Errata, deviations and closeout

No new suspected pinned-source or blueprint defect established. Existing confirmed E-PDE-W-1/2 (`docs/errata/ledger.json:2635–2660`) govern the corrected 1/16 and actions I=abs(z)². This audit used the local blueprint and adopted ledger, not fresh original-PDF page images. Bool signs, zero-based finite modes, tuple filters and signed-count predicates are faithful encodings. Counting balanced patterns and reusing the moment formula is a valid alternate route for finite resavg. Finite restriction and the absence of independent complex coordinates are explicit remaining deviations from full source scope (F2).

Only `/root/code/KAM-inp-wpc/docs/tracks/W/audits/W0-NORMAL-audit-2.md` was created/edited in the repository by this audit. Audit-owned temporary probe/log files were removed after recording evidence. The Round-1 report remains untouched. No git mutation, proof repair, frozen change, root regeneration or claim of full W0/W3/W5/W7 closure was made. F1 is closed only for the checked finite polar contract; F2 remains open. Audit complete.
