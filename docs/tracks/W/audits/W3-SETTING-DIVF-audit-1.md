# W3-SETTING-DIVF independent package audit 1

Date: 2026-10-31. Auditor: maud-wpka-1. **Overall: FAIL for complete source-label coverage (F1).**
The four highlighted analytic results pass statement review: corrected quartic identification,
the divisor bound, the smoothing generator, and the homological identity on all of the base space.
The failure concerns the general Hamiltonian-field definition within `bpW:w3:hamfield-def`,
not a false concrete divisor or homological theorem.

No provider or seal is present. Provider/frozen-type and seal-body probes are N/A by the handoff's
AUDIT FOCUS. This report does not certify W3's later flow, real-restriction, remainder, transport,
W5/W8 assembly, or frozen `nlw2`.

## Snapshot and authority

- Worktree: `/root/code/KAM-inp-wpka`, resolving to
  `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpka`.
- Audited HEAD: `47fa21b99dcdc37a18295701c6a4afb96e1c3a12`.
- Comparison `inp`: `9c6d9128c2032acd1fb764896a149d5153119206`, also the current
  `/root/code/KAM-inp` HEAD when checked.
- Read the package brief, AGENTS.md, PLAN.md, DECISIONS.md, combined handoff and its AUDIT FOCUS.
  The generic brief's `docs/tracks/W/statement.md` does not exist; read
  `docs/tracks/W/W-STATEMENTS.md` instead, with D30/D41 overriding its old draft-status prose.
- Source: current `inp` `blueprint-W/parts/w3-birkhoff.tex`; byte-identical in both checkouts,
  SHA256 `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161`.
  Source fidelity was checked against the blueprint, including its adopted errata, rather than
  treating the prover handoff as mathematical authority. This is not a fresh PDF-source audit.
- Compared `git diff inp...HEAD`, specifically `-- KAM/Wave/Birkhoff`: 26 new modules,
  5161 lines. The full diff also contains the two individual handoffs and 26 generated imports
  in `KAM/Root/Wave.lean`. Regenerated roots are expressly authorized in AUDIT FOCUS.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
  Initial worktree status contained only the untracked combined handoff. No source was edited.

The statement-audit skill's carrier/body and expanded-premise checks were used as methodology.
This is a helper-package audit, not a manifest-bound frozen-statement/seal audit.

## Finding F1: the general field predicate silently requires a smoothing lift

**FAIL**, source `bpW:w3:hamfield-def`, blueprint lines 154–168;
`KAM/Wave/Birkhoff/HamClass.lean:35–55`, with dependent specializations at 79 and 94.

The blueprint first defines a general Hamiltonian field as
“A map $X_P:U\to\mathfrak W$ ... if $DP(w)v=\Omega(X_P(w),v)$”. Only subsequently does
it define the subclass A(U) whose field takes values in the strictly smaller W+.

The exported `IsBirkHamField` instead requires

```lean
deriv_eq : ∀ w ∈ U, ∀ v,
  fderiv ℂ P w v = birkOmegaPlus a p ha hp (X w) v
```

Here `birkOmegaPlus` is `Ω (birkEmbed a (p+1) p X) v`; `X` is read at weight p+1.
Consequently, even the existential existence of this predicate requires a W+-valued lift of
the field. It does not express the blueprint's general W-valued Hamiltonian-field predicate.
This is an additional regularity requirement in a definition, not a stronger proved estimate.

Concrete separation: let Y have weighted coordinates `Y(true,j)=1/j`, `Y(false,j)=0`.
Then Y belongs to W, since the sum of `1/j²` converges, but its physical sequence does not
belong to W+: its p+1 weighted coordinates are identically 1 on the positive side.
The continuous linear Hamiltonian `P(w)=Ω(Y,w)` has the blueprint field `X_P(w)=Y`
everywhere. If the implementation predicate had any lift X for this P on the whole space,
nondegeneracy would give `birkEmbed (X w)=Y`. Since the embedding acts on weighted coordinates
by `1/j`, this would force `X(w)(true,j)=1`, contradicting membership in lp².
This is a mathematical counterexample to equivalence of the predicates; it is not claimed as
a Lean-compiled counterexample.

`birkField_eq` and `birkField_coord` are valid for the narrower predicate, but do not export
the full general uniqueness/coordinate statements. The current `IsBirkClassA` itself is
faithful: requiring exactly this smoothing lift and analyticity into W+ is part of its source
definition. The proofs for concrete quartics and F construct the lift and bound it, so F1
does not refute those results or the homological identity.

Required correction for full label acceptance: expose the general W-valued predicate with
Ω directly, and keep the smoothing predicate distinctly named, or obtain an explicit owner
ruling narrowing the claimed implementation of this source label. No repair was made here.

## Label verdicts

All declaration names below are in `KAM.Wave`.

| Source label | Main declarations | Verdict | Reason |
|---|---|---|---|
| space | `BirkIdx`, `BirkSpace`, `birkCoord`, `birkEmbed`, `birkRho`, `lpDiagCLM` | PASS | Positive-mode/sign indexing, exact weighted-coordinate interpretation, norm-one injective inclusion, conjugate-linear isometric involution. |
| coords | `birkZ`, `birkZinv`, `birkZEquiv`, coordinate/norm/real-form lemmas | PASS | Correct `(q ± ip)/√2`, inverse, max-product norm bounds and fixed real form, at every indicated weight. |
| omega | `birkOmega`, `birkOmega_nondegenerate`, `birkOmega_birkZ`, `birkOmega_birkRho` | PASS | Correct i and sign convention, bounded antisymmetric bilinear form, nondegeneracy and real canonical form. |
| hamfield-def, general part | `IsBirkHamField`, `birkField_eq`, `birkField_coord` | FAIL | F1: general W-valued field replaced by a W+-valued lift. |
| hamfield-def, A(U) | `IsBirkClassA`, `BirkClassA`, `IsBirkClassA.field_rho` | PASS | Open invariant domain, reality, analytic P, full derivative identity, analytic field into W+. |
| forms | `IsBirkSmoothing`, `birkDiag`, `birkDiagField`, bounds, derivative and class-A lemmas | PASS | Source smoothing predicate; `d=n+1`, including `1≤n` where d≥2 is needed; correct d and d(d−1). |
| Lambda | `birkLambda`, `fderiv_birkLambda_apply`, `birkXLam`, `birkLambda_field`, `not_exists_birkXLam_bounded` | PASS WITH NOTES | Correct quadratic form, derivative on all W, W+→W field and √(1+m) bound. Nonexistence export states no bounded extension; see N1. |
| majorant | `birkMajorant_eq`, `birkMajorant_bound` | PASS | Correct λ factors, absolute convergence and one-weight gain with C* depending only on p. |
| quartic | `IsBirkQuartCoef`, `birkGradML`, `birkQuartForm`, `birkQuart_isSmoothing`, `birkQuart_isClassA`, norm bounds | PASS | Coefficient premises expanded; symmetry/reality/bound are source inputs, not the smoothing conclusion. Normalization 1/16 and C*/4 retained. |
| quartic-ident | `birkQuartP_birkZ`, `birkQuartP_birkZ_real`, `birkZinv_birkQuartX_birkZ`, normal-part lemmas, `birkQuartP_bar`, `birkPaired_iff_divisor` | PASS | Series identity for a≥0; integral `waveG` identity under source a>0; corrected A,B on complex W; actual landed nonresonance is applied. |
| divisor | `birk_divisor_sorted`, `birk_divisor_bound`, `birk_divisor_bound_tan`, `birkDeltaStar` | PASS | Exact m/[27(n²+m)^(3/2)], all sixteen signs, minimum supplied by an attained index; δ*=m/[27(4+m)^(3/2)]. |
| Fdef | `birkFx`, `birkFcoef`, `birkFform`, `birkFgrad`, `birkS` | PASS | Correct support, division, i/16 normalization via δ* rescaling, S=4∇F. |
| F | `birkF_isSmoothing`, `norm_birkS_le`, `birkS_pairing`, `birkS_perm`, `birkS_rho`, `birkF_real`, `norm_birkF_le`, `birkF_isClassA` | PASS | Correct W+ target, C_F=C*/δ*, four-slot pairing symmetry, reality, cubic field and analytic class. |
| homological | `summable_birkLamQuartTerm`, `birk_delta_mul_fx`, `birk_euler`, `birk_DLam_XF`, `birk_homological`, `birk_homological'` | PASS | Bounded derivative of Λ at arbitrary w∈W applied to the explicitly embedded smoothing field. Correct sign and both identities; no w∈W+ premise. |

N1 (coverage note): the blueprint says “X_Λ does not map W into itself.” The formal negative
export at `Lambda.lean:297` proves absence of a **bounded linear** extension with those
coordinates. It does not itself give a point outside the multiplier domain. Thus cite the
formal export at precisely that strength; the stronger non-selfmapping assertion would need
an additional argument, for example a weighted sequence with coefficients 1/j. This note
does not affect the bounded derivative or homological result.

`bpW:w3:real-restrict` is explicitly excluded by the handoff and remains unimplemented here.
The a=0 series version is not promoted to an integral/reconstruction identity requiring a>0.

## Expanded premises and semantic checks

For the principal divisor and analytic exports, the following table separates each input.
Each comma-separated parameter row denotes the separate parameters named there, not a hidden bundle.
No consumer-ready conclusion is assumed in these main theorems.

| Export/family | Input | Bin | Source |
|---|---|---|---|
| divisor bound | `m : ℝ` | TYPING | Mass parameter. |
| divisor bound | `hm : 0<m` | STANDING | `bpW:w0:mass`, W3 standing data. |
| divisor bound | `x : Fin 4 → BirkIdx` | TYPING | Four nonzero signed indices. |
| divisor bound | `hsel : ∃ ε, Σ ε_t abs(x_t)=0` | SOURCE | First sentence of `bpW:w3:divisor`; ε independent of signs of x. |
| divisor bound | `hnp : ¬birkPaired x` | SOURCE | Same sentence. |
| divisor bound | `t0 : Fin 4` | TYPING | Representation of attained minimum. |
| divisor bound | `ht0 : ∀t, abs(x_t0)≤abs(x_t)` | SOURCE | Source n=min; witness exists on the nonempty finite tuple. |
| tangential consequence | `x` | TYPING | Same index carrier. |
| tangential consequence | `hT`, `hg`, `hnp` | SOURCE | x∈T, g_x≠0, not paired, exactly the source corollary. |
| quartic-ident / F / homological | `m` | TYPING | Fixed mass. |
| quartic-ident / F / homological | `hm` | STANDING | m>0. |
| quartic-ident / F / homological | implicit `a`, `p` | TYPING | Weight parameters. |
| quartic-ident / F / homological | `ha : 0≤a`, `hp : 1/2≤p` | STANDING | W3 standing data. |
| quartic-ident / F / homological | `w`, argument tuples, permutation σ, direction v where present | TYPING | Arbitrary points/slots of the source spaces; σ for explicit symmetry statements. |
| generic quartic | coefficient function `c` | TYPING | Source coefficient family. |
| generic quartic | `IsBirkQuartCoef.perm` | SOURCE | c invariant under all slot permutations. |
| generic quartic | `IsBirkQuartCoef.conj_neg` | SOURCE | c_-x=conj(c_x). |
| generic quartic | `IsBirkQuartCoef.bound` | SOURCE | abs(c_x)≤abs(g_x). |
| generic majorant | `hu`, `hu'`, `hu'' : IsEll ...` | SOURCE | Inputs belong to the indicated weighted spaces; these are typing/membership conditions, not a smoothing bound on the output. |

Divisor-bound counts: SOURCE 3, STANDING 1, TYPING 3, RULED 0, EXCESS 0.
For `birk_homological` and `birkQuartP_bar`: SOURCE 0, STANDING 3, TYPING 4
(m,a,p,w), RULED 0, EXCESS 0. The same count applies to `norm_birkS_le` with its tuple
in place of w. Permutation/reality versions add only the displayed argument data.

Expanded `IsBirkClassA` fields are precisely `IsOpen U`, ρ-invariance of U, reality of P,
`AnalyticOnNhd ℂ P U`, the derivative pairing for every point/direction, and
`AnalyticOnNhd ℂ X U`. These fields define the manuscript class. In concrete class-A
theorems they are **proved**, not hypotheses. The generic `IsBirkSmoothing` premise in
form-calculus helpers is the source's definition of a smoothing form; concrete quartic/F
exports discharge its bound and pairing from coefficient estimates. No proof obligation
is smuggled into an instance. F1 is instead the separate wrong carrier in the general predicate.

The divisor proof obtains the sorted selection alternatives internally. It cases on all four
Boolean signs. `birkDiv_C3` excludes only all-equal magnitudes, so `a=b<c=d` remains
covered for the nonpaired outer pattern. It does not discard this case by comparing with a
zero inner-pair divisor. Convexity is supplied by an exact algebraic second-difference identity;
this changes the proof method, not the source constant or scope.

For the paired quartic, `QuartPaired.lean:142` actually calls landed
`quartic_nonresonance`, after deriving nonzero sine coefficient and translating signs.
The action formula counts six sign placements and the distinct/equal mode multiplicities;
`QuartBarAlg.lean:148` uses landed `actionA`, and its `birkActionB_eq` identifies the infinite
normal-mode coefficient with landed `actionB`. The variables w_j,w_-j remain independent
complex variables, with action w_j w_-j; no real-slice assumption enters that theorem.

## Definition classification and whole-carrier behavior

The declaration inventory below gives every one of the 95 explicit definitions, abbreviations,
and structures its source label and classification. The general field predicate is the sole
definition-fidelity failure found.

| Family | Classification and behavior |
|---|---|
| Space/sign/index/reindexing/finite counting | Literal arithmetic or explicit equivalences; no arbitrary witness selection. Bool×PNat indexes exactly Z without zero. |
| `birkCoord`, `birkEmbed`, `birkUnit` | Literal positive-weight division, ratio inclusion, physical unit vector. All weights are strictly positive even for arbitrary real weight exponents. |
| `birkZ`, inverse, equivalence, real map, rho | Explicit coordinate constructions with proved lp membership, inverse and norm bounds. They are defined on their entire Banach carriers. |
| Omega/Lambda bilinear maps | Explicit absolutely convergent series bundled as continuous maps using proved bounds. Λ is quadratic on all W. `birkXLam` is W+→W, and no unbounded operator on W is totalized. |
| `IsBirkHamField` | Literal predicate, **FAIL** body/public-carrier match to general source field (F1). No choice or fallback is involved. |
| `IsBirkClassA`, `BirkClassA`, `IsBirkSmoothing`, `IsBirkQuartCoef` | Literal manuscript predicates, with all fields expanded above; PASS. Parameterizing a smoothing form by its gradient is an explicit witness, not assuming that a concrete quartic is smoothing. |
| Majorant, folded sequences, atoms, gradient/quartic sums | Literal formula helpers. Bare raw-function/coefficient sum helpers use Lean's total `tsum`; analytic uses always discharge absolute convergence from weighted membership and coefficient bounds. No divergent `tsum` value is used to obtain a source identity. |
| Gradient lp/multilinear maps, quartic maps/forms, diagonals | Explicit formula constructions from proved membership and continuity. Output gradient is read at p+1; pairing uses the p+1→p embedding. No deferred characterization or nonunique choice. |
| Paired/tangential/normal sets and restricted coefficients | Literal indicator restrictions and signed-multiset equality. Their zero branches are exactly the source support/projection, not defaults hiding missing mathematics. |
| Actions and `birkActionB` | Literal w_j w_-j and corrected coefficient; positive mass guarantees the λ denominators are nonzero. |
| `birkL`, `birkDelta`, `birkDeltaStar`, `birkCF` | Arithmetic helpers given by explicit sqrt/difference/rpow/quotient formulas. They are total arithmetic expressions for real m; every source estimate/application supplies m>0. No physical frequency or source positive constant is asserted for nonpositive m. |
| `birkFx`, `birkFcoef`, `birkFform`, `birkFgrad`, `birkS` | Literal source support and scaled explicit quartic constructions. Division by a possibly zero divisor is used only with zero numerator or else guarded by the proved positive δ* bound. The rescaling divides by δ*>0. |
| `birkHterm`, `birkHtermAt` | Literal finite products; absolute convergence of the subsequent series is proved, including the extra λ factor. |

For all PASS literal definitions: BODY_MATCH OK; PUBLIC_CARRIER OK in the source interpretation
or expressly scoped raw formula helper described above; WELL_DEFINEDNESS and CHARACTERIZATION
N/A_LITERAL; CHOICE_INDEPENDENCE N/A. For bundled explicit map constructions, their displayed
coordinate/series equations and lp membership proofs establish well-definedness on the whole
stated carrier. There is no characterization-defined object chosen from unproved existence.
For `IsBirkHamField`: BODY_MATCH FAIL; PUBLIC_CARRIER FAIL; WELL_DEFINEDNESS/CHARACTERIZATION
N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT FAIL.

## Validation

The following operations ran serially. D53's cap was inherited by all subprocesses of lint;
`w_build.sh` itself applies the exact required scope to its single Lake invocation. No uncapped
Lean/Lake/leanchecker was launched. There were no resource-budget overrides and no application build.

1. Slim lint, and no other lint entry point:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpka
   ```

   Exit **0**. Complete output:

   ```text
check_lean_modules: PASS (3583 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   In particular, the two LunarBand application exports in that output are file-hash checks,
   not application rebuilds. No stale-root exception was needed.

2. Targeted import-closure build through the D53 serial compile-gate driver:

   ```sh
   /root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpka KAM.Wave.Birkhoff.Homological
   ```

   The driver acquired slot 2 and invoked:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.Birkhoff.Homological
   ```

   Lake output ended `Build completed successfully (3331 jobs).` The target transitively imports
   all 26 reviewed modules; no root/application target was requested. This was a warm validation,
   with replayed build jobs, not a clean rebuild. Warnings were deprecations and unused simp/
   section-variable warnings, including `Homological.lean:111`.

   **Driver exit was 1 despite Lake success.** The driver's last command inside the loop is
   `[ $rc -ne 0 ] && { ...; exit $rc; }`; when Lake returns 0 the test is false and the shell loop
   leaves status 1. There was no `[w_build] FAILED` diagnostic. This is a wrapper exit-status
   defect, not evidence of a Lean build failure. The wrapper was inspected, not edited.

3. Declaration axiom closure and five exact statement/composition probes:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/maud_wpka_1.lean
   ```

   Exit **0**, no error or warning. Probe imports `KAM.Wave.Birkhoff.Homological`, which reaches
   every package module, and runs `#print axioms KAM.Wave.<name>` for every explicit declaration
   in the inventory (307 theorems and 95 defs/abbrevs/structures). All 402 returned only the
   allowed axiom subset. Exact distinct-output counts:

   | Axiom list | Count |
   |---|---:|
   | `[]` (printed as `does not depend on any axioms`) | 10 |
   | `[Quot.sound]` | 1 |
   | `[propext]` | 4 |
   | `[propext, Classical.choice, Quot.sound]` | 380 |
   | `[propext, Quot.sound]` | 7 |

   Selected raw output:

   ```text
   'KAM.Wave.birkQuartP_bar' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birk_divisor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birk_divisor_bound_tan' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkF_isSmoothing' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkS_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkS_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birkF_isClassA' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birk_homological' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.birk_homological'' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The five `example` checks independently restate the divisor estimate, S's C*/δ* bound,
   S's reality and symmetry, and the homological identity written with S(w,w,w). The last
   composes `birkXF_eq` with `birk_homological` and quantifies over arbitrary `w : BirkSpace`;
   no smoothing-domain hypothesis on w is supplied. No provider-type probe is applicable.

   Axiom probe generation is reproducible by importing Homological, then scanning each of
   the 26 files for its top-level `theorem`, `def`, `abbrev`, `structure` declaration names
   (including names after `@[simp]`) and emitting `#print axioms KAM.Wave.<name>`.
   The complete per-declaration results are encoded in the inventory's axiom column below.
   Temporary `.lake/abi-scratch/maud_wpka_1.lean` was deleted after validation.

4. Kernel replay and name checks: the user explicitly states these were already run by the
   launcher and their output is unavailable in this pane. Neither was rerun; no exit code
   from that unseen run is invented here. They are **launcher evidence, not independently
   inspected receipts**. The new targeted build, axiom probe and statement probes above are
   independent observations. No `leanchecker` invocation was made by this auditor.

5. Hygiene/source integrity: no forbidden proof escape/resource override/provider import/frozen
   theorem import appears in the new package. Maximum file length is 392 (Coords), far below
   1500. All 26 files have the required module headers, public imports, module docstrings and
   exposed public noncomputable sections. Protected diff is empty as above. The authorized
   generated Wave root contains exactly the 26 added imports. `git diff --check inp...HEAD`
   exits **2**, with the sole output:

   ```text
   KAM/Wave/Birkhoff/Lambda.lean:282: trailing whitespace.
   +  rw [← birkNegEquiv.tsum_eq] 
   ```

   This is cosmetic (N2), separate from the passing prescribed source lint. It was not repaired.
   Final tracked implementation remains byte-identical to audited HEAD.

Raw transient logs: `/tmp/maud-wpka-1-{lint,build,probe}.log`; material results are copied here.


## Source errata, implementation deviations, and limits

No new blueprint mathematical defect was found. F1 is an implementation/source correspondence
defect, and should be recorded as such rather than changing the blueprint silently.

Existing source defects relevant here, quoted in the current blueprint and recorded in
`docs/errata/ledger.json`, remain visible:

- E-W-Pos96W-1, P96-W p.285 Case 1: “δ′(m)=½(1/λ_i+1/λ_j+1/λ_k−1/λ_l) ≥ 1/λ_i”.
  At (1,10,10,19), m=1, the left side is approximately 0.426778, below 0.707107.
  The valid half-sized bound and the present algebraic proof avoid the false inequality.
- E-W-Pos96W-2, p.286 Case 2: “it suffices to study δ_{+−−+}”. At i=j<k=l that
  comparison is zero, whereas the outer divisor is positive. The code handles the outer case directly.
- E-W-Pos96W-3, p.286: “λ_{j+2i}−λ_j ≥ 2(λ_{j+1}−λ_j) ≥ 2i f′(j)”.
  The first factor must be 2i; the code uses summed monotone discrete increments.
- E-PDE-W-1, source quartic normalization: the current blueprint's adopted correction uses
  1/16 in signed complex coordinates. The package retains that correction and its corrected A,B.

These are existing blueprint/ledger quotations, not newly verified PDF transcriptions in this run.
The earlier handoff's lint-history correction is retained: its claim of exit 0 at 32c9b184
was superseded by the later width fixes. Only the current snapshot's actual lint result is used.
The audit introduced no mathematical/source deviation and edited no implementation or protected file.

## Complete explicit declaration inventory

One row for every explicit public declaration added under Birkhoff (402 total). Names are
relative to `KAM.Wave`; locators are under `KAM/Wave/Birkhoff/`. Automatically generated
structure projections are covered by the expanded structure fields, not counted as separate
source claims. PASS for an auxiliary theorem means it is valid at its displayed helper
scope; it is not an assertion that the theorem independently closes the entire label.

Axioms: S=`[propext, Classical.choice, Quot.sound]`; PQ=`[propext, Quot.sound]`;
P=`[propext]`; Q=`[Quot.sound]`; 0=no axioms. Every entry was printed by the capped probe.
For defs/abbrevs/structures, the note gives the literal/explicit-construction classification;
the family table above supplies its whole-carrier explanation.

| Label | Declaration / source locator | Kind | Verdict | Axioms | Reason / classification |
|---|---|---|---|---|---|
| coords | `birkSqrt2` (Coords.lean:37) | abbrev | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkSqrt2_sq` (Coords.lean:39) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkSqrt2_ne` (Coords.lean:42) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkSqrt2` (Coords.lean:46) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `conj_birkSqrt2` (Coords.lean:49) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birk_parallelogram` (Coords.lean:52) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birk_sq_le` (Coords.lean:58) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZfun` (Coords.lean:63) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkZfun_sq_le` (Coords.lean:66) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `summable_birkZfun_sq` (Coords.lean:77) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `memℓp_birkZfun` (Coords.lean:85) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZfun_add` (Coords.lean:89) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZfun_smul` (Coords.lean:94) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZfun_pair_sq` (Coords.lean:100) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_sq_birkZfun` (Coords.lean:116) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZ` (Coords.lean:131) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZ_apply` (Coords.lean:146) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_sq_birkZ` (Coords.lean:149) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_le_norm_birkZ` (Coords.lean:153) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkZ_le` (Coords.lean:161) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birk_hasSum_sq_pair` (Coords.lean:176) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinvFst` (Coords.lean:185) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinvSnd` (Coords.lean:188) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkZinvFst_sq_le` (Coords.lean:191) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkZinvSnd_sq_le` (Coords.lean:198) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `memℓp_birkZinv` (Coords.lean:207) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinv` (Coords.lean:217) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinv_fst_apply` (Coords.lean:247) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinv_snd_apply` (Coords.lean:250) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_birkZinv_le` (Coords.lean:253) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZinv_birkZ` (Coords.lean:267) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZ_birkZinv` (Coords.lean:279) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZEquiv` (Coords.lean:294) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZEquiv_apply` (Coords.lean:297) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkZEquiv_symm_apply` (Coords.lean:299) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `norm_le_sqrt_two_mul_birkZinv` (Coords.lean:302) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkCoord_birkZ_true` (Coords.lean:309) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkCoord_birkZ_false` (Coords.lean:316) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkCoord_mul_birkZ` (Coords.lean:323) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkReal` (Coords.lean:337) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkReal_apply` (Coords.lean:341) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkReal_injective` (Coords.lean:344) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `birkRho_birkZ_real` (Coords.lean:353) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| coords | `exists_birkZ_of_birkRho_eq` (Coords.lean:363) | theorem | PASS | S | Explicit complex/real coordinate map, inverse or norm/membership identity. |
| divisor | `birkDivisor_vec4` (Divisor.lean:29) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birk_divisor_sorted` (Divisor.lean:37) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birkL_pow_three` (Divisor.lean:111) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birk_divisor_bound` (Divisor.lean:120) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birkDeltaStar` (Divisor.lean:166) | def | PASS | S | Literal formula/predicate or explicit bundled construction. All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `quarticSel_exists_eps` (Divisor.lean:168) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birk_divisor_bound_tan` (Divisor.lean:182) | theorem | PASS | S | All-sign/minimum/selection-rule estimate or literal δ*. |
| divisor | `birkL_sub_self` (DivisorCore.lean:30) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkBeta_le_half` (DivisorCore.lean:38) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkBeta_le_ratio` (DivisorCore.lean:49) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C0` (DivisorCore.lean:58) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C1` (DivisorCore.lean:71) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDelta_pos` (DivisorCore.lean:100) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkL_step` (DivisorCore.lean:107) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDelta_ge_beta` (DivisorCore.lean:114) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDelta_nonneg_mono` (DivisorCore.lean:118) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C3` (DivisorCore.lean:122) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C2` (DivisorCore.lean:140) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C1i` (DivisorCore.lean:158) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkDiv_C1ii` (DivisorCore.lean:190) | theorem | PASS | S | Explicit sorted-sign subcase or increment lower bound. |
| divisor | `birkL` (DivisorReal.lean:29) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `lam_eq_birkL` (DivisorReal.lean:33) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_sq` (DivisorReal.lean:36) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_pos` (DivisorReal.lean:39) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_mono` (DivisorReal.lean:42) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_gt_self` (DivisorReal.lean:48) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `one_le_birkL` (DivisorReal.lean:52) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_second_diff` (DivisorReal.lean:59) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkDelta` (DivisorReal.lean:105) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkDelta_mono` (DivisorReal.lean:107) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkDelta_ge` (DivisorReal.lean:115) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_add_ge` (DivisorReal.lean:130) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_incr_mono` (DivisorReal.lean:140) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| divisor | `birkL_incr_sub` (DivisorReal.lean:153) | theorem | PASS | S | Literal sqrt/increments or proved algebraic convexity estimate. |
| Fdef/F | `birkFx` (FCoef.lean:29) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkFcoef` (FCoef.lean:33) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkDivisor_perm` (FCoef.lean:36) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkLam_neg` (FCoef.lean:40) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkDivisor_neg` (FCoef.lean:43) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkFx_perm` (FCoef.lean:49) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkFx_neg` (FCoef.lean:57) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `abs_birkFx_le` (FCoef.lean:68) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| Fdef/F | `birkFcoef_isCoef` (FCoef.lean:82) | theorem | PASS | S | Literal supported generator coefficient or proved symmetry/divisor bound. |
| F | `birkCF` (FForm.lean:34) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `IsBirkSmoothing.birkScale` (FForm.lean:37) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkDeltaStar_pos` (FForm.lean:52) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkFform` (FForm.lean:60) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkFgrad` (FForm.lean:64) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkS` (FForm.lean:68) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `norm_inv_deltaStar` (FForm.lean:72) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkF_isSmoothing` (FForm.lean:77) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `norm_birkS_le` (FForm.lean:87) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkS_pairing` (FForm.lean:105) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkOmegaPlus_ext` (FForm.lean:116) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `snoc_comp_perm3` (FForm.lean:125) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `snoc_rho` (FForm.lean:140) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkS_perm` (FForm.lean:154) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkF_real` (FForm.lean:163) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkS_rho` (FForm.lean:172) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `norm_birkF_le` (FForm.lean:188) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkXF_eq` (FForm.lean:198) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| F | `birkF_isClassA` (FForm.lean:207) | theorem | PASS | S | Explicit scaled smoothing generator or analytic/symmetry/reality consequence. |
| quartic majorization | `birkFoldNorm` (Fold.lean:26) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `birkFoldNorm_nonneg` (Fold.lean:29) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `ellWeight_mul_norm_birkCoord` (Fold.lean:32) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `ellWeight_mul_birkFoldNorm` (Fold.lean:38) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `summable_sq_birkFoldNorm` (Fold.lean:44) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `isEll_birkFoldNorm` (Fold.lean:53) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| quartic majorization | `ellTsumNorm_birkFoldNorm_le` (Fold.lean:57) | theorem | PASS | S | Literal sign-folded norm or proved weighted membership/bound. |
| forms | `IsBirkSmoothing` (Forms.lean:41) | structure | PASS | S | Literal formula/predicate or explicit bundled construction. Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiag` (Forms.lean:52) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiagField` (Forms.lean:56) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiag_analyticOnNhd` (Forms.lean:64) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiagField_analyticOnNhd` (Forms.lean:72) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `snoc_const_apply` (Forms.lean:81) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `update_const_eq_snoc_comp` (Forms.lean:88) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `hasFDerivAt_birkDiag` (Forms.lean:101) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `fderiv_birkDiag_apply` (Forms.lean:111) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `birkOmegaPlus_smul` (Forms.lean:122) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiag_field` (Forms.lean:128) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `snoc_const_self` (Forms.lean:133) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `norm_birkDiag_le` (Forms.lean:141) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `norm_birkDiagField_le` (Forms.lean:158) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `norm_birkDiagField_sub_le` (Forms.lean:170) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| forms | `birkDiag_isClassA` (Forms.lean:187) | theorem | PASS | S | Source smoothing-form definition or its diagonal calculus. |
| hamfield-def | `birkOmegaPlus` (HamClass.lean:35) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `birkOmegaPlus_eq` (HamClass.lean:38) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `norm_birkOmegaPlus_le` (HamClass.lean:41) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `IsBirkHamField` (HamClass.lean:52) | structure | FAIL | S | F1: literal predicate requires a W+-lift in place of the general W-valued field. |
| hamfield-def | `IsBirkClassA` (HamClass.lean:60) | structure | PASS | S | Literal full A(U) predicate; W+ field and both analyticity requirements match source. |
| hamfield-def | `BirkClassA` (HamClass.lean:70) | def | PASS | S | Literal full A(U) predicate; W+ field and both analyticity requirements match source. |
| hamfield-def | `IsBirkClassA.hamField` (HamClass.lean:73) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `birkField_eq` (HamClass.lean:79) | theorem | PASS WITH NOTES | S | Valid specialization to smoothing fields; fails full general-source coverage (F1). |
| hamfield-def | `birkField_coord` (HamClass.lean:94) | theorem | PASS WITH NOTES | S | Valid specialization to smoothing fields; fails full general-source coverage (F1). |
| hamfield-def | `birkRhoR` (HamClass.lean:111) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `birkRhoR_apply` (HamClass.lean:120) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `birk_fderiv_rho` (HamClass.lean:123) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| hamfield-def | `IsBirkClassA.field_rho` (HamClass.lean:146) | theorem | PASS | S | Smoothing-class calculus; general-field coverage is restricted by F1. |
| homological | `summable_birkLamQuartTerm` (HomSum.lean:34) | theorem | PASS | S | Proved absolute convergence with the extra λ factor. |
| homological | `birk_delta_mul_fx` (Homological.lean:31) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkCoord_birkXF` (Homological.lean:58) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkHterm` (Homological.lean:70) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `summable_birkHterm` (Homological.lean:74) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkHtermAt` (Homological.lean:99) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkHtermAt_swap` (Homological.lean:102) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkHtermAt_tsum` (Homological.lean:111) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `summable_birkHtermAt` (Homological.lean:122) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birk_euler` (Homological.lean:132) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birkLam_cast` (Homological.lean:144) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birk_DLam_XF` (Homological.lean:150) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birk_homological` (Homological.lean:194) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| homological | `birk_homological'` (Homological.lean:227) | theorem | PASS | S | Literal Euler term or all-W homological calculation with proved convergence. |
| Lambda | `birk_weight_succ` (Lambda.lean:36) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birk_lam_mul_coord` (Lambda.lean:44) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birk_tsum_sq_split` (Lambda.lean:55) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birk_tsum_sq_true_le` (Lambda.lean:60) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birk_tsum_sq_false_le` (Lambda.lean:65) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkHalf_summable` (Lambda.lean:70) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLamTerm` (Lambda.lean:90) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `norm_birkLamTerm_le` (Lambda.lean:94) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `summable_birkLamTerm` (Lambda.lean:102) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLamBil` (Lambda.lean:107) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLamBil_apply` (Lambda.lean:138) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda` (Lambda.lean:142) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda_eq` (Lambda.lean:144) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `norm_birkLambda_le` (Lambda.lean:151) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda_analyticOnNhd` (Lambda.lean:173) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda_birkZ` (Lambda.lean:183) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `hasFDerivAt_birkLambda` (Lambda.lean:193) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda_term_eq` (Lambda.lean:202) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `summable_birkLambda_term` (Lambda.lean:214) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `fderiv_birkLambda_apply` (Lambda.lean:227) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkXLam` (Lambda.lean:247) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkXLam_apply` (Lambda.lean:256) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `norm_birkXLam_le` (Lambda.lean:260) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkCoord_birkXLam` (Lambda.lean:265) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `birkLambda_field` (Lambda.lean:277) | theorem | PASS | S | Explicit quadratic form, derivative or W+→W multiplier. |
| Lambda | `not_exists_birkXLam_bounded` (Lambda.lean:297) | theorem | PASS WITH NOTES | S | N1: precisely no bounded linear extension; no explicit non-selfmapping witness. |
| majorant | `birkMajorant` (Majorant.lean:33) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal majorant or weighted/summable sign-fold estimate. |
| majorant | `birkMajorant_eq` (Majorant.lean:38) | theorem | PASS | S | Literal majorant or weighted/summable sign-fold estimate. |
| majorant | `birkMajorant_bound` (Majorant.lean:65) | theorem | PASS | S | Literal majorant or weighted/summable sign-fold estimate. |
| majorant | `birkFold` (Majorant.lean:88) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal majorant or weighted/summable sign-fold estimate. |
| majorant | `birk_three_sum` (Majorant.lean:93) | theorem | PASS | S | Literal majorant or weighted/summable sign-fold estimate. |
| omega | `birkPair_summable` (Omega.lean:37) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmegaTerm` (Omega.lean:54) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `norm_birkOmegaTerm_le` (Omega.lean:57) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `summable_birkOmegaTerm` (Omega.lean:64) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmegaTerm_add_left` (Omega.lean:68) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmegaTerm_add_right` (Omega.lean:72) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmegaTerm_smul_left` (Omega.lean:76) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmegaTerm_smul_right` (Omega.lean:80) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega` (Omega.lean:86) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_apply` (Omega.lean:110) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `norm_birkOmega_le` (Omega.lean:115) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_antisymm` (Omega.lean:126) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkUnit` (Omega.lean:137) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkCoord_birkUnit` (Omega.lean:140) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_unit_neg` (Omega.lean:148) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_nondegenerate` (Omega.lean:164) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_birkRho` (Omega.lean:178) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_birkZ` (Omega.lean:193) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| omega | `birkOmega_birkZ_real` (Omega.lean:217) | theorem | PASS | S | Source bilinear form or absolute convergence/nondegeneracy identity. |
| quartic-ident | `birkMk` (QuartBar.lean:29) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkPat` (QuartBar.lean:32) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `card_birkPosAbs` (QuartBar.lean:34) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `card_pos_add_neg` (QuartBar.lean:41) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkPat_eq_two_of_paired` (QuartBar.lean:50) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkS0` (QuartBar.lean:59) | def | PASS | P | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkPat_exists_perm` (QuartBar.lean:61) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `card_birkPat_two` (QuartBar.lean:66) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkV` (QuartBar.lean:76) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkQuartP_eq_sum_V` (QuartBar.lean:81) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkV_eq_zero_of_pat` (QuartBar.lean:95) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkV_perm` (QuartBar.lean:106) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `summable_birkV_term` (QuartBar.lean:122) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkV_sum_eq_six` (QuartBar.lean:135) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birk_pair_eq_iff` (QuartBar.lean:151) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkMk_s0_paired` (QuartBar.lean:171) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkAction` (QuartBar.lean:179) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkCoefBar_s0` (QuartBar.lean:182) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `waveTriCoef_swap_last` (QuartBar.lean:195) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkKterm` (QuartBar.lean:203) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkV_s0_eq` (QuartBar.lean:210) | theorem | PASS | S | Explicit six-pattern/multiplicity regrouping or action formula helper. |
| quartic-ident | `birkActionB` (QuartBarAlg.lean:32) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkActionB_eq` (QuartBarAlg.lean:35) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `lamTan_eq` (QuartBarAlg.lean:38) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `exists_modeIdx_of_le` (QuartBarAlg.lean:40) | theorem | PASS | PQ | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `modeIdx_le_two` (QuartBarAlg.lean:43) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `tsum_tan_split` (QuartBarAlg.lean:50) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `waveTriCoef_rsrs` (QuartBarAlg.lean:119) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `waveTriCoef_rsrs_comm` (QuartBarAlg.lean:133) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkQuartP_bar` (QuartBarAlg.lean:148) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkCoefTan` (QuartBarAlg.lean:233) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkCoefTan_isCoef` (QuartBarAlg.lean:235) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkCoefAll_eq_tan_add_nor` (QuartBarAlg.lean:240) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic-ident | `birkQuartP_all_eq_tan_add_nor` (QuartBarAlg.lean:258) | theorem | PASS | S | Corrected A,B action expression or summable tangential/normal split. |
| quartic | `IsBirkQuartCoef` (QuartForm.lean:34) | structure | PASS | S | Literal formula/predicate or explicit bundled construction. Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartSum_update_add` (QuartForm.lean:44) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartSum_update_smul` (QuartForm.lean:55) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartMap` (QuartForm.lean:66) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartForm` (QuartForm.lean:76) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartForm_apply` (QuartForm.lean:91) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartSum_perm` (QuartForm.lean:95) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartForm_perm` (QuartForm.lean:109) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartSum_rho` (QuartForm.lean:115) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuartForm_rho` (QuartForm.lean:129) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkQuart_isSmoothing` (QuartForm.lean:140) | theorem | PASS | S | Source coefficient predicates or symmetric smoothing form construction. |
| quartic | `birkG` (QuartGrad.lean:35) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkCoordL` (QuartGrad.lean:38) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkAtom` (QuartGrad.lean:44) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkAtom_apply` (QuartGrad.lean:48) | theorem | PASS | S | Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkGradTerm` (QuartGrad.lean:53) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quartic atom/gradient term or proved majorization. |
| quartic | `norm_birkGradTerm_le` (QuartGrad.lean:63) | theorem | PASS | S | Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkGrad_majorize` (QuartGrad.lean:73) | theorem | PASS | S | Explicit quartic atom/gradient term or proved majorization. |
| quartic | `summable_birkGradTerm` (QuartGrad.lean:102) | theorem | PASS | S | Explicit quartic atom/gradient term or proved majorization. |
| quartic | `birkGradSum` (QuartGrad.lean:107) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit quartic atom/gradient term or proved majorization. |
| quartic | `norm_birkGradSum_le` (QuartGrad.lean:111) | theorem | PASS | S | Explicit quartic atom/gradient term or proved majorization. |
| quartic-ident | `birkCoefAll` (QuartIdent.lean:38) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkCoefAll_isCoef` (QuartIdent.lean:40) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkCoefAll_apply` (QuartIdent.lean:43) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkCoord_fold` (QuartIdent.lean:47) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkQuartP_birkZ` (QuartIdent.lean:63) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkQuadEquiv` (QuartIdent.lean:97) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkQuadEquiv_apply` (QuartIdent.lean:103) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkQuartP_birkZ_real` (QuartIdent.lean:115) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkCoord_birkQuartX_birkZ` (QuartIdent.lean:148) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic-ident | `birkZinv_birkQuartX_birkZ` (QuartIdent.lean:194) | theorem | PASS | S | Part-0 identification; a>0 only for real integral waveG. |
| quartic | `birkGradCoord` (QuartML.lean:31) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradSeq` (QuartML.lean:35) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `norm_neg_I_sgn_div` (QuartML.lean:43) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `norm_birkGradSeq_le` (QuartML.lean:48) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradSeq_sq` (QuartML.lean:65) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `memℓp_birkGradSeq` (QuartML.lean:107) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradLp` (QuartML.lean:112) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `norm_birkGradLp_le` (QuartML.lean:117) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradTerm_eq_atom` (QuartML.lean:168) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradSumML` (QuartML.lean:175) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradMLmap` (QuartML.lean:195) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradML` (QuartML.lean:218) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkGradML_apply` (QuartML.lean:223) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkCoord_birkGradML` (QuartML.lean:229) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `norm_birkGradML_le` (QuartML.lean:239) | theorem | PASS | S | Explicit smoothing gradient, proved lp membership or multilinear bound. |
| quartic | `birkQuartP` (QuartMain.lean:39) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkQuartX` (QuartMain.lean:43) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkQuart_isClassA` (QuartMain.lean:48) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkQuartP_rho` (QuartMain.lean:54) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `norm_birkQuartP_le` (QuartMain.lean:60) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `norm_birkQuartX_le` (QuartMain.lean:66) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `norm_birkQuartX_sub_le` (QuartMain.lean:74) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkQuartCoefOn` (QuartMain.lean:89) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkG_perm` (QuartMain.lean:92) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `birkG_neg` (QuartMain.lean:105) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic | `isBirkQuartCoef_on` (QuartMain.lean:109) | theorem | PASS | S | Literal quartic diagonal/support or analytic/norm consequence. |
| quartic-ident | `birkNormalMul` (QuartNormal.lean:32) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkNormalPart` (QuartNormal.lean:35) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkNormalPart_apply` (QuartNormal.lean:38) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkCoord_birkNormalPart` (QuartNormal.lean:41) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `norm_birkNormalPart_le` (QuartNormal.lean:45) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkNormalSet` (QuartNormal.lean:51) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkCoefNor` (QuartNormal.lean:54) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkCoefNor_isCoef` (QuartNormal.lean:56) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkCoefNor_eq_zero` (QuartNormal.lean:60) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkQuartP_normal` (QuartNormal.lean:70) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkCoord_birkQuartX_normal` (QuartNormal.lean:88) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkQuartX_normal` (QuartNormal.lean:109) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkQuartX_tangential` (QuartNormal.lean:120) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `norm_birkQuartP_normal_le` (QuartNormal.lean:136) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `norm_birkQuartX_normal_le` (QuartNormal.lean:144) | theorem | PASS | S | Literal normal projection/support; output p+1 weight. |
| quartic-ident | `birkPosAbs` (QuartPaired.lean:33) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkNegAbs` (QuartPaired.lean:37) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired` (QuartPaired.lean:42) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkTanSet` (QuartPaired.lean:45) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkBarSet` (QuartPaired.lean:48) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPosAbs_perm` (QuartPaired.lean:50) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkNegAbs_perm` (QuartPaired.lean:54) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkNeg_ite_pos` (QuartPaired.lean:58) | theorem | PASS | PQ | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkNeg_ite_neg` (QuartPaired.lean:63) | theorem | PASS | PQ | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPosAbs_neg` (QuartPaired.lean:68) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkNegAbs_neg` (QuartPaired.lean:72) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired_perm` (QuartPaired.lean:76) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired_neg` (QuartPaired.lean:81) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkBarSet_perm` (QuartPaired.lean:86) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkBarSet_neg` (QuartPaired.lean:91) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkCoefBar` (QuartPaired.lean:96) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkCoefBar_isCoef` (QuartPaired.lean:98) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkDivisor` (QuartPaired.lean:102) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkLamSum` (QuartPaired.lean:105) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkLamSum_ite` (QuartPaired.lean:108) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired_divisor_eq_zero` (QuartPaired.lean:112) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkSgnU` (QuartPaired.lean:125) | def | PASS | P | Literal formula/predicate or explicit bundled construction. Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkSgnU_cast` (QuartPaired.lean:127) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkSgnU_ite_pos` (QuartPaired.lean:131) | theorem | PASS | PQ | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkSgnU_ite_neg` (QuartPaired.lean:136) | theorem | PASS | PQ | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired_of_divisor` (QuartPaired.lean:142) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic-ident | `birkPaired_iff_divisor` (QuartPaired.lean:156) | theorem | PASS | S | Literal pairing/resonance; landed nonresonance invoked, not assumed. |
| quartic | `birkSplit4` (QuartSum.lean:31) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `birkInit4` (QuartSum.lean:41) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `birkAtom_split4` (QuartSum.lean:43) | theorem | PASS | S | Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `summable_birkQuartTerm` (QuartSum.lean:55) | theorem | PASS | S | Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `birkQuartSum` (QuartSum.lean:112) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `snoc_eq_vec3` (QuartSum.lean:115) | theorem | PASS | S | Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `birkInit4_snoc` (QuartSum.lean:119) | theorem | PASS | S | Explicit series or absolutely convergent pairing/regrouping. |
| quartic | `birkQuartSum_eq_omega` (QuartSum.lean:125) | theorem | PASS | S | Explicit series or absolutely convergent pairing/regrouping. |
| majorant/quartic reindexing | `birkPiEquiv` (Reindex.lean:26) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkPiEquiv_apply` (Reindex.lean:29) | theorem | PASS | Q | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkAbs` (Reindex.lean:33) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkNegPi` (Reindex.lean:36) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkNegPi_apply` (Reindex.lean:38) | theorem | PASS | 0 | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkNegPi_birkNegPi` (Reindex.lean:41) | theorem | PASS | PQ | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkNegPiEquiv` (Reindex.lean:46) | def | PASS | PQ | Literal formula/predicate or explicit bundled construction. Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birk_tsum_pi` (Reindex.lean:53) | theorem | PASS | S | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birk_summable_pi` (Reindex.lean:61) | theorem | PASS | S | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birk_sign_sum_prod` (Reindex.lean:70) | theorem | PASS | S | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birk_pi_fold` (Reindex.lean:78) | theorem | PASS | S | Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkTriEquiv` (Reindex.lean:101) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Explicit finite/index equivalence or summable regrouping helper. |
| majorant/quartic reindexing | `birkTriEquiv_apply` (Reindex.lean:107) | theorem | PASS | S | Explicit finite/index equivalence or summable regrouping helper. |
| space | `BirkIdx` (Space.lean:34) | abbrev | PASS | 0 | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `BirkSpace` (Space.lean:37) | abbrev | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkNeg` (Space.lean:40) | def | PASS | 0 | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkNeg_birkNeg` (Space.lean:42) | theorem | PASS | P | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkNeg_snd` (Space.lean:45) | theorem | PASS | 0 | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkNegEquiv` (Space.lean:48) | def | PASS | P | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkSgn` (Space.lean:55) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkSgn_neg` (Space.lean:57) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkSgn_mul_self` (Space.lean:60) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_birkSgn` (Space.lean:63) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkSgn_conj` (Space.lean:66) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkLam` (Space.lean:70) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord` (Space.lean:73) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_mul_weight` (Space.lean:76) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_add` (Space.lean:81) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_smul` (Space.lean:85) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_sub` (Space.lean:89) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_neg` (Space.lean:93) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birk_one_le_weight` (Space.lean:97) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_birkCoord_le` (Space.lean:104) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birk_summable_iff` (Space.lean:111) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birk_tsum_split` (Space.lean:117) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birk_hasSum_split` (Space.lean:122) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `memℓp_lpDiag` (Space.lean:133) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `lpDiagCLM` (Space.lean:145) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `lpDiagCLM_apply` (Space.lean:167) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_lpDiagCLM_le` (Space.lean:170) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_le_norm_of_lpDiag_apply` (Space.lean:175) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `not_exists_lpDiag_of_unbounded` (Space.lean:189) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_birkEmbedRatio_le_one` (Space.lean:200) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkEmbed` (Space.lean:206) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkEmbed_apply` (Space.lean:210) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `norm_birkEmbed_le` (Space.lean:213) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_birkEmbed` (Space.lean:216) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkEmbed_injective` (Space.lean:224) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `memℓp_birkRho` (Space.lean:236) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkRho` (Space.lean:242) | def | PASS | S | Literal formula/predicate or explicit bundled construction. Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkRho_apply` (Space.lean:255) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkRho_birkRho` (Space.lean:258) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkRho_injective` (Space.lean:261) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkCoord_birkRho` (Space.lean:264) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
| space | `birkRho_birkEmbed` (Space.lean:271) | theorem | PASS | S | Weighted coordinates, exact signs/inclusion or elementary lp helper. |
