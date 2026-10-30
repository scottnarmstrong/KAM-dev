# W1-KAMSUP independent package audit 1

Date: 2026-10-30 UTC. **Overall: FAIL for whole-carrier source fidelity of the public phase-norm interface.**
The Fourier/lattice replacement estimates pass. All nine modules build, kernel replay passes, and all 126 public declarations have only the permitted axioms. No false proved theorem was found. The failure is the unrestricted carrier of `kamNorm`/`kamOpNorm`, whose off-source fallback is reproducible; it does not invalidate the guarded inequalities.

No frozen theorem/provider/seal belongs to this package; seal readiness is N/A. This report does not close W4, W-NLW2, or a dependency-graph node.

## Scope, authority, and snapshot

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/W/audits/W1-KAMSUP-handoff.md`, including AUDIT FOCUS. The prompt overrides the brief's generic main-worktree output location: this report is written only at `/root/code/KAM-inp-wpg/docs/tracks/W/audits/W1-KAMSUP-audit-1.md`.

Tier 2, read-only package audit: review the entire `git diff inp...HEAD`, reconstruct the blueprint statements, inspect every new public declaration and definition, then adversarially test suspect carriers and run hygiene. Report/scratch only; no implementation repair, git mutation, root regeneration, or parallel Lean invocation. All Lean-related commands use `LEAN_NUM_THREADS=1` and `nice -n 5` (the prescribed build/lint wrappers supply nice). Independent here means independent of the package author; no additional reviewer or subagent was used. The machine-checked carrier counterexample is the refutation evidence.

Frozen-v1:

- HEAD `f89dd8b1825a1bb4dffd6fdbfb2f303a0e47ff22`.
- Local `inp` `e78c95b46ab1321ef5896600b7ee7fc9babfa351`.
- `git diff inp...HEAD`: nine added Lean modules, nine generated imports in `KAM/Root/Wave.lean`, and the handoff; 11 files, 1980 insertions. New modules total 1894 physical lines.
- Primary source: `blueprint-W/parts/w1-sequences.tex:926-1186`, labels `bpW:w1:kam-space`, `kam-conventions`, `kam-domain`, `fourier-shift`, `fourier-l2`, `fourier-banach`, `lattice`, `schur`.
- `docs/tracks/W/statement.md` does not exist; read the actual track statement document `docs/tracks/W/W-STATEMENTS.md` and D41. Its old draft-status prose is superseded by D41; no frozen W theorem is imported by this package.

SHA256 at frozen-v1:

| Input | SHA256 |
|---|---|
| `KAM/Wave/KamSupport/FourierBanach.lean` | `4b8b1437fccd74579e4745486763956f7090642b2d1e63055cc7cc85918fbc44` |
| `KAM/Wave/KamSupport/FourierBessel.lean` | `222c5e4e81280a429085f0377fb2dcfbace4a1ade806d99153b0b8b607d9e219` |
| `KAM/Wave/KamSupport/FourierL2.lean` | `56fdda6c17b937eb5b47f62ed628ef60d359bbfaaaf38a0a2ad73257def927b4` |
| `KAM/Wave/KamSupport/FourierShift.lean` | `a70e00f565b32b679a06d0cd312cb9a6becdbaae81757508d31c175c3c71ad33` |
| `KAM/Wave/KamSupport/HilbertMatrix.lean` | `72681df4af248fc50f3ab5d5542a8bcecc9e49dbaef36901a4198e018001dce7` |
| `KAM/Wave/KamSupport/KamSpace.lean` | `8f56e16529fed0d83766743492ab0b5cf3a3137727920b0158959d7b948fbdda` |
| `KAM/Wave/KamSupport/Lattice.lean` | `37344a2c710512a5fa7f04d5c624a66f5d3f4135843b4f2286b3f08629c13c60` |
| `KAM/Wave/KamSupport/LatticeCount.lean` | `f12bcd708dca6ad250a6c3d9c74be826bc57ac6cca3fee2b4380c6276e8f6716` |
| `KAM/Wave/KamSupport/SchurTest.lean` | `cd7c21eb584338a0b38383a71efadef5ae71a90523f9048898d3d94f7465433c` |
| `blueprint-W/parts/w1-sequences.tex` | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |

## Findings and refutation

### F1 — FAIL: public source norm carrier admits a zero fallback

Anchor: `KAM/Wave/KamSupport/KamSpace.lean:45-61,92-104` at frozen-v1. Literal definition:

```lean
def kamOpNorm (r s : ℝ) (L : KamPhase →ₗ[ℂ] KamPhase) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ W, kamNorm r (L W) ≤ C * kamNorm s W}
```

The blueprint at `w1-sequences.tex:931-938` says **“For s,r>0”** and **“the least C≥0 ... (the operator norm; used only for bounded L, Lean ContinuousLinearMap.opNorm)”**. The public definition accepts zero/negative radii and arbitrary algebraic linear maps, with no boundedness evidence. In Lean, `Real.sInf_empty = 0`. Consequently a map having no admissible bound is assigned zero, which is not a least admissible constant.

Concrete elaborated witness: `W = (0, (fun _ => 1), 0, 0)` and the linear map `L(θ,y,u,v) = (y,0,0,0)`. The probe proves all of:

- `W ≠ 0` and `kamNorm 0 W = 0`;
- `kamNorm 1 (L W) = 1`;
- `{C | 0 ≤ C ∧ ∀ V, kamNorm 1 (L V) ≤ C * kamNorm 0 V} = ∅`;
- `kamOpNorm 1 0 L = 0`.

Thus the exported “norm” can vanish on a nonzero vector and the exported “operator norm” can be zero despite `1 ≤ 0` being the purported admissibility inequality. This witness deliberately targets the **declared carrier**, not the positive-radius source theorem. Separately, the probe proves for arbitrary `r,s,L` that absence of a finite admissible bound implies `kamOpNorm r s L = 0`; even positive radii do not enforce boundedness of an algebraic `LinearMap`. On the infinite-dimensional phase space unbounded algebraic maps exist (for example extend the assignment `e_j ↦ j e_j` from the finite span of sequence basis vectors to a Hamel basis). This last existence explanation is mathematical, not a separately compiled Lean existence theorem.

Adversarial check: the infimum construction **does** give the intended least constant once its admissible set is nonempty and the source radius is positive. The existing `kamOpNorm_apply_le` explicitly takes `C`, `hC0`, and `hC : ∀ W, ... ≤ C * ...`; these prevent exploiting the fallback in that theorem. This refutes a stronger accusation of an unsound inequality, but does not repair the public carrier or establish boundedness from its current type. The handoff's claim that the theorem gives admissibility “for 0 < s” omits these essential arguments. D31 approves certain named track P totalizations; it is not an approval of this new W interface.

Disposition: whole-carrier definition fidelity fails; the proved conditional lemmas remain valid. A repair should enforce positive radii and bounded maps (or a source-domain subtype with proved finite bounds), and expose the full least-admissible characterization there. Do not silently reinterpret a totalized helper as the source norm. No repair made.

### F2 — FAIL under the brief's literal binder test: nonnegative domination constant added

Anchors: `HilbertMatrix.lean:358-360,396-398`; source `w1-sequences.tex:1158-1164` (`schur` iii–iv). The source says **“If F_ij satisfies ... then F defines a bounded operator ...”**, and does not bind `c ≥ 0`. Both `kamSchurBound_of_dominated` and the source-facing `exists_clm_of_dominated` explicitly require `(hc : 0 ≤ c)`.

Adversarial check: searched the W0 conventions and W1 standing hypotheses; no standing nonnegativity convention for this `c` is specified there. Nonnegative bounds are natural in the intended application, and the theorem is mathematically correct for them. Nevertheless that is a premise restriction absent from the literal node, which the audit brief explicitly disallows. The extra premise cannot simply be inferred from domination: `A=0`, `F=0`, `c=-1` satisfies the displayed domination inequalities. The conclusion remains true in that degenerate case, so this is a formalization restriction, not a counterexample to the blueprint. Either prove the omitted negative-constant case or obtain/record the explicit source convention. No pinned-source erratum is inferred.

### Notes (not blockers)

- N1: Hilbert summation wrapper `kamFourierL2_summation` omits explicit absolute/uniform convergence conjuncts. The imported `kamFourierBanach_summation` supplies exactly those conjuncts for the same Hilbert carrier and coefficient hypothesis. Count the node through both exports, not the shortened wrapper alone.
- N2: Banach (iv) exposes subtraction linearity and the difference coefficient bound. The weighted/difference versions follow by applying (ii) to `u₁-u₂` and rewriting coefficients with `kamFourierBanach_coeff_sub`; no separately named full weighted Lipschitz wrapper is present. Addition/scalar linearity is available from the Bochner integral API, not explicitly packaged under new W names.
- N3: Schur (iv) is the generic positive diagonal weight-invariance statement. Together with the representative-operator theorem (iii) and the prior transport API it supplies the weighted result. It is not a new raw weighted-space operator construction.
- N4: The handoff's “largest 330 lines”/“no module over 330 lines” is stale: `HilbertMatrix.lean` has 409 lines. It still satisfies the 1500-line rule.
- N5: `HilbertMatrix.lean:29` names nonexistent `kamSchur_weights_dominated`; the actual export is `KAM.Wave.KamDominated.weighted` at line 339. Documentation-only stale name.

## Source comparison and constants

| Node | Verdict | Source correspondence |
|---|---|---|
| `fourier-banach` (i) | PASS | Any complex Banach `F`; full-radius coefficient decay `M exp(-2πs|k|₁)`; no finite-dimensional restriction. `M≥0` follows from the bound at zero. |
| `fourier-banach` (ii) | PASS | `0<σ<s`, exact `coth(πσ)^n M`; weighted version has `n≥1,c≥0`, and exact `M S_{n,c}(σ)`; summability included. |
| `fourier-banach` (iii) | PASS | All six conclusions: absolute convergence, cutoff-uniform convergence, bound, holomorphy, periodicity, coefficients. |
| `fourier-banach` (iv) | PASS WITH NOTES | Subtraction and coefficient difference theorem exact; other versions compose as N2. |
| `lattice` (i) | PASS | `HasSum`, exact hyperbolic cotangent; stronger by allowing `n=0`. |
| `lattice` (ii) | PASS | Actual finite fibers (not infinite-set ncard fallback); injective sign/multiset code, stars-and-bars, binomial symmetry, power bound. |
| `lattice` (iii) | PASS | `b=c+(n-1:ℕ)` equals `c+n-1` under `n≥1`; exact `2^n(2b/(eε))^b exp(ε/2)(1+2/ε)`, `ε=2πσ`; `b=0` uses real `0^0=1`, checked in probe. |
| `lattice` (iv) | PASS | `τ≥1,γ,β≥0`; exponent `γτ+β`; `B_σ²` keeps external `2^n` and exactly substitutes `σ/π`. |
| `fourier-shift` | PASS | Arbitrary η inside strip, Banach values, no boundedness premise. Derives boundedness on an intermediate strip using periodicity, then scalar shift and separating dual. Sign checked against positive Fourier character. |
| `fourier-l2` (i) | PASS | Bessel suffices for upper bound. Finite sums, orthants, endpoint limit yield summability and exact `2^n M²`; no operator-valued square-sum assertion. |
| `fourier-l2` (ii) | PASS WITH NOTES | Full source statement available via Banach summation (N1). |
| `fourier-l2` (iii) | PASS | Representation on all of `T_s`, stronger than each smaller strip; follows from existing Banach representation. |
| `schur` (i)–(ii) | PASS | `π/√3` off-diagonal bound, diagonal norm ≤ operator norm, absolute row convergence and faithful matrix entries. |
| `schur` (iii) | FAIL (F2) | Exact constants and operator characterization, but source-facing export adds `0≤c`. |
| `schur` (iv) | PASS WITH NOTES | Positive weight-ratio invariance is exact; (iii)'s nonnegative-constant restriction remains in assembly. |
| `kam-space` | FAIL (F1) | Weighted carrier and formulas faithful on positive/bounded locus; public norm domain too broad. |
| `kam-conventions` | PASS WITH NOTES | Conjugation identity, sum/max comparison and strip conversion correct. Vector-field angle scaling is a blueprint convention, not a theorem supplied by the strip-only conversion lemma. |
| `kam-domain` | PASS | Open/convex and monotonicity/margin statements exact on positive radii. `_hσs` unused is harmless: a retained source premise; the proof uses `σ≤1`. |

The weighted-coordinate representation is explicitly authorized by the blueprint's realization table (`w1-sequences.tex:39-66`) and track design. Removing `a,p` from the *carrier* is faithful: interpretation uses κ, and `kamEmbed` really applies `embedCLM` on both sequence components. Inherited `coeffW_embedCLM` preserves the physical coefficients. No outgoing result or source conclusion is smuggled into a parameter bundle.

Binder inventory for the source-facing theorem families (repeated binders grouped; exact declarations listed below):

| Binders | Classification | Source |
|---|---|---|
| dimensions, index/coefficient/function/space parameters; normed/Hilbert/complete scalar instances | TYPING | Source carriers, Banach/Hilbert definitions |
| positive strip widths and losses, loss < width, `n≥1` where required | SOURCE | Fourier and lattice node preambles |
| holomorphy, periodicity, pointwise bound; summable weighted coefficients for converse | SOURCE | Fourier hypotheses |
| `c≥0` lattice exponent; `τ≥1`, `γ,β≥0` | SOURCE | Lattice (iii)–(iv) |
| bounded operator A; entrywise domination off/diagonal | SOURCE | Schur preamble and (iii), expanded `KamDominated` |
| `hc : 0≤c` in Schur source-facing theorem | EXCESS (F2) | Not in the literal Schur node or W0 standing conventions |
| positive radius, domain membership, perturbation norm bound, monotone radii/weights; `0<σ≤1`, `2σ<s` | SOURCE | Domain/phase-space source locus |
| Schur row/column finite-sum bounds | SOURCE for Schur-test helper | Explicit helper theorem assumptions, not an assumed blueprint conclusion |
| `C,hC0,hC` in `kamOpNorm_apply_le`/`kamOpNorm_le` | Conditional helper inputs | Transparently names an admissible bound; not a proof that every declared L has one (F1) |
| finite-row-square bounds in `kamHilbert_cs`, coefficient identities in `kamBessel_cross` | Conditional helper inputs | Distinct intermediate lemmas; discharged in actual main proofs |

## Definitions: complete classification

Each public definition/abbreviation/structure is listed; there are 24. `KamSchurBound` and `KamDominated` are literal source predicates, not result-shaped assumption packages. No new classical choice of a source object occurs.

| Definition | Kind/body and whole-carrier assessment | Verdict |
|---|---|---|
| `KamPhase` | Product of two finite complex vectors and two complex ℓ² spaces; exact weighted-coordinate realization. | PASS |
| `kamNorm` | Literal scaled sum on positive radius; unrestricted real radius includes division-by-zero degeneration. BODY_MATCH on source locus OK; PUBLIC_CARRIER FAIL; WELL_DEFINEDNESS/CHARACTERIZATION literal, choice N/A. | FAIL F1 |
| `kamDomain` | Literal open-inequality predicate; no selection/default branch. Empty/non-source parameter sets are not used as source domains; all radius-dependent claims guard positivity. | PASS WITH NOTES: source use requires positive parameters |
| `kamEmbed` | True diagonal transport on both sequence components, with order evidence; no source object replaced by identity. | PASS |
| `kamOpNorm` | Real infimum with no finite-bound/positive-radius carrier restriction. BODY_MATCH only on bounded positive locus; PUBLIC_CARRIER FAIL; claimed least-admissible characterization unavailable globally; CHOICE N/A. | FAIL F1 |
| `kamL1` | Natural sum of absolute integer coordinates, exact on all modes. | PASS |
| `kamAbsMultiset` | Finite multiplicity encoding by coordinate; cardinal/count identities proved. | PASS |
| `kamLatticeCode` | Sign bits plus absolute-value multiset; injectivity proved including zero coordinates. | PASS |
| `kamLatticeConst` | Literal real-power formula; no explicit case/default branch; matches source for `n≥1,c≥0,σ>0`, including `b=0`. Outside that locus only a scalar formula is claimed, not a lattice bound. | PASS WITH NOTES |
| `kamChi` | Exact real-torus character, on every mode and real point. | PASS |
| `kamTrigPoly` | Genuine finite Fourier polynomial. | PASS |
| `kamOrthant` | Bool sign convention gives either ±s′; genuine case encoding, not a fallback. | PASS |
| `KamSchurBound` | Literal row/column modulus bounds for every finite partial sum. | PASS |
| `kamSchurFun` | Raw `tsum` expression on unrestricted matrices/sequences; can totalize divergent inputs. Auxiliary series expression only; **not** a globally characterized Schur operator. Every use constructing `kamSchurCLM` proves absolute convergence under its actual h and ℓ² input. | PASS WITH NOTES: retain auxiliary status |
| `kamSchurCLM` | Domain contains actual row/column bound h; series converges for every ℓ² input, membership/linearity/boundedness proved; HasSum gives all coordinates, hence uniquely determines map. No arbitrary choice/default relied on. | PASS |
| `kamBasis` | Actual single-coordinate unit vector. | PASS |
| `kamEntry` | Evaluation of bounded operator on actual unit basis. | PASS |
| `kamRowTest` | Finite conjugate row combination; exact coordinates and norm identity. | PASS |
| `kamHilbertKernel` | Zero diagonal explicitly prescribed by source; off-diagonal denominator nonzero for distinct positive integers. | PASS |
| `kamHilbertConst` | Literal π/√3; positive nonzero denominator. | PASS |
| `kamHilbertB` | Nonnegative entry modulus times kernel, embedded into K; exact source matrix. | PASS |
| `kamHilbertCLM` | Schur constructor with proved `kamHilbertB_bound`; HasSum and norm theorem characterize it for every declared bounded A. | PASS |
| `kamEntryDiagCLM` | Prior diagonal multiplier constructor with entry bound proved from A; true diagonal. | PASS |
| `KamDominated` | Exactly two entrywise domination clauses, expanded above; no hidden summability/operator-existence conclusion. | PASS |

## Complete public declaration ledger

Namespace prefix is `KAM.Wave`. File names below refer to `KAM/Wave/KamSupport/<File>.lean` at frozen-v1. Every row was inspected; auxiliary results are judged as helpers and not substitutes for a full source node. The two private lemmas (`integrable_cube`, `kamInvSq_sum_image_le`) were also read and are covered by kernel replay.

| Node / file:line | Public declaration | Verdict | Reason / scope |
|---|---|---|---|
| `fourier-banach` / `FourierBanach:38` | `kamFourierBanach_coeff_le` (theorem) | PASS | Exact Banach source estimate/convergence conclusion and constants. |
| `fourier-banach` / `FourierBanach:50` | `kamFourierBanach_sum_le` (theorem) | PASS | Exact Banach source estimate/convergence conclusion and constants. |
| `fourier-banach` / `FourierBanach:64` | `kamFourierBanach_weighted_sum_le` (theorem) | PASS | Exact Banach source estimate/convergence conclusion and constants. |
| `fourier-banach` / `FourierBanach:107` | `kamFourierBanach_summation` (theorem) | PASS | Exact Banach source estimate/convergence conclusion and constants. |
| `fourier-banach` / `FourierBanach:124` | `kamFourierBanach_coeff_sub` (theorem) | PASS WITH NOTES | N2: exact subtraction/coefficient result; weighted versions compose. |
| `fourier-banach` / `FourierBanach:138` | `kamFourierBanach_coeff_sub_le` (theorem) | PASS WITH NOTES | N2: exact subtraction/coefficient result; weighted versions compose. |
| `fourier-l2/Bessel` / `FourierBessel:36` | `kamChi` (def) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:38` | `continuous_kamChi` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:42` | `conj_kamChi` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:50` | `kamChi_mul` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:53` | `torusAverage_kamChi` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:56` | `norm_kamChi` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:63` | `kamTrigPoly` (def) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:67` | `continuous_kamTrigPoly` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:76` | `kamBessel_cross` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:103` | `kamBessel_quad` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2/Bessel` / `FourierBessel:141` | `kamBessel` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:38` | `kamOrthant` (def) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:40` | `abs_kamOrthant` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:45` | `exists_kamOrthant_eq` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:60` | `kamFourierL2_orthant_le` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:100` | `kamFourierL2_finite_le_of_lt` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:135` | `kamFourierL2_sum_le` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-l2` / `FourierL2:160` | `kamFourierL2_summation` (theorem) | PASS WITH NOTES | N1: full convergence conjuncts in imported Banach summation export. |
| `fourier-l2` / `FourierL2:173` | `kamFourierL2_eq_fourierSum` (theorem) | PASS | Correct Hilbert/Bessel/orthant support; endpoint bound preserved. |
| `fourier-shift` / `FourierShift:36` | `kamCharacter_neg_imag` (theorem) | PASS | Correct integral/character shift; no extra boundedness input. |
| `fourier-shift` / `FourierShift:51` | `kamTorusAverage_clm` (theorem) | PASS | Correct integral/character shift; no extra boundedness input. |
| `fourier-shift` / `FourierShift:62` | `kamFourier_shift` (theorem) | PASS | Correct integral/character shift; no extra boundedness input. |
| `schur` / `HilbertMatrix:41` | `kamBasis` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:44` | `kamEntry` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:47` | `norm_kamBasis` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:52` | `norm_kamEntry_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:60` | `norm_kamEntry_diag_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:64` | `kamEntry_sum_sq_col_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:74` | `kamRowTest` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:78` | `kamRowTest_apply` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:94` | `norm_kamRowTest_sq` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:106` | `kamEntry_sum_sq_row_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:147` | `kamHilbertKernel` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:149` | `kamHilbertKernel_nonneg` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:152` | `kamHilbertKernel_comm` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:157` | `kamHilbertKernel_of_ne` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:161` | `kamHilbertKernel_self` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:171` | `kamHilbertKernel_sum_sq_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:233` | `kamHilbertConst` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:235` | `kamHilbertConst_nonneg` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:238` | `kamHilbertConst_sq` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:242` | `kamHilbertConst_lt_two` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:251` | `kamHilbert_cs` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:268` | `kamHilbertB` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:271` | `norm_kamHilbertB` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:276` | `kamHilbert_row_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:280` | `kamHilbert_col_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:286` | `kamHilbertB_bound` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:293` | `kamHilbertCLM` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:297` | `kamHilbertCLM_hasSum` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:303` | `norm_kamHilbertCLM_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:309` | `kamEntryDiagCLM` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:313` | `norm_kamEntryDiagCLM_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:321` | `KamDominated` (structure) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:325` | `KamDominated.entry_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur` / `HilbertMatrix:339` | `KamDominated.weighted` (theorem) | PASS WITH NOTES | N3: exact positive weight-ratio transfer; compose representative theorem. |
| `schur` / `HilbertMatrix:358` | `kamSchurBound_of_dominated` (theorem) | FAIL | F2: nonnegative c added; constants and proof valid under hc. |
| `schur` / `HilbertMatrix:396` | `exists_clm_of_dominated` (theorem) | FAIL | F2: nonnegative c added; constants and proof valid under hc. |
| `kam-space/domain/conventions` / `KamSpace:40` | `KamPhase` (abbrev) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:45` | `kamNorm` (def) | FAIL | F1: unrestricted source-norm carrier. |
| `kam-space/domain/conventions` / `KamSpace:50` | `kamDomain` (def) | PASS WITH NOTES | See complete definition classification and source-use guards. |
| `kam-space/domain/conventions` / `KamSpace:55` | `kamEmbed` (def) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:60` | `kamOpNorm` (def) | FAIL | F1: unrestricted source-norm carrier. |
| `kam-space/domain/conventions` / `KamSpace:63` | `kamNorm_nonneg` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:66` | `kamNorm_eq_zero` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:92` | `kamOpNorm_apply_le` (theorem) | PASS WITH NOTES | Valid conditional admissible-bound lemma; does not remove F1. |
| `kam-space/domain/conventions` / `KamSpace:106` | `kamOpNorm_le` (theorem) | PASS WITH NOTES | Valid conditional admissible-bound lemma; does not remove F1. |
| `kam-space/domain/conventions` / `KamSpace:110` | `kamOpNorm_nonneg` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:115` | `kamDomain_isOpen` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:125` | `kam_convex_lt` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:136` | `kam_norm_comb` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:141` | `kamDomain_convex` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:159` | `kamDomain_mono` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:166` | `kamDomain_add_mem` (theorem) | PASS | Exact margin bound; unused source premise _hσs harmless. |
| `kam-space/domain/conventions` / `KamSpace:203` | `kamNorm_embed_le` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:214` | `kamNorm_le_of_le_radius` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:233` | `kam_conj_relabel` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:239` | `kam_wave_norm_sum_ge` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:244` | `kam_wave_norm_sum_le` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `kam-space/domain/conventions` / `KamSpace:250` | `kam_strip_period_conversion` (theorem) | PASS | Correct weighted-coordinate/domain/convention helper on stated assumptions. |
| `lattice` / `Lattice:41` | `kamLatticeConst` (def) | PASS WITH NOTES | See complete definition classification and source-use guards. |
| `lattice` / `Lattice:46` | `kamLattice_hasSum_exp` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:53` | `kamGeom_sum_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:75` | `kamLattice_partial_sum_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:103` | `kamLattice_term_fiber` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:133` | `kamLattice_tsum_pow_exp_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:161` | `kamLattice_const_nonneg` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:168` | `kamDivisor_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:176` | `kamLattice_tsum_divisor_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice` / `Lattice:203` | `kamLattice_BSigma_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:35` | `kamL1` (def) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:37` | `kamL1_cast_eq_modeSize` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:41` | `kamAbsMultiset` (def) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:44` | `kamAbsMultiset_count` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:48` | `kamAbsMultiset_card` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:52` | `kamLatticeCode` (def) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:55` | `kamLatticeCode_injective` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:68` | `kamLattice_card_filter_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:92` | `kamLattice_fiber_finite` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:106` | `kamLattice_ncard_fiber_le` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:121` | `kamChoose_add_le_pow` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:136` | `kamLattice_ncard_fiber_le_pow` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `lattice/count` / `LatticeCount:143` | `kamLattice_card_filter_le_pow` (theorem) | PASS | Correct ℓ¹ counting/summation support; exact constants on stated locus. |
| `schur/test` / `SchurTest:31` | `KamSchurBound` (structure) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:39` | `KamSchurBound.bound_nonneg` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:41` | `KamSchurBound.bound_mono` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:45` | `KamSchurBound.sq_row_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:59` | `KamSchurBound.sum_sq_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:64` | `KamSchurBound.sum_sq_partial_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:84` | `KamSchurBound.summable_row` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:103` | `KamSchurBound.sum_sq_tsum_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:115` | `kamSchurFun` (def) | PASS WITH NOTES | See complete definition classification and source-use guards. |
| `schur/test` / `SchurTest:117` | `kamSchurFun_hasSum` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:123` | `norm_kamSchurFun_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:130` | `memℓp_kamSchurFun` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:138` | `norm_kamSchurFun_sq_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:149` | `kamSchurCLM` (def) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:171` | `kamSchurCLM_apply` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:175` | `kamSchurCLM_hasSum` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |
| `schur/test` / `SchurTest:180` | `norm_kamSchurCLM_le` (theorem) | PASS | Correct matrix/Schur support; full coordinate semantics and norm bounds. |

## Verification evidence

The commands were run sequentially. Shell logs are `/tmp/W1-KAMSUP-audit-{build,kernel,axioms,carrier,lint}.log`; these are local run evidence, not committed artifacts.

Module list `M` (in the exact order used by build and replay):

```text
KAM.Wave.KamSupport.LatticeCount
KAM.Wave.KamSupport.Lattice
KAM.Wave.KamSupport.FourierBanach
KAM.Wave.KamSupport.SchurTest
KAM.Wave.KamSupport.HilbertMatrix
KAM.Wave.KamSupport.FourierShift
KAM.Wave.KamSupport.FourierBessel
KAM.Wave.KamSupport.FourierL2
KAM.Wave.KamSupport.KamSpace
```

1. `env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpg <M>`: **exit 0**, `Build completed successfully (3244 jobs).` This is the prescribed targeted incremental gate build; no clean/rebuild of the library was done.
2. `env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose <M>`: **exit 0**; output is exactly nine `replaying <module>` lines (KamSpace, FourierL2, FourierBessel, FourierShift, HilbertMatrix, SchurTest, FourierBanach, Lattice, LatticeCount).
3. `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1AuditAxioms.lean`: **exit 0**. The probe imports all nine modules, then emits `#print axioms KAM.Wave.<name>` once for every declaration in the complete ledger. All **126/126** lines say `[propext, Classical.choice, Quot.sound]`; includes **102 public theorems and 24 definitions/abbreviations/structures**. No `sorryAx` or custom axiom. Examples:

```text
'KAM.Wave.kamFourierBanach_weighted_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamLattice_tsum_pow_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamFourier_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exists_clm_of_dominated' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamOpNorm_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1AuditCarrier.lean`: final corrected probe **exit 0, no output**. Initial probe attempts had local construction/import errors; these were corrected only in scratch, and are not package failures. Final source SHA256 `4c5b430ecd498715517ac41cfd0f82bb452b05a3d1164bfaf3a9c22c3664c2fa`. It proves the concrete F1 identities, the empty-bound-set implication, and the `n=1,c=0` lattice-constant formula. The exact key witness is reproducible with:

```lean
import KAM.Wave.KamSupport.KamSpace
noncomputable section
open KAM.Wave
def auditW : KamPhase := (0, fun _ => 1, 0, 0)
def auditL : KamPhase →ₗ[ℂ] KamPhase where
  toFun W := (W.2.1, 0, 0, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
example : kamNorm 0 auditW = 0 := by simp [kamNorm, auditW]
example : kamNorm 1 (auditL auditW) = 1 := by simp [kamNorm, auditL, auditW]
example : kamOpNorm 1 0 auditL = 0 := by
  unfold kamOpNorm
  have he : {C : ℝ | 0 ≤ C ∧ ∀ W, kamNorm 1 (auditL W) ≤ C * kamNorm 0 W} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro C h
    have h' := h.2 auditW
    norm_num [kamNorm, auditL, auditW] at h'
  rw [he, Real.sInf_empty]
```

5. Lint via the **only authorized SLIM wrapper**:

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpg
```

**Exit 0**, exact output:

```text
check_lean_modules: PASS (1659 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

There is no generated-root warning or other exception to waive in this run.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, exit 0. `KAM/Root/Wave.lean` changes are exactly the nine authorized generated public imports. No frozen/provider import or DRAFT theorem enters any new module. The frozen `WaveSpace` **definition** is permitted and unchanged.
7. `git diff --check inp...HEAD`: **exit 0, no output**. All nine modules have copyright, `module`, appropriate imports/docstring, and public section/exposure. Largest file 409 lines; no overrides or forbidden proof escape in package code.

## Errata, deviations, and closeout

No new defect in a pinned mathematical source was discovered. Existing `E-W-Pos96K-1` is CONFIRMED in `docs/errata/ledger.json:2572` and explicitly adopted by this blueprint. This audit verifies the replacement estimates against the blueprint, not a fresh page-image audit of the original P96-K quotation. The source's operator-valued square-sum bound is never used here.

The six disclosed deviations were assessed: intermediate-strip scalar duality for the shift and Bessel for Hilbert estimates are valid proof-route substitutions; representation by weighted coordinates is source-authorized; finite-bound infimum is faithful only on its guarded source locus (F1); positive weight transfer is legitimate (N3); the unused margin premise is harmless; lattice real-power and external factor conventions match exactly. F2 is an additional undeclared premise restriction.

Not audited: actual W4 homological-equation consumption, a frozen theorem seal, global graph closure, arbitrary inherited track K proofs from first principles, or the original PDFs beyond the pinned blueprint/errata scope. Imported facts' actual polymorphic signatures were checked, and all dependencies of the public exports are covered by axiom inspection/kernel replay.

Decision log: apply the prompt's exact report location and focus-specific exceptions; keep audit separate from repair; no state-changing git or production edits. Findings remain open for the package owner. The report is complete even though the package receives FAIL. Required closeout: enforce/approve a faithful norm domain (F1), remove or explicitly source the nonnegative-c premise (F2), and re-audit changed signatures. Scoped Fourier/lattice approval does not waive those findings.

Final workspace check: HEAD unchanged. The shared `inp` ref advanced during this audit from `e78c95b46ab1321ef5896600b7ee7fc9babfa351` to `7b86cf178eaaffba3a7a4205a561b41ef3660455` (another package landing). Both have the identical merge base with HEAD, `72cd9d25f9e995b13475054d22d51d2872bb42aa`; the complete `git diff inp...HEAD` remains byte-for-byte identical to the saved initial diff. Protected-path and diff whitespace checks were rerun successfully; all nine module hashes and blueprint hash above rechecked against frozen-v1; both temporary audit probes deleted. `git status --short` shows only this untracked report. Report trailing-whitespace check and declaration-ledger coverage check pass.
