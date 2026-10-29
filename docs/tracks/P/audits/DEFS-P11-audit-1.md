# DEFS-P11 independent definitions audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-defaud`.
HEAD: `91dc441efbdc614303b82bef60b36c8fbc45819b`; current `inp`: `02f1bcd96b3681d37a276e77c2ec795dbece6ae4`.
`git diff inp...HEAD` is empty (exit 0). The commits differ, but the three-dot comparison contains no package changes. The pre-existing untracked handoff is untouched.

## Verdict

**FAIL for closing all three definition nodes under the handoff's whole-carrier, no-fallback policy.** This is not a failed proof-package build. There are no new public declarations, provider exports, frozen theorem anchors or proposed seals in this package; provider-type and seal-body probes are inapplicable.

| Node | Verdict | Exact closure issue / LEAN_REF |
|---|---|---|
| `bpP:p11:sec-conv#data` | **NOT CLOSABLE** | The source weighted norm takes values in `[0,∞]`; `Weighted.wsum`/`wnorm` are real-valued totalizations with divergent/unbounded behavior. `p11WBound` correctly expresses a finite bound but is a predicate, not this norm. The strip, open polydisc and canonical scaling formulas are present. |
| `bpP:p11:sec-D#data` | **NOT CLOSABLE** | No landed definition of the exact polar shell was located. `Ĝ` is present as a subexpression and `Ĝ₀` as a raw average, but the proposed `h₀`/`f₂` helpers contain a free correction `Z`; their identification with the source formulas is local and conditional. The selected `p11SlowData` has an explicit arbitrary-witness/default branch. The numeric formulas are present, some inline. Naming `P11SlowData` alone does not close these objects. |
| `bpP:p11b:sec-set#data` | **CLOSABLE as definitions only** | Use the literal upstream `SecularSpectrum.good`, not `p11c_phi4`, for Φ₄. LEAN_REF: `PlanarData`, its `Valid/kappa/actions/axes`, `p11c_axes`, `p11c_hatFix`, `p11c_hatMov`, `p11c_secular`, `poincareProd`, `SecularForm.constantTerm/pairA/pairB/coeffs`, `p11c_sigma`, `p11c_frame`, `SecularSpectrum.good/nr4`, `SecularForm.laplace_def`, `p11c_laplace`, `p11c_pairCoeffs` (its b0/b1/D lets), `p11c_coeffs` (its pref let), `p11c_orbitJet` (X/z lets), frozen `Phase/assemble/oscillatorAction/symplecticForm/hamiltonianVectorField`, `p11c_bracket`. No spectral, common-jet, analytic or torsion theorem is certified by this definition closure. |

Authority read: AGENTS.md, PLAN.md, DECISIONS.md, the named independent-audit brief and handoff, all three full NODE records with their source/dependency lines, Part 11 L10–12 and L145–153, Part 11b L14–16, referenced Part 9 good-polynomial definition, Part N weighted norm definition, track P statement, P11A/P11B/P11C design tables and relevant standalone signatures, T1-audit-1.md, and the actual defining Lean bodies. The user's exact absolute destination overrides the generic brief's MAIN-worktree destination. Prior audit workflow notes were used only as a checklist; checks below were rerun here.

## Source-object ledger

Names are in `KAM.Planetary` unless qualified. A literal let/subexpression is explicitly identified as such: no nonexistent global alias is claimed. Reusing an expression inside a definition is sufficient for a mere abbreviation such as β₀. It does not identify an arbitrary correction or output witness with a prescribed source function.

### Conventions: `bpP:p11:sec-conv#data`

| Source object | Lean declaration / exact locator | Verdict | Body / carrier assessment |
|---|---|---|---|
| period-one angles and characters | `KAM.Weighted.coeff`, `KAM/Weighted/Norm.lean:48`; `modeWeight`, same file:52 | FAITHFUL | Coefficient is the period-one torus integral with the 2π character; weight is exp(2π s modeSize k), with integer Fourier indices. |
| max norms and induced operator norms | `P11Vec/P11CVec/P11Phase`, `KAM/Planetary/WeakMeasure/Basic.lean:24–26`; frozen `Phase`, `KAM/Frozen/Planetary/Defs/Phase.lean:37` | FAITHFUL | Pi and product carriers retain their standard max norms; no replacement instance. Euclidean physical lengths remain explicit sums of squares. |
| weighted norm `wn(u,V,σ)` | `KAM.Weighted.wsum`, `KAM/Weighted/Norm.lean:55`; `wnorm`, same file:69; candidate `p11WBound`, `KAM/Planetary/Preparation/RectangularBracket.lean:40` | NOT FAITHFUL | `wsum : ℝ` is zero if the positive series is not summable. `wnorm : ℝ` is a conditionally complete real supremum over `polyNbhd D r`, not an extended norm over arbitrary V. `p11WBound V s f M` explicitly includes summability and correctly expresses a finite bound; it is not a function returning the source norm. |
| `T_σ` | `KAM.complexStrip`, `KAM/Frozen/Defs/ComplexStrip.lean:23` | FAITHFUL | Every coordinate satisfies abs(Im θ_i) < σ. This is also correct for zero dimension and nonpositive σ with the coordinatewise convention. |
| open polydisc `D(c,r)` | `Metric.ball c r` on `Fin m → ℂ`; `p11Box`, `KAM/Planetary/Preparation/RectangularBracket.lean:36` | FAITHFUL | Open max-norm ball; p11Box is its two-block coordinatewise version with independently specified radii. `Weighted.polydisc` at Domains:39 is **closed** and is not the intended candidate. For dimension zero, the coordinatewise and norm-ball conventions at nonpositive r differ; the source uses positive radii, and this is not an assertion equating them for all real radii. |
| canonical 1-chart `T` | `p11FastScaleL/p11FastScale`, `KAM/Planetary/Preparation/HoloChart.lean:43,56`; `p11PolarScaleL/p11PolarScale`, `KAM/Planetary/Preparation/Polar.lean:103,115` | FAITHFUL | On disjoint fast/slow blocks these scale angles by 2π and actions by (2π)⁻¹. Their composition is exactly the displayed T, everywhere. `Hamiltonian.angleScale` alone scales only angles and is not this canonical chart. |

For example, with one angle, no parameters and s>0, u(θ)=1/(1−exp(−2πs)exp(2πiθ)) is holomorphic and periodic on the open strip. Its nonnegative Fourier coefficients are exp(−2πsk), so every nonnegative weighted term is 1 and the source norm is infinite. The Lean zero-on-nonsummability behavior cannot represent this case. This is a mathematical counterexample to whole-carrier fidelity, not an independently formalized Fourier calculation.

The norm failure is about the requested object on its public carrier, not a claim that finite-bound estimates proved using `WSummable` are invalid. A finite-norm-only interpretation would require an explicit revised closure contract; this audit does not introduce one.

### Step D: `bpP:p11:sec-D#data`

| Source object | Lean declaration / exact locator | Verdict | Body / carrier assessment |
|---|---|---|---|
| Π | `p11PolarC`, `KAM/Planetary/Preparation/Polar.lean:33`; slow projection `p11PolPt`, `KAM/Planetary/Preparation/SlowAverageOsc.lean:36` | FAITHFUL | Principal sqrt(ρ̃/π) times sin/cos(2πζ), with untouched fast blocks. Literal signed formula, no witness/default branch. Analyticity is only asserted where the root branch permits it. |
| polar shell `P_ε` | No exact landed shell declaration found. Related `p11SlowAvgBox`, `KAM/Planetary/Preparation/SlowAverageF2.lean:31`; `p11SlowBox`, `KAM/Planetary/Preparation/SlowDivisor.lean:36`; `p11RePos`, `KAM/Planetary/Preparation/SlowAverageDom.lean:28` | MISSING | The first two are action boxes including fast J restrictions; the last is only a positive-real-part condition. None is the source set of slow angle/action pairs with both abs(Im ζ)<σF/6 and abs(ρ̃−2πε)<πε. Existing strip/ball constructors can express it, but that assembled source set is not a landed declaration. |
| `Ĝ(J,ζ,ρ̃)` | `Fast.G (p11SlowJ z.2, p11PolPt z)` subexpression of `p11SlowF2`, `KAM/Planetary/Preparation/SlowAverageF2.lean:66` | FAITHFUL | Literal pullback of the supplied fast-averaged G by Π. No separate `Ghat` alias was located; this expression, not the whole f₂ helper, is the reference. |
| `Ĝ₀` | `p11PolarAverage Fast.G`, `KAM/Planetary/Preparation/PolarAverage.lean:69` | FAITHFUL | Raw unit-torus integral of G at the exact principal-root polar point for every argument; no choice of extension. Standard Bochner integral totalization is visible, not a custom branch. On the analytic source domain the integrand is integrable. |
| `h₀= h̃+ε Ĝ₀` | Candidate `p11SlowH0`, `KAM/Planetary/Preparation/SlowAverageF2.lean:58`; `P11SlowSpecOf`, `KAM/Planetary/Preparation/SlowData.lean:54` | NOT FAITHFUL | Helper body is h+ε(p11SlowSec+Z), with arbitrary parameter Z. The record/spec identifies h₀ with the raw mean only for I in V (SlowData:63–65); this does not give the requested whole-carrier definition. The direct source expression using `p11PolarAverage` is constructible, but is not this helper for arbitrary Z. |
| `f₂=ε(Ĝ−Ĝ₀)+f₁∘(id,Π)` | `p11SlowF2`, `KAM/Planetary/Preparation/SlowAverageF2.lean:63` | NOT FAITHFUL | Contains p11SlowSec+Z rather than the raw mean. `P11SlowPolarOut` at same file:36 restricts the needed average equalities to its domain and positive-real actions. Correct local construction does not make this arbitrary-Z function the source function everywhere. |
| `K₂` | `p11K2`, `KAM/Planetary/Preparation/SlowData.lean:36` | FAITHFUL | Exactly 3ν/(π(σF/12)) log(1/ε), including real ν and unchanged parameter dependence. |
| `α_(1)` | `P11SlowSpecOf` divisor subexpression, `KAM/Planetary/Preparation/SlowData.lean:79–82` | FAITHFUL | γ/4 K₂^(−τ) when the fast Fourier block is nonzero; the full conditional expression includes the slow ε factor. No separate named α_(1) is claimed. |
| `α_(2)` | Same expression, `KAM/Planetary/Preparation/SlowData.lean:80–82` | FAITHFUL | ε γ/4 K₂^(−τ) when the fast block vanishes, with ε appearing once. |
| `s₂` | `p11s2`, `KAM/Planetary/Preparation/SlowData.lean:38` | FAITHFUL | min(s₁/4, γ/(8 L K₂^(τ+1))), literal signed formula. |
| `r_*` | Second radius in `p11SlowBox`, `KAM/Planetary/Preparation/SlowDivisor.lean:37`, also `P11SlowSpecOf`, SlowData:57 | FAITHFUL | Literal π ε expression. No standalone `rStar` declaration. |
| `σ₃` | `P11SlowSpecOf` local `s`, `KAM/Planetary/Preparation/SlowData.lean:59`; `p11K2`, same file:37 | FAITHFUL | Literal σF/12 expression, not a chosen strip width. |
| slow frequency / Ω̃ | `p11SlowSec`, `KAM/Planetary/Preparation/SlowAverageOsc.lean:40`; `P11SlowSpecOf`, SlowData:66–69 | FAITHFUL-WITH-NOTE | Ω/(2π) is literal in the linear ρ̃ term. The derivative identity for h₀ additionally needs the local h₀ identification; no global frequency theorem is inferred. |

`P11SlowData` (SlowData:40) is an output structure with six arbitrary function fields, not a definition of these six source objects. `p11SlowData` (SlowSigned:105–106) is `if h : ∃ A, ... then h.choose else default`; `p11SlowConstant` (SlowSigned:102–103) similarly uses choice and an `else 1`. These are **NOT FAITHFUL** as substitutes for explicit source definitions under this handoff's no-arbitrary-witness/no-fallback policy. This does not refute the local existence theorem that makes a chosen record satisfy its specification on its stated domain.

The exponential cutoff identity at source L153 is an algebraic identity on the stated positive-ε domain, not another missing definition. No new proof of it, polar holomorphy or the sharp polar norm bound is certified here.

### Planar setting: `bpP:p11b:sec-set#data`

| Source object | Lean declaration / exact locator | Verdict | Body / carrier assessment |
|---|---|---|---|
| G,m₀,m; κ; valid source data | `PlanarData/Valid/kappa`, `KAM/Planetary/PlanarTorsion/Setting.lean:31,36,37` | FAITHFUL | Raw physical scalars and precisely their positivity predicate; no theorem or conclusion field. |
| Ψ, w, u_i | `poincareProd`, `KAM/Planetary/Poincare/Product.lean:45`; frozen `Phase` and `assemble`, `KAM/Frozen/Planetary/Defs/Assemble.lean:38`; `p11c_hatFix/hatMov`, Setting:44–46 | FAITHFUL | Existing physical product chart; coordinates are (λ,ξ;Λ,η). Planetary slow pair i is (ξ_i,η_i), not two contiguous Pi blocks with reversed signs. |
| a_i, Λ_i, A₂ | `PlanarData.axes/actions`, Setting:39,41; `p11c_axes`, Setting:38 | FAITHFUL | Explicit I²/(m²κ), m sqrt(κa), and 0<a0<a1. No custom branch. Inverse identities require source positivity; invalid parameters are not physical data. |
| α | local `alpha`, `p11c_Q`, `KAM/Planetary/PlanarTorsion/SpectralAdapter.lean:39` | FAITHFUL | Literal a0/a1; physical cone implies 0<α<1. |
| S_fix | `p11c_secular (p11c_hatFix p)`, Setting:44,48 | FAITHFUL | Frozen radian secular average of the actual physical pullback. |
| S_mov | `p11c_secular (p11c_hatMov p)`, Setting:45,48 | FAITHFUL | Same chart and average, retaining central-mass term. Equality of jets is an inherited theorem obligation, not a defining field. |
| C₀ | `SecularForm.constantTerm`, `KAM/Planetary/SecularForm/Coefficients.lean:37` | FAITHFUL | Negative pair sum with the normalized b_(1/2)^0 integral. |
| a₁₂ | `SecularForm.pairA`, Coefficients:31; local A in `p11c_Q`, SpectralAdapter:40 | FAITHFUL | G m0 m1 α b_(3/2)^1/(4 a1), with inner planet numbered 0. |
| b₁₂ | `SecularForm.pairB`, Coefficients:34; local B in `p11c_Q`, SpectralAdapter:41 | FAITHFUL | Same prefactor and b_(3/2)^2. |
| Q_h | `SecularForm.coeffs`, Coefficients:42; `p11c_Q`, SpectralAdapter:37 | FAITHFUL | Matrix diagonals −A/I_i, off-diagonals B/sqrt(I0 I1); no doubled Q. The physical equality bridge is `p11c_Q_eq_coeffs` in SpectralAdapter. |
| σ_i | `p11c_sigma`, SpectralAdapter:44; upstream `SecularForm.sigma`, Coefficients:121 | FAITHFUL | Explicit trace ± discriminant-root /2 in increasing order, identical to signed definition. Negativity and strict ordering are properties on valid physical axes, not arbitrary-input premises hidden in the definition. |
| ρ in SO(2) | `p11c_frame`, `KAM/Planetary/PlanarTorsion/Frame.lean:38` | FAITHFUL | Explicit normalized eigenvector v=(-Q01,Q00−σ0), matrix [e,Je]. No selected eigenbasis or arbitrary angle lift. Its denominator is nonzero on physical positive data/axes; no claim of SO(2) membership at invalid data. |
| Φ₄ | `SecularSpectrum.good`, `KAM/Planetary/SecularSpectrum/GoodPolynomial.lean:47`, composed with σ; discriminant at :37 | FAITHFUL | Exactly discriminant times the product over K4 and all permutations, as Part 9 L168 defines it. **Do not substitute** signed `p11c_phi4` (Birkhoff/Defs:35): that is only the one-product nonzero-locus adapter and is NOT FAITHFUL as this literal polynomial. |
| NR₄ | `SecularSpectrum.nr4`, GoodPolynomial:35; `k4`, same file:34 | FAITHFUL | Injective spectrum and all nonzero integer modes of l1-size ≤4, exactly Part 9 L166. `p11c_NR4` (Characters/Defs:53) is a parameterized variant without a separate simplicity conjunct; equality of two frequencies is already excluded by k=(1,−1). |
| b_s^(k) | `SecularForm.laplace_def`, `KAM/Planetary/SecularForm/LaplaceCoeff.lean:28`; `p11c_laplace`, `KAM/Planetary/PlanarTorsion/LaplaceReduction.lean:25` | FAITHFUL | Normalized radian integral (2π)⁻¹ ∫ cos(kt)(1+α²−2αcos t)^(−s). Adapter uses division by the s-power; landed equality `p11c_laplace_eq_laplace_def`, SpectralAdapter:55, holds for all s,k,α. |
| β₀ | local `b0` in `p11c_pairCoeffs`, `KAM/Planetary/PlanarTorsion/PairCoefficients.lean:34` | FAITHFUL | Exactly `p11c_laplace (1/2) 0 a`. The argument here is α. |
| β₁ | local `b1`, same file:35 | FAITHFUL | Exactly `p11c_laplace (1/2) 1 a`. |
| Δ | local `D`, same file:36 | FAITHFUL | 1−α², with no altered denominator. |
| pref | local `pref` in `p11c_coeffs`, `KAM/Planetary/PlanarTorsion/Quartic/Defs.lean:28` | FAITHFUL | −G m0 m1/a1 with Lean's two planet indices; this m0 is `p.m 0`, not central `p.m0`. |
| ζ=v0+i v1 | local `z` in `p11c_orbitJet`, `KAM/Planetary/PlanarTorsion/OrbitJet/Analytic.lean:41` | FAITHFUL | Literal complex embedding of eccentricity pair, no conjugation or scaling. |
| X=exp(iλ) | local `X` in `p11c_orbitJet`, same file:40 | FAITHFUL | Radian λ; no period-one factor inserted. |
| slow variables z_j=(x_j,y_j) | frozen `Phase 2`, `KAM/Frozen/Planetary/Defs/Phase.lean:37`; `p11c_slowLength/pairDot`, Setting:51–52 | FAITHFUL | z.1 is the x vector, z.2 the y vector. Per-oscillator pair is (z.1 j,z.2 j), not (z.1,z.2) with j treated as a block selector. |
| R_j | `oscillatorAction z.2 z.1`, `KAM/Frozen/Planetary/Defs/OscillatorAction.lean:37` | FAITHFUL | (y_j²+x_j²)/2, exactly the prescribed action. |
| chart form | `KAM.symplecticForm`, `KAM/Frozen/Defs/SymplecticForm.lean:23`; frozen `assemble`, `KAM/Frozen/Planetary/Defs/Assemble.lean:38` | FAITHFUL | Sum dp∧dq in (λ,x;Λ,y), hence dΛ∧dλ+dy∧dx. |
| X_G and bracket | `KAM.hamiltonianVectorField`, `KAM/Frozen/Defs/HamiltonianVectorField.lean:24`; `p11c_bracket`, `KAM/Planetary/PlanarTorsion/Characters/Defs.lean:59` | FAITHFUL | Field (∂yG,−∂xG), bracket fderiv F applied to that field. Λ is held as a parameter by passing F I and G I. |

Literal arithmetic, real sqrt, principal complex sqrt, integrals and derivatives retain their library totalizations. They contain no newly invented branches. Physical positivity, collision avoidance, integrability and differentiability retain their source domains; no universal regularity or inverse-dictionary assertion is being smuggled into these definitions. In contrast, the source explicitly allows an infinite weighted norm, which a real-valued totalized sum cannot represent.

## Signature and source discrepancies

Whitespace-normalized declaration comparison with `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` and `P11CSignatures.lean` returned `MATCH` for all 12 checked declarations:
`p11PolarC`, `p11PolarR`, `p11PolarAverage`, `p11K2`, `p11s2`, `p11WBound`, `p11c_laplace`, `p11c_sigma`, `p11c_frame`, `p11c_phi4`, `p11c_NR4`, `p11c_bracket`. This does not turn an approved adapter into a different mathematical object. No signed formula was silently repaired.

1. **Norm carrier gap.** `blueprint-N/parts/p4-weighted-norms.tex`, definition `bpN:p4:norm`, L50 says the norm is “∈[0,∞]”; Part 11 L10–12 imports it. Lean Norm:54 explicitly says “junk `0` if not summable; use `WSummable` alongside”, and Norm:68 says the supremum is “meaningful only under `HasFiniteWNorm`”. The design table P11A L196's reference to “existing Weighted/frozen definitions” is insufficient for unconditional definition closure. This is an implementation/closure mismatch, not evidence that the pinned mathematical norm definition is false.
2. **Step D coverage gap.** P11A design L199 names `p11K2`, `p11s2`, `P11SlowData` for all Step D data. Those names omit the exact shell and do not make the record fields canonical formulas. Local specifications and construction theorems remain valid at their stated scope; the no-fallback definition closure is stronger.
3. **Φ₄ adapter distinction (declared, not new source erratum).** Part 9 L168 defines “D(σ) ∏ R_k(σ)” with R_k a permutation product. `p11c_phi4` contains only ∏(k·σ). For two frequencies, writing this latter product P, the literal upstream polynomial is D P², not P. P11C design L187 explicitly says this is an adapter for the **nonzero locus**, “not an assertion that two possibly differently normalized polynomials are definitionally equal”. `Generic.lean:110` supplies the physical nonzero-locus bridge. The faithful source definition is already landed as `SecularSpectrum.good`; the setting node can cite it directly.

No new pinned-source mathematical erratum or frozen-statement defect was established. No deviation was introduced by the auditor. The declaration/classification gaps above must not be reported as failed kernel checks or as closure of analytic theorem nodes.

## Validation

All auditor Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1`; each direct Lean/kernel invocation used `nice -n 5`. The compile gate supplies niceness internally. No resource override, cache fetch, clean, package update or library-wide build was used.

Targeted builds:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-defaud KAM.Planetary.Preparation.SlowData KAM.Planetary.Preparation.SlowAverageF2 KAM.Planetary.PlanarTorsion.Birkhoff.Defs KAM.Planetary.PlanarTorsion.Characters.Defs KAM.Planetary.PlanarTorsion.OrbitJet KAM.Planetary.SecularSpectrum.GoodPolynomial KAM.Weighted.Norm
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-defaud KAM.Planetary.Preparation.HoloChart
```

Both exit **0**; final lines respectively `Build completed successfully (9429 jobs).` and `Build completed successfully (9281 jobs).` These are Lake job counts including cached dependencies, not a library rebuild. Replayed upstream unused-variable/simp/deprecation warnings remain; no target failed.

Probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/DefsP11Audit.lean
```

The first invocation exposed a missing scratch import for `p11FastScale`; after adding `import KAM.Planetary.Preparation.HoloChart` and building that module, the corrected invocation exited **0**, with no proof errors. It verified literal `rfl` formulas for σ_i, K₂, R_j and the bracket, and proved from `¬ WSummable f s I` that `wsum f s I = 0` using `tsum_eq_zero_of_not_summable`. This last probe establishes the fallback behavior, not existence of divergence for every source function.

All 26 inspected definitions depend on exactly `[propext, Classical.choice, Quot.sound]`. Exact output:

```text
'KAM.complexStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.modeWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.wsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.wnorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11s2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowF2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.nr4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_phi4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_NR4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_orbitJet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.SlowData KAM.Planetary.Preparation.SlowAverageF2 KAM.Planetary.Preparation.HoloChart KAM.Planetary.PlanarTorsion.Birkhoff.Defs KAM.Planetary.PlanarTorsion.Characters.Defs KAM.Planetary.PlanarTorsion.OrbitJet KAM.Planetary.SecularSpectrum.GoodPolynomial KAM.Weighted.Norm
```

Exit **0**. Exact output:

```text
replaying KAM.Weighted.Norm
replaying KAM.Planetary.SecularSpectrum.GoodPolynomial
replaying KAM.Planetary.PlanarTorsion.OrbitJet
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Polar
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Line
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Jet
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Algebra
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
replaying KAM.Planetary.PlanarTorsion.OrbitJet.Expansion
replaying KAM.Planetary.PlanarTorsion.Characters.Defs
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Defs
replaying KAM.Planetary.Preparation.HoloChart
replaying KAM.Planetary.Preparation.SlowAverageF2
replaying KAM.Planetary.Preparation.SlowData
```

Required lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **0**. Exact output:

```text
check_lean_modules: PASS (1215 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated-root exception was needed in this checkout; module checks, frozen-anchor guard and all 144 frozen ABI hashes passed.

Static/import checks: the eight target modules' recursive local KAM import closure contains **406 modules**, no provider and no frozen theorem module; frozen imports are definitions, so no DRAFT_SORRY theorem is consumed. Target file line counts: SlowData 119; SlowAverageF2 195; HoloChart 503; Birkhoff/Defs 77; Characters/Defs 64; OrbitJet 78; GoodPolynomial 287; Weighted/Norm 171. Headers, module declarations, public imports, docstrings and exposed public sections were inspected. There are no new declarations to audit for additional conclusion-shaped premises; selected-data structures were explicitly rejected as formula definitions where appropriate.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff --check`: exit 0. Only this report was written outside the disposable `.lake/abi-scratch/` audit files. Scratch files were removed after validation. No state-changing git command was run.
