# Lean design: the general torus-certificate black box and its lunar client (track SO)

Design SO-DESIGN, **Revision 3**, 2026-10-29, branch `inp-design-so` (Revision 1: `628569c9`; Revision 2:
`d2352a2d`, audited FAIL in `docs/tracks/SO/audits/SO-DESIGN-audit-2.md`). This is
planning evidence only. It claims no proof, touches no frozen file and freezes nothing. Appendix A (the
exact draft signatures) elaborates against the shared `inp` build with `sorry` bodies only (§9).

Scope (owner, 2026-10-29, D30 and the scope decision in `SPIN-ORBIT-PLAN.md`): a fully general checker
`checkTorusCertificate` with its soundness theorem, derived through the sealed isoenergetic theorem
`KAM.Iso.Apost.g1_explicit`. It covers any `n ≥ 2` and any rationally independent reference vector (the
Diophantine membership is the external input). Hamiltonians are finite expressions with division by
certified nonvanishing expressions; embeddings are Fourier data in all coordinates. The lunar spin–orbit
system (band `|p − 1| ≤ 33/1000`) is the first client. A genuine `n = 3` nonresonant toy is part of the
validation.

### Input pins

Revision 2 base: `inp-design-so` at `ad56e402` (Revision 1 plus audit 1). `inp` read at `ae496996`, which
includes the landed SO-MODEL, SO-DIO and SO-CLOCK. Running siblings were read at: SO-PI `inp-sopi`
`779c9632`, SO-REPLAY `inp-soreplay` `b3c96def` (prototype only, no measurements), and SO-GEN `inp-sogen`
`c281945d` (work in progress). SO-CONST has no commits yet.

| Input | SHA-256 |
|---|---|
| `KAM:docs/campaign/design/SPIN-ORBIT-PLAN.md` (with owner rulings O1–O4) | `3998c99a574d101e4d407f4f13b171ad522a7f50c4aa163d5b43ccd2d533a957` |
| `docs/tracks/SO/audits/SO-DESIGN-audit-1.md` | `ebc2d1f535242dddbc45718ad9c1cd942baf6ec4dd3e0269a015f625de0784f2` |
| `KAM:docs/explorations/lunar-spin-orbit-certificate-proposal.md` | `67227392977b384340c8ae7fdd2010b88fb5aeadd05672c53bab79ded2ea3d0a` |
| `KAM:docs/explorations/lunar-spin-orbit-feasibility-report.md` | `9c333266c380a96172125ffcca3ecf5aedde2d59056a3cedaeaef7a318697241` |
| `KAM/Iso/Apost/G1.lean` | `202ba7ef0fe5c215ece86970a40a8265d508243f303c2c417ce2f71250b57f40` |
| `KAM/Iso/Charts/Inputs.lean` (`IG1Body`) | `a8f405840e6a94be71deeb6632aba601e237961933f3d4e26e81e5bb21ad3bfe` |
| `KAM/Iso/Apost/Defs.lean` (`isoC1`, `isoC2`) | `bfe66bba3354dbcd66b5bbaa2dab630018b6fb44259e31cad47a319032bb8163` |
| `inp-sopi:KAM/Certificate/Arith/PiHigh.lean` | `0ee583ddcb69816240e0a38376de2819c71688941cc990f97f1dd00a1e907880` |
| `inp:KAM/Certificate/Clock.lean` | `a3c36e266fa80bb5bcf863db553398e443b21e159719faf6eb11458f0fcf9bf1` |
| `inp:KAM/Certificate/QuadraticDiophantine.lean` | `511dafebbd09f98e74dcdf9f7cb95401186269e1c04efe2d5f55ab5aa14af632` |
| `inp:KAM/SpinOrbit/Model.lean` | `d9b99918c48809dd7713fcd0560a58b0c347a99bb603bea05d316aef22f8d46f` |
| `inp:KAM/SpinOrbit/Hamiltonian.lean` | `586af68ee2cc4d5bdefbabc9d40aa7950d24c2970ea026d3d9d69e63e6bb295e` |

## Revision 3

Revision 3 is a small, targeted repair of the three new findings of the independent design audit 2
(verdict FAIL, base `0cb95879`) and of the residual items it lists under F3 and F6. Nothing else changes;
the Revision 2 table below stays valid except where this table supersedes it.

| Item | Change | Where |
|---|---|---|
| **F7** (HIGH) averaged torsion not attached to the dimension | `torsionAvgCheck` now takes `n` and **first** checks the exact shapes `ModelMatrix.HasShape (n + 1) T` and `HasShape (n + 1) S` (decidable list-length tests: `n + 1` rows, each of length `n + 1`); it rejects otherwise, and all its matrix arithmetic is on `(n+1) × (n+1)` arrays. New law-free contract `torsionAvgCheck_shape` (pass ⇒ both shapes; this also states the F7 negative test). `torsionAvgCheck_sound` is stated for that same `n` (`h : torsionAvgCheck n T S σTμ = true`). Because `torsionIdx n` is a bijection onto `{0, …, n}`, `HasShape (n+1) T` plus `T.Encloses n (torsionIdx n) ρ F` makes the checked list matrix exactly the denoted bordered matrix, so the audit's `3×3` matrix `A` with singular leading block can no longer certify the `n = 1` average. The producer now also exports the shape: `torsionModels_sound` concludes `HasShape (n + 1) T ∧ T.Encloses … ∧ continuity`. `checkTorsion` calls `torsionAvgCheck n` with `c.torsInv`, and `checkTorsion_sound` assembles at the certificate's own `n`. The general inverse test is not restricted (no principal-block condition, no `2 ≤ n` substitute). New negative test 9 (§8). | §1.9, §4, §8; A §F, §G |
| **F8** (MEDIUM) norm bounds false at `n = 0` | `norm_fderiv_hamiltonianVectorFieldℂ_le` and `norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` take `(hn : 1 ≤ n)`; the row-sum premise is then nonvacuous and forces `0 ≤ B`. The checker derives `1 ≤ n` from `StaticFacts.hn : 2 ≤ n` in `checkHamBounds_sound`. | §1.3, §4; A §E |
| **F9** (MEDIUM) lunar `J`-row identity | Corrected. Since `H` is affine in `J` with `∂_J H ≡ 1` and the other partials independent of `J`, `X_H(K̃) = X_H(K₀)`, so `E(K̃) = E(K₀) − (0, 0, 0, D_{sω*}ΔJ)`: **`E(K̃)_J = E(K₀)_J − D_{sω*}ΔJ`**, which is `p r − D_{sω*}ΔJ` under the scalar pilot identities (and only then). Gate G-J now budgets the **sum**: `B_r + B₁ + B_c ≤ e/2`, where `B_r = sup|E(K₀)_J|` (`= sup|p r|` under the pilot identities), `B₁ = sup|D_{sω*}ΔJ|`, and `B_c` bounds every other candidate-replacement error (finite Fourier `q, φ, p` data differing from the pilot's scalar embedding, coefficient rounding/truncation), with the `q, φ, p` rows `≤ e/2` likewise. The previous stand-alone target `B₁ ≤ e/4` is withdrawn. The mandatory recomputation of the **actual full residual** of `K̃` by the checker (and by SO-GEN's exact evaluator) is unchanged; no identity is used in soundness. | §6, §10 |
| **F3** residual (torsion/sub-check contract) | Closed by F7: the producer→consumer pair `torsionModels_sound` → `torsionAvgCheck_sound` now matches on `n`, shape, enclosure and continuity, with no unstated premise. Also from the audit's soundness notes: `CertPoly.add` is **exact list concatenation** (law-free, no error term) with `eval_add` an equality, because a uniform bound for all complex `θ` cannot hold for rounded nonzero modes; rounded coefficient merging lives only in the strip-weighted `CertModel.add`. Implementation obligations recorded for SO-EXPR/SO-BALL: jet compilation/pruning must keep every denominator-validation slot (folding `0 * (1/0)` to `0`, or `.pow a 0` to `1`, must not drop a denominator that `NonvanishingOn` requires). | §1.4, §4, §7; A §B |
| **F6** residual (SO-BALL's dependence on `CertArith ℚ`) | The trivial exact instance `instCertArithRat` / `instLawfulCertArithRat` (`val = cast`, zero errors) moves to the **pre-gate** SO-AIF (`Arith/Rat.lean`); SO-BALL imports it. SO-ABK (post-gate) keeps only `Arith/Fixed` and the production-backend choice. Lines move from SO-ABK to SO-AIF; totals are unchanged. | §5, §7; A §A |

## Revision 2

Revision 2 answers every finding of the independent design audit 1 (verdict FAIL) and the owner rulings
O1–O4. The table lists each change and where it lives. "A §X" means section X of Appendix A.

| Item | Change | Where |
|---|---|---|
| **F1** (BLOCKING) frequencies | The single-`ℚ(√d)` carrier `CertFreq` is **removed**. The certificate carries only a rational box `freqBox : FreqBox` (centre and radius per coordinate). The black box quantifies over an **exact real vector** `ωstar : Fin n → ℝ` and takes two proved facts about it: `hω : FreqEncloses n c.freqBox ωstar` (its denotation lies in the box) and the external input `hdio : IsDiophantine γ τ ωstar`. Every sub-check is uniform over the box. Any rationally independent `n`-tuple is therefore admissible. A provider `algFreq`/`algFreq_encloses` covers coordinates in `ℚ(x)` for a certified real `x` (`checkRootEnclosure`, any `m`-th root). The lunar `n = 2` case keeps its exact `ℚ(√5)` instance (`lunarFreq{Minus,Plus}_eq`, then `lunar{Lower,Upper}Cert_freq`). The genuine `n = 3` example is `cubicFreq = (∛2/2, ∛4/2, 1/2)`, which is `(1/12, 2)`-Diophantine by the norm form of `ℚ(∛2)`; it comes with a positive-residual toy, `toyCert3_torus`. Diophantine membership stays external and is not weakened, and the headline is not restricted to `n = 2`. | §1.10, §4, §8; A §G "Exact frequencies", §J |
| **F2** (HIGH) arithmetic laws | Option "restructure". (a) Real data has a **law-free direct denotation** `CertRealPoly.eval` (constant `val zero` plus the sum of `c χ_k + c̄ χ_{−k}`). `CertEmbedding.eval` uses it, and a missing component denotes `0` rather than a backend `ofInt 0`. Reality of `K` (`isRealOnReals`), differentiability and periodicity are law-free and unconditional; the audit's `α = Unit` carrier is harmless for them. (b) Every theorem about a *computed* object assumes `[LawfulCertArith α]`: `eval_toPoly` (the explicit "constant plus conjugate-pair sum" denotation theorem), `conjugateSymmetric`, `CC.toC_conj`, `CC.toC_zero`, `eval_add`, `eval_conjReflect`, the model and witness theorems, and all sub-check contracts. (c) Backend default values were rechecked. `ModelMatrix.Encloses` requires every entry to be present, `polyMatrix` and `CertEmbedding.eval` default to `0`, and `compose_sound` states `ms.length = wanted.length` and indexes without a default. | §2; A §A, §B, §D, §F |
| **F3** (MEDIUM) torsion contract | `torsionModels_sound` is stated. Its inputs are the validated weight and `π`, a successful `gramCheck` whose certified `(δ, β)` is passed into `torsionModels`, successful construction, the frequency box with `FreqEncloses` of the exact `ω`, the scalar `s`, `K` mapping the strip into an open `D`, and `e.NonvanishingOn D`. Its conclusion is the entrywise enclosure of the **literal frozen** `extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)` (the `torsion` block with `DN[sω]`, the border column `sω`, and the last row `DH(K) N`) together with its continuity. `gramCheck_sound` now also exports `‖G⁻¹ − B‖ ≤ δβ/(1−δ)`. All eight sub-check contracts are stated, with an acyclic assembly route to every `G1Hyps` field (§4). `hT`, Gram invertibility and torsion continuity are derived, never assumed. | §1.9, §4; A §F, §G "Sub-check contracts" |
| **F4** (MEDIUM) toy | Revision 1's zero-error `ℚ(√5)` toy was unrepresentable and is replaced. **T2**: `H = J + p²/2`, `K = (θ, (ν̃, −ν̃²/2))` with **rational** `ν̃ ≈ ν₋`, reference vector `(ν₋/2, 1/2)` from SO-DIO, `s = 2`, and a **positive** residual budget `err ≥ |ν̃ − ν₋|`. **T2d** is T2 with a division in `H`, to exercise O2. **T3** is the `n = 3` analogue with `cubicFreq`. All three discharge the Diophantine premise (`toyCert{2,2d,3}_torus`). A separate checker-only test **TR** keeps exact rational `ν = 1/2` and zero error, and is labelled as having no Diophantine premise (its vector is resonant). | §8; A §J |
| **F5** (MEDIUM) Fourier `J` | Both remedies apply. (a) The checker evaluates **every** sub-check on the actual four-component candidate `K̃ = (q, φ, p, J̃)`: invariance, energy, `DK`, Gram, torsion and graph checks all read `J̃`'s data. No pilot identity (`H(K) = E₀`, zero energy error) is used anywhere in soundness. (b) Feasibility gate **G-J** applies before SO-DATA. SO-GEN must deliver exact finite data plus explicit strip-weighted budgets for `ΔJ := J̃ − J₀`, where `J₀ = E₀ − p²/2 − V(q, φ)` is the exact energy lift and `H(K̃) − E₀ = ΔJ` holds identically. The budgets are `B₀ = sup_{T_ρ}|ΔJ|`, `B₁ = sup_{T_ρ}|D_{sω*}ΔJ|`, and `B₂ = max(sup|∂ΔJ|, sup|∂²ΔJ|)`, with targets `B₀, B₁ ≤ e/4` and `B₂ ≤ 10⁻⁹⁰`. SO-GEN must also recompute every sub-check margin on `K̃` independently of the scalar pilot. *(Revision 3, F9: the `J`-row identity and the G-J targets are corrected; see the Revision 3 table.)* | §6, §7 (gate G-J) |
| **F6** (MEDIUM) gating | Packages are split into a **pre-gate** set (backend-neutral interfaces, ℚ-only mathematics, structural semantics) and a **post-gate** set (backend instances, performance-sensitive algorithms, data), which waits for the SO-REPLAY verdict. SO-ARITH is split into SO-AIF (interface, pre-gate) and SO-ABK (backends, post-gate). SO-CONST and SO-PI are running pre-gate, and SO-CLOCK has **landed** (`inp` `092a9d11`). `phaseBasis` lives in the shared basic module `KAM/Certificate/PhaseBasis.lean` (landed), which `Expr/Diff`, `NormBridge` and `Clock` import. The line totals are recomputed. | §7 |
| **O1** momentum window | Kept: the headline initial region is the constant window `lunarPLo < p₀ < lunarPHi` (about `(0.9819, 1.0181)`), and graph-error transport is deferred. Literal rational endpoints replace the names before the freeze. | §6 |
| **O2** division | `HamExpr.div` and `SlpOp.inv` are added; `HamExpr.eval` uses `/`. `HamExpr.NonvanishingOn` (recursive, concrete) states that every denominator is nonzero on a set. Holomorphy is structural on open sets where it holds (`contDiffOn_eval`), and the jets need it (`jet_d1/d2/d3`). Periodicity and reality stay unconditional. Nonvanishing on `D` is **certified** by the new ℚ ball arithmetic `Slp.balls`, which fails on any `inv` whose operand ball contains `0` (`nonvanishingOn_of_balls`, part of `checkHamBounds`). Along `K`, a reciprocal **a-posteriori witness** (`invWitness_sound`, scalar Neumann series) certifies nonvanishing on the strip and encloses `1/b`, with no lower-bound data. The norm bridges take local `ContDiffAt`. | §1.1, §1.4, §1.7; A §C, §D, §E |
| **O3** SO-PI now | SO-PI (`KAM/Certificate/Arith/PiHigh.lean`, running, backend-independent) provides `piLoQ/piUpQ`, Machin `piLowRat/piUpRat` (width `≤ 10⁻¹⁴⁰`) and `eLowRat/eUpRat`. `PiEnclosure` carries its Machin parameters, and `checkPiEnclosure` validates the backend ball against them. `supBound` uses lower `π` bounds for negative degrees. `cRUpQ` uses `eLowRat`. | §1.6; A §A |
| **O4** analytic graphs | Kept out of the first freeze (later corollary). | §11 |

Further audit notes were adopted. `checkWeight` requires `0 < ρ` (positive width), and `checkStatic`
checks `weight.rho = params.rho`. The exp-witness radius formula is now explicit (A §C). The SOS check pays
its residual (`m ≤ m₀ − r`, with `m₀` as certificate data). The graph check requires a strict remaining
monotonicity margin `mono > disp/ρ∞`. `so_confinement` uses the global Lipschitz bound of `soField`, not
the lunar range. The upper-certificate companions (`lunarUpperCert_ham/_passes`, `lunarUpperGraph_passes`)
are stated. The `exp` halving fallback is the syntactic rewrite `exp a ↦ (exp (a/2))²` in the jet compiler
(`Complex.exp_add`) and needs no interface change. The client now imports the **real** SO-MODEL and SO-DIO
modules: `soHC`, `soField`, `soEpsQ`, `soAQ`, `KAM.Certificate.lunarNu*`. There are no stand-ins for them.

## 1. Decisions

1. **Expression language (`HamExpr n`).** The constructors are: rational constant, `π`, action coordinate
   `I_j`, period-one modes `cos(2π k·θ)` and `sin(2π k·θ)` (`k ∈ ℤⁿ`), `+`, `×`, **`/`** (O2), natural
   power, `exp`, `sin` and `cos`. Every constructor maps real points to reals, and angles enter only
   through integer modes. **Periodicity, translation invariance and reality are therefore structural and
   unconditional** (`eval_add_int`, `eval_real`; `x/0 = 0` keeps both true even off the certified set).
   **Holomorphy is structural on any open set where `NonvanishingOn` holds** (`contDiffOn_eval`). The
   checker certifies `NonvanishingOn D` by ball arithmetic on `D` (decision 4). Complex exponentials
   `e^{2πik·θ}` are internal to the straight-line program, not user syntax, so reality stays structural.
2. **Domain.** `D = T_{ρ_H} × Π_i {|I_i − c_i| < r_i}` (`certDomain`) with rational `ρ_H > 0`, centre `c`
   and radii `r`. It is open and translation invariant by construction. The checker certifies
   `ball(K θ, μ) ⊆ D` on `T_ρ` by `ρ + ι_i + μ ≤ ρ_H` and `sup|A_i − c_i| + μ ≤ r_i`, where
   `ι_i = min(sup|U_i|, ρ Σ_j sup|∂_j U_i|)`. The second form of `ι_i` is the mean value inequality from
   the real point, where `Im U_i = 0`.
3. **Norms.** These are exactly the existing API: max norms on `Fin n → ℂ` and on the product; operator
   norms of `fderiv` and `iteratedFDeriv`; the matrix row-sum norm via `open scoped Matrix.Norms.Operator`.
   New bridges (A §E) bound `‖DH‖`, `‖D²H‖`, `‖DX_H‖` and `‖D²X_H‖` by sums of partials along
   `phaseBasis a`, assuming **local** `ContDiffAt` (division). The two `X_H` bridges also take
   `1 ≤ n` (Revision 3, F8: at `n = 0` the row-sum premise is vacuous and a negative `B` would make
   them false); the checker supplies it from `2 ≤ n`.
4. **Derivatives: the checker differentiates symbolically.** The certificate carries no derivative data.
   `HamExpr` is compiled to a straight-line program (`Slp`) whose ops are const with `2π`-degree, action,
   character, add, mul, exp and **inv**. `HamExpr.jet` appends forward-mode derivative slots up to order 3
   (`(x⁻¹)' = −x⁻¹x⁻¹x'`). `jet_d1/d2/d3` hold at every point of an open set where `NonvanishingOn`
   holds. On `D`, all slots are evaluated by **ℚ ball arithmetic** (`Slp.balls`: centre and radius, with
   `exp` via `certCExp`). Balls replace Revision 1's majorants (majorant = `|centre| + radius`) and also
   certify every `inv` operand away from `0`. Cauchy-only bounds remain rejected (a factor of about 6 in
   `M`, about `6^{30}` in the constants). Derivatives of `K` are exact Fourier multipliers on its data
   (`CertModel.ofDeriv`). Implementation obligation (audit 2, Revision 3): constant folding and pruning
   in the jet compiler must preserve every denominator-validation slot that `NonvanishingOn` of the
   source expression needs (`0 * (1/0)` folded to `0`, or `.pow a 0` to `1`, keeps its `inv` operand in
   the ball pass), so a successful ball evaluation always certifies the syntactic expression.
5. **Enclosure semantics: Fourier models in the sup norm on the open strip.** A model `(deg, P, r)`
   denotes `(2π)^deg (P + T)`, where `P` is a finite polynomial and `sup_{T_ρ}|T| ≤ r`
   (`CertModel.Encloses`). Truncation and rounding move `|c_k| w^{|k|₁}` into `r`, where `w ≥ e^{2πρ}` is
   validated once by `checkWeight` (which requires `ρ > 0`).
6. **`2π`-degree tagging.** Model coefficients never contain `π`; the factor `(2π)^deg` is symbolic. Mixed
   degrees use `CertModel.toDeg` with a validated `PiEnclosure`. Validation is against SO-PI's Machin
   bounds at the certificate's parameters `(machinK, machinJ)`, so widths down to `10⁻¹⁴⁰` are available
   (O3). Upper bounds of `(2π)^deg` use `piUpQ` for `deg ≥ 0` and `piLoQ` for `deg < 0`. In the lunar
   problem every cancelling sum is degree-homogeneous (`angleDeg = −1`).
7. **Nonlinear composition: a-posteriori witnesses, not Taylor series.**
   - *`exp`:* the witness `E ≈ exp g₀`, where `g₀` is the degree-zero polynomial part. With `|g₀| ≤ B`, pin
     error `ε₀` and residuals `r_j ≥ sup|∂_jE − (∂_j g₀)E|`, the radius is
     `exp(2B)(ε₀ + Σ_j(1/2 + ρ)r_j) + exp(B)(exp η − 1)`, where `η` is the radius of `g`.
   - *Characters:* `χ_k∘K = χ_k · exp(2πi k·U)`, with witnesses keyed by the normalized index.
   - *Reciprocal (O2):* the witness `Q ≈ 1/(P + T)`. From `δ ≥ sup|1 − Q(P + T)|` and `δ < 1` it follows
     that `b ≠ 0` on `T_ρ` and `|1/(P + T) − Q| ≤ sup|Q| δ/(1 − δ)` (`invWitness_sound`). It needs one
     product and no lower-bound data.
   - *Halving fallback:* `exp a ↦ (exp(a/2))²`, a syntactic rewrite.
8. **Gram inverse on the complex strip (bilinear `DKᵀDK`).** This is unchanged. The certificate supplies a
   polynomial matrix `B(θ)`, and the checker certifies `δ = sup‖I − BG‖ < 1`, `β ≥ sup‖B‖` and
   `β/(1 − δ) ≤ σB − μ`. `gramCheck_sound` exports invertibility, the row-sum bound **and**
   `‖G⁻¹ − B‖ ≤ δβ/(1 − δ)`. The torsion models consume the last bound.
9. **Averaged bordered torsion (contract `torsionModels_sound`).** The entry models of the literal frozen
   `extendedTorsion H K (sω)` are built for every `ω` in the box:
   - the `torsion` block, from `DX_H∘K` (jet `d2` composed with `K`) and `N = Ω₀ DK B` with the radius
     from decision 8;
   - `DN[sω] = Ω₀(D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])` with `D(G⁻¹)[sω] = −G⁻¹(DG[sω])G⁻¹`
     (`KAM.fderiv_matrix_inv_apply`);
   - the border column `sω` (a ball from the box);
   - the last row `DH(K)N` (jet `d1` composed with `K`).

   The average is the zero mode ± radius. A constant witness `S` gives
   `δ_T = ‖I − SC‖ + ‖S‖‖R‖ < 1`. **(Revision 3, F7.)** `torsionAvgCheck n` first checks that `T`
   and `S` have exactly `n + 1` rows of length `n + 1` (`ModelMatrix.HasShape`), and
   `torsionModels_sound` exports that shape for the producer's output, so the certified inverse is the
   inverse of the whole `(n+1) × (n+1)` average and never of a larger matrix containing it.
10. **Frequencies (F1).** The certificate carries a rational box, and the theorem takes the exact
    `ωstar : Fin n → ℝ` with `FreqEncloses` and `IsDiophantine`. `ω* ≠ 0`, the ray margins
    `ν ≤ (s−1)‖ω*‖`, `ν ≤ (σω−s)‖ω*‖` and every `sω`-dependent model use only the box. The box fact is
    proved outside the checker by a provider:
    - `algFreq_encloses` with `checkRootEnclosure` for algebraic coordinates (lunar: `ℚ(√5)`; toy:
      `ℚ(∛2)`);
    - a user-specific lemma for any other exact vector.

    Box radii are `≤ 10⁻¹¹⁰` in the lunar certificates (rationals with large denominators).
11. **Constants.** `τ ∈ ℕ`. `cRUpQ` bounds `c_R` from `piLoQ` and `eLowRat`. The rational mirrors `isoC1Q`
    and `isoC2Q` dominate the real constants (SO-CONST, running).
12. **Trust boundary: the kernel only.** Sub-checks are `Bool` functions proved `= true` by
    `decide +kernel`. Never `native_decide`, `Lean.ofReduceBool`, axioms or `implemented_by`. Recursion is
    structural only, over `List`.
13. **Staging.** `checkTorusCertificate` is the conjunction of eight named sub-checks, each with its own
    soundness contract (A §G); data modules prove each `= true` separately. A check that would need a
    recursion-depth or heartbeat override is a design signal (rule 1), to be reported and never masked.
14. **Lunar headline (O1).** The barriers are continuous invariant graphs. The initial region is a
    constant momentum window `lunarPLo < p₀ < lunarPHi` (any `q₀, φ₀`), certified by SOS bounds of `p` on
    the two real tori plus the displacement bound.
15. **Certificates are pure data.** `TorusCertificate` contains no proof and no real number. Every real
    object (the exact `ω*`, the exact torus) enters only through the soundness theorem's binders.

## 2. Carriers and conventions

- Ambient types are `Fin n → ℝ` and `Fin n → ℂ`; indices are `Fin n → ℤ`. Phase points are
  `(Fin n → ℂ) × (Fin n → ℂ)` (angles first), and phase indices `Fin n ⊕ Fin n` follow
  `KAM.Torus.sumVec` order. Never `EuclideanSpace`.
- Keys are `CertKey = List ℤ`, denoted by `certKeyFun n` (missing entries are `0`). Lists may hold
  duplicate or padded keys; the exact sums handle these. Optimized algorithms validate and canonicalize
  key shapes before relying on them.
- **Denotations are law-free; correctness theorems carry `[LawfulCertArith α]`** (F2).
  - `CertPoly.eval` and `CertRealPoly.eval` are direct.
  - `CertRealPoly.toPoly` (computed, with `CC.conj`) agrees with the direct denotation under the laws
    (`eval_toPoly`), and its coefficients are conjugate symmetric (`conjugateSymmetric`).
  - `CertPoly.eval_eq_fourierSum` bridges to `KAM.fourierSum`.
- `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))`. It is primary, real and entire by construction,
  with law-free proofs.
- Parameters of `g1_explicit` are exact rationals in `CertParams`. The theorem's `ν` is `nuRay`.
- Backend numbers are `α` with `CertArith α` (data) and `LawfulCertArith α` (laws, proved once per
  backend); complex backend numbers are `CC α`. Ball arithmetic on `D` and frequency boxes are always
  in `ℚ`.

## 3. Reuse map and upstream interfaces

| Need | Existing declaration (reused, read-only) |
|---|---|
| sealed theorem | `KAM.Iso.Apost.g1_explicit`, body `KAM.Iso.Charts.IG1Body` |
| constants | `KAM.Iso.Apost.isoC1`, `isoC2`, `hatcStar`, `hatCDelta`; `KAM.Apost.cR`, `delta0`, `aExp` |
| characters, series | `KAM.character`, `fourierSum`, `norm_character_le`, `norm_fourierSum_le`, `torusAverage`, `torusAverage_character`, `differentiableOn_fourierSum` |
| reality | `Fourier.ConjugateSymmetric`, `fourierSum_im_eq_zero` |
| matrices | `KAM.norm_le_iff_forall_rowSum`, `matrix_neumann_uniform`, `fderiv_matrix_inv_apply`, `KAM.Torus.sumVec`, `colMat`, `sqMat`, `norm_colMat`, `norm_sqMat`, `Apost.tangentMat`, `norm_tangentMat` |
| Cauchy (graph) | `norm_coordinate_fderiv_le_of_mem_complexStrip`, `torusCoeff_fderiv_real`, `eq_zero_of_torusCoeff_eq_zero` |
| ODE | `KAM.ODE.IsSolutionIn`, `IsInvariantSet`, `gen_barrier`, `gen_uniqueness`, `gen_local`, `IsMaximalSolution`, `gen_continuation` |
| transcendental bounds | Mathlib `Real.exp_bound`, `Complex.exp_bound`; SO-PI `piLowRat_lt_pi`, `pi_lt_piUpRat`, `eLowRat_lt_exp_one` |

**Upstream interfaces (status at `inp` `ae496996`).**

| Owner | Name | Status / shape consumed |
|---|---|---|
| SO-MODEL | `KAM.SpinOrbit.soField`, `soHC`, `soV`, `soVC`, `soEpsQ`, `soAQ` | landed; imported (`soHamExpr_eval : soHamExpr.eval z = soHC z`) |
| SO-DIO | `KAM.Certificate.lunarNu{Minus,Plus}`, `_eq`, `_half_isDiophantine` | landed; imported (`IsDiophantine (1/42) 1 ![ν/2, 1/2]`) |
| SO-CLOCK | `KAM.Certificate.phaseBasis`, `clock_frequency` | landed (092a9d11), statement identical to A §H; stand-in in A only because the shared build predates it |
| SO-PI | `piLoQ`, `piUpQ`, `atanS`, `piLowRat`, `piUpRat`, `PiHighCert`, `eLowRat`, `eUpRat` | running (`inp-sopi` 779c9632); verbatim stand-in block in A §A |
| SO-CONST | `cRUpQ`, `isoC1Q`, `isoC2Q`, dominance theorems | running (no commits yet); A §F signatures |
| SO-GEN | Lean data emitter; budgets `B₀, B₁, B₂` (gate G-J) | in progress |
| SO-REPLAY | backend choice, shard sizes | prototype only; gate for post-gate packages |

SO-MODEL's `ScalarEmbedding` identities are not on the black-box path. They remain a generator tool:
the generator's `J₀` is exactly the scalar lift.

## 4. The black box: every hypothesis of `g1_explicit`

```
checkTorusCertificate_sound (h : checkTorusCertificate c = true) {ωstar}
  (hω : FreqEncloses n c.freqBox ωstar) (hdio : IsDiophantine γ τ ωstar) : CertifiedTorus c ωstar
```

applies

```
KAM.Iso.Apost.g1_explicit (n := n) hn (τ := (c.params.tau : ℝ)) hτ
  (ρ := c.params.rho) (ρinf := c.params.rhoInf) hρinf hρinfρ
  (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
  (μ := c.params.μ) (γbar := c.params.γbar) (σω := c.params.σω) (ν := c.params.nuRay)
  hM hσK hσB hσT hμ hγbar hσω hν ωstar hωstar
```

and feeds `.2.2.2` the arguments `(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.params.s, c.params.γ,
c.params.err, c.params.E0)` and the fields of `G1Hyps c ωstar`, in the frozen order. It then replaces
`isoC2 · e/(γ²ρ^{2τ})` by `disp` (`hdisp`). Audit 1 replayed this bridge for Revision 1 with no
placeholder in the bridge proof itself. Revision 2 changes only the provenance of `ωstar` (a binder
instead of a projection).

**Assembly route (acyclic).** Each `G1Hyps` field comes from exactly one contract:

| `G1Hyps` fields | contract | depends on |
|---|---|---|
| `hn hτ hρinf hρinfρ hM hσK hσB hσT hμ hγbar hσω hν hs1 hsσ hγ hγγbar he0` | `checkStatic_sound` (`StaticFacts`) | — |
| `hωstar hν1 hν2` | `checkStatic_freq` | Static, `hω` |
| `hK hKp hKr` | `TorusCertificate.emb_structural` (law-free) | — |
| `hbd`, plus `NonvanishingOn D` | `checkHamBounds_sound` (balls + jets + §E bridges) | Static (weights) |
| `hopen htransl hholo hper hreal` | `TorusCertificate.ham_structural` | `NonvanishingOn D` |
| `hball hDK` | `checkEmbedding_sound` | Static |
| `hG` | `checkGram_sound` (from `gramCheck_sound`) | Static |
| `hE` | `checkInvariance_sound` (`compose_sound`, `jet_d1` at `K θ ∈ D`, box) | Static, HamBounds, Embedding, `hω` |
| `hEn` | `checkEnergy_sound` (`Encloses.average`) | Static, HamBounds, Embedding |
| `hTu hTb` | `checkTorsion_sound` = `torsionModels_sound` + `torsionAvgCheck_sound` | Static, HamBounds, Embedding, Gram, `hω` |
| `hC1 hdisp` | `checkSmallness_sound` (SO-CONST dominance) | Static |

Notes on the table:
- `K θ ∈ D` follows from `hball` with `μ > 0`.
- The continuity premise of `torsionAvgCheck_sound` is the last conjunct of `torsionModels_sound`; its
  enclosure premise is the middle conjunct, at the same `n`; the exact shape (first conjunct, and
  `torsionAvgCheck_shape`) ties the checked list dimension to `n + 1` (Revision 3, F7).
- `checkHamBounds_sound` passes `1 ≤ n` (from `StaticFacts.hn`) to the two §E norm bridges (F8).
- `CertifiedTorus c ωstar` is the `IG1Body` conclusion verbatim, with `disp` as the closeness bound. It
  is never a hypothesis (rule 6). `hω` is a typing fact about the input vector, of the same kind as
  `hdio`, and is supplied by a provider.

## 5. Arithmetic layer and the replay gate

The checker is generic in `α` with `[CertArith α]`; soundness needs `[LawfulCertArith α]`. Two instances
are planned:
- `ℚ`: exact, with zero error terms; trivial, hence **pre-gate** in SO-AIF (`Arith/Rat.lean`), because the
  pre-gate ball arithmetic (SO-BALL) denotes its `CC ℚ` balls through it (Revision 3, F6);
- `CertFixed P`: floor rounding, with ulp errors carried in `mulErr`/`addErr`.

Data numbers are exact in both; only computed centres round. Ball arithmetic on `D`, frequency boxes,
root enclosures, `π` and `e` are always computed in `ℚ`, independently of the backend.

SO-REPLAY must report the following (decision rule unchanged from Revision 1):
1. Kernel time and memory of one product of two polynomials of the SO-GEN support at about 450-bit
   coefficients, for both backends (including `Nat.gcd` normalization for `ℚ`), and the recursion depth
   on lists of that length. Choose `ℚ` if a full stage replays in under about 1 h and 16 GB per torus and
   within 3× of fixed point.
2. For fixed point, the accumulated ulp radius after a stage, which must stay `< 10⁻¹¹⁰`.
3. The largest list one `decide +kernel` carries without a depth override (this sets the `List.all`
   split size).
4. The elaboration time of a 1500-line data shard.

Additions for Revision 2:
5. One reciprocal-witness check (one product), for a client with division.
6. One `checkPiEnclosure` at `(50, 15)`.

If nothing fits, the levers are those of the plan (sharper `n = 2`, `τ = 1` constants), never
overrides.

## 6. The lunar client

- **Hamiltonian.** `soHamExpr : HamExpr 2 = J + ½p² + Σ_{m=1}^{7}(−ε A_m) cos(2π(2q − mφ))`, angles
  `(q, φ)`, actions `(p, J)`. `soHamExpr_eval` bridges to the landed `soHC`, and `soHamExpr_clock` gives
  `∂_J 𝓗 ≡ 1`. The expression is division-free, so `NonvanishingOn` holds trivially.
- **Certificates.** Two certificates `lunar{Lower,Upper}Cert : SoGraphCert SoBackend`.
  - Parameters as the pilot: `n = 2`, `τ = 1`, `ρ = 1/200`, `ρ∞ = 1/400`, `μ = 1/1000`,
    `M = σK = σB = σT = 4`, `σω = 3`, `s = 2`, `γ = γbar = 1/42`, `E₀ = 0`, `e ≈ 1e−103`.
  - The box of `(ν±/2, 1/2)` has radius `≤ 10⁻¹¹⁰`. `lunar{Lower,Upper}Cert_freq` are proved from
    `lunarFreq{Minus,Plus}_eq` (the exact `ℚ(√5)` instance), `algFreq_encloses` and
    `sqrt_mem_of_checkRootEnclosure`.
  - `U = (v/2π, 0)` with `angleDeg = −1`; `A = (p, J̃)`.
- **Four-component candidate and budgets (F5).** `J̃ = J₀ + ΔJ` is finite Fourier data.
  - The checker re-evaluates every sub-check on `K̃ = (q, φ, p, J̃)`, so soundness uses no pilot identity.
  - Exactly, `H(K̃) − E₀ = ΔJ`. Since `𝓗` is affine in `J` with `∂_J 𝓗 ≡ 1` and its other partials do
    not depend on `J`, `X_H(K̃) = X_H(K₀)`, hence (Revision 3, F9, correcting Revision 2)
    `E(K̃) = E(K₀) − (0, 0, 0, D_{sω*}ΔJ)`, i.e. **`E(K̃)_J = E(K₀)_J − D_{sω*}ΔJ`**, and the
    `q, φ, p` rows of `E(K̃)` equal those of `E(K₀)`. Under the scalar pilot identities `E(K₀)_J = p r`,
    so `E(K̃)_J = p r − D_{sω*}ΔJ`; if the Fourier `q, φ, p` data no longer satisfy those identities,
    only the general difference formula and the actual full residual apply.
  - Feasibility gate **G-J** (SO-GEN, before SO-DATA), on `T_{1/200}`: report `B₀ = sup|ΔJ|`,
    `B₁ = sup|D_{sω*}ΔJ|`, `B₂ = max(sup|∂ΔJ|, sup|∂²ΔJ|)`, `B_r = sup|E(K₀)_J|` (`= sup|p r|` under the
    pilot identities), and `B_c`, a bound for every other candidate-replacement error (finite Fourier
    `q, φ, p` data versus the pilot's scalar embedding, coefficient rounding and truncation). Targets:
    `B_r + B₁ + B_c ≤ e/2`, the `q, φ, p` rows of `E(K₀)` plus `B_c` `≤ e/2`, `B₀ ≤ e/4` (energy),
    `B₂ ≤ 10⁻⁹⁰`. The Revision 2 target `B₁ ≤ e/4` alone did not account for `B_r` and is withdrawn.
    These are feasibility targets only: the checker recomputes the actual full residual of `K̃`.
  - SO-GEN must also report every sub-check margin on `K̃`, recomputed by its exact evaluator:
    invariance, energy, `DK`, ball, Gram `δ`, torsion `δ_T`, smallness `C₁e/(γ⁴ρ⁴) ≤ 1/2`, graph `mono`,
    and `p` range.

  These margins are recorded independently of the scalar pilot.
- **Clock** (`KAM.Certificate.clock_frequency`, landed): gives `s∞ = 2` and a constant `K∞,1 − θ₁` on
  reals.
- **Graph** (`soBarrier_of_cert`).
  - `∂_{θ₀}q ≥ mono₀ − r` on the candidate (paid SOS), transferred to the exact torus by Cauchy on
    `T_{ρ∞}` (error `≤ disp/ρ∞`). This requires `mono > disp/ρ∞`.
  - With the clock, the result is a continuous, doubly 1-periodic graph `P(q, φ)` with
    `pLo − disp ≤ P ≤ pHi + disp`.
  - Invariance follows from `gen_uniqueness`.
- **Barrier** (`so_confinement`). Two ordered invariant graphs bound an invariant open slab. Global
  existence comes from the global Lipschitz bound of `soField` (periodic bounded force, linear in `p`),
  not from a lunar range. Uniqueness comes from `gen_uniqueness`. Both time directions are covered.
- **Final theorems.** `lunar_barriers` and `lunar_spin_confinement`, as in Revision 1. `lunarPLo` and
  `lunarPHi` are replaced by literal rationals before the freeze (O1 approved).

## 7. Modules, import DAG and packages

All paths are new unless marked landed. Every file is < 1500 lines (target ≤ 800). `→` means "imports".

```
Certificate/PhaseBasis                         (landed, SO-CLOCK)  → Torus/Basic
Certificate/Clock                              (landed, SO-CLOCK)  → PhaseBasis, Frozen defs, Strip/*
Certificate/Arith/PiHigh                       (SO-PI, running)    → Mathlib only
Certificate/Arith/{Interface,PiEnclosure,Roots,Transcendental}     → Arith/PiHigh
Certificate/Arith/Rat                          (pre-gate, SO-AIF)  → Arith/Interface
Certificate/Arith/Fixed                        (post-gate)         → Arith/Interface
Certificate/Freq                               → Arith/Roots, Frozen/Defs/IsDiophantine
Certificate/CubicDiophantine                   → Freq
Certificate/Poly/Basic                         → Arith/Interface, Strip/FourierSeries
Certificate/Poly/Ops                           (post-gate)         → Poly/Basic
Certificate/Model/Basic                        → Poly/Basic, Arith/Transcendental, Strip/Averages
Certificate/Model/Ops                          (post-gate)         → Model/Basic, Poly/Ops, Arith/PiEnclosure
Certificate/Model/{Exp,Inv}                    (post-gate)         → Model/Ops
Certificate/Expr/Basic                         → PhaseBasis, Poly/Basic (CertKey)
Certificate/Expr/{Slp,Diff}                    → Expr/Basic, PhaseBasis
Certificate/Expr/Ball                          → Expr/Slp, Model/Basic (weights), Arith/{Rat,Transcendental}
Certificate/NormBridge                         → PhaseBasis, Frozen/Defs/HamiltonianVectorFieldC
Certificate/MatrixInv                          → Matrix/Neumann, Matrix/Inverse   (approx-inverse lemmas)
Certificate/Embedding                          (post-gate)         → Poly/*, Model/Ops
Certificate/Expr/Compose                       (post-gate)         → Expr/Slp, Model/{Exp,Inv}, Embedding
Certificate/Gram                               (post-gate)         → Model/Ops, MatrixInv, Embedding
Certificate/Torsion/{Frame,Models}             (post-gate)         → Gram, Expr/Compose, Freq, Frozen/Iso/Defs/*
Certificate/Constants                          (SO-CONST, running) → Iso/Apost/Defs, Arith/PiHigh
Certificate/Positivity                         (post-gate)         → Model/Ops
Certificate/Defs                               (post-gate)         → all of the above
Certificate/Sound/{Static,Ham,Embedding,Invariance,Energy,Gram,Torsion,Smallness} → Defs, NormBridge
Certificate/Soundness                          → Sound/*, Iso/Apost/G1
Certificate/Tests/{Toy2,Toy3,Rat,Negative}     → Soundness, CubicDiophantine, QuadraticDiophantine
SpinOrbit/{Model,PeriodOne,Hamiltonian,ScalarEmbedding}   (landed, SO-MODEL)
Certificate/QuadraticDiophantine                          (landed, SO-DIO)
SpinOrbit/HamExpr                              → Expr/Basic, SpinOrbit/Hamiltonian
SpinOrbit/Freq                                 → Freq, QuadraticDiophantine
SpinOrbit/Barrier                              → SpinOrbit/Model, ODE/*            (so_confinement, SoBarrier)
SpinOrbit/Graph/Inverse                        → Clock, Strip/*, SpinOrbit/Barrier (exact torus ⇒ graph)
SpinOrbit/Graph/Cert                           (post-gate)         → Soundness, Positivity, Graph/Inverse, HamExpr
SpinOrbit/Data/{Lower,Upper}/Part*             (post-gate, generated) → Defs
SpinOrbit/Lunar{Lower,Upper}Passes             → Data, Defs      (decide +kernel per sub-check)
SpinOrbit/LunarConfinement                     → all SpinOrbit
```

No module imports a provider or a frozen theorem anchor. `g1_explicit` lives in the implementation module
`KAM/Iso/Apost/G1`.

**Gate.** *Pre-gate* packages are backend-neutral or ℚ-only mathematics with no performance-sensitive
kernel algorithm. They may start as soon as they are briefed. *Post-gate* packages (backend instances,
polynomial/model algorithms, witnesses, composition, Gram/torsion construction, `Defs`, soundness of the
concrete checks, data) wait for the SO-REPLAY verdict (§5). Their algorithm choices (convolution strategy,
precision split, shard sizes) depend on it. SO-DATA additionally waits for gate **G-J** (§6).

| Package | Gate | Modules | Lines (est.) | Inputs |
|---|---|---|---|---|
| SO-CLOCK | landed | PhaseBasis, Clock | (400, done) | — |
| SO-PI | pre (running) | Arith/PiHigh | 500 | — |
| SO-CONST | pre (running) | Constants | 700 | SO-PI (`eLowRat`; or Mathlib bounds) |
| SO-AIF | pre | Arith/{Interface,PiEnclosure,Roots,Transcendental,Rat} | 700 | SO-PI |
| SO-FREQ | pre | Freq, SpinOrbit/Freq | 350 | SO-AIF |
| SO-DIO3 | pre | CubicDiophantine | 350 | SO-FREQ |
| SO-PBASE | pre | Poly/Basic, Model/Basic | 800 (A: Poly 400, B: Model 400) | SO-AIF |
| SO-EXPR | pre | Expr/{Basic,Slp,Diff} | 1700 (A: Basic+structural+`NonvanishingOn` 600; B1: Slp+`d1`/`d2` 550; B2: `d3` 550) | SO-PBASE (A) |
| SO-BALL | pre | Expr/Ball | 450 | SO-EXPR, SO-AIF (`Arith/Rat`) |
| SO-NORM | pre | NormBridge | 400 | — |
| SO-MINV | pre | MatrixInv | 300 | — |
| SO-HAMX | pre | SpinOrbit/HamExpr | 200 | SO-EXPR |
| SO-CONF | pre | SpinOrbit/Barrier | 600 | — |
| SO-GRAPHM | pre | SpinOrbit/Graph/Inverse | 600 | SO-CONF |
| SO-ABK | post | Arith/Fixed (and the production-backend choice) | 500 | SO-AIF, SO-REPLAY |
| SO-POLY | post | Poly/Ops | 650 | SO-PBASE, SO-ABK |
| SO-MALG | post | Model/Ops | 650 | SO-POLY |
| SO-EXPW | post | Model/{Exp,Inv} | 800 | SO-MALG |
| SO-EMB | post | Embedding, Expr/Compose | 800 | SO-EXPW, SO-EXPR |
| SO-MAT | post | Gram | 600 | SO-MALG, SO-EMB, SO-MINV |
| SO-TORS | post | Torsion/{Frame,Models} | 1000 (two packages) | SO-MAT, SO-EMB, SO-FREQ |
| SO-POS | post | Positivity | 350 | SO-MALG |
| SO-DEFS | post | Defs | 600 | all of the above |
| SO-SOUND | post | Sound/*, Soundness | 1400 (A: static/ham/emb/energy/small 700; B: inv/gram/torsion/G1 700) | SO-DEFS, SO-TORS, SO-NORM, SO-BALL |
| SO-TEST | post | Tests/{Toy2,Toy3,Rat,Negative} | 450 | SO-SOUND, SO-DIO3 |
| SO-GRAPH | post | SpinOrbit/Graph/Cert | 400 | SO-SOUND, SO-POS, SO-GRAPHM, SO-HAMX |
| SO-DATA | post + G-J | generator emitter + Data shards | generated | SO-GEN, SO-DEFS |
| SO-LUNAR | post | Lunar*Passes, LunarConfinement | 400 | all |

**Totals (recomputed, F6/feasibility note).**
- Pre-gate: 500 + 700 + 700 + 350 + 350 + 800 + 1700 + 450 + 400 + 300 + 200 + 600 + 600 = **7,650**
  (plus SO-CLOCK's landed 400).
- Post-gate: 500 + 650 + 650 + 800 + 800 + 600 + 1000 + 350 + 600 + 1400 + 450 + 400 + 400 = **8,600**. (Revision 3 moved 100 lines of `Arith/Rat` from SO-ABK to SO-AIF.)
- Hand-written total still to write: **16,250**. Adding SO-CLOCK (landed, 400) and the rest of wave 0
  (landed, about 1,500) gives about 18,150 in all.
- With a 30–40% overrun on the unwritten 16,250: 21.1k–22.8k new lines, about 23–24.7k overall, inside the
  plan's 21–37k. (This replaces Revision 1's "16–17k plus wave 0", which audit 1 found inconsistent with
  its own table.)

The estimate risks the audit names (third-order jets, fixed-point error accounting, the complex path
argument, torsion derivative models, graph inversion) are unchanged and carry the overrun.

## 8. Validation plan

- **Positive toys with the external premise discharged (F4, F1):**
  - **T2**: `H = J + p²/2`, `K = (θ, (ν̃, −ν̃²/2))`, rational `ν̃` with `|ν̃ − ν₋| ≤ 10^{−N}`, reference
    vector `(ν₋/2, 1/2)` (SO-DIO), `s = 2`, `err ≥ |ν̃ − ν₋|`, positive. Result: `toyCert2_torus`.
  - **T2d**: T2 with `H = J + (p²/2)·((3 + cos 2πq)/(3 + cos 2πq))`, which exercises `div`, balls and a
    reciprocal witness. Result: `toyCert2d_torus`.
  - **T3** (`n = 3`, `τ = 2`): `H = I₂ + I₀²/2 + I₁²/2`, `K = (θ, (a, b, −(a² + b²)/2))` with rational
    `a ≈ ∛2`, `b ≈ ∛4`, `ω* = cubicFreq` (`IsDiophantine (1/12) 2`, norm-form proof), positive residual.
    Result: `toyCert3_torus`.
  - `N` is fixed by `isoC1Q` at the toy's `(n, τ, ρ)`; SO-TEST computes it, and rationals of any size are
    cheap.
- **Checker-only test TR** (labelled: no Diophantine premise). Exact rational `ν = 1/2`, zero error,
  resonant vector `(1/4, 1/2)`. Only `toyRatCert_passes`.
- **Negative tests** (`checkTorusCertificate c = false` by `decide +kernel`, each failing in its intended
  sub-check):
  1. a false residual bound fails `checkInvariance`;
  2. Gram witness `B = 0` or `δ ≥ 1` fails `checkGram`, and an invalid torsion witness fails
     `checkTorsion`;
  3. `μ = 0` fails `checkStatic`;
  4. an exp witness with a wrong mean fails the pin;
  5. `w < e^{2πρ}` fails `checkWeight`;
  6. **(O2)** a division whose denominator ball contains `0` on `D` fails `checkHamBounds`, and a
     reciprocal witness with `δ ≥ 1` fails composition;
  7. **(F1)** a box that does not exclude `0`, or that violates a ray margin, fails `checkStatic`;
  8. **(O3)** a `PiEnclosure` narrower than the Machin bounds fails `checkPiEnclosure`;
  9. **(F7)** at `n = 1`, a torsion model matrix or witness `S` with `3` rows (or a row of length `≠ 2`),
     e.g. the audit's self-inverse `A = [1 0 0; 0 0 1; 0 1 0]`, fails `torsionAvgCheck 1` and hence
     `checkTorsion`, although `A` is a valid inverse pair with zero defect.
- **Axiom audit.** `#print axioms` of `checkTorusCertificate_sound`, every `*Passes` and `*_torus` theorem
  and the two lunar theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- **Cross-check.** SO-GEN's exact evaluator recomputes every sub-check margin from the same data (gate
  G-J).

## 9. Elaboration of Appendix A

Command (gated, `LEAN_NUM_THREADS=1`, one process):

```
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean
```

Result on Revision 3: **exit 0, 156 warnings, all `declaration uses 'sorry'`, no error** (Revision 2:
the same counts, 1337 lines). This establishes elaboration only. The file has 1360 lines, imports the real `KAM.SpinOrbit.{Model,
Hamiltonian}` and `KAM.Certificate.QuadraticDiophantine`, and keeps verbatim stand-ins only for SO-PI
(running) and for SO-CLOCK's `phaseBasis` and `clock_frequency`. SO-CLOCK has landed on `inp` but is not
yet in the shared build. The landed `clock_frequency` statement was compared and is identical.

## 10. Risks

| Risk | Signal | Response |
|---|---|---|
| Kernel replay too slow or too deep | SO-REPLAY; a stage needs an override | shard with `List.all`; fixed point; sharper `n = 2` constants (plan lever); never an override |
| Ball arithmetic on `D` exceeds `M = 4` | `checkHamBounds` margin | per-coordinate radii, smaller `ρ_H`; the pilot majorant 2.69 leaves room |
| Witness pin radius dominated by `e^{2B}` | `checkInvariance` margin | halving rewrite `exp a ↦ (exp(a/2))²` |
| `B_r + B₁ + B_c` exceeds `e/2` | gate G-J | raise the SO-GEN truncation threshold for `J̃`; `J̃` is cheap (no witness) |
| Gram/torsion witnesses weak | `δ`, `δ_T` near 1 | Fourier-model `B`; Newton-refined `B` from the generator |
| Toy T3 constants (`n = 3`, `τ = 2`) huge | `isoC1Q` | larger `N` (rational size only), larger `ρ` (the toy is entire) |
| Coarse balls for a division client | inv fails on `D` | smaller `D`, or split the denominator's constant part |
| Jet size for large `n` | elaboration/replay | order-3 slots only on `D`, never composed; pruning |

## 11. Owner rulings (2026-10-29, 11:10) and open points

- **O1** (constant momentum window): adopted (§6). Graph-error transport is deferred.
- **O2** (division in v1): adopted (§1.1, §1.4, §1.7, A §C/§D).
- **O3** (SO-PI now): adopted. The package is running; the interface is in A §A.
- **O4** (analytic graphs and conjugacy later): adopted. They are outside the first freeze.

There are no new open questions. One item remains for the freeze: the literal rational window endpoints
(from SO-GEN/SO-DATA).

## 12. Hard rules for every Lean brief (verbatim)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat
   elaboration failure is a design signal to refactor or split the proof, not something to mask with a
   larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused
   modules, preserving public import paths as cheap facades.

Also: never use the identifier `EuclideanSpace`. Never use `native_decide`, `Lean.ofReduceBool`, `axiom`,
`admit`, `unsafe`, `opaque` or `implemented_by`. Every file is a Lean module. Run one Lean process at a
time, through the compile gate.

## Appendix A. Exact signatures

The file `.drafts/design/SOSignatures.lean` (copy at `/root/code/KAM-inp/.drafts/design/`), verbatim:

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.G1
public import KAM.Strip.FourierSeries
public import KAM.Strip.Averages
public import KAM.Diophantine.SolverAlgebra
public import KAM.Matrix.Neumann
public import KAM.Matrix.Inverse
public import KAM.Torus.Basic
public import KAM.ODE.Exit
public import KAM.ODE.Maximal
public import KAM.SpinOrbit.Model
public import KAM.SpinOrbit.Hamiltonian
public import KAM.Certificate.QuadraticDiophantine

/-!
# SO-DESIGN Revision 3: exact draft signatures (track SO, lunar spin-orbit certificate project)

Design document: `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Appendix A is this file). Every proof
and every non-trivial definition body is `sorry`: this file only fixes the Lean surface. It is a
transient elaboration check against the shared `inp` build; it is never imported.

Sections mirror the planned modules (§7 of the design):

* §A `KAM/Certificate/Arith/{Interface,Transcendental,PiHigh,Roots}`: the late-bound arithmetic
  interface (laws separate from data; correctness theorems carry `[LawfulCertArith α]`), the
  backend-independent rational transcendental bounds, SO-PI (stand-in block), root enclosures.
* §B `KAM/Certificate/Poly/*`: exact finite Fourier data, law-free denotations.
* §C `KAM/Certificate/Model/*`: Fourier models; `exp` and reciprocal a-posteriori witnesses.
* §D `KAM/Certificate/{PhaseBasis,Expr/*}`: the expression language (with division, ruling O2),
  its straight-line program, jets, ball arithmetic on the domain, composition with `K`.
* §E `KAM/Certificate/NormBridge`: operator/multilinear norms on `ℂⁿ × ℂⁿ` from partials.
* §F `KAM/Certificate/{Embedding,MatrixCert,Gram,Torsion,Constants,Positivity}`.
* §G `KAM/Certificate/{Freq,Defs,Sound/*,Soundness}`: frequencies (exact real vector + proved
  rational box, finding F1), the certificate, the sub-check contracts, the black box.
* §H `KAM/Certificate/Clock`: the general clock lemma.
* §J `KAM/Certificate/{CubicDiophantine,Tests/*}`: the `n = 3` nonresonant example and toys.
* §I `KAM/SpinOrbit/*`: the lunar client, against the real SO-MODEL / SO-DIO modules.

Stand-ins (only so that this file elaborates against the shared `inp` build): `phaseBasis` and
`clock_frequency` (LANDED on `inp` at 092a9d11 as `KAM/Certificate/{PhaseBasis,Clock}.lean`, not
yet in the shared build) and the SO-PI block (running on `inp-sopi` as
`KAM/Certificate/Arith/PiHigh.lean`), copied with their exact statements.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus

/-! ## §A. Certified arithmetic interface (`KAM/Certificate/Arith/Interface.lean`) -/

/-- A certified arithmetic backend (data only). `val a` is the exact real denoted by `a`.
`add`/`mul` may round (fixed point) or be exact (`ℚ`); `addErr`/`mulErr` bound the rounding error.
`upAdd`/`upMul` round upward and are used on nonnegative radii only. Comparisons are one-sided
tests. Definitions over `CertArith` are computational and law-free; every correctness theorem that
uses a value of `ofInt`, `neg`, `add`, `mul` or a comparison assumes `[LawfulCertArith α]`
(finding F2). -/
class CertArith (α : Type) where
  val : α → ℝ
  ofInt : ℤ → α
  /-- outward conversions of an exact rational parameter -/
  ofRatUp : ℚ → α
  ofRatDown : ℚ → α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  abs : α → α
  addErr : α → α → α
  mulErr : α → α → α
  upAdd : α → α → α
  upMul : α → α → α
  ble : α → α → Bool
  blt : α → α → Bool
  beq : α → α → Bool

/-- Soundness of a backend (one `Prop`-valued class, proved once per backend). -/
class LawfulCertArith (α : Type) [CertArith α] : Prop where
  val_ofInt : ∀ z : ℤ, CertArith.val (CertArith.ofInt (α := α) z) = z
  ofRatUp_ge : ∀ q : ℚ, (q : ℝ) ≤ CertArith.val (CertArith.ofRatUp (α := α) q)
  ofRatDown_le : ∀ q : ℚ, CertArith.val (CertArith.ofRatDown (α := α) q) ≤ q
  add_err : ∀ a b : α, |CertArith.val (CertArith.add a b) - (CertArith.val a + CertArith.val b)| ≤
    CertArith.val (CertArith.addErr a b)
  val_neg : ∀ a : α, CertArith.val (CertArith.neg a) = -CertArith.val a
  mul_err : ∀ a b : α, |CertArith.val (CertArith.mul a b) - CertArith.val a * CertArith.val b| ≤
    CertArith.val (CertArith.mulErr a b)
  val_abs : ∀ a : α, CertArith.val (CertArith.abs a) = |CertArith.val a|
  upAdd_ge : ∀ a b : α, CertArith.val a + CertArith.val b ≤ CertArith.val (CertArith.upAdd a b)
  upMul_ge : ∀ a b : α, 0 ≤ CertArith.val a → 0 ≤ CertArith.val b →
    CertArith.val a * CertArith.val b ≤ CertArith.val (CertArith.upMul a b)
  ble_sound : ∀ a b : α, CertArith.ble a b = true → CertArith.val a ≤ CertArith.val b
  blt_sound : ∀ a b : α, CertArith.blt a b = true → CertArith.val a < CertArith.val b
  beq_sound : ∀ a b : α, CertArith.beq a b = true → CertArith.val a = CertArith.val b

open CertArith

/-- A complex backend number `re + i im` (exact data or a computed centre). -/
structure CC (α : Type) where
  re : α
  im : α

/-- The complex number denoted by a `CC` (law-free). -/
def CC.toC {α : Type} [CertArith α] (c : CC α) : ℂ := ⟨val c.re, val c.im⟩

/-- Exact conjugation of a backend complex number. -/
def CC.conj {α : Type} [CertArith α] (c : CC α) : CC α := ⟨c.re, neg c.im⟩

theorem CC.toC_conj {α : Type} [CertArith α] [LawfulCertArith α] (c : CC α) :
    c.conj.toC = (starRingEnd ℂ) c.toC := sorry

/-- The zero of a backend complex number (needs `val_ofInt`). -/
theorem CC.toC_zero {α : Type} [CertArith α] [LawfulCertArith α] :
    (⟨ofInt 0, ofInt 0⟩ : CC α).toC = 0 := sorry

/-! ### Backends (`KAM/Certificate/Arith/{Rat,Fixed}.lean`)

The exact rational instance is trivial (`val = cast`, zero errors) and is PRE-gate, in SO-AIF
(`Arith/Rat.lean`): the pre-gate ball arithmetic `Slp.balls` (SO-BALL) denotes `CC ℚ` through it
(audit 2, F6). Only the fixed-point backend and the choice of the production backend wait for
the SO-REPLAY verdict (SO-ABK). -/

/-- Backend 1: exact rationals (`addErr = mulErr = 0`; pre-gate, SO-AIF). -/
instance instCertArithRat : CertArith ℚ := sorry

instance instLawfulCertArithRat : LawfulCertArith ℚ := sorry

/-- Backend 2: fixed point, `m ↦ m / 2^P` with floor rounding and tracked ulp errors. -/
structure CertFixed (P : ℕ) where
  m : ℤ

instance instCertArithFixed (P : ℕ) : CertArith (CertFixed P) := sorry

instance instLawfulCertArithFixed (P : ℕ) : LawfulCertArith (CertFixed P) := sorry

/-! ### Transcendental constants (`KAM/Certificate/Arith/Transcendental.lean`, in `ℚ`) -/

/-- A kernel-computable upper bound for `exp q` (`q ≥ 0`): argument halving `s` times, Taylor
order `N`, Lagrange remainder, then `s` squarings, all in `ℚ`. -/
def ratExpUp (q : ℚ) (s N : ℕ) : ℚ := sorry

theorem exp_le_ratExpUp {q : ℚ} (hq : 0 ≤ q) (s N : ℕ) : Real.exp q ≤ ratExpUp q s N := sorry

/-! ### SO-PI (STAND-IN of `KAM/Certificate/Arith/PiHigh.lean`, `inp-sopi` 779c9632; ruling O3)

Backend-independent rational enclosures: coarse `piLoQ < π < piUpQ`; Machin
`piLowRat k j < π < piUpRat k j` (width `≤ 10^{-140}` at `(50, 15)`, kernel-checked); `e` by
Taylor. The backend wraps them into a `PiEnclosure` (`checkPiEnclosure`). -/

def piLoQ : ℚ := 3141592 / 1000000

def piUpQ : ℚ := 3141593 / 1000000

theorem piLoQ_lt_pi : (piLoQ : ℝ) < Real.pi := sorry

theorem pi_lt_piUpQ : Real.pi < piUpQ := sorry

/-- Partial sum `∑_{i<m} (-1)^i x^(2i+1)/(2i+1)` of the arctangent series. -/
def atanS (x : ℚ) (m : ℕ) : ℚ :=
  ∑ i ∈ Finset.range m, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))

def piLowRat (k j : ℕ) : ℚ := 16 * atanS (1 / 5) (2 * k) - 4 * atanS (1 / 239) (2 * j + 1)

def piUpRat (k j : ℕ) : ℚ := 16 * atanS (1 / 5) (2 * k + 1) - 4 * atanS (1 / 239) (2 * j)

theorem piLowRat_lt_pi (k j : ℕ) : (piLowRat k j : ℝ) < Real.pi := sorry

theorem pi_lt_piUpRat (k j : ℕ) : Real.pi < (piUpRat k j : ℝ) := sorry

/-- The hook for the arithmetic interface: rationals `lo < π < hi`. -/
structure PiHighCert where
  lo : ℚ
  hi : ℚ
  lo_lt : (lo : ℝ) < Real.pi
  lt_hi : Real.pi < (hi : ℝ)

def eSum (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, 1 / (m.factorial : ℚ)

def eRem (n : ℕ) : ℚ := ((n : ℚ) + 1) / ((n.factorial : ℚ) * n)

def eLowRat (n : ℕ) : ℚ := eSum n - 2 * eRem n

def eUpRat (n : ℕ) : ℚ := eSum n + 2 * eRem n

theorem eLowRat_lt_exp_one {n : ℕ} (hn : 0 < n) : (eLowRat n : ℝ) < Real.exp 1 := sorry

theorem exp_one_lt_eUpRat {n : ℕ} (hn : 0 < n) : Real.exp 1 < (eUpRat n : ℝ) := sorry

/-! ### `π` at backend precision (`KAM/Certificate/Arith/PiEnclosure.lean`) -/

/-- An enclosure `|π - centre| ≤ rad` at backend precision, with the Machin parameters
`(machinK, machinJ)` that validate it. Used when models of different `2π`-degrees are added
(`CertModel.toDeg`) and for lower bounds of `(2π)^deg`, `deg < 0`. Data only. -/
structure PiEnclosure (α : Type) where
  centre : α
  rad : α
  machinK : ℕ
  machinJ : ℕ

/-- Validation: `centre - rad ≤ piLowRat k j` and `piUpRat k j ≤ centre + rad` (outward
conversions `ofRatDown`/`ofRatUp`, backend comparisons). -/
def checkPiEnclosure {α : Type} [CertArith α] (pe : PiEnclosure α) : Bool := sorry

theorem checkPiEnclosure_sound {α : Type} [CertArith α] [LawfulCertArith α] {pe : PiEnclosure α}
    (h : checkPiEnclosure pe = true) : |Real.pi - val pe.centre| ≤ val pe.rad := sorry

/-! ### Root enclosures (`KAM/Certificate/Arith/Roots.lean`) -/

/-- `0 ≤ lo`, `lo^m ≤ d ≤ hi^m`, `0 ≤ hi`: encloses the real `m`-th root of `d`. -/
def checkRootEnclosure (m d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ lo) && decide (lo ^ m ≤ (d : ℚ)) && decide ((d : ℚ) ≤ hi ^ m) && decide (0 ≤ hi)

theorem rpow_mem_of_checkRootEnclosure {m d : ℕ} {lo hi : ℚ} (hm : 0 < m)
    (h : checkRootEnclosure m d lo hi = true) :
    (lo : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / m) ∧ (d : ℝ) ^ ((1 : ℝ) / m) ≤ hi := sorry

theorem sqrt_mem_of_checkRootEnclosure {d : ℕ} {lo hi : ℚ}
    (h : checkRootEnclosure 2 d lo hi = true) :
    (lo : ℝ) ≤ Real.sqrt d ∧ Real.sqrt d ≤ hi := sorry

/-- A certified scalar complex exponential ball (Taylor order `N`, `Complex.exp_bound`):
returns a centre and a radius. -/
def certCExp {α : Type} [CertArith α] (z : CC α) (zRad : α) (N : ℕ) : CC α × α := sorry

theorem certCExp_sound {α : Type} [CertArith α] [LawfulCertArith α] (z : CC α) (zRad : α)
    (N : ℕ) {w : ℂ} (hw : ‖w - z.toC‖ ≤ val zRad) :
    ‖Complex.exp w - (certCExp z zRad N).1.toC‖ ≤ val (certCExp z zRad N).2 := sorry

/-! ## §B. Exact finite Fourier data (`KAM/Certificate/Poly/Basic.lean`, `Poly/Ops.lean`) -/

/-- A Fourier index, stored as a list of length `n` (kernel-friendly lexicographic order). -/
abbrev CertKey : Type := List ℤ

/-- The index `Fin n → ℤ` denoted by a key (missing entries are `0`). -/
def certKeyFun (n : ℕ) (k : CertKey) : Fin n → ℤ := fun i => k.getD i.val 0

/-- A finite complex Fourier polynomial (duplicates allowed; optimized algorithms validate and
canonicalize key lengths and order before relying on them). -/
structure CertPoly (α : Type) where
  terms : List (CertKey × CC α)

/-- The denoted trigonometric polynomial `Σ c_k e^{2πi k·θ}` (law-free). -/
def CertPoly.eval {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) : ℂ :=
  (P.terms.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum

/-- Its coefficient family (sum over repeated keys; zero off the support). -/
def CertPoly.coeff {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α) (k : Fin n → ℤ) : ℂ :=
  ((P.terms.filter fun t => decide (certKeyFun n t.1 = k)).map fun t => t.2.toC).sum

/-- Bridge to the project's Fourier series (`KAM.fourierSum`). -/
theorem CertPoly.eval_eq_fourierSum {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α)
    (θ : Fin n → ℂ) : P.eval n θ = fourierSum (P.coeff n) θ := sorry

theorem CertPoly.differentiable_eval {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α) :
    Differentiable ℂ (P.eval n) := sorry

theorem CertPoly.eval_add_int {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α)
    (θ : Fin n → ℂ) (k : Fin n → ℤ) : P.eval n (θ + fun i => (k i : ℂ)) = P.eval n θ := sorry

/-- Real Fourier data on the half lattice: `a₀ + Σ_{(k, c) ∈ half} (c χ_k + c̄ χ_{-k})`. -/
structure CertRealPoly (α : Type) where
  zero : α
  half : List (CertKey × CC α)

/-- The denotation of real data, defined directly (law-free; no backend zero or conjugation). -/
def CertRealPoly.eval {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ) :
    ℂ :=
  (val P.zero : ℂ) + (P.half.map fun t => t.2.toC * character (certKeyFun n t.1) θ +
    (starRingEnd ℂ) t.2.toC * character (-certKeyFun n t.1) θ).sum

/-- Reality is structural and law-free: each pair is `2 Re (c χ_k)` on reals. -/
theorem CertRealPoly.eval_real {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α)
    (x : Fin n → ℝ) : (P.eval n fun i => (x i : ℂ)).im = 0 := sorry

theorem CertRealPoly.differentiable_eval {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α) :
    Differentiable ℂ (P.eval n) := sorry

theorem CertRealPoly.eval_add_int {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α)
    (θ : Fin n → ℂ) (k : Fin n → ℤ) : P.eval n (θ + fun i => (k i : ℂ)) = P.eval n θ := sorry

/-- The full polynomial: the zero term (imaginary part `ofInt 0`), each half term and its
conjugate at `-k` (`CC.conj`, `List.map Neg.neg` on keys). -/
def CertRealPoly.toPoly {α : Type} [CertArith α] (P : CertRealPoly α) : CertPoly α := sorry

/-- The explicit `toPoly` denotation (constant plus conjugate-pair sum); needs the laws. -/
theorem CertRealPoly.eval_toPoly {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (P : CertRealPoly α) (θ : Fin n → ℂ) : P.toPoly.eval n θ = P.eval n θ := sorry

theorem CertRealPoly.conjugateSymmetric {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (P : CertRealPoly α) : Fourier.ConjugateSymmetric (P.toPoly.coeff n) := sorry

/-- Exact addition by list concatenation (no rounding, law-free). Coefficient merging with
rounding is a model operation (`CertModel.add`), whose error is paid in the strip-weighted
radius; a global bound for all complex `θ` would be false for nonzero modes (audit 2). -/
def CertPoly.add {α : Type} (P Q : CertPoly α) : CertPoly α := ⟨P.terms ++ Q.terms⟩

theorem CertPoly.eval_add {α : Type} [CertArith α] (n : ℕ) (P Q : CertPoly α)
    (θ : Fin n → ℂ) : (P.add Q).eval n θ = P.eval n θ + Q.eval n θ := sorry

/-- Multiplication by the character `χ_m` (index shift; exact, law-free). -/
def CertPoly.shift {α : Type} [CertArith α] (m : CertKey) (P : CertPoly α) : CertPoly α := sorry

theorem CertPoly.eval_shift {α : Type} [CertArith α] (n : ℕ) (m : CertKey) (P : CertPoly α)
    (hm : m.length = n) (θ : Fin n → ℂ) :
    (P.shift m).eval n θ = character (certKeyFun n m) θ * P.eval n θ := sorry

/-- `P ↦ P*(θ) := conj (P (conj θ))`: coefficients `c_k ↦ conj c_{-k}` (exact; uses `neg`). -/
def CertPoly.conjReflect {α : Type} [CertArith α] (P : CertPoly α) : CertPoly α := sorry

theorem CertPoly.eval_conjReflect {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (P : CertPoly α) (θ : Fin n → ℂ) :
    P.conjReflect.eval n θ = (starRingEnd ℂ) (P.eval n fun i => (starRingEnd ℂ) (θ i)) := sorry

/-! ## §C. Fourier models (`KAM/Certificate/Model/Basic.lean`, `Ops.lean`, `Exp.lean`) -/

/-- A strip weight `w ≥ e^{2πρ}` (checked by `checkWeight`); `|χ_k| ≤ w^{|k|₁}` on `T_ρ`. -/
structure CertWeight where
  rho : ℚ
  w : ℚ

/-- `0 < ρ` (positive width: no vacuous strip feeds a real-point bound) and `e^{2πρ} ≤ w` via
`ratExpUp` and `piUpQ`. -/
def checkWeight (W : CertWeight) (s N : ℕ) : Bool :=
  decide (0 < W.rho) && decide (ratExpUp (2 * piUpQ * W.rho) s N ≤ W.w)

theorem norm_character_le_weight {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (k : Fin n → ℤ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖character k θ‖ ≤ (W.w : ℝ) ^ (∑ i, (k i).natAbs) := sorry

/-- A Fourier model: the function `(2π)^deg (P + T)` with `sup_{T_ρ} |T| ≤ rad`. -/
structure CertModel (α : Type) where
  deg : ℤ
  poly : CertPoly α
  rad : α

/-- `m` encloses `f` on the open strip `T_ρ` (sup norm, `2π`-degree factored out). -/
def CertModel.Encloses {α : Type} [CertArith α] (n : ℕ) (ρ : ℝ) (m : CertModel α)
    (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ θ ∈ complexStrip n ρ,
    ‖f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ‖ ≤ (2 * Real.pi) ^ m.deg * val m.rad

/-- A certified upper bound for `sup_{T_ρ} |f|` of an enclosed `f`: `Σ |c_k| w^{|k|₁} + rad`
times an upper bound of `(2π)^deg` (`piUpQ` if `deg ≥ 0`, `piLoQ` if `deg < 0`). -/
def CertModel.supBound {α : Type} [CertArith α] (W : CertWeight) (m : CertModel α) : α := sorry

theorem CertModel.norm_le_supBound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (hm : m.Encloses n W.rho f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : ‖f θ‖ ≤ val (m.supBound W) := sorry

/-- Truncation/precision controls for products. -/
structure ModelConfig where
  /-- keep only product terms with `|k|₁ ≤ cutoff` -/
  cutoff : ℕ
  /-- `exp` Taylor order and halvings for weights and pins -/
  taylorN : ℕ
  halvings : ℕ

def CertModel.add {α : Type} [CertArith α] (W : CertWeight) (a b : CertModel α) :
    CertModel α := sorry

def CertModel.mul {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig)
    (a b : CertModel α) : CertModel α := sorry

/-- Drop terms of weighted size `≤ eps` into the radius (precision reduction). -/
def CertModel.trim {α : Type} [CertArith α] (W : CertWeight) (eps : α) (a : CertModel α) :
    CertModel α := sorry

/-- Re-express a model at another `2π`-degree (validated `π` enclosure `pe`). -/
def CertModel.toDeg {α : Type} [CertArith α] (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (a : CertModel α) : CertModel α := sorry

/-- The model of `∂_j P` for exact data `P` at degree `d`: coefficients `i k_j c_k` (backend
products, their errors in the radius) at degree `d + 1`. -/
def CertModel.ofDeriv {α : Type} [CertArith α] (W : CertWeight) (j : ℕ) (d : ℤ)
    (P : CertPoly α) : CertModel α := sorry

theorem CertModel.Encloses.ofDeriv {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (j : Fin n) (d : ℤ)
    (P : CertPoly α) : (CertModel.ofDeriv W j.val d P).Encloses n W.rho
      (fun θ => (2 * (Real.pi : ℂ)) ^ d * fderiv ℂ (P.eval n) θ (Pi.single j 1)) := sorry

theorem CertModel.Encloses.add {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {a b : CertModel α}
    {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) (hb : b.Encloses n W.rho g)
    (hdeg : a.deg = b.deg) : (CertModel.add W a b).Encloses n W.rho (f + g) := sorry

theorem CertModel.Encloses.mul {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {a b : CertModel α} {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f)
    (hb : b.Encloses n W.rho g) : (CertModel.mul W cfg a b).Encloses n W.rho (f * g) := sorry

theorem CertModel.Encloses.trim {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (eps : α) {a : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) :
    (CertModel.trim W eps a).Encloses n W.rho f := sorry

theorem CertModel.Encloses.toDeg {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (d : ℤ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (ha : a.Encloses n W.rho f) : (CertModel.toDeg W pe d a).Encloses n W.rho f := sorry

/-- The real-torus average of an enclosed function is the zero coefficient up to the radius. -/
theorem CertModel.Encloses.average {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n ρ f)
    (hf : ContinuousOn f (complexStrip n ρ)) :
    ‖torusAverage (fun x : Fin n → ℝ => f fun i => (x i : ℂ)) -
        (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.coeff n 0‖ ≤ (2 * Real.pi) ^ a.deg * val a.rad :=
  sorry

/-! ### A-posteriori witnesses (`KAM/Certificate/Model/{Exp,Inv}.lean`)

`exp`: the witness `E ≈ exp g₀` for the degree-zero POLYNOMIAL part `g₀` of `g` (exact
derivative). With `|g₀| ≤ B`, pin error `ε₀ = |E(0) - exp g₀(0)|` (`certCExp`) and residual bounds
`r_j ≥ sup |∂_j E - (∂_j g₀) E|`, the certified radius is
`exp(2B) (ε₀ + Σ_j (1/2 + ρ) r_j) + exp(B) (exp(η) - 1)`, `η` the radius of `g`.
Reciprocal (ruling O2): the witness `Q ≈ 1/b` for a model `b = (2π)^d (P + T)`; with
`δ ≥ sup |1 - Q (P + T)|` (one product) and `δ < 1`, `b` has no zero on `T_ρ` and
`|1/(P + T) - Q| ≤ sup|Q| δ/(1 - δ)` (scalar Neumann series); no lower bound is assumed. -/

/-- The radius certified for `exp g` by the witness `E` (or `none` if a check fails). -/
def expWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig)
    (g : CertModel α) (E : CertPoly α) : Option α := sorry

theorem expWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {E : CertPoly α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    (⟨0, E, r⟩ : CertModel α).Encloses n W.rho (fun θ => Complex.exp (gf θ)) := sorry

/-- The radius certified for `1/b` by the witness `Q` (or `none` if `δ < 1` fails). -/
def invWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig)
    (b : CertModel α) (Q : CertPoly α) : Option α := sorry

theorem invWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {b : CertModel α} {bf : (Fin n → ℂ) → ℂ} (hb : b.Encloses n W.rho bf)
    {Q : CertPoly α} {r : α} (hQ : invWitnessRadius n W cfg b Q = some r) :
    (∀ θ ∈ complexStrip n W.rho, bf θ ≠ 0) ∧
      (⟨-b.deg, Q, r⟩ : CertModel α).Encloses n W.rho (fun θ => (bf θ)⁻¹) := sorry

/-! ## §D. The Hamiltonian language (`KAM/Certificate/{PhaseBasis,Expr/*}`) -/

/-- STAND-IN of `KAM/Certificate/PhaseBasis.lean` (SO-CLOCK, landed on `inp` 092a9d11): the phase
index `Fin n ⊕ Fin n` (angles `inl`, actions `inr`) and its basis vector. Imported by
`Expr/Diff`, `NormBridge` and `Clock` (finding F6). -/
def phaseBasis {n : ℕ} (a : Fin n ⊕ Fin n) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (sumVec n).symm (Pi.single a 1)

/-- Hamiltonians as finite expressions. Angles enter only through the period-one modes
`cos (2π k·θ)`, `sin (2π k·θ)`; every constructor maps reals to reals, so reality, periodicity
and translation invariance are structural and unconditional. Division (ruling O2) is by an
expression certified nonvanishing on the domain (`NonvanishingOn`, established by the ball
arithmetic of `checkHamBounds`); holomorphy is structural under that condition. -/
inductive HamExpr (n : ℕ) : Type
  | const (q : ℚ)
  | pi
  | action (j : Fin n)
  | cosMode (k : CertKey)
  | sinMode (k : CertKey)
  | add (a b : HamExpr n)
  | mul (a b : HamExpr n)
  | div (a b : HamExpr n)
  | pow (a : HamExpr n) (m : ℕ)
  | exp (a : HamExpr n)
  | sin (a : HamExpr n)
  | cos (a : HamExpr n)

/-- `2π k·θ`. -/
def modePhase (n : ℕ) (k : CertKey) (θ : Fin n → ℂ) : ℂ :=
  2 * Real.pi * ∑ i, (certKeyFun n k i : ℂ) * θ i

/-- The function denoted by an expression (division is Lean's `/`; it is only ever used where
the denominator is certified nonvanishing). -/
def HamExpr.eval {n : ℕ} : HamExpr n → (Fin n → ℂ) × (Fin n → ℂ) → ℂ
  | .const q, _ => (q : ℂ)
  | .pi, _ => (Real.pi : ℂ)
  | .action j, z => z.2 j
  | .cosMode k, z => Complex.cos (modePhase n k z.1)
  | .sinMode k, z => Complex.sin (modePhase n k z.1)
  | .add a b, z => a.eval z + b.eval z
  | .mul a b, z => a.eval z * b.eval z
  | .div a b, z => a.eval z / b.eval z
  | .pow a m, z => a.eval z ^ m
  | .exp a, z => Complex.exp (a.eval z)
  | .sin a, z => Complex.sin (a.eval z)
  | .cos a, z => Complex.cos (a.eval z)

/-- Every denominator of `e` is nonzero at every point of `S`. -/
def HamExpr.NonvanishingOn {n : ℕ} : HamExpr n → Set ((Fin n → ℂ) × (Fin n → ℂ)) → Prop
  | .add a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S
  | .mul a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S
  | .div a b, S => a.NonvanishingOn S ∧ b.NonvanishingOn S ∧ ∀ z ∈ S, b.eval z ≠ 0
  | .pow a _, S => a.NonvanishingOn S
  | .exp a, S => a.NonvanishingOn S
  | .sin a, S => a.NonvanishingOn S
  | .cos a, S => a.NonvanishingOn S
  | _, _ => True

theorem HamExpr.contDiffOn_eval {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (h : e.NonvanishingOn S) : ContDiffOn ℂ ⊤ e.eval S := sorry

theorem HamExpr.eval_add_int {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (k : Fin n → ℤ) : e.eval (z.1 + (fun i => (k i : ℂ)), z.2) = e.eval z := sorry

theorem HamExpr.eval_real {n : ℕ} (e : HamExpr n) (θ I : Fin n → ℝ) :
    (e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := sorry

/-- Straight-line program over `ℂ` (internal). Operands are earlier slot numbers; a constant
carries its `2π`-degree; `char k` is `e^{2πi k·θ}`. Nonlinearities: `exp` and `inv` (`x⁻¹`). -/
inductive SlpOp : Type
  | const (re im : ℚ) (deg : ℤ)
  | action (j : ℕ)
  | char (k : CertKey)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | exp (a : ℕ)
  | inv (a : ℕ)

structure Slp where
  ops : List SlpOp

/-- Value of slot `i` at the phase point `z` (out-of-range operands read `0`; `inv` is `x⁻¹`). -/
def Slp.val (n : ℕ) (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) (i : ℕ) : ℂ := sorry

/-- The program and slot tables of the jet of order three of an expression: slot of `H`,
of `∂_a H`, `∂_a ∂_b H`, `∂_a ∂_b ∂_c H` (`a, b, c` phase indices in `sumVec` order).
Forward-mode differentiation with sharing, zero/constant folding and dependency pruning;
`(x⁻¹)' = -x⁻¹ · x⁻¹ · x'`. -/
structure HamJet where
  prog : Slp
  v0 : ℕ
  d1 : List ℕ
  d2 : List (List ℕ)
  d3 : List (List (List ℕ))

/-- Phase index as a natural number: `inl j ↦ j`, `inr j ↦ n + j`. -/
def phaseNat {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | .inl j => j.val
  | .inr j => n + j.val

def HamExpr.jet {n : ℕ} (e : HamExpr n) : HamJet := sorry

theorem HamExpr.jet_v0 {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    e.jet.prog.val n z e.jet.v0 = e.eval z := sorry

theorem HamExpr.jet_d1 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a : Fin n ⊕ Fin n) :
    e.jet.prog.val n z (e.jet.d1.getD (phaseNat a) 0) = fderiv ℂ e.eval z (phaseBasis a) :=
  sorry

theorem HamExpr.jet_d2 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b : Fin n ⊕ Fin n) :
    e.jet.prog.val n z ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      iteratedFDeriv ℂ 2 e.eval z ![phaseBasis a, phaseBasis b] := sorry

theorem HamExpr.jet_d3 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b c : Fin n ⊕ Fin n) :
    e.jet.prog.val n z
        (((e.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0) =
      iteratedFDeriv ℂ 3 e.eval z ![phaseBasis a, phaseBasis b, phaseBasis c] := sorry

/-- The Hamiltonian domain `D = T_{ρ_H} × Π_i {|I_i - c_i| < r_i}`. -/
def certDomain (n : ℕ) (rhoH : ℚ) (centre radius : List ℚ) :
    Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {z | z.1 ∈ complexStrip n rhoH ∧
    ∀ i : Fin n, ‖z.2 i - ((centre.getD i.val 0 : ℚ) : ℂ)‖ < (radius.getD i.val 0 : ℚ)}

theorem isOpen_certDomain (n : ℕ) (rhoH : ℚ) (centre radius : List ℚ) :
    IsOpen (certDomain n rhoH centre radius) := sorry

theorem certDomain_add_int {n : ℕ} {rhoH : ℚ} {centre radius : List ℚ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n rhoH centre radius)
    (k : Fin n → ℤ) : (z.1 + (fun i => (k i : ℂ)), z.2) ∈ certDomain n rhoH centre radius :=
  sorry

/-- Ball arithmetic of every slot on `D` (no embedding), in `ℚ`: `(centre, radius)` with
`|slot - centre| ≤ radius` on `D`. Constants exact; actions `(c_j, r_j)`; characters
`(0, w_H^{|k|₁})` (`k ≠ 0`); sums and products; `exp` via `certCExp`; `inv` fails (`none`) unless
the operand ball excludes `0`, i.e. `radius < max(|re|, |im|)` of its centre (O2). -/
def Slp.balls (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    Option (List (CC ℚ × ℚ)) := sorry

theorem Slp.val_mem_ball {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ)
    (hi : i < bs.length) :
    ‖p.val n z i - (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 := sorry

/-- Successful ball arithmetic on the jet program certifies every denominator on `D`. -/
theorem HamExpr.nonvanishingOn_of_balls {n : ℕ} (e : HamExpr n) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : e.jet.prog.balls n WH centre radius taylorN = some bs) :
    e.NonvanishingOn (certDomain n WH.rho centre radius) := sorry

/-- The embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` from real Fourier data;
a missing component denotes `0` (no backend default value is used, finding F2). -/
structure CertEmbedding (α : Type) where
  angleDeg : List ℤ
  angle : List (CertRealPoly α)
  actionDeg : List ℤ
  action : List (CertRealPoly α)

def CertEmbedding.eval {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => θ i + (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
      ((K.angle[i.val]?.map fun P => P.eval n θ).getD 0),
    fun i => (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
      ((K.action[i.val]?.map fun P => P.eval n θ).getD 0))

theorem CertEmbedding.differentiable_eval {α : Type} [CertArith α] (n : ℕ)
    (K : CertEmbedding α) : Differentiable ℂ (K.eval n) := sorry

theorem CertEmbedding.isPrimaryOnStrip {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (ρ : ℝ) : IsPrimaryOnStrip (K.eval n) ρ := sorry

/-- Law-free (finding F2): `CertRealPoly.eval_real` and the `0` default. -/
theorem CertEmbedding.isRealOnReals {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) :
    IsRealOnReals (K.eval n) := sorry

/-- Witnesses: one per `exp` slot and one per `inv` slot of the jet program (slot order), and
the character table keyed by the normalized index (coordinates with syntactically zero `U_j`
zeroed; `-k` uses `conjReflect`). -/
structure Witnesses (α : Type) where
  expWit : List (CertPoly α)
  invWit : List (CertPoly α)
  charWit : List (CertKey × CertPoly α)

/-- Composition of the jet slots with `K`: one model per requested slot, or `none` if a witness
check fails. -/
def Slp.compose {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) := sorry

/-- Unconditional in the domain: reciprocal witnesses certify their own nonvanishing. -/
theorem Slp.compose_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (p : Slp)
    (K : CertEmbedding α) (wit : Witnesses α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (wanted : List ℕ) {ms : List (CertModel α)}
    (h : Slp.compose n p K wit W cfg pe wanted = some ms) :
    ms.length = wanted.length ∧ ∀ idx (hidx : idx < ms.length), ms[idx].Encloses n W.rho
      (fun θ => p.val n (K.eval n θ) (wanted.getD idx 0)) := sorry

/-! ## §E. Norms on `ℂⁿ × ℂⁿ` from partial derivatives (`KAM/Certificate/NormBridge.lean`) -/

theorem norm_fderiv_le_sum_partials {n : ℕ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖fderiv ℂ f z‖ ≤ ∑ a : Fin n ⊕ Fin n, ‖fderiv ℂ f z (phaseBasis a)‖ := sorry

theorem norm_iteratedFDeriv_two_le_sum_partials {n : ℕ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖iteratedFDeriv ℂ 2 f z‖ ≤
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
        ‖iteratedFDeriv ℂ 2 f z ![phaseBasis a, phaseBasis b]‖ := sorry

/-- `X_H` in partials: `(X_H)_{inl i} = ∂_{inr i} H`, `(X_H)_{inr i} = -∂_{inl i} H`. -/
theorem hamiltonianVectorFieldℂ_sumVec {n : ℕ} (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) a =
      Sum.elim (fun i => fderiv ℂ H z (phaseBasis (.inr i)))
        (fun i => -fderiv ℂ H z (phaseBasis (.inl i))) a := sorry

/-- Row-sum bound for `DX_H` from second partials; local `C²` (division, O2). `1 ≤ n` makes the
row-sum premise nonvacuous, hence `0 ≤ B` (at `n = 0` the statement fails for `B < 0`, audit 2
F8); the checker derives it from `StaticFacts.hn : 2 ≤ n`. -/
theorem norm_fderiv_hamiltonianVectorFieldℂ_le {n : ℕ} (hn : 1 ≤ n)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 2 H z) {B : ℝ}
    (hB : ∀ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
      ‖iteratedFDeriv ℂ 2 H z ![phaseBasis (Sum.swap a), phaseBasis b]‖ ≤ B) :
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ B := sorry

/-- Bound for `D²X_H` from third partials; local `C³`; `1 ≤ n` as above (F8). -/
theorem norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le {n : ℕ} (hn : 1 ≤ n)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 3 H z)
    {B : ℝ} (hB : ∀ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ c : Fin n ⊕ Fin n,
      ‖iteratedFDeriv ℂ 3 H z ![phaseBasis (Sum.swap a), phaseBasis b, phaseBasis c]‖ ≤ B) :
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ B := sorry

/-! ## §F. Matrix certificates, Gram, torsion, constants, positivity -/

/-- Pointwise approximate-inverse certificate: `‖I - B A‖ ≤ δ < 1` gives `A` invertible and
`‖A⁻¹‖ ≤ ‖B‖/(1-δ)`, `‖A⁻¹ - B‖ ≤ δ‖B‖/(1-δ)` (row-sum norm; no symmetry used). -/
theorem matrix_inv_of_approx_inverse {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A B : Matrix ι ι ℂ} {δ β : ℝ} (hδ : ‖1 - B * A‖ ≤ δ) (hδ1 : δ < 1) (hB : ‖B‖ ≤ β) :
    IsUnit A.det ∧ ‖A⁻¹‖ ≤ β / (1 - δ) ∧ ‖A⁻¹ - B‖ ≤ δ * β / (1 - δ) := sorry

/-- A matrix of models (row-major), e.g. the Gram matrix or its approximate inverse. -/
abbrev ModelMatrix (α : Type) : Type := List (List (CertModel α))

/-- Entrywise enclosure of a matrix-valued function on `T_ρ`; every entry must be present (no
backend default model, finding F2). -/
def ModelMatrix.Encloses {α : Type} [CertArith α] (n : ℕ) {ι : Type*} (idx : ι → ℕ) (ρ : ℝ)
    (M : ModelMatrix α) (F : (Fin n → ℂ) → Matrix ι ι ℂ) : Prop :=
  ∀ i j, ∃ m : CertModel α, (M[idx i]?.bind fun r => r[idx j]?) = some m ∧
    m.Encloses n ρ (fun θ => F θ i j)

/-- Exact shape of a list matrix: `k` rows, each of length `k` (audit 2 F7). With
`ModelMatrix.Encloses n (torsionIdx n)` and `k = n + 1`, the checked list matrix is then the
whole denoted bordered matrix, not a larger matrix containing it as a leading block. -/
def ModelMatrix.HasShape {β : Type} (k : ℕ) (M : List (List β)) : Prop :=
  M.length = k ∧ ∀ r ∈ M, r.length = k

/-- The matrix of a polynomial-matrix witness (missing entries `0`). -/
def polyMatrix {α : Type} [CertArith α] (n : ℕ) (B : List (List (CertPoly α))) (θ : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((B[i.val]?).bind fun r => r[j.val]?).map fun P => P.eval n θ).getD 0

/-- The Gram models `DKᵀ DK` (bilinear, `dotℂ`), computed at reduced precision. -/
def gramModels {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (W : CertWeight)
    (cfg : ModelConfig) (pe : PiEnclosure α) : ModelMatrix α := sorry

theorem gramModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    (K : CertEmbedding α) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) :
    (gramModels n K W cfg pe).Encloses n (fun i : Fin n => i.val) W.rho
      (gramMatrix (K.eval n)) := sorry

/-- Gram check: with the witness `B ≈ G⁻¹`, `sup_{T_ρ}` row sums of `I - B G` give `δ < 1`,
`β ≥ sup ‖B‖`, and `β/(1 - δ) ≤ σB - μ`. Returns the certified `(δ, β)`. -/
def gramCheck {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List
    (CertPoly α))) (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α) (σBμ : ℚ) :
    Option (α × α) := sorry

theorem gramCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    (K : CertEmbedding α) (Binv : List (List (CertPoly α))) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (σBμ : ℚ) {δβ : α × α}
    (h : gramCheck n K Binv W cfg pe σBμ = some δβ) :
    val δβ.1 < 1 ∧ ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det ∧
      (∀ i, ∑ j, ‖(gramMatrix (K.eval n) θ)⁻¹ i j‖ ≤ σBμ) ∧
      ‖(gramMatrix (K.eval n) θ)⁻¹ - polyMatrix n Binv θ‖ ≤
        val δβ.1 * val δβ.2 / (1 - val δβ.1) := sorry

/-- Row/column index of the bordered torsion: `inl i ↦ i`, `inr () ↦ n`. -/
def torsionIdx (n : ℕ) : Fin n ⊕ Unit → ℕ := Sum.elim (fun i => i.val) (fun _ => n)

/-- A rational frequency box: per coordinate `(centre, radius)`; it encloses `ω` when
`|ω_i - centre_i| ≤ radius_i` for every `i` (`FreqEncloses`). -/
abbrev FreqBox : Type := List (ℚ × ℚ)

def FreqEncloses (n : ℕ) (box : FreqBox) (ω : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, |ω i - ((box.getD i.val (0, 0)).1 : ℝ)| ≤ ((box.getD i.val (0, 0)).2 : ℝ)

/-- Entrywise models of `extendedTorsion H K (s ω)` on `T_ρ` for EVERY `ω` in the box: the block
`torsion` from `DX_H ∘ K` (jet `d2` composed with `K`), the normal frame `N = Ω₀ DK B` with the
Gram witness `B` and the certified radius `δβ/(1 - δ)`, `DN[sω] = Ω₀ (D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])`
with `D(G⁻¹)[sω] = -G⁻¹ (DG[sω]) G⁻¹`; the border column `s ω` from the box (ball); the last row
`DH(K) N` (jet `d1` composed with `K`). -/
def torsionModels {α : Type} [CertArith α] (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (δβ : α × α) (box : FreqBox) (s : ℚ)
    (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α) : Option (ModelMatrix α) :=
  sorry

/-- **Torsion producer contract (finding F3).** Validated weight and `π`, a successful Gram
certificate (its `(δ, β)` passed on), successful construction, a frequency in the box, and `K`
mapping the strip into an open set where `e` has no vanishing denominator give the enclosure
of the LITERAL frozen `extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)`, and its continuity. -/
theorem torsionModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (cfg : ModelConfig)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {σBμ : ℚ} {δβ : α × α}
    (hG : gramCheck n K Binv W cfg pe σBμ = some δβ) (box : FreqBox) (s : ℚ)
    {T : ModelMatrix α} (hT : torsionModels n e K wit Binv δβ box s W cfg pe = some T)
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) :
    ModelMatrix.HasShape (n + 1) T ∧ T.Encloses n (torsionIdx n) W.rho
        (KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)) ∧
      ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ a b)
        (complexStrip n W.rho) := sorry

/-- The averaged bordered torsion check at dimension `n` (audit 2 F7). It FIRST checks the exact
shapes `HasShape (n + 1) T` and `HasShape (n + 1) S` (decidable list-length tests) and rejects
otherwise; then centre `C` = zero modes, radius matrix `R`; with the constant witness `S`,
`‖I - S C‖ + ‖S‖ ‖R‖ =: δ_T < 1` and `‖S‖/(1-δ_T) ≤ σT - μ`, all on `(n+1) × (n+1)` arrays. -/
def torsionAvgCheck {α : Type} [CertArith α] (n : ℕ) (T : ModelMatrix α)
    (S : List (List (CC α))) (σTμ : ℚ) : Bool := sorry

/-- A passing averaging check has exact `(n+1) × (n+1)` inputs (law-free; F7 negative tests). -/
theorem torsionAvgCheck_shape {α : Type} [CertArith α] {n : ℕ} {T : ModelMatrix α}
    {S : List (List (CC α))} {σTμ : ℚ} (h : torsionAvgCheck n T S σTμ = true) :
    ModelMatrix.HasShape (n + 1) T ∧ ModelMatrix.HasShape (n + 1) S := sorry

theorem torsionAvgCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {T : ModelMatrix α}
    (hT : T.Encloses n (torsionIdx n) ρ (KAM.Iso.extendedTorsion H K ω))
    (hcont : ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion H K ω θ a b)
      (complexStrip n ρ))
    (S : List (List (CC α))) (σTμ : ℚ) (h : torsionAvgCheck n T S σTμ = true) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K ω).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K ω)⁻¹ i j‖ ≤ σTμ := sorry

/-- A kernel-computable upper bound for `c_R = max 1 (cohConst n τ)` (`piLoQ`, `eLowRat`). -/
def cRUpQ (n τ : ℕ) : ℚ := sorry

theorem cR_le_cRUpQ (n τ : ℕ) : KAM.Apost.cR n τ ≤ cRUpQ n τ := sorry

/-- Rational mirrors of `isoC1`, `isoC2` (`τ ∈ ℕ`, `c_R` replaced by `cRUpQ`); the real
constants are monotone in `c_R` and the rational ones dominate them. -/
def isoC1Q (n τ : ℕ) (ρ ρinf M σK σB σT μ ν γbar : ℚ) : ℚ := sorry

def isoC2Q (n τ : ℕ) (ρ ρinf M σK σB σT : ℚ) : ℚ := sorry

theorem isoC1_le_isoC1Q {n τ : ℕ} {ρ ρinf M σK σB σT μ ν γbar : ℚ} (hn : 2 ≤ n)
    (hτ : n - 1 ≤ τ) (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hν : 0 < ν) (hγbar : 0 < γbar) :
    Iso.Apost.isoC1 n τ ρ ρinf M σK σB σT μ ν γbar ≤ isoC1Q n τ ρ ρinf M σK σB σT μ ν γbar :=
  sorry

theorem isoC2_le_isoC2Q {n τ : ℕ} {ρ ρinf M σK σB σT : ℚ} (hn : 2 ≤ n) (hτ : n - 1 ≤ τ)
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) :
    Iso.Apost.isoC2 n τ ρ ρinf M σK σB σT ≤ isoC2Q n τ ρ ρinf M σK σB σT := sorry

/-- Sum-of-squares lower bound on the real torus. The check forms the model of
`Re-part f - m₀ - g g*` (`g* = conjReflect g`), bounds its sup by `r`, and requires
`m ≤ m₀ - r` (the residual is PAID; a small `r` without that slack is rejected). -/
def checkRealLowerBound {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig)
    (f : CertModel α) (m₀ m : ℚ) (g : CertPoly α) : Bool := sorry

theorem checkRealLowerBound_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {f : CertModel α} {ff : (Fin n → ℂ) → ℂ} (hf : f.Encloses n W.rho ff) {m₀ m : ℚ}
    {g : CertPoly α} (h : checkRealLowerBound W cfg f m₀ m g = true) (x : Fin n → ℝ) :
    (m : ℝ) ≤ (ff fun i => (x i : ℂ)).re := sorry

/-! ## §G. Frequencies, the certificate, the checker and the black box -/

/-! ### Exact frequencies (`KAM/Certificate/Freq.lean`, finding F1)

The black box takes the EXACT reference vector `ω* : Fin n → ℝ` as a real vector, with two proved
facts about it: `FreqEncloses n c.freqBox ω*` (the certificate's rational box, which is all the
checker reads) and `IsDiophantine γ τ ω*` (the external input). Every sub-check is uniform over
the box. Any rationally independent `n`-tuple is admissible. Providers of the box fact: the
algebraic one below (coordinates in `ℚ(x)` for a certified real `x`, e.g. `√5`, `∛2`). -/

/-- `ω_i = Σ_j a_{ij} x^j` for a real number `x`. -/
def algFreq (n : ℕ) (coeffs : List (List ℚ)) (x : ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.range (coeffs.getD i.val []).length,
    (((coeffs.getD i.val []).getD j 0 : ℚ) : ℝ) * x ^ j

/-- Interval evaluation in `ℚ` of each `Σ_j a_{ij} x^j` for `x ∈ [lo, hi]` (`lo ≥ 0`), checked
inside the box; also `box.length = n`. -/
def checkAlgBox (n : ℕ) (coeffs : List (List ℚ)) (lo hi : ℚ) (box : FreqBox) : Bool := sorry

theorem algFreq_encloses {n : ℕ} {coeffs : List (List ℚ)} {lo hi : ℚ} {box : FreqBox} {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ hi) (h : checkAlgBox n coeffs lo hi box = true) :
    FreqEncloses n box (algFreq n coeffs x) := sorry

/-! ### The certificate (`KAM/Certificate/Defs.lean`) -/

/-- Parameters of `g1_explicit` (exact rationals; `τ ∈ ℕ`). `nuRay` is the theorem's `ν`. -/
structure CertParams where
  tau : ℕ
  rho : ℚ
  rhoInf : ℚ
  M : ℚ
  σK : ℚ
  σB : ℚ
  σT : ℚ
  μ : ℚ
  γbar : ℚ
  σω : ℚ
  nuRay : ℚ
  γ : ℚ
  s : ℚ
  err : ℚ
  E0 : ℚ
  /-- claimed explicit displacement bound, checked `≥ isoC2Q e / (γ² ρ^{2τ})` -/
  disp : ℚ

/-- The certificate: problem data, numerical witnesses and controls (data only; no proofs, no
real numbers). -/
structure TorusCertificate (n : ℕ) (α : Type) where
  params : CertParams
  ham : HamExpr n
  /-- `D = T_{ρ_H} × polydisc(centre, radius)` -/
  weightH : CertWeight
  centre : List ℚ
  radius : List ℚ
  /-- rational box of the reference vector `ω*` -/
  freqBox : FreqBox
  emb : CertEmbedding α
  /-- weight of the strip `T_ρ` (its `rho` must equal `params.rho`) -/
  weight : CertWeight
  wit : Witnesses α
  gramInv : List (List (CertPoly α))
  torsInv : List (List (CC α))
  cfgFull : ModelConfig
  cfgLow : ModelConfig
  piEnc : PiEnclosure α
  expHalvings : ℕ
  expOrder : ℕ

section Denotation

variable {n : ℕ} {α : Type} [CertArith α]

def TorusCertificate.D (c : TorusCertificate n α) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  certDomain n c.weightH.rho c.centre c.radius

def TorusCertificate.H (c : TorusCertificate n α) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := c.ham.eval

def TorusCertificate.K (c : TorusCertificate n α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := c.emb.eval n

end Denotation

/-! The sub-checks (each `Bool`, each provable by `decide +kernel` on its own). -/

/-- Shapes (`box.length = n`, list lengths), positivity, `2 ≤ n`, `n - 1 ≤ τ`, `ρ∞ < ρ`,
`1 < s < σω`, `γ ≤ γbar`, `0 ≤ e`, `weight.rho = rho`, both weights, the `π` enclosure, the box
excludes `0` in some coordinate, and the ray margins against the box's lower bound of `‖ω*‖`. -/
def checkStatic {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- Ball arithmetic of the jet on `D` (every denominator certified) and the five bounds
`‖DH‖, ‖X_H‖, ‖DX_H‖, ‖D²X_H‖, ‖D²H‖ ≤ M` on `D`. -/
def checkHamBounds {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `ball (K θ) μ ⊆ D` on `T_ρ` and `‖DK‖ ≤ σK - μ` (row sums of `DK` models). -/
def checkEmbedding {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `sup_{T_ρ} ‖X_H(K) - DK (s ω)‖ ≤ e` at full precision, uniformly for `ω` in the box. -/
def checkInvariance {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `‖⟨H ∘ K⟩ - E₀‖ ≤ e` (zero mode of the composed model ± radius). -/
def checkEnergy {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The Gram certificate (`gramCheck`) with bound `σB - μ`. -/
def checkGram {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `torsionModels` at `s` and the box, then `torsionAvgCheck n` (exact `(n+1)×(n+1)` shapes of
`T` and the witness `c.torsInv`) with bound `σT - μ`. -/
def checkTorsion {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `isoC1Q e < γ⁴ ρ^{4τ}` and `isoC2Q e ≤ disp γ² ρ^{2τ}`. -/
def checkSmallness {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  sorry

/-- **The black-box checker.** -/
def checkTorusCertificate {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c && checkEnergy c &&
    checkGram c && checkTorsion c && checkSmallness c

section Black

variable {n : ℕ} {α : Type} [CertArith α]

/-- Every hypothesis of `KAM.Iso.Apost.g1_explicit` and of `IG1Body`, verbatim, at the data
denoted by `c` and the exact reference vector `ωstar` (`IsDiophantine` excepted). -/
structure G1Hyps (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hωstar : ωstar ≠ 0
  hopen : IsOpen c.D
  htransl : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D
  hholo : DifferentiableOn ℂ c.H c.D
  hper : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z
  hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
    (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  hbd : ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧ ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M
  hK : DifferentiableOn ℂ c.K (complexStrip n c.params.rho)
  hKp : IsPrimaryOnStrip c.K c.params.rho
  hKr : IsRealOnReals c.K
  hball : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D
  hDK : ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ
  hG : ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
    ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ
  hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det
  hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
    (c.params.σT : ℝ) - c.params.μ
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hν1 : (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖
  hν2 : (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hE : ∀ θ ∈ complexStrip n c.params.rho,
    ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err
  hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err
  hC1 : Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1
  hdisp : Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp

/-- The output of the black box: the conclusion of `IG1Body` for the denoted data, with the
explicit rational displacement bound `disp` in place of `C₂ e/(γ²ρ^{2τ})`. -/
def CertifiedTorus (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop :=
  ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < c.params.σω ∧ DifferentiableOn ℂ Kinf (complexStrip n c.params.rhoInf) ∧
    IsPrimaryOnStrip Kinf c.params.rhoInf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, invarianceError c.H Kinf (sinf • ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, c.H (Kinf θ) = ((c.params.E0 : ℝ) : ℂ)) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, Metric.ball (Kinf θ) ((c.params.μ : ℝ) / 2) ⊆ c.D) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf,
      ‖fderiv ℂ Kinf θ‖ ≤ (c.params.σK : ℝ) - (c.params.μ : ℝ) / 2) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, ‖Kinf θ - c.K θ‖ ≤ c.params.disp) ∧
    ‖sinf • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ c.params.disp

/-! ### Sub-check contracts (`KAM/Certificate/Sound/*.lean`, finding F3)

Acyclic assembly: Static → (structural H, K) → HamBounds → Embedding → {Gram, Invariance,
Energy} → Torsion (uses Gram) → Smallness. Every `G1Hyps` field is produced by exactly one
contract below. -/

/-- The `ω`-free static facts. -/
structure StaticFacts (c : TorusCertificate n α) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hrho : c.weight.rho = c.params.rho
  hW : checkWeight c.weight c.expHalvings c.expOrder = true
  hWH : checkWeight c.weightH c.expHalvings c.expOrder = true
  hpe : checkPiEnclosure c.piEnc = true

variable [LawfulCertArith α]

theorem checkStatic_sound {c : TorusCertificate n α} (h : checkStatic c = true) :
    StaticFacts c := sorry

/-- The `ω`-dependent static facts, for every `ω` in the box. -/
theorem checkStatic_freq {c : TorusCertificate n α} (h : checkStatic c = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ωstar ≠ 0 ∧ (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖ ∧
      (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := sorry

/-- Structural facts of `K` (law-free). -/
theorem TorusCertificate.emb_structural (c : TorusCertificate n α) :
    DifferentiableOn ℂ c.K (complexStrip n c.params.rho) ∧ IsPrimaryOnStrip c.K c.params.rho ∧
      IsRealOnReals c.K := sorry

theorem checkHamBounds_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkHamBounds c = true) :
    c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M := sorry

/-- Structural facts of `H` on `D`, given the certified denominators. -/
theorem TorusCertificate.ham_structural (c : TorusCertificate n α)
    (hnv : c.ham.NonvanishingOn c.D) :
    IsOpen c.D ∧ (∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D) ∧
      DifferentiableOn ℂ c.H c.D ∧
      (∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z) ∧
      ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
        (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := sorry

theorem checkEmbedding_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkEmbedding c = true) :
    (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ :=
  sorry

theorem checkGram_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkGram c = true) : ∀ θ ∈ complexStrip n c.params.rho,
      IsUnit (gramMatrix c.K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ := sorry

theorem checkInvariance_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true)
    (h : checkInvariance c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := sorry

theorem checkEnergy_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (h : checkEnergy c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := sorry

/-- Assembled from `torsionModels_sound` (with `D := c.D`, `hKD` from `checkEmbedding_sound`,
`hnv` from `checkHamBounds_sound`, `hG` from `checkGram`) and `torsionAvgCheck_sound` at the
certificate's own `n` (`torsionAvgCheck n`, exact shapes, F7). -/
theorem checkTorsion_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (hg : checkGram c = true)
    (h : checkTorsion c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ := sorry

theorem checkSmallness_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkSmallness c = true) :
    Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1 ∧
    Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
  sorry

/-- All hypotheses of `g1_explicit` from a passing check and a frequency in the box. -/
theorem checkTorusCertificate_hyps {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) : G1Hyps c ωstar := sorry

/-- **The black box.** A passing certificate, an exact reference vector `ωstar` in its box, and a
proved Diophantine input yield an exact analytic invariant torus `K_∞` within `disp` of `K`,
through the sealed `KAM.Iso.Apost.g1_explicit` instantiated at
`(n, τ, ρ, ρ∞, M, σK, σB, σT, μ, γbar, σω, ν, ω*) := (n, c.tau, c.rho, c.rhoInf, c.M, c.σK, c.σB,
c.σT, c.μ, c.γbar, c.σω, c.nuRay, ωstar)` and applied to
`(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.s, c.γ, c.err, c.E0)`. -/
theorem checkTorusCertificate_sound {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  sorry

end Black

/-! ## §H. The clock lemma (`KAM/Certificate/Clock.lean`; LANDED on `inp` 092a9d11, statement
identical; STAND-IN here) -/

/-- If `∂_{I_j} H ≡ 1` on `D` and the exact torus is invariant at `s_∞ ω*`, the clock
coordinate is exact: `s_∞ ω*_j = 1`, and `K_∞,j(θ) = θ_j + c` on reals (nonresonance). -/
theorem clock_frequency {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ρ sinf γ τ : ℝ} {ωstar : Fin n → ℝ} (j : Fin n) (hρ : 0 < ρ)
    (hH1 : ∀ z ∈ D, fderiv ℂ H z (phaseBasis (.inr j)) = 1)
    (hKD : ∀ θ ∈ complexStrip n ρ, Kinf θ ∈ D)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip n ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip n ρ, invarianceError H Kinf (sinf • ωstar) θ = 0)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) :
    sinf * ωstar j = 1 ∧
      ∃ c : ℝ, ∀ x : Fin n → ℝ, (Kinf fun i => (x i : ℂ)).1 j = ((x j + c : ℝ) : ℂ) := sorry

/-! ## §J. A nonresonant `n = 3` frequency and the toys (`KAM/Certificate/CubicDiophantine.lean`,
`KAM/Certificate/Tests/*`; finding F1 example, finding F4) -/

/-- `∛2`. -/
def cbrtTwo : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

/-- The reference vector `(∛2/2, ∛4/2, 1/2)`: rationally independent (`x³ - 2` irreducible). -/
def cubicFreq : Fin 3 → ℝ := ![cbrtTwo / 2, cbrtTwo ^ 2 / 2, 1 / 2]

theorem cubicFreq_eq_algFreq : cubicFreq = algFreq 3 [[0, 1 / 2], [0, 0, 1 / 2], [1 / 2]] cbrtTwo :=
  sorry

/-- Norm-form argument: `β = k₀ + k₁x + k₂x²` (`x = ∛2`) times its real adjugate
`Q = (k₀² - 2k₁k₂) + (2k₂² - k₀k₁)x + (k₁² - k₀k₂)x²` is the integer
`N = k₀³ + 2k₁³ + 4k₂³ - 6k₀k₁k₂ ≠ 0` (descent mod 2); `|Q| ≤ (1 + x)²|k|₁² < 6|k|₁²`. -/
theorem cubicFreq_isDiophantine : IsDiophantine (1 / 12) 2 cubicFreq := sorry

/-- Toy Hamiltonian `I₂ + I₀²/2 + I₁²/2` (isoenergetically nondegenerate; no perturbation). -/
def toyHam3 : HamExpr 3 :=
  .add (.action 2) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    (.mul (.const (1 / 2)) (.pow (.action 1) 2)))

/-- Toy T3: `K(θ) = (θ, (a, b, -(a² + b²)/2))` with RATIONAL `a ≈ ∛2`, `b ≈ ∛4`
(`|a - ∛2|, |b - ∛4| ≤ 10^{-N}`, `N` fixed by `isoC1Q` at `n = 3`, `τ = 2`), `s = 2`, a box of
`cubicFreq` of radius `≤ 10^{-N}`; the residual budget `err ≥ |(a, b) - 2 ω*|` is positive. -/
def toyCert3 : TorusCertificate 3 ℚ := sorry

theorem toyCert3_ham : toyCert3.ham = toyHam3 := sorry

theorem toyCert3_err_pos : 0 < toyCert3.params.err := sorry

theorem toyCert3_passes : checkTorusCertificate toyCert3 = true := sorry

theorem toyCert3_freq : FreqEncloses 3 toyCert3.freqBox cubicFreq := sorry

/-- The genuine `n = 3` black-box application (external Diophantine premise discharged). -/
theorem toyCert3_torus : CertifiedTorus toyCert3 cubicFreq := sorry

/-- Toy T2: `H = J + p²/2`, `K(θ) = (θ, (ν̃, -ν̃²/2))` with rational `ν̃ ≈ ν₋`, reference vector
`(ν₋/2, 1/2)` (SO-DIO), positive residual. Toy T2d: the same with `H` written with a division,
`J + (p²/2)·((3 + cos 2πq)/(3 + cos 2πq))` (exercises O2). -/
def toyCert2 : TorusCertificate 2 ℚ := sorry

def toyCert2d : TorusCertificate 2 ℚ := sorry

theorem toyCert2_passes : checkTorusCertificate toyCert2 = true := sorry

theorem toyCert2d_passes : checkTorusCertificate toyCert2d = true := sorry

theorem toyCert2_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] := sorry

theorem toyCert2d_torus : CertifiedTorus toyCert2d ![lunarNuMinus / 2, 1 / 2] := sorry

/-- Checker-only test (NO Diophantine premise exists: its rational reference vector `(1/4, 1/2)`
is resonant): zero error, exact rational `ν = 1/2`. It exercises the checker only. -/
def toyRatCert : TorusCertificate 2 ℚ := sorry

theorem toyRatCert_passes : checkTorusCertificate toyRatCert = true := sorry

end KAM.Certificate

/-! ## §I. The lunar client (`KAM/SpinOrbit/*`), against the real SO-MODEL and SO-DIO modules -/

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-! ### `KAM/SpinOrbit/HamExpr.lean` -/

/-- `𝓗` in the expression language: `J + p²/2 + Σ_m (-ε A_m) cos(2π(2q - mφ))`. -/
def soHamExpr : HamExpr 2 :=
  .add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    ((List.range 7).foldr (fun m acc =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, -((m : ℤ) + 1)])) acc)
      (.const 0)))

theorem soHamExpr_eval (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soHamExpr.eval z = soHC z := sorry

theorem soHamExpr_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soHamExpr.eval z (phaseBasis (.inr 1)) = 1 := sorry

/-! ### Lunar frequencies (`KAM/SpinOrbit/Freq.lean`): exact `ℚ(√5)` instance of `algFreq` -/

theorem lunarFreqMinus_eq :
    ![lunarNuMinus / 2, 1 / 2] = algFreq 2 [[3039 / 6236, 1 / 6236], [1 / 2]] (Real.sqrt 5) :=
  sorry

theorem lunarFreqPlus_eq :
    ![lunarNuPlus / 2, 1 / 2] = algFreq 2 [[3197 / 6236, -1 / 6236], [1 / 2]] (Real.sqrt 5) :=
  sorry

/-! ### `KAM/SpinOrbit/Graph.lean`: graph inversion of an exact torus -/

/-- An invariant barrier graph `p = P(q, φ)` of the physical flow with values in `[lo, hi]`. -/
structure SoBarrier (lo hi : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_q : ∀ q φ, P (q + 1) φ = P q φ
  periodic_φ : ∀ q φ, P q (φ + 1) = P q φ
  invariant : KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = P x.1 x.2.2}
  lower : ∀ q φ, lo ≤ P q φ
  upper : ∀ q φ, P q φ ≤ hi

/-- Graph data checked on top of a passing torus certificate for `soHamExpr`: a monotonicity
margin `mono` for `∂_{θ₀} q` (checked with the strict remaining margin `mono > disp/ρ∞`), the
range `[pLo, pHi]` of `p` on the real torus, and the SOS witnesses with their certified centres. -/
structure SoGraphCert (α : Type) where
  base : TorusCertificate 2 α
  mono : ℚ
  mono₀ : ℚ
  pLo : ℚ
  pLo₀ : ℚ
  pHi : ℚ
  pHi₀ : ℚ
  sosMono : CertPoly α
  sosLo : CertPoly α
  sosHi : CertPoly α

def checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool := sorry

/-- The barrier produced by a passing graph certificate; the band is widened by `disp`. -/
theorem soBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    (hham : g.base.ham = soHamExpr) (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  sorry

/-! ### `KAM/SpinOrbit/Barrier.lean`: two barriers confine, globally and uniquely
(global existence from the global Lipschitz bound of `soField`, not from a lunar-only range). -/

theorem so_confinement {lo₁ hi₁ lo₂ hi₂ : ℝ} (B₁ : SoBarrier lo₁ hi₁) (B₂ : SoBarrier lo₂ hi₂)
    (x₀ : ℝ × ℝ × ℝ) (h₁ : B₁.P x₀.1 x₀.2.2 < x₀.2.1) (h₂ : x₀.2.1 < B₂.P x₀.1 x₀.2.2) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = x₀ ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, B₁.P (z t).1 (z t).2.2 < (z t).2.1 ∧ (z t).2.1 < B₂.P (z t).1 (z t).2.2) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = x₀ ∧ ∀ t, HasDerivAt y (soField (y t)) t) → y = z := sorry

/-! ### `KAM/SpinOrbit/LunarCertificate.lean`, `LunarConfinement.lean` -/

/-- The backend is fixed after SO-REPLAY (§5); `ℚ` is the placeholder. -/
abbrev SoBackend : Type := ℚ

/-- Generated data (`KAM/SpinOrbit/Data/{Lower,Upper}/*`); bodies are the generated terms. -/
def lunarLowerCert : SoGraphCert SoBackend := sorry

def lunarUpperCert : SoGraphCert SoBackend := sorry

theorem lunarLowerCert_ham : lunarLowerCert.base.ham = soHamExpr := sorry

theorem lunarUpperCert_ham : lunarUpperCert.base.ham = soHamExpr := sorry

theorem lunarLowerCert_passes : checkTorusCertificate lunarLowerCert.base = true := sorry

theorem lunarUpperCert_passes : checkTorusCertificate lunarUpperCert.base = true := sorry

theorem lunarLowerGraph_passes : checkSoGraph lunarLowerCert = true := sorry

theorem lunarUpperGraph_passes : checkSoGraph lunarUpperCert = true := sorry

/-- From `lunarFreqMinus_eq`, `algFreq_encloses` and `sqrt_mem_of_checkRootEnclosure`. -/
theorem lunarLowerCert_freq :
    FreqEncloses 2 lunarLowerCert.base.freqBox ![lunarNuMinus / 2, 1 / 2] := sorry

theorem lunarUpperCert_freq :
    FreqEncloses 2 lunarUpperCert.base.freqBox ![lunarNuPlus / 2, 1 / 2] := sorry

/-- The certified initial momentum window (ruling O1; literal rationals before the freeze). -/
def lunarPLo : ℚ := sorry

def lunarPHi : ℚ := sorry

theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi := sorry

/-- **Theorem A (continuous form).** Two invariant barrier graphs inside the 3.3% band. -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000)) (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) := sorry

/-- **Theorem B.** Every initial state with `lunarPLo < p₀ < lunarPHi` has a unique global
solution, and `|p(t) - 1| ≤ 33/1000` for all real `t`. -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := sorry

end KAM.SpinOrbit

end
```
