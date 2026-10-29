# Lean design: the general torus-certificate black box and its lunar client (track SO)

Design SO-DESIGN, Revision 1, 2026-10-29, branch `inp-design-so`. Planning evidence only: no proof is
claimed, no frozen file is touched, nothing is frozen. Appendix A (the exact draft signatures) elaborates
against the shared `inp` build with `sorry` bodies only (§9).

Scope (owner, 2026-10-29, D30 and the scope decision in `SPIN-ORBIT-PLAN.md`): a FULLY GENERAL checker
`checkTorusCertificate` and its soundness theorem through the sealed isoenergetic theorem
`KAM.Iso.Apost.g1_explicit`, for any `n ≥ 2`, Hamiltonians given as finite expressions, and Fourier
embeddings in all coordinates; the lunar spin–orbit system (band `|p − 1| ≤ 33/1000`) is its first client.

### Input pins

Worktree base `184516586ae9060d87838ff1fb59d2547fe216e5` (= `inp` at launch). Wave-0 siblings read at:
SO-MODEL `inp-somodel` `d900e114`, SO-DIO `inp-sodio` `6d306d20`, SO-REPLAY `inp-soreplay` `b3c96def`
(prototype only, no measurements yet), SO-GEN `inp-sogen` (scripts in progress).

| Input | SHA-256 |
|---|---|
| `KAM:docs/campaign/design/SPIN-ORBIT-PLAN.md` | `a275e9ac09e038227c142f3f235bc8f7e07400efa443172c41d5aa551d22a510` |
| `KAM:docs/explorations/lunar-spin-orbit-certificate-proposal.md` | `67227392977b384340c8ae7fdd2010b88fb5aeadd05672c53bab79ded2ea3d0a` |
| `KAM:docs/explorations/lunar-spin-orbit-feasibility-report.md` | `9c333266c380a96172125ffcca3ecf5aedde2d59056a3cedaeaef7a318697241` |
| `KAM/Iso/Apost/G1.lean` | `202ba7ef0fe5c215ece86970a40a8265d508243f303c2c417ce2f71250b57f40` |
| `KAM/Iso/Charts/Inputs.lean` (`IG1Body`) | `a8f405840e6a94be71deeb6632aba601e237961933f3d4e26e81e5bb21ad3bfe` |
| `KAM/Iso/Apost/Defs.lean` (`isoC1`, `isoC2`) | `bfe66bba3354dbcd66b5bbaa2dab630018b6fb44259e31cad47a319032bb8163` |

## 1. Decisions

1. **Expression language (`HamExpr n`).** Constructors: rational constant, `π`, action coordinate `I_j`,
   period-one angle modes `cos(2π k·θ)` and `sin(2π k·θ)` (`k ∈ ℤⁿ`), `+`, `×`, natural power, `exp`,
   `sin`, `cos`. Every constructor maps real points to reals and angles enter only through integer
   modes, so **holomorphy (entire), translation invariance, periodicity and reality are structural**
   (`HamExpr.contDiff_eval`, `eval_add_int`, `eval_real`) and need no numerical check. There is **no
   division** in version 1: no client needs it (spin–orbit, the restricted problem in action–angle form
   after averaging); the Kepler-forcing extension (proposal §13.1) would add `inv e` with a certified
   lower bound for `|e|` on `D`, as a later constructor. Complex exponentials `e^{2πik·θ}` are internal
   (the straight-line program, decision 4), not user syntax, precisely to keep reality structural.
2. **Domain.** `D = T_{ρ_H} × Π_i {|I_i − c_i| < r_i}` (`certDomain`) with rational `ρ_H`, centre `c` and
   radii `r`: open and translation invariant by construction (`isOpen_certDomain`,
   `certDomain_add_int`). The checker certifies `ball(K θ, μ) ⊆ D` on `T_ρ` by
   `ρ + ι_i + μ ≤ ρ_H` with `ι_i = min(sup|U_i|, ρ Σ_j sup|∂_j U_i|)` (the second bound is the mean
   value inequality from the real point, where `Im U_i = 0`) and `sup|A_i − c_i| + μ ≤ r_i`.
3. **Norms.** Exactly the existing API: max norms on `Fin n → ℂ` and on the product, operator norms of
   `fderiv`/`iteratedFDeriv`, matrix row-sum norm via `open scoped Matrix.Norms.Operator`
   (`KAM.norm_le_iff_forall_rowSum`, `KAM.Torus.norm_colMat`, `norm_sqMat`, `Apost.norm_tangentMat`).
   New bridges (§E of Appendix A) bound `‖DH‖`, `‖D²H‖`, `‖DX_H‖`, `‖D²X_H‖` by sums of partials along
   `phaseBasis a = (sumVec n).symm (Pi.single a 1)`, `a : Fin n ⊕ Fin n`.
4. **Derivatives: the checker differentiates symbolically.** The certificate carries NO derivative
   data. `HamExpr` is compiled to a straight-line program (`Slp`, ops: const with `2π`-degree, action,
   character, add, mul, exp) and `HamExpr.jet` appends forward-mode derivative slots up to order 3 with
   sharing, zero/constant folding and pruning; correctness is `jet_d1/d2/d3` against `fderiv` and
   `iteratedFDeriv`. Order 3 is needed only for `‖D²X_H‖ ≤ M` and is evaluated by majorants on `D` (not
   composed with `K`). Cauchy-only bounds were rejected: with the pilot's clearance they inflate `M` by
   a factor of order 6 and the constants by `~6^{30}` (far beyond the 10⁵ slack). Derivatives of `K`
   are exact Fourier multipliers on its data.
5. **Enclosure semantics: Fourier models in the sup norm on the open strip.** A model is
   `(deg, P, r)` denoting `(2π)^deg (P + T)` with `P` a finite exact polynomial and
   `sup_{T_ρ}|T| ≤ r` (`CertModel.Encloses`). Finite products are exact finite sums; truncation and
   rounding move `|c_k| w^{|k|₁}` into `r`, where `w ≥ e^{2πρ}` is a rational weight validated once by
   `checkWeight` (`ratExpUp`, `π < 3.141593`), and `|χ_k| ≤ w^{|k|₁}` on `T_ρ` (`norm_character_le`).
   Every `2π` is explicit: `∂_j` multiplies coefficients by `i k_j` and raises `deg` by one. The sup
   norm (not weighted ℓ¹) keeps the algebra elementary: no infinite convolution identity is needed.
6. **`2π`-degree tagging (the plan's π-free arithmetic, generalized).** Model coefficients never contain
   `π`; the factor `(2π)^deg` is symbolic. Sums of equal degree are exact; mixed degrees use
   `CertModel.toDeg` with a validated `π` enclosure (`checkPiEnclosure`; coarse Mathlib bounds by
   default). For the lunar problem every cancelling sum is degree-homogeneous when the angle shift is
   stored in radians (`angleDeg = −1`, i.e. `U = v/2π`), so no high-precision `π` is needed; a general
   certificate whose cancellations mix degrees needs package SO-PI (high-precision `π`).
7. **Nonlinear composition: a-posteriori witnesses, not Taylor series.** For each `exp` slot and each
   character `χ_k ∘ K = χ_k · exp(2πi k·U)`, the certificate supplies a polynomial witness `E ≈ exp g`.
   The check computes `R_j = ∂_j E − (∂_j g) E` (`n` full-precision products) and a scalar pin
   `|E(0) − exp g(0)|` (`certCExp`, Taylor with `Complex.exp_bound`). Soundness (`expWitness_sound`):
   `D = E e^{−g}` satisfies `∂_j D = e^{−g} R_j`; integrate along the segment from `0` to the periodic
   representative of `θ` (convex strip, `|Re θ_i| ≤ 1/2`), pin `D(0)`. Witnesses for characters are
   keyed by the index with coordinates of syntactically zero `U_j` removed (lunar: one witness for all
   seven modes `(2, −m)`), and `−k` uses `conjReflect`. Taylor series of models are used nowhere.
8. **Gram inverse on the complex strip (bilinear `DKᵀDK`).** The certificate supplies a matrix `B(θ)` of
   Fourier polynomials (a constant `B` is the special case). The checker forms the models of
   `G = gramMatrix K` (`dotℂ`, not Hermitian) and of `I − B G` at reduced precision, bounds
   `δ = sup_{T_ρ} max row sum < 1` and `β = sup ‖B‖`, and concludes `IsUnit det G`,
   `‖G⁻¹‖ ≤ β/(1−δ) ≤ σB − μ` and `‖G⁻¹ − B‖ ≤ δβ/(1−δ)` pointwise (`matrix_inv_of_approx_inverse`,
   a Neumann series; no positivity of a real Gram matrix is used, as the bilinear form demands).
9. **Averaged bordered torsion.** Entry models of `KAM.Iso.extendedTorsion H K (sω*)` are built from
   `DX_H∘K`, `DH∘K` (jet compositions), the Gram witness with its certified radius, and
   `D(G⁻¹)[ω] = −G⁻¹ (DG[ω]) G⁻¹` (`KAM.fderiv_matrix_inv_apply`). The average is the zero mode ±
   radius (`CertModel.Encloses.average`, `torusAverage_character`). A constant witness `S` gives
   `δ_T = ‖I − S C‖ + ‖S‖‖R‖ < 1` and `‖T̄⁻¹‖ ≤ ‖S‖/(1−δ_T) ≤ σT − μ`. No quadrature is used.
10. **Diophantine input.** `IsDiophantine γ τ ω*` is a hypothesis of the soundness theorem, proved
    outside the checker (SO-DIO for the lunar frequencies). `ω*` is exact in `ℚ(√d)ⁿ` (`CertFreq`);
    the checker sees it only through a validated rational enclosure of `√d` (`checkSqrtEnclosure`).
11. **Constants.** `τ ∈ ℕ`, so every `rpow` in `isoC1`/`isoC2` is a natural power. `c_R` contains
    `π`, `e` and a real power; `cRUpQ` bounds it from `π > 3.141592`, `e > 2.718`. Rational mirrors
    `isoC1Q`, `isoC2Q` dominate the real constants by monotonicity in `c_R` (`isoC1_le_isoC1Q`).
12. **Trust boundary: the kernel only.** Sub-checks are `Bool` functions proved `= true` by
    `decide +kernel` (never `native_decide`, `Lean.ofReduceBool`, axioms or `implemented_by`).
    Checker code uses structural recursion and `List` only (no well-founded recursion, no `partial`), so
    the kernel reduces it; integer work goes through GMP-accelerated `Nat`/`Int` kernel primitives.
13. **Staging.** `checkTorusCertificate` is the conjunction of eight named sub-checks
    (`checkStatic … checkSmallness`); each is proved in its own data module, and long lists are split
    with `List.all` lemmas. A check that would need a recursion-depth or heartbeat override is a design
    signal (rule 1), to be reported, never masked.
14. **Lunar headline.** Continuous invariant barrier graphs (plan) and an explicit initial region given
    by a constant momentum window `lunarPLo < p₀ < lunarPHi` (any `q₀, φ₀`), certified by SOS bounds of
    `p` on the two real tori plus the displacement bound. This needs no graph-error transport; the
    polynomial region `Q₋ + d₋ < p < Q₊ − d₊` of proposal §3.2 is a later refinement (open question O1).

## 2. Carriers and conventions

- Ambient types `Fin n → ℝ`, `Fin n → ℂ`, indices `Fin n → ℤ`; phase points `(Fin n → ℂ) × (Fin n → ℂ)`
  (angles first); phase indices `Fin n ⊕ Fin n` in `KAM.Torus.sumVec` order. Never `EuclideanSpace`.
- Data keys are `CertKey = List ℤ` (kernel-friendly lexicographic order), denoted by `certKeyFun n`.
- `CertPoly.eval` is a finite sum of `KAM.character`; `CertPoly.eval_eq_fourierSum` bridges to
  `KAM.fourierSum`, so all strip lemmas of `KAM/Strip/FourierSeries*.lean` apply.
- Real data (`CertRealPoly`) is stored on a half lattice; its full polynomial is conjugate symmetric
  (`Fourier.ConjugateSymmetric`, reused), hence real on reals (`fourierSum_im_eq_zero`).
- `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` (`CertEmbedding.eval`): primary, real and entire
  by construction.
- Parameters of `g1_explicit` are exact rationals in `CertParams` (the theorem's `ν` is `nuRay`, to
  avoid a clash with the lunar `ν±`). The certificate's `rho` of `weight` must equal `params.rho`
  (checked).
- Backend numbers `α` with `CertArith α` (data class) and `LawfulCertArith α` (soundness); complex
  backend numbers `CC α`.

## 3. Reuse map and upstream interfaces

| Need | Existing declaration (reused, read-only) |
|---|---|
| sealed theorem | `KAM.Iso.Apost.g1_explicit`, body `KAM.Iso.Charts.IG1Body` |
| constants | `KAM.Iso.Apost.isoC1`, `isoC2`, `hatcStar`, `hatCDelta`; `KAM.Apost.cR`, `delta0`, `aExp` |
| characters, series | `KAM.character`, `fourierSum`, `norm_character_le`, `norm_fourierSum_le`, `torusAverage`, `torusAverage_character`, `differentiableOn_fourierSum` |
| reality | `Fourier.ConjugateSymmetric`, `fourierSum_im_eq_zero` |
| matrices | `KAM.norm_le_iff_forall_rowSum`, `matrix_neumann_uniform`, `fderiv_matrix_inv_apply`, `KAM.Torus.sumVec`, `colMat`, `sqMat`, `norm_colMat`, `norm_sqMat`, `Apost.tangentMat`, `norm_tangentMat` |
| Cauchy (graph, clock) | `norm_coordinate_fderiv_le_of_mem_complexStrip`, `torusCoeff_fderiv_real`, `eq_zero_of_torusCoeff_eq_zero` |
| ODE | `KAM.ODE.IsSolutionIn`, `IsInvariantSet`, `gen_barrier`, `gen_uniqueness`, `gen_local`, `IsMaximalSolution`, `gen_continuation` |
| Mathlib transcendental bounds | `Real.pi_gt_d6`, `Real.pi_lt_d6`, `Real.exp_one_gt_d9`, `Real.exp_bound`, `Complex.exp_bound` |

`KAM/Iso/Confinement/*` is chart-specific (`fractD`, `EnergyPatch`); the lunar barrier needs no energy
coordinate (1.5 degrees of freedom: the 2-tori separate the 3-dimensional extended phase space directly),
so only its ODE layer is reused.

**Upstream interfaces (wave 0, to reconcile).** Appendix A copies these names verbatim as stand-ins.

| Owner | Name | Shape consumed |
|---|---|---|
| SO-MODEL | `KAM.SpinOrbit.soField`, `soV`, `soVC`, `soA`, `soAQ`, `soEpsQ`, `soModes` | as in `Model.lean` (d900e114) |
| SO-MODEL item 3 | complex Hamiltonian `𝓗(θ, I) = I₁ + I₀²/2 + soVC θ₀ θ₁` (stand-in `soHamC`) | `soHamExpr_eval : soHamExpr.eval z = 𝓗 z` |
| SO-DIO | `lunarNuMinus`, `lunarNuPlus`, `lunarNu{Minus,Plus}_half_isDiophantine` | `IsDiophantine (1/42) 1 ![ν/2, 1/2]` |
| SO-DIO | `lunarNu{Minus,Plus}_eq` | `ν₋ = (3039 + √5)/3118`, `ν₊ = (3197 − √5)/3118` (for `lunarCert_ωstar`) |
| SO-GEN | Lean data emitter | `SoGraphCert SoBackend` terms, sharded < 1500 lines |
| SO-REPLAY | backend choice and shard sizes | decision §5 |

SO-MODEL's `ScalarEmbedding` identities are NOT on the black-box path (the general checker takes all
four components of `K` as Fourier data; the lunar `J` is the generator's Fourier approximation of
`−p²/2 − V(K)`). They remain useful for the generator and documentation.

## 4. The black box: every hypothesis of `g1_explicit`

`checkTorusCertificate_sound (h : checkTorusCertificate c = true) (hdio : IsDiophantine γ τ ω*) :
CertifiedTorus c` applies

```
KAM.Iso.Apost.g1_explicit (n := n) hn (τ := (c.params.tau : ℝ)) hτ
  (ρ := c.params.rho) (ρinf := c.params.rhoInf) hρinf hρinfρ
  (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
  (μ := c.params.μ) (γbar := c.params.γbar) (σω := c.params.σω) (ν := c.params.nuRay)
  hM hσK hσB hσT hμ hγbar hσω hν c.ωstar hωstar
```

and feeds `.2.2.2` the arguments `(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.params.s, c.params.γ,
c.params.err, c.params.E0)` and the fields of `G1Hyps c` in the frozen order, then replaces
`isoC2 · e/(γ²ρ^{2τ})` by `disp` (`hdisp`). `G1Hyps` (Appendix A) restates every binder verbatim.

| `IG1Body` hypothesis | sub-check | soundness argument |
|---|---|---|
| `hn`, `hτ`, parameter positivity, `ρ∞ < ρ`, `1 < σω`, `ν > 0`, `ω* ≠ 0` | `checkStatic` | `decide` on rationals; `√d` enclosure |
| `IsOpen D`, translation, holomorphy, periodicity, reality of `H` | none (structural) | `isOpen_certDomain`, `certDomain_add_int`, `HamExpr.*` |
| five bounds `≤ M` on `D` | `checkHamBounds` | jet majorants + §E bridges |
| `K` holomorphic, primary, real | none (structural) | `CertEmbedding.*` |
| `ball (Kθ) μ ⊆ D`, `‖DK‖ ≤ σK − μ` | `checkEmbedding` | decision 2; row sums of `DK` models, `norm_tangentMat` |
| Gram unit and row sums `≤ σB − μ` | `checkGram` | decision 8 |
| `T̄` unit and row sums `≤ σT − μ` at `sω*` | `checkTorsion` | decision 9 |
| `1 < s < σω`, `ν ≤ (s−1)‖ω*‖`, `ν ≤ (σω−s)‖ω*‖`, `0 < γ ≤ γbar`, `0 ≤ e` | `checkStatic` | rational and `√d` enclosure |
| `IsDiophantine γ τ ω*` | external input | SO-DIO for the client |
| `‖E(θ)‖ ≤ e` on `T_ρ` | `checkInvariance` | jet `d1` composed with `K`; `X_H` by `hamiltonianVectorFieldℂ_sumVec`; `DK(sω*)` exact multipliers with `ω` enclosure |
| `‖Ē_H(K) − E₀‖ ≤ e` | `checkEnergy` | zero mode of `H∘K` model ± radius |
| `C₁ e/(γ⁴ρ^{4τ}) < 1`; `disp` | `checkSmallness` | `isoC1_le_isoC1Q`, `isoC2_le_isoC2Q` |

`CertifiedTorus c` is the `IG1Body` conclusion verbatim with `disp` as the closeness bound; it is not a
hypothesis anywhere (rule 6).

## 5. Arithmetic layer (late-bound) and the replay gate

The checker is generic in `α` with `[CertArith α]`; soundness needs `[LawfulCertArith α]`. Two
instances are planned: `ℚ` (exact, zero error terms) and `CertFixed P` (integer `m` for `m/2^P`, floor
rounding, ulp errors returned by `mulErr`/`addErr`, radii rounded up by `upAdd`/`upMul`). Data numbers
(the embedding, witnesses) are exact in both; only computed centres round. `ℚ(√d)` is NOT a coefficient
field: `√d` enters only through `ω*`, via an enclosure, so the multiplier `k·ω` is a ball.

What SO-REPLAY must show (decision rule for the owner):

- **For `ℚ`:** kernel time and memory of one product (convolution plus merge) of two polynomials with
  support `S` (the SO-GEN support at threshold 1e−130) at about 450-bit dyadic coefficients, including
  `Nat.gcd` normalization; the kernel's behaviour on lists of length `S` (recursion depth). Choose `ℚ`
  if a full stage (one exp witness: `n` products; the invariance sum; the energy average) replays in
  under about 1 h and 16 GB per torus, and within 3× of fixed point.
- **For fixed point:** the same measurements, plus that the accumulated ulp radius stays below about
  1e−110 after the stage (radius growth per product times the number of products).
- **For both:** the extrapolated total for two tori (≈ 2 witnesses × `n` products at full precision,
  plus O(100) reduced-precision products for Gram and torsion); the largest list a single
  `decide +kernel` can carry without a depth override (sets the `List.all` split size); elaboration time
  of a 1500-line data shard. If no option fits, the levers are those of the plan (sharper `n = 2`,
  `τ = 1` constants; rotated coordinates), not overrides.

## 6. The lunar client

- `soHamExpr : HamExpr 2 = J + ½p² + Σ_{m=1}^{7} (−ε A_m) cos(2π(2q − mφ))` with angle order `(q, φ)`,
  action order `(p, J)` (SO-MODEL item 3). `soHamExpr_eval` bridges to the upstream Hamiltonian,
  `soHamExpr_clock` gives `∂_J 𝓗 ≡ 1`.
- Two certificates `lunar{Lower,Upper}Cert : SoGraphCert SoBackend`: parameters as the pilot (`n = 2`,
  `τ = 1`, `ρ = 1/200`, `ρ∞ = 1/400`, `μ = 1/1000`, `M = σK = σB = σT = 4`, `σω = 3`, `s = 2`,
  `γ = γbar = 1/42`, `E₀ = 0`, `e ≈ 1e−103`, `nuRay` from the ray margin); `ω* = (ν±/2, 1/2)` in
  `ℚ(√5)` (`lunarCert_ωstar`); `U = (v/2π, 0)` with `angleDeg = −1`, `A = (p, J̃)` with `actionDeg = 0`.
- **Clock** (`KAM.Certificate.clock_frequency`, general): `∂_{I_j}H ≡ 1` and invariance give
  `s∞ ω*_j = 1` by averaging the `j`-th angle equation (lunar: `s∞ = 2`, physical frequency `(ν, 1)`),
  and nonresonance of `s∞ω*` (from `IsDiophantine`) makes `K∞,j(x) − x_j` constant on reals
  (coefficients `2πi k·ω ŵ_k = 0`).
- **Graph** (`soBarrier_of_cert`): `∂_{θ₀} q ≥ mono > 0` on the real torus of the candidate (SOS
  check, `checkRealLowerBound`), transferred to the exact torus by Cauchy on `T_{ρ∞}` (error
  `≤ disp/ρ∞`), gives a strictly increasing surjection `θ₀ ↦ q` for each `θ₁`; with the clock, the
  real torus is the graph of a continuous, doubly 1-periodic `P(q, φ)`. Its values are values of `p∞`,
  so `pLo − disp ≤ P ≤ pHi + disp` from SOS bounds of `p` on the candidate. The graph set is invariant
  (`IsInvariantSet soField univ`): the curve `t ↦ K∞(x + t(ν, 1))` projects to a solution of `soField`
  and `gen_uniqueness` applies (the field is `C¹`).
- **Barrier** (`so_confinement`): the open slab between two ordered barriers; `gen_barrier` with
  `S` = the union of the two invariant graphs (frontier of the slab), confinement on the maximal
  interval (`gen_local`), then `gen_continuation` (uniform data on `|p| ≤ 2`, the force is periodic and
  bounded) gives `T± = ±∞`; uniqueness from `gen_uniqueness`. Both time directions.
- **Final theorems:** `lunar_barriers` (two invariant continuous barrier graphs in `[967/1000,
  1033/1000]`, ordered, straddling the window) and `lunar_spin_confinement` (unique global solution and
  `|p(t) − 1| ≤ 33/1000` for every initial state with `lunarPLo < p₀ < lunarPHi`). Before the freeze
  `lunarPLo`, `lunarPHi` are replaced by their literal rationals in the statement text.

## 7. Modules, import DAG and packages

All paths new; every file < 1500 lines (target ≤ 800). `→` means "imports".

```
Certificate/Arith/{Interface,Rat,Fixed,Transcendental,PiHigh}
Certificate/Poly/{Basic,Ops}                   → Arith/Interface, Strip/FourierSeries, Diophantine/SolverAlgebra
Certificate/Model/{Basic,Ops}                  → Poly/*, Arith/Transcendental, Strip/Averages
Certificate/Model/Exp                          → Model/Ops
Certificate/Expr/{Basic,Slp,Diff}              → Arith/Interface, Strip/Fourier
Certificate/Expr/Majorant                      → Expr/Slp, Arith/Transcendental
Certificate/NormBridge                         → Torus/Basic, Frozen/Defs/HamiltonianVectorFieldC
Certificate/Embedding                          → Poly/*, Model/Basic
Certificate/Expr/Compose                       → Expr/Slp, Model/Exp, Embedding
Certificate/{MatrixCert,Gram}                  → Model/Ops, Matrix/Neumann, Embedding
Certificate/Torsion/{Frame,Models}             → Gram, Expr/Compose, Matrix/Inverse, Frozen/Iso/Defs/*
Certificate/Constants                          → Iso/Apost/Defs, Arith/Transcendental
Certificate/Positivity                         → Model/Ops
Certificate/Defs                               → all of the above
Certificate/Sound/{Static,Ham,Embedding,Invariance,Energy,Gram,Torsion,Smallness}  → Defs
Certificate/Soundness                          → Sound/*, Iso/Apost/G1
Certificate/Clock                              → Frozen defs, Strip/FourierDerivative
Certificate/Tests/{Toy,Negative}               → Defs, Soundness
SpinOrbit/{Model,PeriodOne,Hamiltonian,ScalarEmbedding}   (SO-MODEL, wave 0)
Certificate/QuadraticDiophantine                          (SO-DIO, wave 0)
SpinOrbit/HamExpr                              → Expr/Basic, SpinOrbit/Hamiltonian
SpinOrbit/Graph/{Inverse,Barrier}              → Soundness, Clock, Positivity, HamExpr, ODE/*
SpinOrbit/Confine                              → Graph/*, ODE/{Exit,Maximal,Continuation,Uniqueness}
SpinOrbit/Data/{Lower,Upper}/Part*             → Defs            (generated)
SpinOrbit/Lunar{Lower,Upper}Passes             → Data, Defs      (decide +kernel per sub-check)
SpinOrbit/LunarConfinement                     → all SpinOrbit, QuadraticDiophantine
```

No module imports a provider or a frozen theorem anchor (`g1_explicit` lives in the implementation
module `KAM/Iso/Apost/G1`).

| Package | Wave | Modules | Lines (est.) | Inputs |
|---|---|---|---|---|
| SO-ARITH | W1 | Arith/{Interface,Rat,Fixed,Transcendental} | 1100 (two packages: interface+ℚ 500, fixed+transc. 600) | SO-REPLAY verdict |
| SO-POLY | W1 | Poly/{Basic,Ops} | 1200 (A: data+bridge 550, B: merge/convolution correctness 650) | SO-ARITH |
| SO-MALG | W1 | Model/{Basic,Ops} | 1150 (A 500, B 650) | SO-POLY |
| SO-EXPW | W1 | Model/Exp | 600 | SO-MALG |
| SO-EXPR | W1 | Expr/{Basic,Slp,Diff} | 1500 (A: Basic+Slp 750, B: Diff 750) | SO-ARITH |
| SO-MAJ | W1 | Expr/Majorant, NormBridge | 800 | SO-EXPR |
| SO-EMB | W1 | Embedding, Expr/Compose | 800 | SO-EXPW, SO-EXPR |
| SO-MAT | W1 | MatrixCert, Gram | 700 | SO-MALG, SO-EMB |
| SO-CONST | W1 | Constants | 700 | — |
| SO-POS | W1 | Positivity | 350 | SO-MALG |
| SO-PI | W1 (optional) | Arith/PiHigh | 500 | SO-ARITH |
| SO-TORS | W2 | Torsion/{Frame,Models} | 1000 (two packages) | SO-MAT, SO-EMB |
| SO-DEFS | W2 | Defs | 600 | all W1 |
| SO-SOUND | W2 | Sound/*, Soundness | 1400 (A: static/ham/emb/energy/small 700, B: inv/gram/torsion/G1 700) | SO-DEFS, SO-TORS |
| SO-CLOCK | W2 | Clock | 400 | — |
| SO-TEST | W2 | Tests/{Toy,Negative} | 300 | SO-SOUND |
| SO-GRAPH | W2 | HamExpr, Graph/{Inverse,Barrier} | 800 | SO-SOUND, SO-CLOCK, SO-POS, SO-MODEL |
| SO-CONF | W2 | Confine | 600 | SO-GRAPH |
| SO-DATA | W3 | generator emitter + Data shards | generated | SO-GEN, SO-DEFS |
| SO-LUNAR | W3 | Lunar*Passes, LunarConfinement | 400 | all |

Hand-written total ≈ 16–17k lines (plus wave 0 ≈ 1.5k); with the usual 30–40% overrun, 21–24k,
inside the plan's 21–37k. W1 packages without arrows between them run in parallel (SO-CONST, SO-CLOCK,
SO-EXPR, SO-ARITH first).

## 8. Validation plan

- **Toy positive certificate** (SO-TEST): `n = 2`, `H = J + p²/2` (integrable), `K(θ) = (θ, (ν, −ν²/2))`
  with `ν ∈ ℚ(√5)`; every sub-check passes with zero invariance error.
- **Negative tests** (`checkTorusCertificate c = false` by `decide +kernel`, each failing in the
  intended sub-check, also stated per sub-check): (i) a false residual bound (`err` below the actual
  residual of a perturbed toy `K`) fails `checkInvariance`; (ii) an invalid Gram witness (`B = 0`, or
  `B` with defect `δ ≥ 1`) fails `checkGram`; an invalid torsion witness fails `checkTorsion`;
  (iii) `μ = 0` fails `checkStatic`; (iv) an exp witness with a wrong mean (multiplied by `1 + 10⁻⁶`)
  fails the pin; (v) a weight `w < e^{2πρ}` fails `checkWeight`.
- **Axiom audit:** `#print axioms` of `checkTorusCertificate_sound`, every `*Passes` theorem and the two
  final lunar theorems: only `propext`, `Classical.choice`, `Quot.sound` (no `Lean.ofReduceBool`).
- **Cross-check:** SO-GEN's exact Python evaluator recomputes every sub-check margin from the same data.

## 9. Elaboration of Appendix A

Command (gated): `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh
/root/code/KAM-inp-design-so .drafts/scratch/SOSignatures.lean` → exit 0, 109 warnings, all
`declaration uses 'sorry'`, no error. The upstream stand-ins (§I) are verbatim copies so that the client
signatures elaborate on `inp`; implementations import the real modules instead.

## 10. Risks

| Risk | Signal | Response |
|---|---|---|
| Kernel replay too slow or too deep | SO-REPLAY; a stage needs an override | shard with `List.all`; fixed point; sharper `n = 2` constants (plan lever); never an override |
| Crude majorants on `D` exceed `M = 4` | `checkHamBounds` margin | per-coordinate radii, smaller `ρ_H`; pilot majorant 2.69 leaves room |
| Witness pin radius dominated by `e^{2 sup|g|}` | `checkInvariance` margin | split `exp` by halving (`E = F²`, witness `F`) |
| Mixed `2π` degrees in a general client | `toDeg` radius | SO-PI high-precision enclosure |
| Gram/torsion witnesses weak | `δ`, `δ_T` near 1 | Fourier-model `B`; Newton-refined `B` from the generator |
| Jet size for large `n` (order 3: `(2n)³` slots) | elaboration/replay | order-3 slots only majorized, never composed; pruning |
| Upstream name drift (SO-MODEL item 3) | reconciliation | bridge lemma `soHamExpr_eval` only |

## 11. Open questions for the owner

- **O1.** Headline initial region: constant momentum window (this design) versus the polynomial graph
  region `Q₋ + d₋ < p < Q₊ − d₊` with graph-error transport (proposal §3.2, §7.2)? The window is
  explicit, nonempty by `lunarPLo < lunarPHi`, and avoids the transport estimate; pilot numbers suggest
  a window of about `(0.9819, 1.0181)`.
- **O2.** Division-free expression language for version 1 (Kepler forcing deferred)?
- **O3.** Is the optional high-precision `π` package (SO-PI) wanted in the first black box, or only when
  a non-homogeneous client appears?
- **O4.** Real-analytic graphs and the analytic conjugacy (proposal Theorem A items 1, 3) remain a later
  corollary, as the plan states; confirm they are out of the first freeze.

## 12. Hard rules for every Lean brief (verbatim)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat
   elaboration failure is a design signal to refactor or split the proof, not something to mask with a
   larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused
   modules, preserving public import paths as cheap facades.

Also: never the identifier `EuclideanSpace`; never `native_decide`, `Lean.ofReduceBool`, `axiom`,
`admit`, `unsafe`, `opaque`, `implemented_by`; every file a Lean module; one Lean process at a time
through the compile gate.

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

/-!
# SO-DESIGN: exact draft signatures (track SO, lunar spin-orbit certificate project)

Design document: `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Appendix A is this file). Every proof
and every non-trivial definition body is `sorry`: this file only fixes the Lean surface. It is a
transient elaboration check against the shared `inp` build; it is never imported.

Sections mirror the planned modules (§6 of the design):

* §A `KAM/Certificate/Arith/*`: the late-bound certified-arithmetic interface.
* §B `KAM/Certificate/Poly/*`: exact finite Fourier data and its denotation (`fourierSum`).
* §C `KAM/Certificate/Model/*`: Fourier models (polynomial + sup radius on `T_ρ`, `2π`-degree).
* §D `KAM/Certificate/Expr/*`: the Hamiltonian expression language, its straight-line program,
  symbolic jets, majorants on the domain and composition with the embedding.
* §E `KAM/Certificate/NormBridge`: operator/multilinear norms on `ℂⁿ × ℂⁿ` from partials.
* §F `KAM/Certificate/{Embedding,MatrixCert,Gram,Torsion,Constants,Positivity}`.
* §G `KAM/Certificate/Defs`, `Soundness`: the certificate, the checker, the black box.
* §H `KAM/Certificate/Clock`: the general clock lemma.
* §I `KAM/SpinOrbit/*`: the lunar client (upstream SO-MODEL / SO-DIO names are STAND-INS here,
  copied verbatim from `inp-somodel` dec1fb13 and `inp-sodio` working tree, only so that the
  client signatures elaborate; the real modules replace them).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus

/-! ## §A. Certified arithmetic interface (`KAM/Certificate/Arith/Interface.lean`) -/

/-- A certified arithmetic backend. `val a` is the exact real denoted by `a`. `add`/`mul` may
round (fixed point) or be exact (`ℚ`); `addErr`/`mulErr` bound the rounding error. `upAdd`/`upMul`
round upward and are used on nonnegative radii only. Comparisons are sound one-sided tests. -/
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

/-- The complex number denoted by a `CC`. -/
def CC.toC {α : Type} [CertArith α] (c : CC α) : ℂ := ⟨val c.re, val c.im⟩

/-- Backend 1: exact rationals (`addErr = mulErr = 0`). -/
instance instCertArithRat : CertArith ℚ := sorry

instance instLawfulCertArithRat : LawfulCertArith ℚ := sorry

/-- Backend 2: fixed point, `m ↦ m / 2^P` with floor rounding and tracked ulp errors. -/
structure CertFixed (P : ℕ) where
  m : ℤ

instance instCertArithFixed (P : ℕ) : CertArith (CertFixed P) := sorry

instance instLawfulCertArithFixed (P : ℕ) : LawfulCertArith (CertFixed P) := sorry

/-! ### Transcendental constants (`KAM/Certificate/Arith/Transcendental.lean`) -/

/-- A kernel-computable upper bound for `exp q` (`q ≥ 0`): argument halving `s` times, Taylor
order `N`, Lagrange remainder, then `s` squarings, all in `ℚ`. -/
def ratExpUp (q : ℚ) (s N : ℕ) : ℚ := sorry

theorem exp_le_ratExpUp {q : ℚ} (hq : 0 ≤ q) (s N : ℕ) : Real.exp q ≤ ratExpUp q s N := sorry

/-- A coarse certified enclosure of `π`: `piLoQ < π < piUpQ` (Mathlib's `Real.pi_gt_d6`,
`Real.pi_lt_d6`). -/
def piLoQ : ℚ := 3141592 / 1000000

def piUpQ : ℚ := 3141593 / 1000000

theorem piLoQ_lt_pi : (piLoQ : ℝ) < Real.pi := sorry

theorem pi_lt_piUpQ : Real.pi < piUpQ := sorry

/-- An enclosure `|π - centre| ≤ rad` of `π` at backend precision, used when models of
different `2π`-degrees are added (`CertModel.toDeg`). Data only; validated by the checker. -/
structure PiEnclosure (α : Type) where
  centre : α
  rad : α

/-- Kernel-computable validation of a `π` enclosure: the coarse bounds `piLoQ, piUpQ` when they
suffice, otherwise a Machin-series enclosure (package SO-W1-PI; optional). -/
def checkPiEnclosure {α : Type} [CertArith α] (pe : PiEnclosure α) : Bool := sorry

theorem checkPiEnclosure_sound {α : Type} [CertArith α] [LawfulCertArith α] {pe : PiEnclosure α}
    (h : checkPiEnclosure pe = true) : |Real.pi - val pe.centre| ≤ val pe.rad := sorry

/-- Square-root enclosure check for `ℚ(√d)` frequencies: `0 ≤ lo`, `lo² ≤ d ≤ hi²`. -/
def checkSqrtEnclosure (d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ lo) && decide (lo * lo ≤ d) && decide ((d : ℚ) ≤ hi * hi) && decide (0 ≤ hi)

theorem sqrt_mem_of_checkSqrtEnclosure {d : ℕ} {lo hi : ℚ}
    (h : checkSqrtEnclosure d lo hi = true) :
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

/-- A finite complex Fourier polynomial: key-sorted terms (sortedness is checked, not assumed). -/
structure CertPoly (α : Type) where
  terms : List (CertKey × CC α)

/-- The denoted trigonometric polynomial `Σ c_k e^{2πi k·θ}`. -/
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

/-- Real Fourier data on the half lattice: `a₀ + Σ_{k ≻ 0} (c_k χ_k + c̄_k χ_{-k})`. -/
structure CertRealPoly (α : Type) where
  zero : α
  half : List (CertKey × CC α)

/-- The full (conjugate-symmetric) polynomial of a real datum. -/
def CertRealPoly.toPoly {α : Type} [CertArith α] (P : CertRealPoly α) : CertPoly α := sorry

theorem CertRealPoly.conjugateSymmetric {α : Type} [CertArith α] (n : ℕ)
    (P : CertRealPoly α) : Fourier.ConjugateSymmetric (P.toPoly.coeff n) := sorry

theorem CertRealPoly.eval_real {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α)
    (x : Fin n → ℝ) : (P.toPoly.eval n fun i => (x i : ℂ)).im = 0 := sorry

/-- Exact (or rounded, with the error returned) operations on polynomials. -/
def CertPoly.add {α : Type} [CertArith α] (P Q : CertPoly α) : CertPoly α × α := sorry

/-- `∂_j` of a polynomial without the factor `2π`: coefficient `i k_j c_k` (the factor `2π`
is carried by the model degree). -/
def CertPoly.derivNo2pi {α : Type} [CertArith α] (j : ℕ) (P : CertPoly α) : CertPoly α := sorry

/-- Multiplication by the character `χ_m` (index shift; exact). -/
def CertPoly.shift {α : Type} [CertArith α] (m : CertKey) (P : CertPoly α) : CertPoly α := sorry

/-- `P ↦ P*(θ) := conj (P (conj θ))`: coefficients `c_k ↦ conj c_{-k}` (exact). -/
def CertPoly.conjReflect {α : Type} [CertArith α] (P : CertPoly α) : CertPoly α := sorry

/-! ## §C. Fourier models (`KAM/Certificate/Model/Basic.lean`, `Ops.lean`, `Exp.lean`) -/

/-- A strip weight `w ≥ e^{2πρ}` (checked by `checkWeight`); `|χ_k| ≤ w^{|k|₁}` on `T_ρ`. -/
structure CertWeight where
  rho : ℚ
  w : ℚ

/-- `e^{2πρ} ≤ w` via `ratExpUp` and `piUpQ`. -/
def checkWeight (W : CertWeight) (s N : ℕ) : Bool :=
  decide (0 ≤ W.rho) && decide (ratExpUp (2 * piUpQ * W.rho) s N ≤ W.w)

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

/-- A certified upper bound for `sup_{T_ρ} |f|` of an enclosed `f` (uses `w` and `piUpQ`). -/
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

/-- Re-express a model at another `2π`-degree (exact on the polynomial when no `π` is needed;
otherwise uses the enclosure `pe`, moving the error into the radius). -/
def CertModel.toDeg {α : Type} [CertArith α] (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (a : CertModel α) : CertModel α := sorry

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

/-! ### The a-posteriori exponential (`KAM/Certificate/Model/Exp.lean`)

`E` is a witness for `exp g`. The check computes, at full precision, the models of
`R_j = ∂_j E - (∂_j g) E` (`j < n`) and a scalar pin `|E(0) - exp g(0)|` (`certCExp`). The
soundness proof writes `E = e^g D`, `∂_j D = e^{-g} R_j`, bounds `D - D(0)` along the segment from
`0` to the periodic representative of `θ` (convexity of `T_ρ`, `|Re θ_i| ≤ 1/2`), and pins
`D(0)`. The witness approximates `exp` of the POLYNOMIAL part of `g` (whose derivative is exact);
the radius of `g` enters through `|e^{g+t} - e^g| ≤ |e^g| (e^{|t|} - 1)`. No Taylor series of a
Fourier model is formed. -/

/-- The radius certified for `exp g` by the witness `E` (or `none` if a check fails). -/
def expWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig)
    (g : CertModel α) (E : CertPoly α) : Option α := sorry

theorem expWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {E : CertPoly α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    (⟨0, E, r⟩ : CertModel α).Encloses n W.rho (fun θ => Complex.exp (gf θ)) := sorry

/-! ## §D. The Hamiltonian language (`KAM/Certificate/Expr/*`) -/

/-- The phase index `Fin n ⊕ Fin n` (angles `inl`, actions `inr`) and its basis vector. -/
def phaseBasis {n : ℕ} (a : Fin n ⊕ Fin n) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (sumVec n).symm (Pi.single a 1)

/-- Hamiltonians as finite real-analytic expressions. Angles enter only through the
period-one modes `cos (2π k·θ)`, `sin (2π k·θ)`; every constructor maps reals to reals, so
reality, periodicity, translation invariance and holomorphy are structural. No division
(decision §1.1). -/
inductive HamExpr (n : ℕ) : Type
  | const (q : ℚ)
  | pi
  | action (j : Fin n)
  | cosMode (k : CertKey)
  | sinMode (k : CertKey)
  | add (a b : HamExpr n)
  | mul (a b : HamExpr n)
  | pow (a : HamExpr n) (m : ℕ)
  | exp (a : HamExpr n)
  | sin (a : HamExpr n)
  | cos (a : HamExpr n)

/-- `2π k·θ`. -/
def modePhase (n : ℕ) (k : CertKey) (θ : Fin n → ℂ) : ℂ :=
  2 * Real.pi * ∑ i, (certKeyFun n k i : ℂ) * θ i

/-- The entire function denoted by an expression. -/
def HamExpr.eval {n : ℕ} : HamExpr n → (Fin n → ℂ) × (Fin n → ℂ) → ℂ
  | .const q, _ => (q : ℂ)
  | .pi, _ => (Real.pi : ℂ)
  | .action j, z => z.2 j
  | .cosMode k, z => Complex.cos (modePhase n k z.1)
  | .sinMode k, z => Complex.sin (modePhase n k z.1)
  | .add a b, z => a.eval z + b.eval z
  | .mul a b, z => a.eval z * b.eval z
  | .pow a m, z => a.eval z ^ m
  | .exp a, z => Complex.exp (a.eval z)
  | .sin a, z => Complex.sin (a.eval z)
  | .cos a, z => Complex.cos (a.eval z)

theorem HamExpr.contDiff_eval {n : ℕ} (e : HamExpr n) : ContDiff ℂ ⊤ e.eval := sorry

theorem HamExpr.eval_add_int {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (k : Fin n → ℤ) : e.eval (z.1 + (fun i => (k i : ℂ)), z.2) = e.eval z := sorry

theorem HamExpr.eval_real {n : ℕ} (e : HamExpr n) (θ I : Fin n → ℝ) :
    (e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := sorry

/-- Straight-line program over `ℂ` (internal). Operands are earlier slot numbers; a constant
carries its `2π`-degree; `char k` is `e^{2πi k·θ}`. Nonlinearity is `exp` only. -/
inductive SlpOp : Type
  | const (re im : ℚ) (deg : ℤ)
  | action (j : ℕ)
  | char (k : CertKey)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | exp (a : ℕ)

structure Slp where
  ops : List SlpOp

/-- Value of slot `i` at the phase point `z` (out-of-range operands read `0`). -/
def Slp.val (n : ℕ) (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) (i : ℕ) : ℂ := sorry

/-- The program and slot tables of the jet of order three of an expression: slot of `H`,
of `∂_a H`, `∂_a ∂_b H`, `∂_a ∂_b ∂_c H` (`a, b, c` phase indices in `sumVec` order).
Forward-mode differentiation with sharing, zero/constant folding and dependency pruning. -/
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

theorem HamExpr.jet_d1 {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (a : Fin n ⊕ Fin n) :
    e.jet.prog.val n z (e.jet.d1.getD (phaseNat a) 0) = fderiv ℂ e.eval z (phaseBasis a) :=
  sorry

theorem HamExpr.jet_d2 {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (a b : Fin n ⊕ Fin n) :
    e.jet.prog.val n z ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      iteratedFDeriv ℂ 2 e.eval z ![phaseBasis a, phaseBasis b] := sorry

theorem HamExpr.jet_d3 {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ))
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

/-- Majorant of every slot on `D` (no embedding): `|c|`, `|c_j| + r_j`, `w_H^{|k|₁}`, sums,
products, `|e^x| ≤ e^{|x|}` (`ratExpUp`). -/
def Slp.majorants (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ)
    (s N : ℕ) : List ℚ := sorry

theorem Slp.norm_val_le_majorant {n : ℕ} (p : Slp) {WH : CertWeight} {centre radius : List ℚ}
    {s N : ℕ} (hW : checkWeight WH s N = true) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ) :
    ‖p.val n z i‖ ≤ (p.majorants n WH centre radius s N).getD i 0 := sorry

/-- The embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` from real Fourier data. -/
structure CertEmbedding (α : Type) where
  angleDeg : List ℤ
  angle : List (CertRealPoly α)
  actionDeg : List ℤ
  action : List (CertRealPoly α)

def CertEmbedding.eval {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => θ i + (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
      ((K.angle.getD i.val ⟨CertArith.ofInt 0, []⟩).toPoly.eval n θ),
    fun i => (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
      ((K.action.getD i.val ⟨CertArith.ofInt 0, []⟩).toPoly.eval n θ))

theorem CertEmbedding.differentiable_eval {α : Type} [CertArith α] (n : ℕ)
    (K : CertEmbedding α) : Differentiable ℂ (K.eval n) := sorry

theorem CertEmbedding.isPrimaryOnStrip {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (ρ : ℝ) : IsPrimaryOnStrip (K.eval n) ρ := sorry

theorem CertEmbedding.isRealOnReals {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) :
    IsRealOnReals (K.eval n) := sorry

/-- Exp witnesses: one per `exp` slot of the jet program (slot order), and the character table
keyed by the normalized index (coordinates with syntactically zero `U_j` zeroed; `-k` uses
`conjReflect`). -/
structure Witnesses (α : Type) where
  expWit : List (CertPoly α)
  charWit : List (CertKey × CertPoly α)

/-- Composition of the jet slots with `K`: one model per requested slot, or `none` if a
witness check fails. -/
def Slp.compose {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) := sorry

theorem Slp.compose_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (p : Slp)
    (K : CertEmbedding α) (wit : Witnesses α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (wanted : List ℕ) {ms : List (CertModel α)}
    (h : Slp.compose n p K wit W cfg pe wanted = some ms) :
    ∀ idx < wanted.length, (ms.getD idx ⟨0, ⟨[]⟩, CertArith.ofInt 0⟩).Encloses n W.rho
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

/-- Row-sum bound for `DX_H` from second partials of a `C²` Hamiltonian. -/
theorem norm_fderiv_hamiltonianVectorFieldℂ_le {n : ℕ} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hH : ContDiff ℂ 2 H) (z : (Fin n → ℂ) × (Fin n → ℂ)) {B : ℝ}
    (hB : ∀ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
      ‖iteratedFDeriv ℂ 2 H z ![phaseBasis (Sum.swap a), phaseBasis b]‖ ≤ B) :
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ B := sorry

/-- Bound for `D²X_H` from third partials of a `C³` Hamiltonian. -/
theorem norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le {n : ℕ}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hH : ContDiff ℂ 3 H) (z : (Fin n → ℂ) × (Fin n → ℂ))
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

/-- Entrywise enclosure of a matrix-valued function on `T_ρ`. -/
def ModelMatrix.Encloses {α : Type} [CertArith α] (n : ℕ) {ι : Type*} (idx : ι → ℕ) (ρ : ℝ)
    (M : ModelMatrix α) (F : (Fin n → ℂ) → Matrix ι ι ℂ) : Prop :=
  ∀ i j, ((M.getD (idx i) []).getD (idx j) ⟨0, ⟨[]⟩, CertArith.ofInt 0⟩).Encloses n ρ
    (fun θ => F θ i j)

/-- The Gram models `DKᵀ DK` (bilinear, `dotℂ`), computed at reduced precision. -/
def gramModels {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (W : CertWeight)
    (cfg : ModelConfig) (pe : PiEnclosure α) : ModelMatrix α := sorry

theorem gramModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    (K : CertEmbedding α) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) :
    (gramModels n K W cfg pe).Encloses n (fun i : Fin n => i.val) W.rho
      (gramMatrix (K.eval n)) := sorry

/-- Gram check: with the model-matrix witness `B ≈ G⁻¹`, `sup_{T_ρ}` row sums of `I - B G`
give `δ < 1`, and `sup ‖B‖/(1 - δ) ≤ σB - μ`. Returns the certified `(δ, β)`. -/
def gramCheck {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List
    (CertPoly α))) (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α) (σBμ : ℚ) :
    Option (α × α) := sorry

theorem gramCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    (K : CertEmbedding α) (Binv : List (List (CertPoly α))) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (σBμ : ℚ) {δβ : α × α}
    (h : gramCheck n K Binv W cfg pe σBμ = some δβ) :
    ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix (K.eval n) θ)⁻¹ i j‖ ≤ σBμ := sorry

/-- Entrywise models of the extended torsion `extendedTorsion H K ω` on `T_ρ`, built from the
jet compositions (`DX_H ∘ K`, `DH ∘ K`), the Gram witness with its certified radius, and
`D(G⁻¹)[ω] = -G⁻¹ (DG[ω]) G⁻¹` (`KAM.fderiv_matrix_inv_apply`). -/
def torsionModels {α : Type} [CertArith α] (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (ω : List (CC α)) (ωRad : α)
    (W : CertWeight) (cfg : ModelConfig) (pe : PiEnclosure α) : Option (ModelMatrix α) :=
  sorry

/-- The averaged bordered torsion check: centre `C` = zero modes, radius matrix `R`; with the
constant witness `S`, `‖I - S C‖ + ‖S‖ ‖R‖ =: δ_T < 1` and `‖S‖/(1-δ_T) ≤ σT - μ`. -/
def torsionAvgCheck {α : Type} [CertArith α] (T : ModelMatrix α) (S : List (List (CC α)))
    (σTμ : ℚ) : Bool := sorry

theorem torsionAvgCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {T : ModelMatrix α}
    (hT : T.Encloses n (fun a : Fin n ⊕ Unit => Sum.elim (fun i => i.val) (fun _ => n) a) ρ
      (KAM.Iso.extendedTorsion H K ω))
    (hcont : ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion H K ω θ a b)
      (complexStrip n ρ))
    (S : List (List (CC α))) (σTμ : ℚ) (h : torsionAvgCheck T S σTμ = true) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K ω).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K ω)⁻¹ i j‖ ≤ σTμ := sorry

/-- A kernel-computable upper bound for `c_R = max 1 (cohConst n τ)` (`piLoQ`, `e > 2.718`). -/
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

/-- Sum-of-squares lower bound on the real torus: `Re f - m = |g|² + h` with `sup |h| ≤ m'`
(`|g|² = g · g*` on reals; `g* = conjReflect g`). -/
def checkRealLowerBound {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig)
    (f : CertModel α) (m : ℚ) (g : CertPoly α) : Bool := sorry

theorem checkRealLowerBound_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig)
    {f : CertModel α} {ff : (Fin n → ℂ) → ℂ} (hf : f.Encloses n W.rho ff) {m : ℚ}
    {g : CertPoly α} (h : checkRealLowerBound W cfg f m g = true) (x : Fin n → ℝ) :
    (m : ℝ) ≤ (ff fun i => (x i : ℂ)).re := sorry

/-! ## §G. The certificate, the checker and the black box (`KAM/Certificate/Defs.lean`,
`Soundness.lean`) -/

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

/-- A frequency in `ℚ(√d)ⁿ`: `ω*_i = a_i + b_i √d`, with a checked rational enclosure of `√d`. -/
structure CertFreq where
  d : ℕ
  coords : List (ℚ × ℚ)
  sqrtLo : ℚ
  sqrtHi : ℚ

def CertFreq.toReal (n : ℕ) (F : CertFreq) : Fin n → ℝ :=
  fun i => ((F.coords.getD i.val (0, 0)).1 : ℝ) +
    ((F.coords.getD i.val (0, 0)).2 : ℝ) * Real.sqrt F.d

/-- The certificate: problem data, numerical witnesses and controls. -/
structure TorusCertificate (n : ℕ) (α : Type) where
  params : CertParams
  ham : HamExpr n
  /-- `D = T_{ρ_H} × polydisc(centre, radius)` -/
  weightH : CertWeight
  centre : List ℚ
  radius : List ℚ
  freq : CertFreq
  emb : CertEmbedding α
  /-- weight of the strip `T_ρ` (its `rho` must equal `params.rho`) -/
  weight : CertWeight
  wit : Witnesses α
  gramInv : List (List (CertPoly α))
  torsInv : List (List (CC α))
  cfgFull : ModelConfig
  cfgLow : ModelConfig
  piEnc : PiEnclosure α
  /-- SOS witnesses etc. are client data (graph checks), not part of the black box -/
  expHalvings : ℕ
  expOrder : ℕ

section Denotation

variable {n : ℕ} {α : Type} [CertArith α]

def TorusCertificate.D (c : TorusCertificate n α) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  certDomain n c.weightH.rho c.centre c.radius

def TorusCertificate.H (c : TorusCertificate n α) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := c.ham.eval

def TorusCertificate.K (c : TorusCertificate n α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := c.emb.eval n

def TorusCertificate.ωstar (c : TorusCertificate n α) : Fin n → ℝ := c.freq.toReal n

end Denotation

/-! The sub-checks (each `Bool`, each provable by `decide +kernel` on its own). -/

/-- Shapes, positivity, `2 ≤ n`, `n - 1 ≤ τ`, `ρ∞ < ρ`, `1 < s < σω`, ray margins (with the
`√d` enclosure), `γ ≤ γbar`, `0 ≤ e`, `ω* ≠ 0`, weights. -/
def checkStatic {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The five bounds `‖DH‖, ‖X_H‖, ‖DX_H‖, ‖D²X_H‖, ‖D²H‖ ≤ M` on `D` (jet majorants). -/
def checkHamBounds {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `ball (K θ) μ ⊆ D` on `T_ρ` and `‖DK‖ ≤ σK - μ` (row sums of `DK` models). -/
def checkEmbedding {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `sup_{T_ρ} ‖X_H(K) - DK (s ω*)‖ ≤ e` at full precision. -/
def checkInvariance {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `‖⟨H ∘ K⟩ - E₀‖ ≤ e`. -/
def checkEnergy {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The Gram certificate (`gramCheck`) with bound `σB - μ`. -/
def checkGram {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The averaged bordered torsion certificate at `s ω*` with bound `σT - μ`. -/
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
denoted by `c` (`IsDiophantine` excepted: it is the external input). -/
structure G1Hyps (c : TorusCertificate n α) : Prop where
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
  hωstar : c.ωstar ≠ 0
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
  hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • c.ωstar)).det
  hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • c.ωstar))⁻¹ i j‖ ≤
    (c.params.σT : ℝ) - c.params.μ
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hν1 : (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖c.ωstar‖
  hν2 : (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖c.ωstar‖
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hE : ∀ θ ∈ complexStrip n c.params.rho,
    ‖invarianceError c.H c.K ((c.params.s : ℝ) • c.ωstar) θ‖ ≤ c.params.err
  hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err
  hC1 : Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1
  hdisp : Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp

/-- The output of the black box: the conclusion of `IG1Body` for the denoted data, with the
explicit rational displacement bound `disp` in place of `C₂ e/(γ²ρ^{2τ})`. -/
def CertifiedTorus (c : TorusCertificate n α) : Prop :=
  ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < c.params.σω ∧ DifferentiableOn ℂ Kinf (complexStrip n c.params.rhoInf) ∧
    IsPrimaryOnStrip Kinf c.params.rhoInf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, invarianceError c.H Kinf (sinf • c.ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, c.H (Kinf θ) = ((c.params.E0 : ℝ) : ℂ)) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, Metric.ball (Kinf θ) ((c.params.μ : ℝ) / 2) ⊆ c.D) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf,
      ‖fderiv ℂ Kinf θ‖ ≤ (c.params.σK : ℝ) - (c.params.μ : ℝ) / 2) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, ‖Kinf θ - c.K θ‖ ≤ c.params.disp) ∧
    ‖sinf • c.ωstar - (c.params.s : ℝ) • c.ωstar‖ ≤ c.params.disp

variable [LawfulCertArith α]

/-- Sub-check soundness (one theorem per sub-check; listed for the package table). -/
theorem checkStatic_sound {c : TorusCertificate n α} (h : checkStatic c = true) :
    2 ≤ n ∧ (n : ℝ) - 1 ≤ (c.params.tau : ℝ) ∧ c.ωstar ≠ 0 := sorry

theorem checkHamBounds_sound {c : TorusCertificate n α} (h : checkHamBounds c = true) :
    ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧ ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M := sorry

theorem checkInvariance_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkInvariance c = true) : ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • c.ωstar) θ‖ ≤ c.params.err := sorry

/-- All hypotheses of `g1_explicit` from a passing check. -/
theorem checkTorusCertificate_hyps {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) : G1Hyps c := sorry

/-- **The black box.** A passing certificate with a proved Diophantine input yields an exact
analytic invariant torus `K_∞` within `disp` of `K`, through the sealed
`KAM.Iso.Apost.g1_explicit` instantiated at
`(n, τ, ρ, ρ∞, M, σK, σB, σT, μ, γbar, σω, ν, ω*) := (n, c.tau, c.rho, c.rhoInf, c.M, c.σK, c.σB,
c.σT, c.μ, c.γbar, c.σω, c.nuRay, c.ωstar)` and applied to
`(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.s, c.γ, c.err, c.E0)`. -/
theorem checkTorusCertificate_sound {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) c.ωstar) : CertifiedTorus c :=
  sorry

end Black

/-! ## §H. The clock lemma (`KAM/Certificate/Clock.lean`) -/

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

end KAM.Certificate

/-! ## §I. The lunar client (`KAM/SpinOrbit/*`) -/

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-! ### STAND-INS (verbatim from SO-MODEL `inp-somodel` dec1fb13 / SO-DIO `inp-sodio`); the
real modules `KAM.SpinOrbit.Model`, `KAM.Certificate.QuadraticDiophantine` replace these. -/

def soEcc : ℝ := 549 / 10000

def soEps : ℝ := 69 / 200000

def soCoeffPoly {R : Type*} [Field R] (e : R) : ℕ → R
  | 1 => -e / 4 + e ^ 3 / 32
  | 2 => 1 / 2 - 5 * e ^ 2 / 4 + 13 * e ^ 4 / 32
  | 3 => 7 * e / 4 - 123 * e ^ 3 / 32
  | 4 => 17 * e ^ 2 / 4 - 115 * e ^ 4 / 12
  | 5 => 845 * e ^ 3 / 96 - 32525 * e ^ 5 / 1536
  | 6 => 533 * e ^ 4 / 32
  | 7 => 228347 * e ^ 5 / 7680
  | _ => 0

def soEccQ : ℚ := 549 / 10000

def soEpsQ : ℚ := 69 / 200000

def soAQ (m : ℕ) : ℚ := soCoeffPoly soEccQ m

def soA (m : ℕ) : ℝ := soCoeffPoly soEcc m

def soModes : Finset ℕ := Finset.Icc 1 7

def soV (q φ : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * Real.pi * (2 * q - m * φ))

def soVC (q φ : ℂ) : ℂ :=
  -(soEps : ℂ) * ∑ m ∈ soModes, (soA m : ℂ) * Complex.cos (2 * Real.pi * (2 * q - m * φ))

def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)

def lunarG : ℝ := (Real.sqrt 5 - 1) / 2

def lunarNuMinus : ℝ := 1 - 1 / (40 + lunarG)

def lunarNuPlus : ℝ := 1 + 1 / (40 + lunarG)

theorem lunarNuMinus_half_isDiophantine :
    IsDiophantine (1 / 42) 1 ![lunarNuMinus / 2, 1 / 2] := sorry

theorem lunarNuPlus_half_isDiophantine :
    IsDiophantine (1 / 42) 1 ![lunarNuPlus / 2, 1 / 2] := sorry

/-- Upstream interface (SO-MODEL item 3, name to reconcile): the autonomous complex Hamiltonian
`𝓗(θ, I) = I₁ + I₀²/2 + V(θ₀, θ₁)`, angles `(q, φ)`, actions `(p, J)`. -/
def soHamC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ := z.2 1 + z.2 0 ^ 2 / 2 + soVC (z.1 0) (z.1 1)

/-! ### `KAM/SpinOrbit/HamExpr.lean` -/

/-- `𝓗` in the expression language: `J + p²/2 + Σ_m (-ε A_m) cos(2π(2q - mφ))`. -/
def soHamExpr : HamExpr 2 :=
  .add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    ((List.range 7).foldr (fun m acc =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, -((m : ℤ) + 1)])) acc)
      (.const 0)))

theorem soHamExpr_eval (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soHamExpr.eval z = soHamC z := sorry

theorem soHamExpr_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soHamExpr.eval z (phaseBasis (.inr 1)) = 1 := sorry

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
margin `m` for `∂_{θ₀} q` and the range `[pLo, pHi]` of `p` on the real torus (SOS witnesses). -/
structure SoGraphCert (α : Type) where
  base : TorusCertificate 2 α
  mono : ℚ
  pLo : ℚ
  pHi : ℚ
  sosMono : CertPoly α
  sosLo : CertPoly α
  sosHi : CertPoly α

def checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool := sorry

/-- The barrier produced by a passing graph certificate; the band is widened by `disp`. -/
theorem soBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    (hham : g.base.ham = soHamExpr) (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) g.base.ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  sorry

/-! ### `KAM/SpinOrbit/Barrier.lean`: two barriers confine, globally and uniquely -/

theorem so_confinement {lo₁ hi₁ lo₂ hi₂ : ℝ} (B₁ : SoBarrier lo₁ hi₁) (B₂ : SoBarrier lo₂ hi₂)
    (x₀ : ℝ × ℝ × ℝ) (h₁ : B₁.P x₀.1 x₀.2.2 < x₀.2.1) (h₂ : x₀.2.1 < B₂.P x₀.1 x₀.2.2) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = x₀ ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, B₁.P (z t).1 (z t).2.2 < (z t).2.1 ∧ (z t).2.1 < B₂.P (z t).1 (z t).2.2) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = x₀ ∧ ∀ t, HasDerivAt y (soField (y t)) t) → y = z := sorry

/-! ### `KAM/SpinOrbit/LunarCertificate.lean`, `LunarConfinement.lean` -/

/-- The backend is fixed after SO-REPLAY (decision §1.3); `ℚ` is the placeholder. -/
abbrev SoBackend : Type := ℚ

/-- Generated data (`KAM/SpinOrbit/Data/{Lower,Upper}/*`); bodies are the generated terms. -/
def lunarLowerCert : SoGraphCert SoBackend := sorry

def lunarUpperCert : SoGraphCert SoBackend := sorry

theorem lunarLowerCert_ham : lunarLowerCert.base.ham = soHamExpr := sorry

theorem lunarLowerCert_passes : checkTorusCertificate lunarLowerCert.base = true := sorry

theorem lunarLowerGraph_passes : checkSoGraph lunarLowerCert = true := sorry

theorem lunarLowerCert_ωstar : lunarLowerCert.base.ωstar = ![lunarNuMinus / 2, 1 / 2] := sorry

theorem lunarUpperCert_ωstar : lunarUpperCert.base.ωstar = ![lunarNuPlus / 2, 1 / 2] := sorry

/-- The certified initial momentum window (rationals read from the data). -/
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
