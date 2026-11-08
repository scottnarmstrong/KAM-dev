# SJS-RIGOR: how to make the two SJS floating-point results rigorous

6 November 2026, branch `inp-bsjs`. Scoping only: no Lean, no `lake build`, no producer run. The only computation is
a cost formula evaluated in Python (formulas in 3.3–3.4). Nothing here is frozen.

The two results:
- **SJSU gate 2** (PR #8): near-torus approximate integrals for the secular Sun–Jupiter–Saturn–Uranus model
  `SJSU18-O2`.
- **SJS-X1** (PR #9): the Fourier support of FH25's planar Sun–Jupiter–Saturn torus.

**Citations.** `path:line` is this branch; `main:path:line` marks files only on `main`. Both PRs are now merged into
`inp` (PR #9 at `b0af27263`, PR #8 at `9ddda9b7c`); their files are cited at their repository paths, and every cited PR
file is byte-identical on `inp` and on `refs/pr/8` / `refs/pr/9` (checked with `git diff --quiet`).

**Labels.** **measured**: a cited receipt. **proved**: a compiled Lean theorem at the cited line. **estimate**: this
plan's arithmetic or judgement, with its method stated next to it.

## 0. Summary

**Gate 2 can become a literal theorem in the Hénon–Heiles style:** for every initial state in an explicit neighbourhood
Q of the nominal secular state, `SJSU18-O2` has a unique solution on [−T, T], T = 5·10⁹ yr, along which the three
eccentricities stay in explicit intervals.
- **The confinement theorem exists:** `hamiltonian_approxIntegrals_confinement`
  (`KAM/Application/Confinement/ApproxIntegral.lean:295-307`, proved). Its hypotheses are exactly the gate's checks.
- **Missing: a checker** that proves those hypotheses for literal Fourier–Taylor observables on a tube of action width
  δ, in exact or ball arithmetic. It needs a modal polar chart with a canonical shift, Fourier models of half-integer
  powers of the torus graph, and a packed Fourier–Taylor layer.
- **Existing checkers cannot do it.** `checkTorusChain_sound` takes exact-ℚ Fourier–Taylor *polynomial* Hamiltonians
  (`KAM/EffectiveStability/FT/Basic.lean:34-48`), which the model in polar coordinates is not; a list checker would be
  3–4 orders too slow (3.4).
- **Estimates:** 7–13k new Lean lines; kernel arithmetic 2.5–250 CPU-h (central 4–6); ledger 0.6–12.5 GB of literals;
  gates before any Lean under 3 CPU-h in total.

**X1 is a measurement, not a statement.** Its rigorous counterpart is sjs-plan's M3, a certified KAM torus of FH25's
planar three-body problem (`docs/explorations/sjs-plan.md:57-59`).
- **The theorem form exists:** `CertifiedTorus` (`KAM/Certificate/Defs.lean:356-368`) through route B.
- **What X1 changes:** the cost narrows to 10–94 CPU-h (one `Nat` per model or 8 GB shards; 107–590 under the default
  `Nat` limit) and a 55–140 GB ledger (`scripts/sjs/x1/results/x1_cost.json`; `sjs-x1-support.md:27-33`); the
  near-resonant mode k₀ sets the generator's residual target (`sjs-x1-support.md:153-174`).
- **Still missing:** a 48-digit torus (`sjs-x1-support.md:63`, `:199`); a Kepler node, which `HamExpr` lacks
  (`KAM/Certificate/Expr/Basic.lean:39-52`); packed 3-D blocks; an enclosure of the sampled majorants; rented
  hardware. No double-double torus from X1 is certifiable as it stands.
- **B5** (`certifiedTorus_confinement`) would add finite-time stability near the torus; with today's Cauchy constant it
  is expected to be weak (2.3).

**Recommendation.** Certify gate 2 first: it is 1–2 orders cheaper than M3 and its confinement theorem is proved. Run
gates SR-1 to SR-7 (section 4) before any Lean. Keep X1 on sjs-plan's track (gates X2, X3, X6, E1; its eight pending
decisions). Section 6 asks 10 owner decisions.

## 1. Target theorems

### 1.1 Gate 2 → T2-CONF, literal finite-time confinement for SJSU18-O2

- **Model.** H is `SJSU18-O2` exactly as published: 7,941 complex (38,466 real) coefficients, degrees 2–18, written to
  25 digits (`docs/explorations/sjsu-model-recovery.md:11-13`, `:317-349`), read as exact decimal rationals in the real
  form (ξ, η) ∈ ℝ³ × ℝ³ with the repository ordering q = η, p = ξ
  (`docs/explorations/sjsu-effective-stability.md:94-100`). The owner already ruled that phase 1 certifies this
  polynomial (`sjsu-model-recovery.md:389-395`).
- **Nominal point.** z⋆ is the Table 1 map of the same ruling, as decimal literals.
- **Initial set.** Q = {z : ‖z − z⋆‖∞ ≤ r} with a rational r (alternatives: decision 3). Estimate r ≈ δ/(2 Lip F)
  ≈ 10⁻⁵ at δ = 10⁻⁶, with Lip F ≈ 0.05 (F ≈ |w|² − B₀ at |w| ≈ 0.018); gate SR-7 measures it.
- **Claim.** For every z₀ ∈ Q there is a solution z of ż = X_H(z), z(0) = z₀, on an open interval containing [−T, T],
  T = 5·10⁹ yr; every solution through z₀ agrees with it (the uniqueness clause of `ApproxIntegral.lean:241-257`); and
  for |t| ≤ T and j = J, S, U, e_j^lo ≤ e_j(z(t)) ≤ e_j^hi, with e_j computed from Γ_j = (ξ_j² + η_j²)/2 and Λ_j
  (`sjsu-effective-stability.md:185-187`).
- **Constants.** Rational literals fixed before the run: r, T, six eccentricity bounds. The measured float tube ranges
  at δ = 10⁻⁶ are [0.02692, 0.06101], [0.01058, 0.08439], [0.00708, 0.06201] (`sjsu-near-torus-gate.md:211-219`); the
  statement rounds them outward, e.g. [0.026, 0.062], [0.010, 0.085], [0.007, 0.063].
- **Proof-internal.** F_j, the tube, η and D stay in the proof, as for Hénon–Heiles: the only premise is z₀ ∈ Q. The
  model statement is the sealed `henonHeiles_confinement`
  (`KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean:32-48`: H inline, a box Q, T = 10¹⁰, existence,
  uniqueness, action bounds). Difference: 38,466 terms cannot be inline, so H must be a frozen *data definition*
  (decision 7).
- **Kind.** A literal application; **owner freeze approval needed.** It instantiates
  `hamiltonian_approxIntegrals_confinement` (`ApproxIntegral.lean:295-307`), an ordinary sufficient-condition theorem;
  H is C² on the open W = {w_j ≠ 0} that the polar chart needs (`sjsu-near-torus-gate.md:304-308`). The eccentricity
  bounds are a separate enclosure over the closure of D (inside the tube), since e_j is not affine in F.

**Sufficient-condition layer (ordinary, no freeze).** A new `checkTube_sound`: a passing tube certificate (F, τ̃, S, δ,
κ, η, a, b) gives `hη` (bracket bound on the closure of D), `hsep` (frontier separation), `hQ`, `hQD`, and a compact
closure of D inside W. Every hypothesis of `ApproxIntegral` is used as stated; no conclusion-shaped premise enters
(AGENTS.md rule 6).

**Optional T2-KAM (all time, on one torus).** An analytic invariant 3-torus of `SJSU18-O2` with frequency s∞ω*, ω*
explicit and (γ, τ)-Diophantine, within `disp` of the numerical torus through the nominal point. Route: `CertifiedTorus`
through the v2/packed certifier, with H as a `HamExpr` in modal polar action–angle form (actions, `sqrt`, `pow`,
`cosMode`/`sinMode`; `KAM/Certificate/Expr/Basic.lean:39-52`), as LG00's √(I₁I₂) model did
(`docs/explorations/sjs-lg00-scout.md`). It confines nothing in three degrees of freedom
(`docs/explorations/program-b-plan.md:660-662`); its cost is unmeasured (7,941 terms against LG00's 69).

### 1.2 X1 → T1-KAM (the M3 headline), and the optional T1-NEAR

**X1 itself** measures S(L) and β on a double-double torus: in-band residual 6·10⁻³², out-of-band truncation
2.3·10⁻²⁶ (`sjs-x1-support.md:107-110`), "no enclosure of anything" (`:60`). The support is a cost input; no theorem
says "S(L) = …".

**T1-KAM** (sjs-plan package A1, **owner freeze approval needed**, `sjs-plan.md:422`):
- **Model.** H_FH is FH25 (2.1)–(2.2), the reduced planar Sun–Jupiter–Saturn problem, with exact decimal constants
  (masses (0.9546, 0.2856), μ = 10⁻³, FH's angular momentum; `sjs-x1-support.md:67-72`), written in the synodic
  regular chart (Λ₁, I₅, I₆; b₁, b₂, b₃) (`sjs-plan.md:77-82`).
- **Frequency.** ω* is the explicit cubic-field vector with |ω* − ω_FH| ≤ 10⁻⁸, certified γ = 2.8·10⁻⁷ at τ = 2
  (`sjs-plan.md:380-398`).
- **Claim.** There are s∞ ∈ (1, σ_ω) and an embedding K∞ of T³, holomorphic on a strip, real on reals and primary, with
  H∘K∞ ≡ E₀, DK∞·(s∞ω*) = X_H∘K∞ exactly, and ‖K∞ − K_c‖ ≤ `disp`: the conjunction `CertifiedTorus`
  (`KAM/Certificate/Defs.lean:356-368`). Physical form: for every θ₀, t ↦ K∞(θ₀ + s∞ω*t) solves Hamilton's equations for
  all t ∈ ℝ, with eccentricities in explicit intervals, through LG00's transport layer (`KAM/Application/Physical.lean`,
  `KAM/Application/Transport.lean:51-91`).
- **Kind.** A literal application of route B isoenergetic; sjs-plan decision 6 says no new theorem work is needed
  (`sjs-plan.md:44`). The Diophantine property is a separate hypothesis of the soundness theorems, not part of
  `CertifiedTorus` (`main:KAM/CertificateSharp/Packed/Trunc/Route.lean:376`); package D1 discharges it
  (`sjs-plan.md:429`). Horizon: all time, on the torus only.

**T1-NEAR (optional corollary).** `certifiedTorus_confinement`
(`KAM/EffectiveStability/CertifiedTorusRoute.lean:49-71`) turns a `CertifiedTorus` into existence past [−T, T],
uniqueness, and chart-action drift ≤ η|t| for |w₀.2| ≤ a, with η ≥ C₃B²/2 and C₃ = `routeC3` = 64(Mμ/2)/r³
(`:39-40`). It also needs `RouteChecks` (`KAM/EffectiveStability/TorusRoute/Bound.lean:35-42`), including the
projection bound n(κc + disp/δ) < 1. A freeze only if headlined; 2.3 says why it is expected to be weak.

### 1.3 What needs owner freeze approval

| Object | Kind | Freeze? |
|---|---|---|
| T2-CONF; the `SJSU18-O2` data definition and z⋆ it names | literal application | yes (decisions 3, 4, 7) |
| `checkTube_sound`, chart lemmas, packed FT layer | ordinary infrastructure | no; audited |
| T2-KAM | literal application | yes, if pursued (decision 1) |
| T1-KAM (sjs-plan A1) | literal application | yes; sjs-plan decisions 1–8 pending |
| T1-NEAR | instance of `certifiedTorus_confinement` | only if headlined |

## 2. Routes, using what exists

### 2.1 What exists (proved unless marked)

- **Approximate-integral first exit.** `KAM/Application/Confinement/ApproxIntegral.lean`: a priori bound `:167-175`;
  maximal solution `:198-238`; Hamiltonian on an open W `:295-307`; W = univ `:312-325`; with observables `:331-349`.
- **B1-T, sealed.** `KAM/Frozen/EffectiveStability/TorusConfinement.lean:33-59`: Ψ symplectic on {|J| < b + ε},
  H∘Ψ = N(J) + R with R periodic, |∂_φR| ≤ η on |J| ≤ b, a + Tη < b ⇒ existence past ±T, uniqueness, drift ≤ η|t|.
- **B1-E, sealed.** `KAM/Frozen/EffectiveStability/OscillatorConfinement.lean:103-136`: the same on oscillator discs.
- **Torus chain checker.** `KAM/EffectiveStability/TorusChainCheck.lean:117-135`: a Lie chain of `FTPoly` generators
  with exact `ftEqCheck` identities; **H must be an `FTPoly` with ℚ coefficients** (`FT/Basic.lean:34-48`), and the
  conclusion is about `ftEvalR c.H` itself.
- **Oscillator chain checker.** `KAM/EffectiveStability/OscillatorChainCheck.lean:120-144`: Cartesian polynomials over
  `CertCoeff K` (ℚ, ℚ(√2); `KAM/EffectiveStability/Poly/Coeff.lean:32`).
- **Physical boxes.** `TorusChainPhysical.lean:118-143`, `OscillatorChainPhysical.lean:259-293`,
  `OscillatorChainPhysicalDisc.lean:52-84` (all in `KAM/EffectiveStability/`).
- **B5.** `KAM/EffectiveStability/CertifiedTorusRoute.lean:49-71`, design `docs/tracks/B/B5-DESIGN.md`:
  `CertifiedTorus` + `RouteChecks` ⇒ B1-T near the torus with η = C₃b²/2.
- **Canonical chart chains.** `KAM/EffectiveStability/ChartChain.lean:30-97`: `IsCanonicalChart` is closed under
  composition.
- **Poisson bracket and a second approximate-integral consumer.** `KAM/Application/LambdaDrift/Poisson.lean:42`
  (`pb a b w = Da(w) X_b(w)`); `KAM/Application/LambdaDrift/Bridge.lean:85` (HD 11964).
- **v2 certifier.** `KAM/Certificate/Defs.lean:303-368`; `HamExpr` (`sqrt`, `div`, `exp`, trigonometric modes) at
  `KAM/Certificate/Expr/Basic.lean:39-52`.
- **Packed route (main).** `main:KAM/CertificateSharp/Packed/`: GMP-resident packed Fourier models, jets, Gram,
  torsion; LG00 was proved this way (`sjs-x1-support.md:178-182`).

### 2.2 Gate 2: the route

**`ApproxIntegral` is a confinement statement**, a sufficient-condition theorem; it is neither a transfer lemma nor a
stand-in. Hypotheses of `hamiltonian_approxIntegrals_confinement` (`ApproxIntegral.lean:295-302`): W open, H C² on W;
D open with compact closure inside W; each F_j differentiable on W; |fderiv F_j z (X_H z)| ≤ η_j on the closure of D;
Q ⊆ D with a_j ≤ F_j ≤ b_j on Q; T ≥ 0; every frontier point of D has some j with F_j < a_j − Tη_j or
F_j > b_j + Tη_j. Conclusion: the maximal solution exists past ±T, stays in D, and drifts ≤ η_j|t| (`:303-306`).

**Instantiation.** The gate's D, Q, a = c − δ/2, b = c + δ/2 (`sjsu-near-torus-gate.md:157-167`) give T < δ/(2η).
Elementary argument: the face check puts every tube-face point outside the closure of D, so the frontier of D lies
where some |F_j − c_j| = δ, and separation reads δ > δ/2 + Tη_j.

**Chart (used only inside `checkTube_sound`): z ↦ w ↦ (I, q) ↦ (u, q).**
1. **w = V′ᵀz with V′ an exactly orthogonal rational matrix** (Cayley transform). The gate's V is a floating Jacobi
   rotation (`sjsu-near-torus-gate.md:43-45`); a real orthogonal V acts on (ξ, η) as one rotation, which is symplectic,
   and a float V is not. The scope report already asked for a rational symplectic map
   (`sjsu-effective-stability.md:308-310`).
2. **Polar chart** w_j = √I_j e^{iq_j}, canonical on I_j > 0.
3. **Shift** I = B₀(φ) + u, B₀ = I* + c₀ + ∇_qS: exactly canonical for *any* trigonometric polynomial S, being the
   time-one map of S (`sjsu-near-torus-gate.md:131-132`). S is literal data: 2,790 modes, 396 above 10⁻²⁰ (`:296`).
4. **F_j are literal functions of (u, φ)**, φ = (q₁ − q₃, q₂ − q₃). Rotation invariance (Σk = 0 for every monomial)
   makes every function depend on the angles only through φ (`:100-101`); gate SR-1 checks it exactly.

The Lean lemma needed is bracket transport: for the canonical map Φ, d(G∘Φ⁻¹)(X_H)∘Φ = {G, H̃}, with H̃ = H∘Φ in (u, q).

**What the checker proves** (sup norms as weighted ℓ¹ majorants of enclosed Fourier–Taylor coefficients):
- (a) **rates:** η_j ≥ sup of |{F_j, H̃}| over the tube {u = τ̃(φ) + v, |v_j| ≤ κδ}, including dropped products and the
  binomial tails in v (`sjsu-near-torus-gate.md:168-176`; `scripts/sjsu/gate2/measure.py:1-9`);
- (b) **faces:** |F_j − c_j| > δ on |v_j| = κδ (measured margin 0.58–0.82 δ, `:164-167`);
- (c) **initial set:** Q ⊆ {|F_j − c_j| ≤ δ/2} ∩ tube;
- (d) **regularity:** the closed tube lies in W (it stays ≥ 2.3·10⁻⁵ from w_j = 0, `:261`);
- (e) **eccentricities:** bounds on the tube.

**Why not the existing torus routes.**
- **B1-T via `checkTorusChain_sound`.** Its H must be a ℚ `FTPoly` in the chart variables. In polar actions,
  H = Σ c ∏ I_j^{n_j/2} e^{ik·q} has half-integer powers, so it becomes Fourier–Taylor only after an infinite binomial
  expansion about B₀(φ), with B₀^{s}, s half-integer. That needs a model-error term R_model with |∂R| ≤ ε, and **there
  is none** in either checker or physical theorem (`TorusChainCheck.lean:117-135`). The normalizing generators would
  also need exact `ftEqCheck` of 10⁵–10⁶-term Lie sums; on Hénon–Heiles, about 5·10³ monomials already hit kernel deep
  recursion (`docs/tracks/B/PROPOSAL-MERGED-MAJORANT.md:7-14`).
- **B5, then a Birkhoff chain in the Ψ_K chart.** That composition is "later" (`B5-DESIGN.md:39`), not built, and
  needs the same analytic-remainder hook. B5 alone gives η = C₃b²/2 (`B5-DESIGN.md:36-38`) with no Birkhoff gain.
  Estimate: a torsion variation of order 10⁻² per year per action unit gives η ≈ 10⁻¹⁴ at b = 10⁻⁶, so T ≈ 10⁷ yr,
  two orders short of 5 Gyr, before the Cauchy constant makes it worse.
- **So the literal-observable route**, which needs no normal-form identity, canonical inverse or Diophantine statement
  in the kernel (`sjsu-effective-stability.md:257-273`); only (a)–(e) are checked.

**Checker route (a) or (b) of the gate report (`sjsu-near-torus-gate.md:264-268`): recommend (a)**, a packed
Fourier–Taylor checker. Route (b), multiplying by powers of |w_j|, composes F (u-degree 8) with B₀ (Fourier order 60):
polynomial degree of order 480 in w (estimate), far larger than (a).

### 2.3 X1: the route to T1-KAM, and what B5 adds

**Route.** Sjs-plan's packages A1–E3 (`sjs-plan.md:416-434`): the v2 certifier in route-B isoenergetic form through the
packed layer; the synodic regular chart with a new trusted Kepler-equation node (B1, 1–2k lines); the cubic
Diophantine lemma (D1); a 48-digit generator (E1).

**How X1 feeds it.** (1) The cost model is re-run with the measured S(L) (`scripts/sjs/x1/x1_cost.py:1-17`). (2) The
near-resonant k₀ = (27, −67, 31) forces a residual below (k₀·ω)²/|T| at k₀ (`sjs-x1-support.md:173`), and no grid band
may cut k₀'s satellites (`:115-122`). (3) It removes the plan's ×3 support uncertainty (`sjs-plan.md:32`).

**X1's torus is not certificate input.** Route B needs a raw invariance error of 10^−38.0 (`sjs-plan.md:112-115`), i.e.
L = 45, about 48 digits (`sjs-x1-support.md:63`). X1 sits at the double-double floor (about 32 digits) with
out-of-band truncation 2.3·10⁻²⁶.

**PR #9's Lean.** PR #9's own commit `41c336fd7` has no Lean. The `KAM/CertificateSharp/Packed/**` files in its diff
came in by merging `main` (`bfd3a0b0e`); `main` landed them as `22baf9a16` ("mag-core-land"), byte-identical. They give:
- **`Trunc/`:** truncated Gram and torsion memos plus an exact `DK` memo; soundness
  `checkV2With_jetBaseLTPackedJLT_sound` concludes `CertifiedTorus`
  (`main:KAM/CertificateSharp/Packed/Trunc/Route.lean:376`). This matches "the torsion stage is cheap at 3–6 digits"
  (`sjs-plan.md:292`): useful for SJS.
- **`CheckParts.lean`:** `checkEmbedding_of` (`main:…/CheckParts.lean:26`) checks a large certificate in parts.
- **`CertifiedCongr.lean`:** transfers `CertifiedTorus` to a generated copy with the *same* `ham`
  (`main:…/CertifiedCongr.lean:35-51`); not a change of Hamiltonian.
- **`JetLift*`:** Hamiltonians linear in one action (MAG); not SJS's case.
- **`Shift/`:** window-sized powers as shifts, past the 2²⁴ `Nat.pow` limit. **The shift fast path rejects `inv` and
  `sqrt` witness blocks** (`main:KAM/CertificateSharp/Packed/Shift/Chain.lean:17-18`), and SJS's H needs `inv`, `sqrt`
  and a Kepler node: SJS must use the non-shift path or extend `Shift`.

**What B5 adds (T1-NEAR).** `certifiedTorus_confinement` needs `CertifiedTorus`, `G1Hyps`, `IsDiophantine`,
`RouteChecks`, margins and η ≥ `routeC3`·B²/2 (`CertifiedTorusRoute.lean:49-55`); the horizon is about b/η = 2/(C₃b).
Estimate (sjs-plan's sampled box majorant M ≈ c_D²Xh ≈ 1.65·10³, `sjs-plan.md:93`; illustrative μ = 10⁻⁴, r = 10⁻²):
C₃ ≈ 5·10⁶, so T ≈ 400/(10⁹ b) time units, a few hundred years at b = 10⁻⁹. This is an order of magnitude, not a
measurement; gate SX-8 computes it with the projection bound (n = 3 needs ‖Du‖ ≲ 0.3). Verdict: cheap once T1-KAM
exists, but not a headline without a Birkhoff layer on top of B5 (`B5-DESIGN.md:39`).

## 3. Gaps

### 3.1 The model

**SJSU18-O2: no model error; Laplace coefficients do not enter the theorem.**
- The 25 written digits are the coefficients by definition (`sjsu-model-recovery.md:338-342`, `:389-395`). As decimals
  they are exact rationals with denominators 10^k; a ball checker converts them with directed rounding
  (`sjsu-effective-stability.md:505-509`).
- Laplace coefficients enter only the recipe that produced the polynomial (mpmath at 40 digits, not enclosed;
  `sjsu-model-recovery.md:85-99`).
- **If the owner wanted the infinite-precision recipe (decision 2), η_model would enter:** η_j becomes
  η_j + Σ_k sup|∂_kF_j| · sup|ΔX_k| (`sjsu-effective-stability.md:270-273`; `program-b-plan.md:399`, "η = η_finite +
  η_Lie + η_Fourier + η_model + η_rounding"). Size (estimate): about 10⁻³² against η ≈ 10⁻²⁰, from coefficient error
  ≤ 5·10⁻²⁶ relative, |X_H| ≲ 7·10⁻⁶ at nominal amplitude (per-degree majorants, `sjsu-near-torus-gate.md:63-65`) and
  |∂F| ≲ 0.05. The cost is proof, not arithmetic: Δ must be proved, either by enclosing the whole recipe in Lean (1.08M
  first-order terms, `sjsu-model-recovery.md:385`; 5–15k lines, `sjsu-effective-stability.md:528-531`) or by a premise,
  which AGENTS.md rule 6 forbids. Keep the published polynomial.
- **Data in Lean.** 38,466 rationals of about 83 bits of mantissa (25 digits), magnitudes 10⁻⁵ to 1.4·10¹³
  (`sjsu-model-recovery.md:335-336`); the JSON is 3.2 MB (`:319`). Estimate: 1–2 MB of Lean data, about 25–40 modules
  under the 1,500-line cap.
- **Fidelity.** The model is "a reconstruction, not the authors' file" (`sjsu-model-recovery.md:13`). The theorem
  says nothing about averaged or N-body dynamics; that belongs in prose (`sjsu-effective-stability.md:139-144`,
  `:438-444`).

**FH25 (X1): no truncation, η_model = 0.** H is a closed form with exact decimal constants; transcendental pieces are
enclosed by ball arithmetic (`sqrt` exists; the Kepler node is new, `sjs-plan.md:423`). The regular-variable recoding
agrees with the Delaunay route to 7.8·10⁻⁶² at 200 bits (`sjs-x1-support.md:73-78`): evidence for the statement, not a
proof. Statement audit A1 must pin (2.1)–(2.2) against FH25 itself.

### 3.2 What the floating measurements do not yet establish

**Gate 2** (each item is a check the certificate must replace):
1. **Noise floor.** η includes a float64 floor of about 10⁻¹⁹ (`sjsu-near-torus-gate.md:177-182`); it binds for
   δ ≤ 10⁻⁶ (η_full = 8.7·10⁻²⁰ at every δ ≤ 10⁻⁶, `scripts/sjsu/gate2/results/t2-L10-K50-LB8-v14.log`). Estimate:
   removing it raises T by up to 10× (the T_band80 column, `:193-201`, itself not a bound).
2. **Aliasing.** Compositions are formed on a 128² grid and their Fourier coefficients summed (`measure.py:1-9`,
   `torus2.py:90-101`); aliasing is unbounded. A certificate needs alias-free products and an explicit Fourier tail of
   B^{s}.
3. **Tail range.** Binomial tails use grid samples of B₀ + τ̃ for B_min, B_max (`torus2.py`, `Bmin = … .min()`); an
   enclosure over all φ is needed.
4. **Modal rotation.** V is floating; needs the rational orthogonal V′ of 2.2.
5. **Pullback.** c = F(z⋆) and the pullback are floating; in the certificate F is literal and c is enclosed.
6. **Exact identities.** Rotation invariance and the AMD identity are float-measured: the {C, H} coefficients reach
   4.9·10⁻⁴ by rounding (`:57-58`); the AMD identity holds to 2·10⁻³¹ (`:177`). Gate SR-1 checks them exactly.
7. **Untrusted data is fine.** The pruned observables (2–4k complex coefficients each, `:292-294`) and S are producer
   data; only their brackets are checked (`:270-273`).

**X1.** No enclosure (all majorants sampled, `sjs-plan.md:84`, `:104`); no Kepler node; L = 45 not reached; the
intermediates' support (0.3–2.2× K) not re-measured (`sjs-x1-support.md:61`); no kernel measurement above
F = 920 Mbit (`sjs-plan.md:452`).

### 3.3 Certificate sizes

**Gate 2, method (estimate).**
- A Fourier–Taylor model is Taylor slots in v (monomials of degree ≤ L_v in three variables) times Fourier modes in the
  hexagon |k₁| + |k₂| + |k₁ + k₂| ≤ K, which has 1 + 3(K/2)(K/2 + 1) modes. Check: K = 50, degree 8 gives
  165 × 1,951 = 321,915, exactly the gate's unpruned F (`sjsu-near-torus-gate.md:278`).
- Precision p = 96–128 bits per real coefficient: η ≈ 10⁻²¹ against derivative scales of about 10⁻³ needs about 60
  bits, plus dynamic range and guard bits.
- Packed cell width w = 2p + log₂(coefficients) + 2; operand bits 2.25·w·box (`sjs-plan.md:273`), the square box over
  the hexagon being about 1.33; a truncated product has C(L_v + 6, 6) slot pairs.
- About 150 full-product equivalents per certificate: 18 for the three brackets (6 each) plus about 130 to build H̃ over
  its 714 groups of exponent vectors n = a + b by nested Horner.
- Ledger: one literal model per product output, sjs-plan's ledger rule (`sjs-plan.md:277`).

| Scenario | Slots × modes | Coeff./model | Model | Ledger |
|---|---|---:|---:|---:|
| Low: L_v = 8 + Cauchy tail, K = 50, p = 96 | 165 × 1,951 | 3.2·10⁵ | 4 MB | 0.58 GB |
| Central: L_v = 8, K = 60, p = 112 | 165 × 2,791 | 4.6·10⁵ | 6 MB | 0.97 GB |
| Gate's degree: L_v = 14, K = 60, p = 112 | 680 × 2,791 | 1.9·10⁶ | 27 MB | 4.0 GB |
| High: L_v = 14, K = 100, p = 128 | 680 × 7,651 | 5.2·10⁶ | 83 MB | 12.5 GB |

Small inputs, under 10 Mbit in total (estimate): H (38,466 coefficients, about 3.2 Mbit), S (2,790 modes), τ̃ and the
B^{±1/2} witnesses (3 Fourier models each of about 3k modes), F (3 × 2–4k coefficients).

**Comparison** (measured unless marked):
- **Hénon–Heiles (B3).** 1.64 MB of Lean in 65 files; 1,216 certificate monomials, about 1.3·10⁵ unmerged; about 27
  CPU-min, peak 3.4 GB (`PROPOSAL-MERGED-MAJORANT.md:9-20`); replay of 5 core modules 52.4 s / 4.28 GB
  (`docs/tracks/B/freeze/SEAL-AUDIT-HH-1.md:263-267`).
- **SO-3 lunar lock.** 242.1 MB in 13,668 modules (`docs/tracks/SO/audits/LOCK-DATA-handoff.md:83`); 132.7 h serial
  (a projection, `docs/campaign/OVERNIGHT.md:3301`); replay sample of 621 modules 9.1 h
  (`LOCK-DATA-handoff.md:135-148`); heavy segments 18–25 GB, local jobs under 10G (`:177`).
- **LG00 T′.** 30.1 CPU-h, 5,183 modules, 7.78 GB on the per-coefficient route (`sjsu-effective-stability.md:472-477`);
  1.75–2.7 CPU-h per torus packed (`sjs-x1-support.md:179-180`).
- **Gate 2 (estimate).** Ledger 0.6–12.5 GB, inputs < 10 Mbit, ≤ 8 GB per declaration targeted.
- **M3 SJS torus (model).** Ledger 55–140 GB; input 0.95–1.16·10¹⁰ bits (340–550 GB charged at 288-bit chunks, 57–70 GB
  long-line); 10–94 CPU-h, 107–590 under the default limit; peaks 5.5–16 GB (`x1_cost.json`; `sjs-x1-support.md:27-40`).

Gate 2's central ledger is about 4× SO-3's source; M3's is 230–580× SO-3's and 50–150× gate 2's.

### 3.4 Kernel time and the scaling assumptions

**(i) Packed law, the plan.** Measured to 460 Mbit: 8 ns per operand bit per `Nat.mul`, a cycle costs κ = 2–3
multiplications, peak ≈ 0.45 GB + 10·F (`sjs-plan.md:246-250`). With 3.3's formulas (estimate):

| Scenario | Per full product | 150 products | Ledger elaboration | Charged (288-bit / long-line) |
|---|---:|---:|---:|---:|
| Low | 60–90 s | 2.5–3.7 CPU-h | 1.2–1.7 CPU-h | 167–218 GB / 28 GB |
| Central | 98–148 s | 4.1–6.2 CPU-h | 1.9–2.8 CPU-h | 279–364 GB / 46 GB |
| L_v = 14, K = 60 | 21–32 min | 53–80 CPU-h | 8–12 CPU-h | 1.1–1.5 TB / 191 GB |
| High | 66–100 min | 166–249 CPU-h | 25–36 CPU-h | 3.6–4.7 TB / 0.6 TB |

Literal rates are V2-PACKED's 0.9–1.3 µs of elaboration and 36–47 B charged per bit
(`docs/campaign/design/V2-PACKED.md:248-249`), spread over declarations of at most 4 GB. The Taylor degree is the
dominant lever: recommend L_v = 8 with a Cauchy tail on a polydisc of radius about 10κδ, since the gate's
U-by-degree log shows the degree ≥ 9 remainder is what matters at δ = 10⁻⁶ (`t2-L10-K50-LB8-v14.log`). Gate SR-4 must
confirm it.

**(ii) List checker, scaled from Hénon–Heiles.** Assumption: time linear in monomial operations,
27 CPU-min / 1.3·10⁵ ≈ 12 ms per monomial. One dense × sparse bracket product (1.3·10⁶ × 3·10³) then costs about
1.35·10⁴ CPU-h: **infeasible**. The per-coefficient landed product, about 1.3·10⁻⁴·S^1.9 s
(`docs/explorations/themes/sun-jupiter-saturn.md:46-47`), is equally out of reach.

**(iii) Byte scaling, from Hénon–Heiles and SO-3.** Assumption: time proportional to certificate bytes, 0.27 CPU-h/MB
(HH) to 0.55 (SO-3, a projection). Gate 2's 0.6–12.5 GB would then cost 160–6,900 CPU-h, and M3's 55–140 GB
1.5–7.7·10⁴ CPU-h, consistent with sjs-plan's 7·10⁴–5·10⁵ for today's checker (`sjs-plan.md:303`). This is an upper
reference for per-coefficient work per byte; the packed layer is what breaks it, so far validated only in 2-D (LG00).

### 3.5 What must be proved new in Lean

**Gate 2 (T2-CONF)**, estimates, overlapping rather than additive:
- **N1 (0.3–0.6k by hand).** `SJSU18-O2` data definition (generated, about 25–40 modules), z⋆, the T2-CONF statement.
  Reuses the Hénon–Heiles freeze pattern; decision 7.
- **N2 (1–2k).** Charts: the Cayley-orthogonal rotation is symplectic; the polar chart is canonical on I > 0; the
  gradient shift is canonical; bracket transport; angle reduction by charge balance. Reuses `ChartChain.lean`
  (`IsCanonicalChart`), `LambdaDrift/Poisson.lean` (`pb`), `Transport.lean`.
- **N3 (3–5k).** Packed Fourier–Taylor models on T² × box: enclosure semantics, truncated product with dropped-product
  bound, ∂_φ, ∂_v, Taylor shift by τ̃, weighted ℓ¹ sup bound, binomial and Cauchy tails. Reuses V2-PACKED's `Digits`,
  `Round`, `Product` and the `PackLayout` Kronecker lemma (`V2-PACKED.md:7-40`).
- **N4 (0.5–1k).** Witnesses for B^{1/2} and B^{−1/2} on Fourier models (positivity, Newton residual), on the
  `sqrtWitness_sound` pattern (`docs/tracks/SO/audits/LOCK-SQRT-audit-1.md:45`).
- **N5 (1.5–3k).** `checkTube` and `checkTube_sound`: items (a)–(d) of 2.2 into
  `hamiltonian_approxIntegrals_confinement`.
- **N6 (0.3–0.6k).** Eccentricity enclosure on the tube (Γ_j via V′ and √(I_l I_m) cos(q_l − q_m)), using N3–N4.
- **N7 (0.3–0.5k).** Application, provider, opt-in library (D51, `docs/DECISIONS.md:409`; pattern
  `scripts/build_roots.json:49-57`, KAMHenonHeiles).
- **Total 7–13k.** The scope report had 3–7k for the checker and 3–8k for model and coordinates
  (`sjsu-effective-stability.md:524-532`); its 2–4k for first exit is now done in 355 lines (`ApproxIntegral.lean`).

**X1 (T1-KAM)**, sjs-plan's packages re-read against what has landed: A1 statement 0.5–1k; B1 Kepler node 1–2k; B2
reverse gradient 1–2k (optional); C1–C4 packed layer planned at 5.5–9.5k (`sjs-plan.md:425-428`), of which V2-PACKED
has landed the 2-D models, jets, frames and torsion and proved LG00 (`V2-PACKED.md` §§12–14;
`sjs-x1-support.md:178-182`), so 2–5k remain (estimate: 3-D layouts with blocks under the `Nat` limit, the anisotropic
tail norm, the `Shift` path for `inv`/`sqrt`); D1 cubic Diophantine 0.3–0.5k; physical transport to heliocentric
eccentricities 0.5–1k (estimate). **Total about 4.5–11.5k Lean**, plus E1 SJS-GEN in 2–3k Python (`sjs-plan.md:430`).

## 4. Go/no-go gates

E1-report style (`docs/tracks/B/b3/out/E1-report.md:7-8`, `:34-100`): literal criteria, report the failing term, never
shrink the box silently (`docs/tracks/B/B3-READY.md:58-65`). Each runs in the foreground under
`systemd-run --user --scope -p MemoryMax=4G` unless noted. Costs are estimates.

**Gate 2**
- **SR-1 EXACT-MODEL** (≤ 5 CPU-min, < 1 GB). Python `Fraction`: all 7,941 terms have Σ(a − b) = 0; reality and
  reversibility exact; {C, H} ≡ 0 with C = Σ|z_j|²; z⋆ parsed exactly.
  PASS iff every identity has zero defect. FAIL: the φ-reduction and AMD shortcut are unusable; stop and report errata.
- **SR-2 RATIONAL-ROTATION** (≤ 20 CPU-min). A rational Cayley-orthogonal V′ with ‖V′ − V‖max ≤ 10⁻¹²; rerun
  `torus2.py --L 8 --K 50 --LB 6 --Lv 12 --G2 128` with H in V′ coordinates (3.8 GB measured for this configuration,
  `scripts/sjsu/gate2/README.md:37`).
  PASS iff T_full(δ = 10⁻⁶) is within 10 % of 2.7·10¹² yr (`sjsu-near-torus-gate.md:282`) and the face margin ≥ 0.5δ.
  FAIL: use the symplectic pair η = Qy, ξ = Q⁻ᵀx with rational Q.
- **SR-3 ALIAS** (≤ 30 CPU-min, ≤ 4 GB). The δ = 10⁻⁶ row recomputed with zero-padded (≥ 2× maximum mode) products,
  unpruned; per-coefficient majorants compared.
  PASS iff majorant sums change by ≤ 10 % of η_j. FAIL: raise grid sizes in 3.3 and re-price.
- **SR-4 BALL-MIRROR** (≤ 1 CPU-h, ≤ 4 GB). Python ball (or directed double-double) mirror of (a)–(e) at L_v = 8 plus a
  Cauchy tail, K = 50, δ = 10⁻⁶ only: outward-rounded H, B^{±1/2} enclosures, binomial and Cauchy tails, ℓ¹ sup.
  PASS iff, for j = J, S, U, (δ/2)/η_j ≥ 10¹⁰ yr (2× over 5 Gyr) and the face margin ≥ 0.3δ. FAIL: report the dominant
  term; options are a smaller δ, L_v = 10–14, a larger K; never shrink Q silently.
- **SR-5 OPCOUNT** (≤ 10 CPU-min). The certificate's straight-line program (packed operations and sizes) from SR-4's
  data, priced with sjs-plan's laws.
  PASS iff kernel ≤ 50 CPU-h, ledger ≤ 5 GB and every declaration ≤ 8 GB by the memory law. FAIL: redesign (Taylor
  degree, Horner order, blocks) before any Lean.
- **SR-6 KSHARD** (≤ 1 CPU-h, ≤ 4 GB, one targeted build; after decision 5). One real-size slot-pair product plus a mask
  bound in `decide +kernel`, as a throwaway module without proofs.
  PASS iff time is within 3× of 8 ns/bit × κ and peak ≤ 0.45 GB + 10F + 1 GB. FAIL: re-price; consider block products.
- **SR-7 Q-RADIUS** (≤ 10 CPU-min). The largest r with ball(z⋆, r) ⊆ Q, from SR-4's enclosure of ∇F on the tube.
  PASS iff r ≥ 10⁻⁶ in z units. FAIL: decision 3, option (b) or (c).

**X1 / M3** (sjs-plan's gates, refreshed)
- **SX-2 = X2 PACKED-GATE** (< 1 CPU-h, < 8 GB). A real 3-D reversible product in blocks on X1's coefficients at
  S ≈ 10⁵–4·10⁵ (`sjs-x1-support.md:196-197`). PASS iff within 3× of the laws of `sjs-plan.md:246-250`. FAIL: the
  sparse-block fallback, and the target becomes a funded project (`sjs-plan.md:434`).
- **SX-3 = X3 BALL-H** (< 1 CPU-h). Ball mirror of the synodic H on the box against sampled majorants
  (`sjs-plan.md:375`). PASS iff the enclosure is ≤ 20× the sample (about 20 % in S, `sjs-plan.md:120-121`). FAIL
  (≥ 100×): L ≈ 51, cost ×1.6 (`sjs-plan.md:451`).
- **SX-6 = X6 ROUTE-B-LOW** (< 1 CPU-h). Route-B budgets at L_low = 3–6 for frames and torsion (`sjs-plan.md:378`).
  PASS iff the budgets pass at L_low ≤ 6. FAIL: the torsion stage is re-priced at 17 digits.
- **SX-7 KEPLER** (< 1 CPU-h). Python interval-Newton prototype of the regular Kepler node on the box. PASS iff the
  enclosure width is ≤ 20× the sampled spread. FAIL: another formulation of the node.
- **SX-8 NEAR-B5** (**over 1 CPU-h**: X1's torus must be regenerated, about 1.5 CPU-h, `sjs-x1-support.md:112-113`).
  κc, `disp` and `routeC3` on X1's torus give T(b) for T1-NEAR. PASS iff n(κc + disp/δ) < 1 and T(10⁻⁹) ≥ 10³ yr.
  FAIL: drop T1-NEAR for this torus.
- **SX-E1 SJS-GEN** (**owner allocation**: 18–62 CPU-h per Newton step, `sjs-plan.md:203`, `:210-211`). A 48-digit
  torus with residual at k₀ below (k₀·ω)²/|T| (`sjs-x1-support.md:173`). PASS iff the raw residual ≤ 10^−38 at L = 45.
  FAIL: triple- or quad-double rework (`sjs-x1-support.md:199-202`).

## 5. Staged plan and costs

Prover-hours use 100–200 Lean lines per prover-hour, the rate PROPOSAL-MERGED-MAJORANT assumes (`:46-49`, 0.3–0.6k
lines in 2–4 prover-hours); it is an estimate, not a measurement. Calendar assumes one numerics worker, two provers and
an independent auditor, with compile jobs serialized.

**Gate 2 → T2-CONF**

| Stage | Content | Prover-h | CPU-h | RAM | Calendar |
|---|---|---:|---:|---|---|
| G-0 | Owner decisions 1–7 | — | — | — | days |
| G-1 | SR-1–SR-5, SR-7; producer upgrade (exact V′, alias-free, balls) | numerics | ≤ 3 | ≤ 4 GB | 3–6 days |
| G-2 | N1 statement and data; statement audit; freeze | 5–10 | < 1 | — | 3–5 days |
| G-3 | N2–N6, each package audited | 35–110 | builds | ≤ 8 GB | 2–4 weeks |
| G-4 | SR-6, then the production certificate (opt-in library) | 5–10 | 5–60 | ≤ 10 GB/lane | 1–2 weeks |
| G-5 | Seal audits, `#print axioms`, replay sample | auditor | ≤ 10 | ≤ 10 GB | 3–5 days |

The producer upgrade is 1–2k lines of Python. G-2 runs in parallel with G-3. G-4's central figure is about 10 CPU-h
(arithmetic 4–6 plus literals 2–3), serial.
**Total (estimate):** 50–130 prover-hours, under 75 CPU-h, 5–8 weeks of calendar after G-0. It fits the local 32 GB box
with one heavy lane; no rented hardware unless SR-5 projects more than 5 GB of ledger.

**X1 → T1-KAM** (sjs-plan, updated)

| Stage | Content | Prover-h | CPU-h | RAM / disk | Calendar |
|---|---|---:|---:|---|---|
| X-0 | Sjs-plan decisions 1–8; SX-E1 allocation | — | — | — | — |
| X-1 | SX-3, SX-6, SX-7 (Python); SX-2 (kernel) | — | ≤ 4 | < 8 GB | 1 week |
| X-2 | A1, B1, remaining C, D1, transport | 25–115 | builds | — | 3–5 weeks |
| X-3 | E1 SJS-GEN, 48-digit torus | — | 50–190 | 10–30 GB | 1–2 weeks |
| X-4 | Production run, one torus | — | 10–94 | 55–140 GB ledger | days |
| X-5 | Seal audits; optional SX-8 and T1-NEAR | auditor | ≤ 20 | — | 1 week |

X-2 is 4.5–11.5k lines; X-3 is 3 Newton steps × 18–62 CPU-h at 10–30 GB (`sjs-plan.md:203`, `:208`); X-4 is 107–590
CPU-h under the default limit and needs a rented 48-core machine with 256 GB and 1–2 TB NVMe (`sjs-plan.md:42`,
`:347`). Sjs-plan's 4–6 weeks (×2 either way, `sjs-plan.md:48-49`) stands: X1 removes the ×3 on S, but the Kepler node,
the enclosure of M (SX-3) and the 48-digit generator remain.

## 6. OWNER DECISIONS

1. **What gate 2 becomes.** (a) T2-CONF only: finite-time confinement through `ApproxIntegral` and a packed tube
   checker; (b) (a) plus T2-KAM, an all-time torus of `SJSU18-O2`; (c) stop at the floating gate.
   **Recommended: (a).** (b) adds a v2 run on a 7,941-term `HamExpr` of unmeasured cost and confines nothing.
2. **Model of record.** (a) `SJSU18-O2` as published, 25-digit decimals as exact rationals (already ruled 1 November,
   `sjsu-model-recovery.md:393`); (b) the infinite-precision recipe with a proved η_model.
   **Recommended: (a).** (b) costs 5–15k lines for a 10⁻³² effect.
3. **Initial set Q.** (a) a sup-norm ball of radius r about z⋆ in (ξ, η): simple, positive volume, one orbit's
   neighbourhood; (b) a band about the whole torus, {|I_j − B̃_j(φ)| ≤ r_j}, with B̃ a short explicit trigonometric
   polynomial (tens of modes); (c) the F-sublevel set itself, which puts thousands of literal coefficients in the
   statement. **Recommended: (a) first, then (b)** once SR-7 sizes it; never shrink Q silently
   (`sjsu-effective-stability.md:566-570`).
4. **Tube width and horizon.** (a) δ = 10⁻⁶, T = 5·10⁹ yr, the eccentricity intervals of 1.1 (float margin 860× at its
   peak, `sjsu-near-torus-gate.md:21-22`); (b) δ = 10⁻⁷ (smaller relative width, about 20× margin); (c) T = 10¹⁰.
   **Recommended: (a)**; SR-4 may move it to (b).
5. **Checker route.** (a) packed Fourier–Taylor models (N3, N4); (b) polynomial observables times powers of |w_j|.
   **Recommended: (a)**, with SR-6 measured before any freeze, as the gate report asked
   (`sjsu-near-torus-gate.md:317-318`).
6. **Where the generic layer lives.** (a) core: `KAM/EffectiveStability/Tube/*` and a packed FT module under
   `KAM/CertificateSharp/Packed/`; (b) inside the application. **Recommended: (a)**, reusable for HD 11964's
   approximate integrals (`KAM/Application/LambdaDrift/Bridge.lean:85`); data stays in an opt-in library (D51).
7. **Frozen data format for `SJSU18-O2`.** (a) generated frozen data modules (about 25–40 files), each pinned in the
   manifest; (b) one frozen definition reading a hash-pinned literal blob; (c) a ruling that the data definition is
   reviewed by hash and generator rather than line by line. **Recommended: (a)**, with a generator test of
   byte-identity against `applications/sjsu/data/sjsu18-o2.json` (sha256 `702b0b3a…`, `sjsu-model-recovery.md:319-324`).
8. **X1 track.** Rule on sjs-plan's eight decisions (`sjs-plan.md:37-46`), with X1's updates: decision 3, allow
   `LEAN_NAT_MAX_SIZE`; decision 4, rent (ledger 55–140 GB); and the E1 generator's precision (triple-double or packed
   Newton). **Recommended:** approve SX-2, SX-3, SX-6 and SX-7 now (each under 1 CPU-h); defer the rest until they
   report.
9. **B4 × B5 composition** (a Fourier–Taylor Birkhoff chain in the Ψ_K chart with an analytic-remainder hook).
   (a) defer; (b) scope it now as the general torus-plus-Birkhoff route for T1-NEAR and the SJSU torus.
   **Recommended: (a)**; T2-CONF does not need it.
10. **Compute budget.** (a) gate 2: ≤ 3 CPU-h of gates, ≤ 75 CPU-h of production on local lanes; X1: SX gates ≤ 4
    CPU-h, E1 and the production run only after explicit allocation; (b) a larger envelope now.
    **Recommended: (a)**, matching the scope report's staged 100 → 1,000 CPU-h rule
    (`sjsu-effective-stability.md:571-573`).

## 7. Uncertainties, errata and deviations

**Uncertainties.**
- The packed Fourier–Taylor costs extrapolate 2-D Fourier laws to Fourier × Taylor products; the 150 product
  equivalents for building H̃ are a judgement (±3×).
- The Cauchy-tail design (L_v = 8) is untested; without it the cost moves to the L_v = 14 rows (53–249 CPU-h).
- Removing the noise floor may move T either way; aliasing (SR-3) is unmeasured.
- T1-NEAR's horizon uses sampled majorants and illustrative μ and r.

**A suspected inconsistency in non-pinned docs (not a source erratum).** `docs/campaign/design/V2-PACKED.md:356` says
the kernel "refuses `Nat.pow` results above 16.8 Mbit (`LEAN_NAT_MAX_SIZE`)", while `sjs-plan.md:262-264` gives the
`Nat` size limit as 2²⁷ bytes and the `Nat.pow` exponent limit as 2²⁴. The two name different limits.

**Brief deviation.** The brief calls PRs #8 and #9 open and lists `KAM/CertificateSharp/Packed/**` as PR #9's Lean.
Both are merged into `inp`; PR #9's own commit has no Lean, and the Packed files in its diff are `main`'s `22baf9a16`
(2.3).
