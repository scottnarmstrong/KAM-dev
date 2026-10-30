# SO-LOCK: Lean design of "the Moon stays locked in synchronous rotation forever"

**Status:** design, 30 October 2026 (package DESIGN-LOCK, branch `inp-lockdesign`). No proofs, nothing frozen.
Governing decisions: D45 (route (a′), statement L1, N = 65, certified periodic orbit, no Birkhoff) and its
addendum (the headline names ψ* explicitly), D29/D34–D44 for the certifier and the SO stack. Source study:
[`SO-LOCK-SCOPE.md`](../studies/SO-LOCK-SCOPE.md). Signatures: `.drafts/design/SOLockSignatures.lean`
(elaborated, only `sorry` warnings, §1.6). Owner-facing statements: [`FREEZE-PROPOSAL-LOCK.md`](FREEZE-PROPOSAL-LOCK.md).

Notation (period-one units, the frozen model `soField` on x = (q, p, φ)): ψ = q − φ (turns), q̇ = p,
ṗ = −soVq(q, φ), φ̇ = 1. A *synchronous orbit* is ψ(φ) with q(t) = φ(t) + ψ(φ(t)), p = 1 + ψ′(φ),
equivalently ψ″(φ) = −soVq(φ + ψ(φ), φ).

## 0. Summary

- **Headline** `lunar_sync_lock`: for every initial state with libration action around ψ* below I_in, the solution is
  global and unique and, for all real t, |ψ(t) − ψ*(φ(t))| ≤ Rψ, |p(t) − 1 − ψ*′(φ(t))| ≤ Rp and |q(t) − φ(t)| < 1/4.
  ψ* = `lunarSyncOrbit` is a **named definition**, characterised as *the unique odd one-periodic synchronous orbit*.
- **Key design finding.** The synchronous orbit is unique *globally* (no pinning ball, no Fourier data in the
  statement). The force is globally Lipschitz in q with constant L = 16π² ε Σ|Aₘ| ≈ 0.067. An odd 1-periodic
  solution vanishes at 0 and 1/2, and the Dirichlet inverse of ∂² on [0, 1/2] has sup-norm ≤ 1/32. So the
  fixed-point map is a contraction with factor ≈ 0.002 on *all* odd periodic continuous functions. Banach's theorem
  then gives existence, global uniqueness and the location bound at once. This replaces the recommended
  weighted-ℓ¹ Newton–Kantorovich, which is not needed because ε is small (§2).
- **Route (a′) unchanged:** a rational trigonometric centre c (data, *not* in any statement), an exact centre shift,
  elliptic polar coordinates with rational Ω, the v2 certifier `checkTorusCertificateV2 routeAV2` applied unchanged,
  one new trusted primitive `HamExpr.sqrt`. `HamExpr` is **not frozen**: grep of `KAM/Frozen`, `manifest` finds
  no mention, so a constructor can be added (§4).
- **Estimate:** about 3.5–4.6k new Lean lines in about 14 files, each under 900 lines, plus data modules.

## 1. Statements

### 1.1 Meaning-carrying definitions

```lean
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = -soVq (φ + ψ φ) φ

open Classical in
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

def lunarOmega : ℚ := 1644 / 10000   -- DATA (≈ 2π ω₀)
```

- `soVq` is landed, not frozen. If the definition is frozen, `-soVq` should be written as
  `deriv (fun s => soV s φ) (φ + ψ φ)`, exactly as in the frozen `soField`. Recommended for the freeze: write it
  as `(soField (φ + ψ φ, 1 + deriv ψ φ, φ)).2.1`, so that the statement mentions only frozen `soField`.
  For owner review.
- **Oddness** is part of the definition. It encodes reversibility. Without it, φ ↦ ψ(φ + a) shifts would not be
  orbits anyway, because the field depends on φ; but the even-part freedom is what uniqueness needs (ψ(0) = 0 = ψ(1/2)).
  Uniqueness among all 1-periodic (not necessarily odd) orbits is also true for the same contraction reason on
  the periodic problem ψ″ − 0 = f. That problem is not invertible, because constants are in the kernel; it is
  solved there by the mean condition. That variant is heavier. We keep "odd".
- The `Classical.choose` definition is canonical because of `lunarSyncOrbit_unique`. The headline never depends on
  the junk branch, because `lunarSyncOrbit_spec` holds.
- **"The resonance angle stays bounded"** is written out literally in the conclusion:
  `|(z t).1 - (z t).2.2| < 1 / 4` (ψ = q − φ; the separatrix is at 1/4). No extra definition.
- **Solid-torus region:** not in the headline. The headline's premise is the elliptic tube `libAction Ω ψ* x < I_in`.
  The solid torus V lives in LOCK-CONF (§5).
- **Polar coordinates:** not in the headline (§3).

### 1.2 Theorems for the freeze proposal

```lean
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 13 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 1 / 10000          -- DATA
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 11 / 1000) :            -- DATA I_in
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 22 / 100 ∧            -- DATA Rψ
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 37 / 1000 ∧               -- DATA Rp
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
theorem lunar_sync_lock_nonvacuous (φ₀ : ℝ) :
    libAction lunarOmega lunarSyncOrbit
      (φ₀ + lunarSyncOrbit φ₀, 1 + deriv lunarSyncOrbit φ₀, φ₀) < 11 / 1000
```

`lunar_sync_lock_nonvacuous` is trivially true, because the action of ψ* itself is 0. It is kept only as the
analogue of `lunarPLo_lt_lunarPHi`, and dropping it is recommended (owner review). The meaningful non-vacuity
is that the tube is a nonempty open set of positive measure, which is obvious from the formula.

### 1.3 Choice discussion (existential vs named orbit)

- **Rejected: an existential ψ\* with a pinning ball.** The addendum requires naming ψ*.
- **Rejected: a ball-pinned definition** (`IsSyncOrbit ψ ∧ |ψ − c| ≤ r` with c an explicit Fourier list). It would
  put about 20 rational coefficients into the frozen text, and it only becomes canonical once uniqueness in the ball
  is proved.
- **Chosen: the global characterisation.** It costs nothing extra, because the contraction gives global
  uniqueness for free (§2), and the frozen text contains no data except the four scalar literals and Ω.

### 1.4 Literal rules (to be fixed from final LOCK-GEN data; placeholders now)

- **Ω:** the rational used in the certified polar coordinates (4 significant digits).
- **Tube transfer to centre ψ\*.** The tori are certified around c. By the triangle inequality in the Ω-norm,
  `sqrt_libAction_le` gives √𝓘_c ≤ √𝓘_ψ* + δ, with δ = √π(√Ω r + r′/√Ω), where r and r′ are the certified
  sup bounds of |ψ* − c| and |ψ*′ − c′|.
- **I_in:** the largest 3-digit rational with (√I_in + δ)² ≤ min P − disp, where min P is the graph's certified
  lower bound g.pLo.
- **Rψ, Rp:** the smallest 2- resp. 3-digit rationals with
  - √((√I_out + δ)²/(πΩ)) + r ≤ Rψ;
  - √(Ω(√I_out + δ)²/π) + r′ ≤ Rp;

  where I_out = max P + disp.
- **Corollary 1/4:** Rψ + sup|ψ*| < 1/4, which needs Rψ ≤ 0.2499. At N = 65, Rψ ≈ 0.21.
- **Sharpness caveat.** The ellipse bound on Rp is coarse: about 3.7 % against the torus's true max |p − 1| of
  about 2.5 %, because the tori are not ellipses. A sharper Rp needs a second invariant-set description (a graph
  in the (ψ, p) plane per φ) and is not proposed. For owner review: accept the coarse Rp, or state the band
  through a certified sup of the Y-coordinate over the torus graph (+150 lines in LOCK-GRAPH, using
  max over θ of Y∘K).

### 1.5 Parametric helpers (unfrozen; distinct names; hypotheses are conclusions of pending packages)

These are in the signatures file:

- `LockBarrier Ω c Iin Iout`: an invariant graph 𝓘_c = P(α, φ). Here α = arg(i√Ω X + Y/√Ω)/(2π), where
  `Complex.arg` is continuous off the negative real axis and the real-axis branch is handled by periodicity; see §5.
- `lock_confinement` (LOCK-CONF);
- `abs_le_of_libAction_lt`, `sqrt_libAction_le` (LOCK-ASSEMBLY glue).

Not in the signatures file (they need the new HamExpr node first): `lockBarrier_of_certV2` (LOCK-GRAPH) and
`lunar_sync_lock_of_cert` (LOCK-ASSEMBLY, over a lawful backend). Their shapes are given in §6.

### 1.6 Elaboration

`inp_sig_check.sh /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignatures.lean` (against the `inp` build):
11 warnings, all `declaration uses 'sorry'`, and no errors. The scratch copy was deleted, and the committed text is
`.drafts/design/SOLockSignatures.lean`.

## 2. The certified periodic orbit (LOCK-PO)

### 2.1 Method chosen: Banach contraction in sup norm on odd periodic functions

- **Space.** B = {d : ℝ → ℝ continuous, 1-periodic, odd}. Use the sup norm, realised as `BoundedContinuousFunction`
  restricted to the closed subspace. This is a complete metric space (closed subset of `ℝ →ᵇ ℝ`).
- **Map.** Let G be the Dirichlet Green operator on [0, 1/2], extended oddly and periodically:
  (G f)(φ) = ∫₀^φ ∫₀^s f − 2φ ∫₀^{1/2} ∫₀^s f on [0, 1/2]. Then (G f)″ = f, (G f)(0) = (G f)(1/2) = 0, and
  ‖G f‖∞ ≤ ‖f‖∞/32. Given a centre c (any C² odd trigonometric polynomial; the rational LOCK-GEN centre or even
  c = 0), set T(d) = G(−soVq(φ + c + d, φ) − c″).
- **Contraction.** ‖T d − T e‖ ≤ (L/32)‖d − e‖, with L = 16π² ε Σ|Aₘ| ≈ 0.067, a factor of about 2·10⁻³.
  Mathlib: `ContractingWith`, `ContractingWith.fixedPoint`, `ContractingWith.dist_fixedPoint_le`,
  `ContractingWith.fixedPoint_unique'`; `BoundedContinuousFunction` is complete. The bound
  ‖T 0‖ ≤ η/32 gives ‖d*‖ ≤ (η/32)/(1 − L/32).
- **Residual η.** η ≥ sup_φ |c″(φ) + soVq(φ + c(φ), φ)|.
  - With c = 0: η = 4πε sup|Σ Aₘ sin 2π(2 − m)φ|. This is ≤ 4πε Σ_{m≠2}|Aₘ| by the triangle inequality, with no
    kernel arithmetic. It gives sup|ψ*| ≲ 2·10⁻⁵ against a true value of 1.2·10⁻⁵. That is enough for
    `lunarSyncOrbit_bound` with the literal 13/10⁶ replaced by 3/10⁵ if needed.
  - With the LOCK-GEN centre: η ≈ 10⁻¹² is certified by ball arithmetic on a 1-D trig expression (existing
    `Slp.balls` with one angle), and r ≈ 3·10⁻¹⁴.
  - **Recommendation:** use c = 0 for the orbit theorem. It is purely analytic, with no data. Then
    ψ* − c_gen ≤ |ψ*| + |c_gen| ≈ 2.5·10⁻⁵ in the tube transfer of §1.4, so δ ≈ √π·√Ω·2.5·10⁻⁵ ≈ 2·10⁻⁵. That
    is negligible against √I ≈ 0.1. The certified-centre variant is kept as a fallback if the margins are tight.
- **Regularity.** The fixed point d* is continuous, so T(d*) = G(continuous) is C², and d* = T d* is C². The
  equation holds pointwise, and oddness and periodicity hold by construction. The derivative bound uses
  |(G f)′| ≤ ‖f‖∞/4.
- **Uniqueness (global).** Let ψ satisfy `IsSyncOrbit`. Then ψ(0) = 0 and ψ(1/2) = 0 (odd + periodic), so
  d = ψ − c solves the Dirichlet problem d″ = F(d), and d = G(d″) = T d, by uniqueness for u″ = 0 with zero
  boundary values. So d is the fixed point.
- **Lean cost.** 600–900 lines in `Lock/PO/{Green,Contraction,Orbit}.lean`. The main work is G: the
  double-integral formulas, `HasDerivAt` of parametric integrals (`intervalIntegral.integral_hasDerivAt_right`), the
  odd periodic extension, and the 1/32 and 1/4 bounds. Risk: low, and it is independent of all certificate code.

### 2.2 Alternatives evaluated

| route | proves | Lean | risk |
|---|---|---|---|
| **Banach in sup norm (chosen)** | existence, global uniqueness, location | 600–900 | low; Mathlib `ContractingWith` |
| radii polynomial / Newton–Kantorovich in weighted ℓ¹ Fourier (brief's recommendation) | existence, local uniqueness, analytic bounds | 1.5–2.5k; needs an ℓ¹ Banach algebra of sine series, composition of `sin` with ℓ¹ series (only the `CertModel` majorant machinery exists, tied to 2-D certificates), and an inverse of the linearisation | medium–high |
| Brouwer on the invariant disc of the time-1 map | existence only, no uniqueness, location only within the disc (≈ 0.2 turn) | ~1k plus Brouwer in 2-D (not in Mathlib) | high; useless location |

Newton–Kantorovich is unnecessary here because the problem is a small perturbation of ψ″ = 0, not of a
resonant operator: L/32 ≪ 1. The scoping study's monodromy remark (ω₀ ≈ 0.026) concerns the *libration*
frequency, which is irrelevant to the periodic problem at frequency 1.

## 3. Symplectic change of variables (LOCK-COORDS)

The certificate Hamiltonian is a `HamExpr 2` on angles (α, φ) and actions (I, J̃). The clock action J̃ is
conjugate to φ, as in `soRotHamExpr`.

1. **Rotated frame** (landed `soRotMap`): (ψ, φ; p′, J′) with p′ = p − 1 and H′ = p′²/2 + J′ + V(ψ + φ, φ) − 1/2.
   The constant is irrelevant.
2. **Centre shift** by the rational odd trigonometric polynomial c (LOCK-GEN data, `lockCentre : List ℚ`), via the
   generating function F₂ = (ψ − c(φ))(c′(φ) + Y) + φJ̃:
   - X = ψ − c(φ), p′ = c′(φ) + Y;
   - J′ = ∂F₂/∂φ = J̃ − c′(φ)(c′(φ) + Y) + X c″(φ) (checked here; agrees with SO-LOCK-SCOPE §2).

   Lean defines both directions explicitly and proves the identity of the pulled-back 2-form. The map is
   polynomial in (X, Y) and trigonometric in φ.
3. **Elliptic polar coordinates:** X = √(I/(πΩ)) sin 2πα and Y = √(IΩ/π) cos 2πα, so dX∧dY = dI∧dα. The inverse is
   I = π(ΩX² + Y²/Ω) (= `libAction Ω c`) and α = arg(…)/(2π). This is defined on the annulus
   I ∈ (I₁, I₂) ⊂ (0, ∞).
4. **K = H′ ∘ Φ as a `HamExpr 2`** in which √(I/π) appears through `HamExpr.sqrt (.mul (.const (1/π…)) (.action 0))`.
   Use `.div … .pi`, because π is not rational. The trig polynomial c(φ) appears through `sinMode`/`cosMode` on the
   key (0, k). V(ψ + φ, φ) = V(φ + c + X, φ) is expanded with `sin(a + b)` into `sin`/`cos` nodes of the
   expression X = √(…)·sinMode(1, 0); the landed `HamExpr.sin`/`.cos` compose.
   - Proved: `lockHamExpr_eval : (lockHamExpr d).eval z = soRotHC (lockMapC d z)` on the complex annulus domain
     where Re(I) > 0.
   - Proved: `lockHamExpr_clock`, the J̃ coefficient is 1, as `soRotHamExpr_clock`.
5. **Conjugacy, real points only.** For a real solution w(t) = (α, φ, I, J̃) of X_K, Φ(w(t)) solves the rotated
   field, hence `soField` after `soRotMapInv`. Proof: chain rule plus the symplectic identity, by direct `fderiv`
   computation on the real annulus. This avoids the complex-analytic conjugacy. Only real-point vector fields
   are needed, because `IsInvariantSet` is about real solutions.
6. **Transport of the invariant set, not the flow.** The certificate gives an invariant graph I = P(α, φ) for K.
   - LOCK-COORDS gives the converse direction: every `soField` solution y inside the annulus image maps by Φ⁻¹ to a
     K-solution. The flow is never transported; this is the same move as `Graph/Inverse` (`soGraph_invariant`).
   - Then K-invariance of the graph, together with the uniqueness of K solutions (C¹ on the annulus), gives
     invariance of {𝓘_c = P(α, φ)} for `soField`, as required by `LockBarrier.invariant`.
   - Subtlety: `IsInvariantSet` quantifies over solutions on any interval J, which may leave the annulus. Membership
     at t₁ and continuity keep the solution in the open annulus near the graph; continuation is by the
     connectedness argument already used in `Graph/Inverse` (`soOrbit` construction). Alternatively, construct the
     orbit on the graph explicitly via the torus parametrisation K∞ and use the global uniqueness of `soField`
     (`so_global_exists_unique`), as `soGraph_invariant` does. **Recommended: the latter** (copy pattern; no
     annulus-exit reasoning).

## 4. `HamExpr.sqrt` (LOCK-SQRT)

- **Is `HamExpr` frozen?** No. It lives in `KAM/Certificate/Expr/Basic.lean`, and no file under `KAM/Frozen/` or
  `manifest/` mentions it; the frozen G1 and the SO anchors talk about functions, not expressions. Adding a
  constructor is allowed. It forces new cases in every `HamExpr` recursion: `eval`, `NonvanishingOn`,
  `contDiffOn_eval`, `eval_add_int`, `exists_real_eval`, the SLP compiler (`Expr/Slp`), the differentiation layers
  (`Diff`, `DiffNode`, `DiffBuild`, `DiffCalculus*`), `Compose`/`ComposeModels`, the sharp/V2 Ham checks
  (`HamClaim`, `HamTrig`, `BallsTrig`, `SplitBounds`), and their soundness proofs. Grep before starting; any
  exhaustive `match` breaks loudly, which is good.
- **Semantics:** `.sqrt a ↦ (a.eval z) ^ (1/2 : ℂ)`, the principal branch (`Complex.cpow`), holomorphic on the slit
  plane. The domain condition is extended by
  `NonvanishingOn (.sqrt a) S := a.NonvanishingOn S ∧ ∀ z ∈ S, 0 < (a.eval z).re`.
  `0 < re` is stronger than slit-plane membership. It is ball-checkable, and it suffices.
  - Holomorphy: `DifferentiableAt.cpow_const` / `differentiableAt_cpow_const_of_mem_slitPlane`
    (`Complex.slitPlane`, `0 < re → mem`).
  - Reality: on real points a.eval is real, and with re > 0 its root is real.
  - Translation invariance: structural.
- **Ball rule.** If |w − s²| ≤ r < s² with s > 0 rational, then |√w − s| ≤ r/s, by
  √w − s = (w − s²)/(√w + s) and Re √w ≥ 0. This is `sqrtSem_ball` in the signatures.
  - The checker picks s by a rational Newton step on the ball centre, then rounds outward. That is the same
    dyadic outward rounding as D39 / SO-BALLFIX's `ballRound`: the radius is rounded up and the centre is rounded
    to a dyadic, with the rounding error added to the radius.
  - It also checks r < s², which certifies Re w ≥ s² − r > 0, i.e. the `NonvanishingOn` condition.
  - Interaction with SO-BALLFIX: the new op is one more case of `ballStep`, rounded like `mul`/`inv`. Coordinate
    with the BALLFIX landing (it is not landed; the log at 8230b16d records a clash with sharp-v2 `BallsTrig`).
    **LOCK-SQRT must start from whatever `Expr/Ball` is on `inp` after BALLFIX lands**, or own the merge.
- **Jet / derivative rules.** d√f = f′/(2√f). The differentiation layer emits `.div f′ (.mul 2 (.sqrt f))`, reusing
  the landed `div` soundness; second derivatives follow by the same rule. No new jet primitive.
- **Composition witness** (the analogue of `ExpWitness`, for the model-level `Compose` path): a Fourier model W with
  checked ‖W·W − f‖ ≤ ε_W and ‖W − W₀‖ < |W₀| (W₀ the mean). Soundness: on the strip, √f = W + E with
  ‖E‖ ≤ ε_W / (2|W₀| − 2‖W − W₀‖ − …), by the same algebra as the ball rule with norms in place of absolute values.
  The rule reads ‖√f − W‖ ≤ ‖f − W²‖ / inf|√f + W|, and inf|√f + W| ≥ 2(|W₀| − ‖W − W₀‖) − ‖√f − W‖ is closed by
  a quadratic inequality that the checker verifies rationally.
- **V2 interaction.** `HamClaim` (claimed |DH|, |D²H| …) is checked against SLP balls, so it needs nothing new
  beyond the ball and jet cases. `BallsTrig`/`SplitBounds` get the extra case. The route witnesses are unchanged.
  The certificate format gains one SLP opcode; that is not a statement change.
- **Soundness obligations:** (i) eval/holomorphy/reality/translation for the new node; (ii) `ballStep` sqrt case
  ⊆ ball; (iii) diff emission correct on {re > 0}; (iv) composition witness sound; (v) all existing soundness
  theorems re-proved with the new case. Independent audit like AUDIT-C6-1 (D45).
- **Cost:** 900–1500 lines across `Expr/Sqrt.lean`, `Expr/BallSqrt.lean`, `Model/SqrtWitness.lean`, plus about
  30–80 lines of new cases in about 12 existing files. Those edits fall outside track SO's files, so the
  orchestrator must assign them (D34-style checker change).

## 5. Confinement (LOCK-CONF)

- **Region.** V = {x | 𝓘_c(x) < r₀} ∪ {x | r₀/2 < 𝓘_c(x) ∧ 𝓘_c(x) < P(α(x), φ)}, with r₀ = I_in (= `LockBarrier.lower`
  bound).
  - α(x) is continuous on {𝓘_c > 0} as a map to the circle. Implement the composite P(α(x), φ) as
    P̃(u, v, φ), with (u, v) = (√Ω X, Y/√Ω)/|·| on the unit circle and P̃ continuous there.
  - `Complex.arg` jumps on the negative axis, but P(·, φ) is 1-periodic, so P ∘ (arg/2π) is continuous; this is
    proved via `Complex.exp`-periodicity or `Circle`.
  - **Design decision:** state `LockBarrier.invariant` with `Complex.arg` (the signatures) and prove a lemma
    `continuousOn_P_arg` once.
- **Openness:** the two pieces are open (continuity of 𝓘_c, and of P∘α on {𝓘_c > r₀/2}).
- **Frontier:** frontier V ⊆ {𝓘_c = P(α, φ)}, because P ≥ I_in = r₀ gives frontier of the first piece ∩ closure V
  ⊆ interior. The proof is the same closure computation as `so_confinement`.
- **Barrier:** `gen_barrier` with F = soField, W = G = univ, S = the invariant graph, and z₀ ∉ S since
  𝓘_c(x₀) < I_in ≤ P. Global existence and uniqueness come from `so_global_exists_unique`.
- **Conclusion:** ∀ t, 𝓘_c(z t) < I_out (V ⊆ {𝓘_c < I_out}), then `abs_le_of_libAction_lt`.
- **Glue in LOCK-ASSEMBLY:** the premise 𝓘_ψ*(x₀) < I_in implies 𝓘_c(x₀) < g.pLo − disp, and the transfer back
  to ψ* gives the conclusion (§1.4).
- **Cost:** 350–550 lines.

## 6. Packages

All Lean is under `KAM/SpinOrbit/Lock/`; data are under `KAM/SpinOrbit/Data/Lock*`. Every file stays below 900
lines (cap 1500).

| package | files | lines | depends on | notes |
|---|---|---:|---|---|
| **LOCK-PO** | `Lock/PO/Green.lean`, `Lock/PO/Contraction.lean`, `Lock/PO/Orbit.lean` | 600–900 | Model, Barrier (Lipschitz of soVq) | defines `IsSyncOrbit`, `lunarSyncOrbit`; proves spec/unique/bound. **Start now**, independent |
| **LOCK-SQRT** | `Certificate/Expr/Sqrt.lean`, `Expr/BallSqrt.lean`, `Model/SqrtWitness.lean` + cases in ~12 existing checker files | 900–1500 | BALLFIX landing | trusted-engine change, own audit; owner of checker files must be assigned |
| **LOCK-COORDS** | `Lock/Coords/Maps.lean` (shift, polar, inverses), `Lock/Coords/Symplectic.lean`, `Lock/Coords/HamExpr.lean` (`lockHamExpr`, `_eval`, `_clock`) | 700–1000 | LOCK-SQRT (only for `HamExpr.lean`; the rest parametric) | |
| **LOCK-GRAPH** | `Lock/Graph.lean` | 250–400 | LOCK-COORDS, V2 engine, `Graph/Inverse` pattern | `lockBarrier_of_certV2 (g : LockGraphCert α) (hc : checkTorusCertificateV2 routeAV2 g.base w = true) (hω …) (hdio …) : LockBarrier Ω c (g.pLo − disp) (g.pHi + disp)` |
| **LOCK-CONF** | `Lock/Confine.lean` | 350–550 | Barrier, ODE | `lock_confinement`, `abs_le_of_libAction_lt`; parametric in `LockBarrier`, **start now** |
| **LOCK-GEN** | scripts + `Data/LockN65/*.lean` (shards, as R2) | data | — | running in `KAM-inp-lockgen` |
| **LOCK-DATA** | `Data/LockN65/Params.lean`, the certificate instance, `#eval`/`decide` replay modules | data + 200 | LOCK-GEN, LOCK-SQRT, COORDS | kernel replay at N = 65 |
| **LOCK-ASSEMBLY** | `Lock/Assembly.lean` (`lunar_sync_lock_of_cert` over a lawful backend), `Lock/AssemblyN65.lean` (instance + literals), provider later | 300–500 | all | `sqrt_libAction_le`; Diophantine via `lunarRotFreqPlusN_isDiophantine_65` |

**Parametric critical path:**

- **Now, in parallel:** LOCK-PO, LOCK-CONF (parametric in `LockBarrier`), LOCK-COORDS/Maps+Symplectic (parametric
  in a C² centre c and Ω), and LOCK-ASSEMBLY's glue (`sqrt_libAction_le`, and `lunar_sync_lock_of_barrier :
  LockBarrier Ω c Iin Iout → (r, r′ bounds) → (literal inequalities) → headline shape`).
- **After LOCK-SQRT:** COORDS/HamExpr, LOCK-GRAPH.
- **Then:** LOCK-DATA, then the instance.

Total: about 3.5–4.6k lines, of which 0.9–1.5k are trusted-engine lines.

## 7. Numerics under v2 at N = 65 (projection)

- **Frequency.** ω = (1/(65+g), 1) is the R2 frequency family; γ = κ/67, τ = 1. The Diophantine lemma is landed.
- **Threshold.** Under `routeAV2` the best available route for the sharp/refined certifier is the frozen-data route,
  ≈ 10⁻²⁰·⁹, on the R1 design inputs. The landed sharp route is ≈ 10⁻²⁵ (and 10⁻³²…⁻³⁴ in the scoping study's
  `sharp_q` around R2).
  - The scoping study's own threshold table used the *sharp* (`Sum.inl`) route.
  - The polar Hamiltonian has a similar torsion (|dω/d𝓘| 0.55–0.92) and M; σK grows (the embedding has
    amplitude ≈ 0.2 in α-units; the √ factor inflates |D²H| near the inner annulus radius).
  - Expect a threshold of 10⁻²⁰–10⁻³⁰. Design to a residual of 10⁻³⁵ at 160–192 bits, as in the scoping study,
    which clears every route with margin.
- **Truncation.** At a ≈ 1.37 (74°) the decay is 0.27 decade per α-harmonic and 1.14 per φ-harmonic, giving
  K ≈ 130, L ≈ 31 for 10⁻³⁵, about 4.0k half-terms per function (≈ 3.3× R2). For a 10⁻²⁵ target (refined
  threshold, if it is the binding one): K ≈ 93, L ≈ 22, about 2.0k half-terms.
- **Cost.** Products scale ≈ (half-terms)², about 11× R2 at 10⁻³⁵ (R2 replay ≈ 62k advice, 1230 shards, so
  ≈ 0.7M advice and ≈ 14k shards). The √ node adds one Newton-ball op per Ham evaluation (negligible), and the
  composition witness for √(I/π) along the torus adds one model product chain of the size of an `ExpWitness`
  (≈ +10 %).
- **Annulus.** At 74°, 𝓘 ∈ [0.012, 0.025] on the torus. The polydisc in I must avoid 0 with r < s² margin, e.g.
  centre 0.018, radius 0.009 (ratio 0.5, which gives ‖√‖ derivative growth ≤ 1/√0.009 ≈ 10.5). This drives σB/M up
  by ~2–3×, one more reason to aim at 10⁻³⁵.
- **LOCK-GEN notes:** `/root/code/KAM-inp-lockgen` had no LOCK-GEN notes yet at writing; it is at `fa002b43` and
  only holds the scoping data. The numbers above are the scoping study's projections, and LOCK-GEN's
  high-precision run supersedes them.

## 8. Decisions, risks, errata, departures

**Decisions taken (reversible; owner review):**

- **(R1) ψ\* is characterised globally** (unique odd 1-periodic synchronous orbit), not ball-pinned.
- **(R2) LOCK-PO by Banach contraction** in sup norm with c = 0, not Newton–Kantorovich in weighted ℓ¹.
- **(R3) Coarse ellipse bounds** for Rψ, Rp (Rp ≈ 3.7 % vs the true 2.5 %).
- **(R4) Drop `lunar_sync_lock_nonvacuous`.**
- **(R5) Write the orbit equation through frozen `soField`** at freeze time.
- **(R6) `NonvanishingOn` for sqrt uses `0 < re`.**

**Risks:**

- Checker files are shared with BALLFIX and V2, so there will be merge contention.
- Arg-continuity bookkeeping in LOCK-CONF.
- √ near the inner annulus edge inflates the majorants.
- Kernel cost ≈ 11× R2.
- The tube transfer needs |c_gen| small (true: c_gen ≈ ψ*).

**Suspected errata:**

- **SO-LOCK-SCOPE §1 L3** says certifying the periodic orbit needs "an additional Newton–Kantorovich certificate".
  A data-free contraction suffices (§2.1). This is a non-pinned note.
- **SO-LOCK-SCOPE §2 route (a′)** names `checkTorusCertificateSharp`. The current certifier is
  `checkTorusCertificateV2 routeAV2` (D44); the sharp certifier is its `Sum.inl` route, so the statement is not
  wrong, only dated.

**Departures from the brief:**

- Newton–Kantorovich was replaced by Banach in sup norm (§2.2 has the justification).
- The orbit is pinned by global uniqueness instead of "within δ of c".
- The `HamExpr.sqrt` ball, jet and witness rules are specified here but not given Lean signatures, because they
  need the new constructor. Only the semantic lemmas are in the signatures file.
