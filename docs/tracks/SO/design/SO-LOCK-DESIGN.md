# SO-LOCK: Lean design of "the Moon stays locked in synchronous rotation forever"

**Status:** design, revision 2, 30 October 2026 (package DESIGN-LOCK, branch `inp-lockdesign`). No proofs, nothing
frozen.

- **Revision 2** answers design audit 1 ([`SO-LOCK-design-audit-1.md`](SO-LOCK-design-audit-1.md), FAIL: F1–F3,
  N1–N5). It adopts the main orchestrator's change to F1 (total real-preserving `sqrtE`) and the LOCK-GEN-1
  numerics. The response table is in §9.
- **Governing decisions:**
  - D45: route (a′), statement L1, N = 65, certified periodic orbit, no Birkhoff;
  - its addendum: the headline names ψ*;
  - D29/D34–D44: the certifier and the SO stack.
- **Sources:**
  - [`SO-LOCK-SCOPE.md`](../studies/SO-LOCK-SCOPE.md);
  - `inp-lockgen:docs/tracks/SO/studies/LOCK-GEN-NUMERICS.md` and `.drafts/handoff-LOCK-GEN-1.md` (LOCK-GEN-1).
- **Lean text:** `.drafts/design/SOLockSignatures.lean`, 342 lines. It elaborates with 29 `sorry` warnings and no
  other diagnostic (§1.6).
- **Owner-facing statements:** [`FREEZE-PROPOSAL-LOCK.md`](FREEZE-PROPOSAL-LOCK.md).

**Notation.** Period-one units, in the landed model `soField` on x = (q, p, φ). `soField` is approved for freezing
by D40 but **not yet frozen**: there is no `KAM/Frozen/SpinOrbit`.

- ψ = q − φ, in turns.
- q̇ = p, ṗ = −soVq(q, φ), φ̇ = 1.
- A *synchronous orbit* is a function ψ(φ) with q(t) = φ(t) + ψ(φ(t)) and p = 1 + ψ′(φ). Equivalently,
  ψ″(φ) = −soVq(φ + ψ(φ), φ).

## 0. Summary

- **Headline `lunar_sync_lock`.** Suppose the libration action of the initial state around ψ* is below 129/10000.
  Then the solution is global and unique, and for all real t:
  - |ψ(t) − ψ*(φ(t))| ≤ 21/100;
  - |p(t) − 1 − ψ*′(φ(t))| ≤ 26/1000;
  - |q(t) − φ(t)| < 1/4.

  ψ* = `lunarSyncOrbit` is a named definition: the unique odd one-periodic synchronous orbit. The literals come
  from LOCK-GEN-1's N = 65 torus and Ω = 8/65 by the rules of §1.4. They are provisional until the kernel accepts
  the certificate.
- **LOCK-PO.** A Banach contraction in sup norm on odd periodic functions. It gives existence, uniqueness among
  odd orbits and the location bound, with no kernel data.
- **Route (a′):**
  - the LOCK-GEN centre c (data; it appears in no headline statement);
  - an exact shift to the landed rotated frame;
  - elliptic polar coordinates with Ω = 8/65;
  - `checkTorusCertificateV2 routeAV2`, unchanged;
  - one new `HamExpr` constructor `.sqrt`, with **total real-preserving semantics `sqrtE`** (F1 as changed by the
    orchestrator). **No landed declaration's statement changes**; the landed files get only new match cases (§4.6).
- **Estimate:** 3.6–4.8k new Lean lines, every new file under 900 lines, plus about 0.3–0.6k lines of new match
  cases in 13 landed checker files (§4.6).

## 1. Statements

### 1.1 Meaning-carrying definitions (exact text in the signatures file)

```lean
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = -soVq (φ + ψ φ) φ

open Classical in
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

def lunarOmega : ℚ := 8 / 65
```

- **The orbit equation.** For the freeze, write it as `(soField (φ + ψ φ, 1 + deriv ψ φ, φ)).2.1`, which equals
  `-soVq …` by the landed `soField_eq` (the audit checked the bridge). The statement then mentions only the
  definitions approved for freezing in D40.
- **Oddness is essential.** It gives the Dirichlet values ψ(0) = ψ(1/2) = 0. Uniqueness among all one-periodic
  orbits is **false**: q has period 1/2 in the force, so ψ + 1/2 is another orbit, namely the second synchronous
  orientation (audit N4). The design claims uniqueness only among odd orbits.
- **`Classical.choose`.** The definition is canonical by `lunarSyncOrbit_unique`. The fallback branch is excluded
  by `lunarSyncOrbit_spec`.
- **"The resonance angle stays bounded"** is written literally: `|(z t).1 - (z t).2.2| < 1 / 4`.
- The polar coordinates and the solid torus do not appear in the headline. They are in §3 and §5.

### 1.2 Theorems for the freeze proposal

```lean
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 17 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 27 / 200000
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
```

`lunar_sync_lock_nonvacuous` stays in the signatures file. It is trivial (ψ* has action 0), and dropping it is
recommended (Q4).

### 1.3 Choice of the orbit name

Three options were considered:

- **An existential orbit:** rejected by the addendum.
- **A ball-pinned predicate:** puts Fourier data into the frozen text.
- **The global odd characterisation (chosen):** canonical through the contraction, and it carries no data.

### 1.4 Literal rules and the numbers (N1: from proved rational bounds)

**Orbit constants**, by exact rational arithmetic with π ≤ 31416/10000 and the exact rationals
Aₘ = `soAQ m`, e = 549/10000, ε = 69/200000:

- Σ|Aₘ| = 0.61973;
- L = 16π²εΣ|Aₘ| ≤ 0.033764 (the Lipschitz constant of soVq in q);
- η = 4πεΣ_{m≠2}|Aₘ| ≤ 5.3540·10⁻⁴ (the sup of the forcing at ψ = 0).

**Contraction around 0 (§2):**

- r₀ := sup|ψ*| ≤ η/(32 − L) = 1.6749·10⁻⁵ ≤ **17/10⁶**;
- r₁ := sup|ψ*′| ≤ (η + L·r₀)/4 = 1.3399·10⁻⁴ ≤ **27/200000** (= 1.35·10⁻⁴).

These are `lunarSyncOrbit_bound`, proved by `norm_num` from the majorants. The literals of revision 1,
13/10⁶ and 1/10⁴, were not reachable by this argument (audit N1) and are replaced.

**Transfer to the certified centre c:**

- sup|c| ≤ Σ|c_k| = 1.23677·10⁻⁵;
- sup|c′| ≤ 2π Σ k|c_k| = 8.0123·10⁻⁵.

Hence:

- r := sup|ψ* − c| ≤ 2.937·10⁻⁵;
- r′ := sup|ψ*′ − c′| ≤ 2.152·10⁻⁴;
- δ := √π (√Ω r + r′/√Ω) ≤ 1.106·10⁻³, with Ω = 8/65 and √Ω = 0.35082.

**Rules**, with lo = g.pLo − disp and hi = g.pHi + disp the certified barrier range. The certified tube is
`sqrt_libAction_le`: √𝓘_c ≤ √𝓘_ψ* + δ.

- **I_in:** the largest 3-significant-digit rational with (√I_in + δ)² < lo.
- **Rψ:** the smallest 2-digit rational with √(hi/(πΩ)) + r ≤ Rψ.
- **Rp:** the smallest 3-digit rational with √(Ωhi/π) + r′ ≤ Rp.
- **Corollary:** Rψ + r₀ < 1/4.

The outputs are bounded around c and then transferred by the pointwise triangle inequality. This is not
re-transferred through δ; revision 1 added δ twice (audit N1, "conservative").

**Numbers** (LOCK-GEN-1: P ∈ [0.013238, 0.016258]; disp ≈ 10⁻³⁸ is negligible):

| literal | value | margin |
|---|---|---|
| I_in | 129/10000 | (√0.013238 − δ)² = 0.012985 |
| Rψ | 21/100 | √(0.016258/(π·8/65)) + r = 0.20509 |
| Rp | 26/1000 | √(8/65 · 0.016258/π) + r′ = 0.025452 |
| corollary | 0.21 + 1.7·10⁻⁵ < 1/4 | — |

Physically, the tube reaches 66° of libration at zero spin offset (|X| ≤ √(I_in/(πΩ)) = 0.1827 turn), and the confinement is
21/100 turn = 75.6° and 2.6 % in spin. The real Moon's forced libration (15.5″) is deep inside the tube.

`lockLiteralCheck` (§7) re-verifies these inequalities from the certificate's `pLo`/`pHi` with rational majorants
of √ and π. It is a `Bool` decided by kernel reduction in a proof term, not by `#eval`.

### 1.5 Parametric helpers (unfrozen; distinct names; hypotheses are conclusions of pending packages)

All of these are typed in the signatures file:

- `LockBarrier`, `lock_confinement`, `abs_le_of_libAction_lt`, `sqrt_libAction_le` (§5);
- the coordinate contracts (§3);
- the sqrt contracts (§4);
- `LockGraphCert`, `lockBarrier_of_certV2`, `lockLiteralCheck`, `lunar_sync_lock_of_cert` (§7).

`LockBarrier.invariant` is **produced** by `lockBarrier_of_certV2` from the certifier and the conjugacy. It is
never assumed by a source-level theorem.

### 1.6 Elaboration

The command was `inp_sig_check.sh /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignatures.lean`, slot 1,
16:21 UTC, against the `inp` build.

- Exit 0, with 29 warnings `declaration uses 'sorry'` and no other diagnostic.
- The first run of revision 2 failed on a missing `open KAM.CertificateSharp.V2` (`routeAV2`). That was fixed and
  re-run.
- The scratch copy was deleted.
- Three placeholder definitions have `sorry` bodies, marked in their docstrings. They cannot be written before
  the `.sqrt` constructor and the checker exist:
  - `lockHamExpr`;
  - `sqrtWitnessRadius`;
  - `lockLiteralCheck`.

## 2. The synchronous periodic orbit (LOCK-PO)

### 2.1 Method: Banach contraction in sup norm on odd periodic functions

**Space.** B = {d ∈ `ℝ →ᵇ ℝ` | d is 1-periodic and odd}. It is a closed subset of a complete space, so it is
complete.

**Map.** G is the Dirichlet inverse of ∂² on [0, 1/2], extended oddly and periodically:

- (G f)(φ) = ∫₀^φ∫₀^s f − 2φ∫₀^{1/2}∫₀^s f on [0, 1/2];
- ‖G f‖∞ ≤ ‖f‖∞/32 and ‖(G f)′‖∞ ≤ ‖f‖∞/4.

Then T(d) := G(−soVq(φ + d, φ)), centred at 0.

**Contraction.** ‖T d − T e‖ ≤ (L/32)‖d − e‖ with L/32 ≈ 1.06·10⁻³.

**Mathlib APIs** (checked by the audit):

- `ContractingWith`, `ContractingWith.fixedPoint`, `ContractingWith.dist_fixedPoint_le`,
  `ContractingWith.fixedPoint_unique'`;
- completeness of `BoundedContinuousFunction`;
- `intervalIntegral.integral_hasDerivAt_right` for G.

**Location.** ‖d*‖ ≤ ‖T 0‖/(1 − L/32) ≤ (η/32)/(1 − L/32) = η/(32 − L). The bound on d*′ is |(G f)′| ≤ ‖f‖/4
with ‖f‖ ≤ η + L‖d*‖ (§1.4).

**Regularity.** d* = T d* = G(continuous) is C², and the equation holds pointwise.

**Uniqueness among odd orbits.** Let ψ satisfy `IsSyncOrbit`. Odd plus periodic gives ψ(0) = ψ(1/2) = 0, and ψ″ is
continuous. Uniqueness of the Dirichlet problem u″ = f, u(0) = u(1/2) = 0 gives ψ = G(ψ″) = Tψ, so ψ = d*.

**Lean cost and risk.** 600–900 lines in `Lock/PO/{Green,Contraction,Orbit}.lean`. Risk is low. The package is
independent of all certificate code, so **it can start now**.

### 2.2 Alternatives evaluated

| route | proves | Lean | risk |
|---|---|---|---|
| **Banach in sup norm (chosen)** | existence, uniqueness among odd orbits, location | 600–900 | low |
| radii polynomial / NK in weighted ℓ¹ (LOCK-GEN-1 closes it numerically: r ∈ [2.3e-59, 1.6e-3]) | existence, local uniqueness, analytic bounds | 1.5–2.5k | medium–high: an ℓ¹ sine algebra, sin-composition, an analytic tail beyond l = 127 (LOCK-GEN caveat) |
| Brouwer on the invariant disc | existence only, location ≈ 0.2 turn | ~1k + 2-D Brouwer (not in Mathlib) | high |

The sharper NK location, 5.5·10⁻⁹ to c, is not needed: δ is dominated by r′ from the crude bound and costs only
0.6 % of √I.

## 3. Coordinates (LOCK-COORDS), corrected after audit F3

**Landed frames.**

- Physical: ((q, φ), (p, J)).
- Rotated: ((Q₀, Q₁), (P₀, P₁)), with `soRotMap` mapping **rotated → physical**:
  - (q, φ) = (Q₀ + Q₁, Q₁);
  - (p, J) = (P₀, P₁ − P₀).
- In the rotated frame, P₀ = p is the *physical* spin, not p − 1, and
  H′ = soRotHC = P₀²/2 − P₀ + P₁ + V(Q₀ + Q₁, Q₁).

**Lock map.** It goes from z = ((α, φ), (I, J̃)) to the rotated frame (exact text: `lockX`, `lockY`, `lockToRotR`):

- X = √(I/(πΩ)) sin 2πα and Y = √(IΩ/π) cos 2πα;
- Q₀ = c(φ) + X, Q₁ = φ;
- P₀ = **1 + c′(φ) + Y**;
- P₁ = J̃ − c′(φ)(c′(φ) + Y) + X c″(φ).

**Symplecticity.**

- The shift comes from F₂(Q; Y, J̃) = (Q₀ − c(Q₁))(1 + c′(Q₁) + Y) + Q₁J̃. That gives P₁ = J̃ − c′(1 + c′ + Y) + Xc″.
- `lockToRotR` drops the summand −c′(φ). This is a function of φ alone: the shear P₁ ↦ P₁ + f(Q₁) is symplectic,
  since f′ dQ₁∧dQ₁ = 0. Dropping it gives the audit's cleaner Hamiltonian.
- The 2-form sign (corrected): dY∧dX = dI∧dα, equivalently dX∧dY = dα∧dI. This is compatible with the frozen
  convention Σ dIᵢ∧dθᵢ, in which X_H = (∂_I H, −∂_θ H) (`KAM.hamiltonianVectorField`).

**Transformed Hamiltonian** (`lockHamiltonianR`):

K = H′ ∘ lockToRotR = J̃ + Y²/2 − c′²/2 + Xc″ + V(φ + c + X, φ) − 1/2.

To check: P₀²/2 − P₀ = (c′ + Y)²/2 − 1/2, and adding P₁ gives the formula.

**Physical projection** (`lockToPhysicalR`): soRotMap ∘ lockToRotR without the clock action, i.e.
(φ + c + X, 1 + c′ + Y, φ). The lemma is `lockToPhysicalR_eq`.

**Contracts** (all typed in the signatures file):

- `libAction_lockToPhysicalR`: 𝓘_c ∘ Φ = I for I ≥ 0.
- `lockToPhysicalR_surj`: the explicit inverse on {𝓘_c > 0}, with angle arg(Y/√Ω + i√Ω X)/2π and action
  `libAction`.
- `lock_conjugacy` (hΩ, **hc : ContDiff ℝ 3 c**, I > 0): fderiv Φ · X_K = soField ∘ Φ. C³ is needed because the
  P₁ component contains c″, whose derivative enters through ∂_φ K. The lock centre is a trigonometric polynomial
  (`lockCentre_contDiff`, C^∞).
- **Complex side** (`lockToRotC`): the same formulas with `sqrtE` and the explicit complex centre and derivatives
  `lockCentreC`, `lockCentreDC`, `lockCentreDDC`. They are written as sine/cosine sums, not `deriv`.
  - `lockToRotC_ofReal` (I > 0) ties it to `lockToRotR (lockCentre cs)`.
  - `lockHamExpr_eval` holds **for all z**, because `sqrtE` is total: (lockHamExpr Ω cs).eval z = soRotHC
    (lockToRotC Ω cs z).
  - `lockHamExpr_clock` holds on 0 < Re I.

**Expression.** `lockHamExpr` is written with:

- `.sqrt (.div (.mul (.const (1/Ω)) (.action 0)) .pi)` and its Ω-twin for √(I/(πΩ)) and √(IΩ/π);
- `sinMode`/`cosMode` on keys (1, 0) for sin/cos 2πα and (0, k) for the centre;
- V expanded through the landed `.cos`/`.sin` nodes of the composite argument 2π(2(c + X) + (2 − m)φ).

**Invariant-set transport.** Only the invariant set is transported, never the flow. LOCK-GRAPH builds, for each
point of the graph, the physical orbit `Φ(K∞(θ + tω))`:

- it is a `soField` solution by `lock_conjugacy`;
- it is unique by `so_global_exists_unique`.

This is the pattern of `Graph/Inverse.lean:223–236` (`soGraph_invariant`). No global inverse polar angle is
needed, and no annulus-exit argument either.

## 4. `HamExpr.sqrt` (LOCK-SQRT), revised for F1 (orchestrator's change) and F2

### 4.1 Semantics: total and real-preserving (F1)

```lean
def sqrtE (z : ℂ) : ℂ := if z.im = 0 ∧ z.re ≤ 0 then 0 else z ^ (1 / 2 : ℂ)
```

- **Like Lean's 0⁻¹ = 0.** It is 0 on the closed nonpositive real axis and the principal root elsewhere.
- **Reals go to reals.** A real x ≤ 0 goes to 0; a real x > 0 goes to the real root. So the landed
  `HamExpr.exists_real_eval` and `HamExpr.eval_real` **stay true unconditionally with their text unchanged**: one
  new proof case each, `sqrtE_ofReal`. The consumer `TorusCertificate.ham_structural` (`Sound/Ham.lean:77`) is
  untouched.
- **Holomorphy.** `sqrtE` agrees with the principal root on `Complex.slitPlane`, which is open, so it is
  holomorphic there (`differentiableAt_sqrtE`). Proof: `DifferentiableAt.cpow_const` from
  `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, plus eventual equality. Revision 1 cited a nonexistent name (N3).
  In particular `sqrtE` is holomorphic on the certified region Re z > 0.
- **Further lemmas:** `sqrtE_sq` (on the slit plane), `sqrtE_re_nonneg` (everywhere), and `hasDerivAt_sqrtE`
  (Re > 0, derivative 1/(2√z)).

### 4.2 Domain safety (like `inv`)

- Revision 1's `NonvanishingOn` change is withdrawn: `HamExpr.NonvanishingOn` is not modified.
- Instead, the new `SlpOp.sqrt a` gets a certified condition `SlpSqrtGood n S ops`: every sqrt operand has
  re > 0 on S. This is the analogue of `SlpInvGood` (`Expr/Ball.lean:380`), and it comes with
  `Slp.sqrtGood_of_balls`.
- Analyticity of the compiled program is proved under `SlpInvGood ∧ SlpSqrtGood`, exactly as the inv case is.
  At the `HamExpr` level, `contDiffOn_eval`'s premise `NonvanishingOn` does not mention sqrt.
- The statement of `HamExpr.contDiffOn_eval` therefore cannot get a sqrt case without a premise. **It keeps its
  text.** Its `.sqrt` case is proved only for expressions whose sqrt arguments are certified; otherwise it needs a
  premise.

**Resolution.** Extend `NonvanishingOn` with a `.sqrt` match arm, i.e. *add a new equation for the new
constructor*:

```lean
| .sqrt a, S => a.NonvanishingOn S ∧ ∀ z ∈ S, 0 < (a.eval z).re
```

- This changes no existing equation, so no landed statement's text changes, and no instance becomes false.
- `contDiffOn_eval` then gets its new case from `differentiableAt_sqrtE`.
- `checkHamBounds_sound` must produce `NonvanishingOn` for sqrt nodes from `SlpSqrtGood` (new lemma
  `nonvanishingOn_of_sqrtGood`), as it does today for `div` from `SlpInvGood`.

### 4.3 Ball rule (outward rounded)

`sqrtE_ball`: |z − s²| ≤ r < s² and s > 0 give 0 < Re z and |√z − s| ≤ r/s.

**The `ballStep` sqrt case:**

1. From the operand ball (m, ρ) with ρ < Re m, compute a dyadic s ≈ √|m| by a rational Newton step.
2. Bound r ≥ |m − s²| + ρ, rounded up.
3. **Check r < s²**, which certifies Re > 0 on the ball. Failure returns `none`, as the inv test does.
4. Output the ball (s, r/s rounded up), using the same outward dyadic rounding as the D39 `ballRound` (BALLFIX)
   for `mul`/`inv`.

New lemmas: `ballStep_sqrt_sound` and the `SlpSqrtGood` prefix lemma (the analogue of `ballsAux_prefix_inv`).

### 4.4 Jet and derivative rules

- d√f = f′/(2√f). The differentiation layer (`Diff`, `DiffNode`, `DiffBuild`, `DiffCalculus`, `DiffCalculus3`)
  emits `.div f′ (.mul (.const 2) (.sqrt f))` and reuses the `div`/`inv` soundness.
- The new node-level lemma is `hasDerivAt_sqrtE` on Re > 0.
- The second and third derivatives used by `DiffCalculus3` follow by re-differentiating the emitted expression.
  No new jet primitive is introduced.

### 4.5 Composition witness (F2: positive real anchor)

Revision 1's witness accepted the opposite root (the audit's counterexample: f = 1, W = −1). The replacement:

- **Witness:** `SqrtWitness α := {poly : CertPoly α, anchor s : ℚ, margin d : ℚ}`.
- **Checker:** `sqrtWitnessRadius n W cfg g S : Option α`. It checks, all with outward-rounded model arithmetic:
  1. 0 ≤ d < s;
  2. ‖W − s‖_strip ≤ d (the model sup bound of `poly − s`);
  3. ‖g − W²‖ ≤ ε;
  4. ‖g − s²‖ < s², which gives Re g > 0 on the strip by the scalar ball rule.

  It returns ε/(s − d), rounded up.
- **Soundness:** `sqrtWitness_sound` concludes `(∀ θ ∈ strip, 0 < Re g θ) ∧ ⟨0, W, r⟩.Encloses (sqrtE ∘ g)`.
  - Pointwise it reduces to `sqrtE_model_error`: Re W ≥ s − d > 0 and Re √f ≥ 0, so |√f + W| ≥ s − d and
    |√f − W| = |f − W²|/|√f + W| ≤ ε/(s − d).
  - The model bounds are uniform sup bounds on the strip, the same semantic norm as `CertModel.Encloses`, so no
    coefficient-norm/pointwise mixing occurs.
- **Use.** The torus Hamiltonian composes √ with the action model I(θ) ∈ [0.0132, 0.0163]. With s² ≈ mean I and
  d ≈ the spread of √I (≈ 0.006 against s ≈ 0.12), the margin is ample.

### 4.6 Landed files that get a new match case (N5 inventory)

**No landed declaration's statement changes.** Every new obligation is a new name or a new case of an existing
induction. Line counts are as of this revision; the cap rechecks happen in LOCK-SQRT.

| landed file (lines) | new case / lemma |
|---|---|
| `Certificate/Expr/Basic.lean` (208) | constructor `sqrt`; `eval` arm `sqrtE`; `NonvanishingOn` arm; cases of `contDiffOn_eval`, `eval_add_int`, `exists_real_eval` |
| `Certificate/Expr/Slp.lean` (125) | `SlpOp.sqrt`, its value, the `slpCompile` arm |
| `Certificate/Expr/Ball.lean` (506) | `ballStep` arm, `SlpSqrtGood`, `Slp.sqrtGood_of_balls`, prefix lemma, compile/eval agreement case |
| `Certificate/Expr/Diff.lean` (445), `DiffNode.lean` (669), `DiffBuild.lean` (343), `DiffCalculus.lean` (163), `DiffCalculus3.lean` (236) | emission arm and its soundness case |
| `Certificate/Expr/Compose.lean` (472), `ComposeModels.lean` (432) | witness list `sqrtWit`, composition arm, soundness case |
| `Certificate/Sound/Ham.lean` (158) | `nonvanishingOn_of_sqrtGood` use in `checkHamBounds_sound` (proof only) |
| `CertificateSharp/Ham/BallsTrig.lean` (409) | trig-ball arm (coordinate with BALLFIX) |
| `CertificateSharp/Kernel/Prune.lean` (222) | pass-through arm for `SlpOp.sqrt` |
| `Certificate/Tests/Ball.lean` (84) | test arm if exhaustive |

**New files:**

- `Certificate/Expr/Sqrt.lean`: `sqrtE` and its lemmas;
- `Certificate/Expr/BallSqrt.lean`;
- `Certificate/Model/SqrtWitness.lean`.

The certificate format gains one SLP opcode and an optional `sqrtWit` list. Existing certificates are unchanged:
they contain no sqrt and their checks reduce identically.

**Ownership.** These files are shared checker code, outside track SO. The orchestrator must assign LOCK-SQRT as a
D34/D39-style checker change with an independent audit (D45). LOCK-SQRT must start from `inp` after BALLFIX
lands, because BALLFIX is not landed and clashes with `BallsTrig`.

## 5. Confinement (LOCK-CONF), unchanged by the audit (consumer PASS)

**The region.** V = {𝓘_c < r₀} ∪ {r₀/2 < 𝓘_c < P(α, φ)}, with r₀ = Iin, the barrier's lower bound.

- **α and the branch cut.** α = arg(Y/√Ω + i√Ω X)/2π. Since P is 1-periodic in α, P∘α is continuous on {𝓘_c > 0}
  despite the cut of `Complex.arg`. This is one lemma, `continuousOn_P_arg`.
- **Open and frontier.** V is open, and frontier V ⊆ {𝓘_c = P(α, φ)}, because P ≥ Iin.
- **`gen_barrier`.** Apply it with W = G = J = univ and S = the invariant graph. The initial point is not in S
  because 𝓘_c(x₀) < Iin ≤ P. Global existence and uniqueness come from `so_global_exists_unique`.
- **Conclusion.** For all t, 𝓘_c(z t) < Iout, and then `abs_le_of_libAction_lt` gives the coordinate bounds.
- **Cost.** 350–550 lines. **It can start now**, because it is parametric in `LockBarrier`.

## 6. Packages

The new Lean files are `KAM/SpinOrbit/Lock/**` and the three new checker files of §4.6. The exceptions are the
landed checker files of §4.6, which get match cases only. Data live in `KAM/SpinOrbit/Data/LockN65/**`. Every new
file is planned under 900 lines (cap 1500).

| package | files | lines | depends on | can start |
|---|---|---:|---|---|
| **LOCK-PO** | `Lock/PO/{Green,Contraction,Orbit}.lean` | 600–900 | Model, Barrier | now |
| **LOCK-CONF** | `Lock/Confine.lean` | 350–550 | Barrier, ODE | now |
| **LOCK-COORDS-R** | `Lock/Coords/{Maps,Inverse,Conjugacy}.lean` (real maps, inverse, `lock_conjugacy`, `lockCentre_contDiff`) | 600–900 | Model, Rotated | now |
| **LOCK-SQRT** | 3 new files + cases in 13 landed files (§4.6) | 900–1500 + 300–600 | BALLFIX landed; ownership assigned | after BALLFIX |
| **LOCK-COORDS-C** | `Lock/Coords/{Complex,HamExpr}.lean` (`lockToRotC`, `_ofReal`, `lockHamExpr`, `_eval`, `_clock`) | 400–600 | LOCK-SQRT (Expr/Sqrt only) | after SQRT's `Expr/Sqrt` |
| **LOCK-GRAPH** | `Lock/Graph.lean` (`LockGraphCert`, `lockBarrier_of_certV2`) | 300–450 | COORDS, V2 engine, `Graph/Cert` | after COORDS-C |
| **LOCK-GEN** | scripts, data emitter | — | — | running |
| **LOCK-DATA** | `Data/LockN65/*.lean`: the certificate as a `def`, shards, and the kernel-checked theorems `lockN65_check : checkTorusCertificateV2 routeAV2 cert w = true := by decide`-style (proof declarations; **no `#eval` in production**, N5; diagnostic evaluation only in scripts or scratch) | data + 200 | GEN, SQRT, COORDS-C | last |
| **LOCK-ASSEMBLY** | `Lock/Assembly.lean` (`sqrt_libAction_le`, `abs_le_of_libAction_lt`, `lockLiteralCheck` and its soundness, `lunar_sync_lock_of_cert`), `Lock/AssemblyN65.lean` (instance, literals, `lunarRotFreqPlusN_isDiophantine_65`) | 400–600 | all | glue now; instance last |

**Parametric critical path:**

1. Now: PO, CONF, COORDS-R, and the ASSEMBLY glue.
2. Then: SQRT, which needs BALLFIX and an owner.
3. Then COORDS-C, then GRAPH, then DATA, then the instance.

**Totals:** 3.6–4.8k new lines plus 0.3–0.6k lines of cases.

## 7. Numerics under v2 at N = 65 (from LOCK-GEN-1)

**Data.**

- **Frequency.** ω = 1/(65 + g) = 0.0152397…, γ = κ/67, τ = 1. The Diophantine lemma is landed.
- **Coordinates.** Centre `lunarLockCentre` (3 harmonics; sup|ψ* − c| = 5.5·10⁻⁹) and Ω = 8/65, the roundest
  choice: P spread ±10 %.
- **Torus.** The amplitude is 73.8°, P ∈ [0.013238, 0.016258], and the twist is dω/d⟨P⟩ ≈ −1.24.
- **Annulus.** For the sqrt domain, take I ∈ [1/80, 1/60], i.e. centre 7/480 and radius 1/480 (ratio 0.14), so
  the ball check r < s² holds with a wide margin. |d√I/dI| ≤ 1/(2√(1/80)) ≈ 4.5, which is a modest increase in
  the majorants.
- **Decay.** 0.29 decades per α-harmonic and 1.45 per φ-harmonic.
- **Full support.** |k| ≤ 129, |l| ≤ 27, with a tail of 4·10⁻⁴⁰ and about 7.1k half-terms per function.
  - The truncated residual is E_α = 4.7·10⁻³⁹ and E_I = 5.2·10⁻⁴².

**Thresholds** (projections with R1's M and σ):

| route | threshold |
|---|---|
| sharp mirror (`Sum.inl`), γ = κ/67 | 10^−28.7 |
| v2 refined (routeARefined) | 10^−12.1 to 10^−12.9 |

**Sizing recommendation.** Truncate to the threshold of the route actually witnessed, with 3 decades of headroom.

| route witnessed | target | support (from the decay) | half-terms | products vs R2 (1.2k) |
|---|---|---|---:|---:|
| v2 refined (**recommended first**) | 10^−16 | \|k\| ≤ 55, \|l\| ≤ 11 | ≈ 1.3k | ≈ 1.2× |
| sharp (fallback) | 10^−32 | \|k\| ≤ 110, \|l\| ≤ 22 | ≈ 5.0k | ≈ 17× |
| full LOCK-GEN data | 10^−39 | 129 × 27 | ≈ 7.1k | ≈ 35× |

- **Kernel cost.** The refined core costs about 140 s and 10.4 GB at prefix 3 (SHARP-CERTIFIER-FOR-SO). The extra
  Ham, frame and sqrt-witness checks add roughly one `checkHamBounds` plus one model product chain (≈ +10 %).
  - At the recommended size, the checker cost is close to R2's.
  - At the sharp fallback, it is ≈ 17× R2's (ballpark ≈ 1M advice and ≈ 20k shards).
  - A diamond support roughly halves every row.
- **Caveat.** The thresholds reuse R1's M and σ, not lock-package constants. √ raises M and σB, and the twist
  (−1.24) differs from R1's. LOCK-GEN phase 2 must compute the lock-package constants before the support is
  fixed. If the refined margin falls below 2 decades, use the sharp row.

## 8. Decisions, risks, errata, departures

**Owner review** (reversible choices taken):

- **Q1:** characterise ψ* globally among odd orbits.
- **Q2:** write the orbit equation through `soField`.
- **Q3:** accept the ellipse bounds (Rp = 2.6 % against the true 2.51 %; the earlier coarseness is gone with
  Ω = 8/65).
- **Q4:** drop the trivial non-vacuity theorem.
- **Q5:** freeze `lunarSyncOrbit_bound` with 17/10⁶ and 27/200000.
- **Q6:** fix the literals by the rules of §1.4 from the kernel-passed data.
- **Q7 (new):** keep the LOCK-GEN centre c (rational, 3 harmonics) for the coordinates while the headline is
  stated around ψ*. The tube transfer costs 0.6 % of √I.

**Risks:**

- contention in the shared checker files (BALLFIX, V2);
- arg-continuity in LOCK-CONF;
- the lock-package constants are not computed yet, and √ inflates the majorants;
- `DiffCalculus3` and the third-derivative claims of v2 through the sqrt emission;
- kernel cost if the sharp fallback is needed.

**Errata** (non-pinned notes):

- SO-LOCK-SCOPE §1 L3 says certifying the orbit needs Newton–Kantorovich. The contraction suffices.
- SO-LOCK-SCOPE §2 names `checkTorusCertificateSharp`. That name is dated (D44).
- Revision 1 of this design (now corrected):
  - the Lipschitz constant 0.067 was overstated (the true value is ≤ 0.0338);
  - the 2-form sign was wrong;
  - the map direction was wrong;
  - the momentum translation was missing;
  - it claimed uniqueness without oddness;
  - it cited a nonexistent Mathlib name.

**Departures from the brief:**

- Banach instead of Newton–Kantorovich.
- Uniqueness among odd orbits instead of "within δ of c".
- Three placeholder definitions with `sorry` bodies in the signatures file (§1.6).

## 9. Response to design audit 1

| finding | fix | location |
|---|---|---|
| F1 HIGH: principal sqrt breaks `exists_real_eval`/`eval_real` | Orchestrator's change adopted: total real-preserving `sqrtE` (0 on nonpositive reals). The landed statements are unchanged and get one new case each. Domain safety comes from the ball check r < s² and `SlpSqrtGood` (the analogue of `SlpInvGood`), plus a new `NonvanishingOn` arm. Consumer `ham_structural` is untouched. Full case inventory in §4.6. | §4.1–4.2, §4.6; sig `sqrtE`, `sqrtE_ofReal`, `differentiableAt_sqrtE`, `sqrtE_sq`, `sqrtE_re_nonneg`, `hasDerivAt_sqrtE` |
| F2 HIGH: the witness accepts the opposite root | Positive real anchor s, margin 0 ≤ d < s, error ε/(s − d). Typed witness, checker and soundness. | §4.5; sig `sqrtE_model_error`, `SqrtWitness`, `sqrtWitnessRadius`, `sqrtWitness_sound` |
| F2 (scalar) | `sqrtE_ball` now also concludes 0 < Re z | §4.3; sig `sqrtE_ball` |
| F3 HIGH: map direction, P₀ translation, 2-form sign | Exact real and complex maps with P₀ = 1 + c′ + Y; `soRotMap` is rotated → physical; dY∧dX = dI∧dα; `lock_conjugacy` with `ContDiff ℝ 3 c`; complex eval identity through `lockToRotC` | §3; sig `lockX`, `lockY`, `lockToRotR`, `lockToPhysicalR`, `lockHamiltonianR`, `lockToPhysicalR_eq`, `libAction_lockToPhysicalR`, `lockToPhysicalR_surj`, `lock_conjugacy`, `lockCentre*`, `lockToRotC`, `lockToRotC_ofReal` |
| N1: literals not reachable | Literals recomputed from proved rational majorants: 17/10⁶, 27/200000. Tube and output literals from LOCK-GEN-1: 129/10000, 21/100, 26/1000, Ω = 8/65. The rules no longer double-count δ. `lockLiteralCheck` re-verifies them. | §1.4; sig `lunarSyncOrbit_bound`, `lunar_sync_lock`, `lunarOmega`, `lockLiteralCheck` |
| N2: untyped interfaces | Typed: `LockGraphCert`, `lockBarrier_of_certV2` (with the `hham` tie, Ω, κ, positivity margin, V2 witness, lawful backend), `lunar_sync_lock_of_cert`, `lockHamExpr_eval`/`_clock`, and the map, inverse and conjugacy contracts. `LockBarrier.invariant` is produced, not assumed. | §1.5, §3, §7; sig §§6–7 |
| N3: nonexistent Mathlib name | Uses `DifferentiableAt.cpow_const` (import `Pow.Deriv`) | §4.1; sig imports |
| N4: uniqueness without oddness | Claim deleted; the ψ + 1/2 counterexample is noted | §1.1 |
| N5: ownership, `#eval` | Checker-file inventory with line counts, an ownership note, and no `#eval` in production (`decide`-style proof declarations) | §4.6, §6 |
| "frozen soField" (consumer note) | Corrected to "landed, approved for freezing (D40)" | Notation, §1.1 |
