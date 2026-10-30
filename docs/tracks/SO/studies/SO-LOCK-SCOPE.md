# SO-LOCK-SCOPE: the Moon stays locked in synchronous rotation forever (D42)

**Status:** scoping study, 30 October 2026. Python, data and Markdown only; no Lean was built. The numbers are
double-precision explorations by untrusted tooling (`scripts/spin_orbit/lock_tori.py`, `lock_analyze.py`; data in
`so-lock-data/`). They are design projections, not certificates.

## Summary

- **Statement.** One certified librational 2-torus is enough; two are not needed. In the 3-dimensional extended
  phase space (ψ, p, φ), the torus bounds a solid torus around the synchronous periodic orbit. Every solution
  starting inside stays inside for all real times, so |ψ(t) − c(φ(t))| stays below the torus amplitude: the Moon
  never leaves synchronous lock. The confinement proof is the same elementary barrier argument as SO-CONF
  (`KAM.ODE.gen_barrier`). No Jordan–Brouwer theorem is needed if the region is written in the new coordinates.
- **Lean route.** Recommended: route (a′). This is (a) without a normal form:
  - an explicit, exact symplectic change of variables to elliptic polar coordinates around an *uncertified*
    rational trigonometric centre curve c(φ);
  - then the landed generic sharp certifier, `checkTorusCertificateSharp`, unchanged, applied to the transformed
    Hamiltonian.
  - The only extension of the trusted expression engine is a square-root primitive in `HamExpr`. No frozen
    statement changes.
  - No Birkhoff normalization is needed: the Fourier data of the embedding absorb the nonlinearity.
  - Estimate: 2.5–3.5k Lean lines, all in new files under 1500 lines.
- **Numerics.**
  - The periodic orbit has max |ψ*| = 1.2·10⁻⁵ turns.
  - The libration frequency is ω₀ = 0.0261687 cycles per orbit, a period of 38.2 orbits.
  - Librational tori exist and converge (residual ≤ 10⁻¹⁴) from 1° up to 80° of libration, against a separatrix at
    90°. They are star-shaped (primary) in the polar coordinates at every amplitude scanned.
  - Their Fourier decay is comparable to the rotational barriers' decay.
  - Two packages:
    - **28.5° at N = 40** (ω = 1/(40+g), |p − 1| ≤ 1.26 %): needs support K ≈ 63 × L ≈ 32, about 2k half-terms.
      This is about R2-sized (1.2k).
    - **≈ 74° at N = 65** (|p − 1| ≤ 2.5 %): needs K ≈ 130, about 4k half-terms.
  - The smallest noble-family torus is N = 38 (≈ 18.6°).
- **Literature.** Celletti (1994) proved a lunar librational torus (8.79°) only for ε ≤ ε_obs/5.26. For the Moon,
  the observed parameter was *not* reached (it was reached for Rhea). A certified lunar librational torus at
  ε = 3.45·10⁻⁴ would be, as far as we found, the first at the true lunar asphericity in this model. It would
  also be the first kernel-checked one.

## 1. Mathematics

### Model and coordinates

The model is the seven-term equation of SPIN-ORBIT-PLAN / proposal §2.3 (`KAM/SpinOrbit/Model.lean`). The setting is
the rotated frame of `KAM/SpinOrbit/Rotated.lean`:

- ψ = q − φ (turns), p (the spin rate), φ (the orbital phase, \dot φ = 1), and the clock action J;
- Hamiltonian H′ = p²/2 − p + J′ + V(ψ + φ, φ);
- equation of motion ψ̈ = −4πε Σₘ Aₘ sin 2π(2ψ + (2 − m)φ).

ψ is defined modulo 1/2: the wells at ψ = 0 and ψ = 1/2 are the two synchronous orientations, and the separatrix
is at |ψ| ≈ 1/4 (90°).

### Statement candidates

**(L1, recommended) one torus, solid-torus confinement.** Data:

- a rational trigonometric polynomial c(φ) (the centre; an approximation of the periodic orbit, *not* certified);
- a rational Ω > 0;
- the elliptic coordinates
  X = ψ − c(φ), Y = p − 1 − c′(φ), 𝓘(ψ, p, φ) = π(Ω X² + Y²/Ω).

Conclusion: there are rationals 0 < I_in < I_out and a continuous, 1-periodic P with I_in ≤ P ≤ I_out such that the
set {𝓘 = P(α, φ)} is invariant (α is the polar angle of (√Ω X, Y/√Ω)), and

> for every (ψ₀, p₀, φ₀) with 𝓘(ψ₀, p₀, φ₀) < I_in, the solution is global, unique, and for all t ∈ ℝ satisfies
> 𝓘(ψ(t), p(t), φ(t)) < I_out. Hence |ψ(t) − c(φ(t))| ≤ √(I_out/(πΩ)) and |p(t) − 1 − c′(φ(t))| ≤ √(Ω I_out/π).

All quantities are explicit rationals. Corollary: |ψ(t)| < 1/4 for all t, so the Moon never leaves the synchronous
resonance. The initial-data set is the explicit open elliptic tube 𝓘 < I_in.

**(L2) shell between two librational tori.** This version confines solutions to an annular shell, bounded away from
the periodic orbit as well. It costs a second certificate, and its only gain is a lower bound on the libration,
which is physically uninteresting. Not recommended.

**(L3) |ψ − ψ*(t)| bounded around the true periodic orbit.** This needs the periodic orbit itself certified: an
additional Newton–Kantorovich certificate. It adds nothing to L1, since c(φ) and ψ* differ by at most 10⁻⁵ turns
and the bound is stated against c. Not recommended. If wanted, the existence of a periodic orbit inside the torus
follows from Brouwer applied to the time-1 map of the invariant disc, which is a separate small project.

### Why a single 2-torus confines (3 dimensions)

The extended phase space is ℝ² × 𝕋 ∋ (ψ, p, φ). Its energy-like dimension count is 3, as for the rotational
barriers. Take an invariant 2-torus T that is a graph 𝓘 = P(α, φ) over (α, φ) ∈ 𝕋², with P > 0.

- T bounds the open solid torus V = {𝓘 < P(α, φ)} ∪ {X = Y = 0}.
- The flow preserves T. A solution starting in V cannot leave without crossing ∂V ⊆ T. Uniqueness and invariance
  of T forbid that crossing.
- This is exactly `gen_barrier`: open V, start in V, frontier ⊆ an invariant set.

The rotational case needs two graphs because a single graph p = P(q, φ) only separates ℝ × 𝕋² into two unbounded
halves. A librational torus already bounds a compact region.

**Lean-friendly form of V** (no α at the centre and no Jordan theorem):
V = {𝓘 < r₀} ∪ {r₀/2 < 𝓘 ∧ 𝓘 < P(α, φ)}, with r₀ ≤ I_in.

- Both pieces are open: α is continuous as a circle-valued map on 𝓘 > 0, and P is periodic.
- The frontier lies in {𝓘 = P(α, φ)}, because P ≥ I_in > r₀ and on {𝓘 = r₀} we have r₀ < P.
- So `so_confinement`'s proof transfers almost verbatim; only the open set changes.

## 2. Lean route

### What the landed certifier actually requires

`checkTorusCertificateSharp` (`KAM/CertificateSharp/`) and G1 are *generic*:

- any `HamExpr n` Hamiltonian on D = T_ρ × polydisc;
- a primary embedding K(θ) = (θ + U(θ), A(θ)) (`KAM/Certificate/Embedding.lean`, `IsPrimaryOnStrip`).

A librational torus is degree 0 in ψ, so it is not primary in (ψ, φ). It becomes primary after any coordinate change
in which the libration angle is a genuine angle. The SO-specific part (`Graph/`, `Barrier.lean`) only turns an exact
primary torus into a graph and the graph into a barrier.

### Route (a′, recommended): exact elliptic polar coordinates around an uncertified centre

The change of variables is a composition of two exact symplectic maps, both explicit.

1. **Centre shift.** The generating function F₂ = (ψ − c(φ))(1 + c′(φ) + Y) + φ J̃ gives
   - X = ψ − c(φ) and p = 1 + c′(φ) + Y;
   - J′ = J̃ − c′(1 + c′ + Y) + X c″, a polynomial correction.

   J̃ still enters linearly with coefficient 1, so the clock structure (`soHamExpr_clock`) is kept.
2. **Elliptic polar coordinates**, for a rational Ω:
   X = √(I/(πΩ)) sin 2πα and Y = √(IΩ/π) cos 2πα. Then dX∧dY = dI∧dα.

   On an annulus I ∈ [I₁, I₂] with I₁ > 0, the transformed Hamiltonian K = J̃ + h(α, I, φ) is real-analytic. As an
   expression it is polynomial in √(I/π), so it needs exactly one new primitive: `HamExpr.sqrt`, the principal
   branch, certified on a polydisc that excludes 0.

The libration tori are then primary graphs I = P(α, φ). Two facts make this cheaper than it looks:

- c(φ) need not be the periodic orbit. Any c inside the torus works, so nothing about the orbit is certified.
- Centring at a good c makes the √I-odd terms O(ε Aₘ I^{3/2}) with Aₘ the odd-m coefficients, so they are tiny.

The frequency vector is (1/(N+g), 1): in the rotated frame this is `lunarRotFreq (lunarNuPlusN N) κ`. SO-DION's
`lunarRotFreqPlusN_isDiophantine` (any N ≥ 8) therefore discharges the Diophantine hypothesis unchanged.

| component | what is certified / proved | est. lines | reuse |
|---|---|---:|---|
| `HamExpr.sqrt` | eval and holomorphy on {Re > 0}; jet rules d√f = f′/(2√f) (through the existing `inv`); ball enclosure (rational s with \|f − s²\| ≤ r, s bounded away from 0); composition witness (a Fourier model W with checked ‖W² − f‖ and ‖W − W(0)‖ < \|W(0)\|), mirroring `ExpWitness` | 900–1500 | `Expr/Ball`, `DiffNode`, `Compose` patterns |
| `SpinOrbit/Lock/Coords` | the two maps and their inverses on the annulus; the symplectic identity; H′ ∘ Φ = K as `HamExpr` (`*_eval` lemmas like `soRotHamExpr_eval`); the conjugacy DΦ · X_K = X_{H′} ∘ Φ | 500–800 | `Rotated.lean`, `HamExpr.lean` |
| `SpinOrbit/Lock/Graph` | exact torus ⇒ graph I = P(α, φ) with rational bounds I_in ≤ P ≤ I_out | 150–300 | `Graph/Cert`, `Graph/Inverse` (the same angle-inversion argument; only the action coordinate is renamed) |
| `SpinOrbit/Lock/Confine` | the open V above, its frontier, `gen_barrier`; the corollary bounds on ψ and p | 300–500 | `Barrier.lean` (`so_global_exists_unique`, `so_confinement` proof) |
| `SpinOrbit/Lock/Assembly` | `lunar_lock_of_sharp` over a lawful backend, plus the concrete instance | 200–400 | `LunarAssemblySharpGen.lean` |
| **total** | | **2.1–3.5k** | the certifier, Diophantine and ODE layers unchanged |

**How it composes with SO-CONF.** SO-CONF's `so_confinement` is used only through its ingredients: global
existence and uniqueness of `soField`, and `gen_barrier`. Φ is used only to *define* V and to transport invariance
(Φ maps solutions of K to solutions of H′, and the torus is invariant for K). The flow itself is never
transported; only the invariant set is. The physical theorem stays stated for `soField`.

### Route (b): G1 for general (non-primary) Lagrangian embeddings

This replaces θ + U(θ) by Aθ + U(θ) with a singular integer matrix A = diag(0, 1).

- Mathematically fine: Moser–de la Llave needs only Lagrangian, rank-n DK, and twist.
- In Lean it needs:
  - a new frozen G1 statement, so an owner-approved freeze and a statement audit;
  - reworking the character composition (χ_k ∘ K = e^{2πi k·Aθ} · exp(2πi k·U)) throughout `Expr/Compose`,
    `ComposeModels`, Gram and torsion;
  - character witnesses exp(4πi U₁) of large models (U₁ is up to 0.22 turns), which inflates M and σK.
- Estimate 3–5k lines, touching audited trusted code. Not recommended.

### Route (c): alternatives considered

- **Birkhoff normal form first, then (a).** This is Celletti's route. A truncated normal form shrinks the
  perturbation, which a classical KAM theorem needed. The sharp a-posteriori certifier does not need it:
  - the tori already pass with residuals of about 10⁻³⁵;
  - a normal form adds a certified high-order transformation (heavy expressions in `HamExpr`) for no gain.

  Use elliptic polar coordinates only.
- **Avoiding √ altogether.** No exactly symplectic map of an annulus into the plane winding around the centre can be
  polynomial in I. The enclosed area of the image curves must be linear in I, and for the elliptic families this
  forces √I. A log-based variant (x + iy = e^{s + 2πiα}, I ∝ e^{2s}) needs `log` instead. √ is the smaller primitive.
- **Truncating √ as a Taylor polynomial.** This breaks exact symplecticity and with it the conjugacy. Rejected.

### Risks

1. **Trusted-engine change.** `HamExpr.sqrt` touches the checker's evaluation, jet and composition layers, which
   are audited code. It needs an independent audit like the sharp certifier's. Its soundness obligations are
   local (one node type), and `inv` and `exp` are exact templates.
2. **Conjugacy proof cost.** The calculus with √ and the time-dependent centre is heavier than `Rotated.lean`'s
   linear map. Keep it in its own modules, and prove the symplectic identity by direct `fderiv` computation on the
   annulus.
3. **Checker cost.** K ≈ 63 (N = 40) to 130 (N = 65) libration harmonics against L = 40 for R2. The term counts are
   2–4× R2's, so products cost roughly 4–15× the R2 replay.
4. **Near-resonance 1:38.** ω₀ ≈ 1/38.2, so the 1:38 island chain sits at about 10°. Noble frequencies avoid it
   automatically; it only rules out tori in a thin band there.
5. **Extrapolation.** The decay rates are measured to 10⁻¹⁶ and extrapolated to 10⁻³⁵. The high-precision run
   (`hpsolve`-style, on the polar data) is the first task of the generator package.

## 3. Numerical feasibility

**Method.** `lock_tori.py` works in the pi-free rotated formulation of `model.py`, with the linear part in θ₁
dropped (a degree-0 torus):

- R(V) = D_t²V + 2ε Σ Aₘ sin(2π(2 − m)θ₂ + 2V) = 0 with V = 2πψ;
- V is odd in (θ₁, θ₂), by reversibility;
- bordered Newton with unknowns (V, ω) at a fixed amplitude a = −2 Im V̂(1, 0), with dense pseudoinverse solves on
  the odd subspace (GMRES with a diagonal preconditioner stalls at the resonant symbol ω² ≈ 4εA₂);
- grid 96 × 16, plus a 128 × 16 cross-check run (log only, up to a = 1.3, matching to all printed digits).

`lock_analyze.py` fits the decay of the polar data U = α − θ₁ and 𝓘, 2 decades above the round-off floor, and
derives the support needed for a 10⁻³⁵ tail.

**Periodic orbit.**
- Residual 3·10⁻¹⁹. max |ψ*| = 1.198·10⁻⁵ turns (= 15.5″ of physical libration, the forced libration).
- ψ̂*(1) = 6.0·10⁻⁶ and ψ̂*(2) = 1.7·10⁻⁷, decaying about 1.3 decades per harmonic.
- Monodromy trace 1.973026, so it is elliptic with ω₀ = 0.0261687 cycles per orbit.

**Tori** (`so-lock-data/summary.md`; rows with an unconverged Newton, a = 0.05 and 0.2, dropped):

| a | 1/ω − g | ψ amplitude | max \|p−1\| | decades/k (U, 𝓘) | decades/l | K, L for 10⁻³⁵ | half-terms ≈ KL |
|---:|---:|---:|---:|---|---:|---|---:|
| 0.02 | 37.60 | 1.1° | 0.0006 | 1.29, 1.70 | 1.11 | 28, 32 | 896 |
| 0.10 | 37.69 | 5.7° | 0.0027 | 0.97, 1.00 | 1.11 | 36, 32 | 1152 |
| 0.30 | 38.47 | 17.2° | 0.0078 | 0.70, 0.69 | 1.11 | 51, 32 | 1632 |
| 0.50 | **40.10** | **28.5°** | **0.0126** | 0.57, 0.56 | 1.11 | **63, 32** | **2016** |
| 0.70 | 42.75 | 39.7° | 0.0168 | 0.48, 0.54 | 1.11 | 74, 32 | 2368 |
| 1.00 | 49.36 | 55.9° | 0.0217 | 0.39, 0.49 | 1.13 | 90, 32 | 2880 |
| 1.30 | 61.36 | 70.9° | 0.0248 | 0.29, 0.36 | 1.14 | 120, 31 | 3720 |
| 1.40 | 67.49 | 75.5° | 0.0254 | 0.26, 0.32 | 1.14 | 133, 31 | 4123 |
| 1.50 | 75.46 | 79.7° | 0.0258 | 0.23, 0.28 | 1.14 | 150, 31 | 4650 |

Notes on the table:

- **Primary in polar coordinates at every amplitude.** The maximal jump of U along θ₁ is ≤ 0.01 turn, so α winds
  exactly once.
- **Annulus.** 𝓘 varies by a factor ≤ 2 on each torus (for example [0.0127, 0.0253] at 80°), so a polydisc with
  0 ∉ disc exists.
- **Twist.** dω/d𝓘 ≈ −0.55 (small amplitude) to −0.92 (80°): monotone and nondegenerate.
- **Frequencies.**
  - 1/ω − g = N picks the noble barrier frequency 1/(N+g).
  - N = 40 sits at a ≈ 0.5 (28.5°); N = 65 at a ≈ 1.37 (≈ 74°, |p − 1| ≤ 0.025).
  - The smallest noble-family torus is N = 38, at ≈ 18.6°.
  - Above ω₀ (N ≤ 37) there are no librational tori.
  - Smaller tori need other Diophantine frequencies (for example 1/(37 + 1/(M+g))), at a worse γ.
- **Physical amplitude.** In degrees it is 360·max |X|, which is the physical angle between the long axis and the
  Earth direction.

**Sharp threshold.** The frequencies are the R2 frequencies, so γ = κ/(N+2) is unchanged. The threshold is
polynomial in the majorants (`sharp_q`, measured around R2):

| change | threshold, log₁₀ |
|---|---:|
| R2 as is | −31.8 |
| σT ×2 | −32.4 |
| σT ×10 | −33.8 |
| M ×2 | −33.3 |
| σB ×2 | −34.2 |
| ρ ×½ | −33.0 |

The torsion here (|dω/d𝓘| ≈ 0.5–0.9 in turn units) is O(1), like R2's, so a plausible package sits at
10⁻³²–10⁻³⁴. A 10⁻³⁵–10⁻³⁶ residual at 160–192 bits, as in R2, clears it. The support K above is sized for that.

**Data sizes** (projection, per torus):
- 2.0k (N = 40) to 4.1k (N = 65) half-terms per Fourier function, against R2's 1.2k;
- advice and shards scale roughly with products, so about 4× (N = 40) to 12× (N = 65) R2's 62k nonzero advice and
  1230 shards.

**Smallest certifiable libration band.** With the Diophantine family that is already landed, any outer torus from
N = 38 (≈ 18.6°) to N ≈ 70 (≈ 76°) is within reach. The initial-data set is the elliptic tube 𝓘 < I_in.

- For N = 40: all initial data with libration amplitude up to ≈ 27° (I_in ≈ 0.95 min P after the disp margin) stay
  within 28.5° and |p − 1| ≤ 1.3 % forever.
- For N = 65: up to about 70° and 74°.

The real Moon's free libration is tiny, and its forced libration (≈ 15″ above) is deep inside either tube.

## 4. Literature

- **Celletti, ZAMP 41 (1990)**, synchronous resonance Part I: rotational trapping tori; the classical ≈ 3 % band.
- **Celletti, ZAMP (1994)**, *Construction of librational invariant tori in the spin-orbit problem*, and the
  Celestial Mechanics companion on librational trapping tori. Method:
  - centre on the synchronous periodic orbit, diagonalise, harmonic-oscillator action–angle variables;
  - Birkhoff normalization;
  - a computer-assisted KAM theorem (floating-point interval arithmetic, outside a proof assistant).

  Result, from the 2007 survey (mp_arc 07-303, §6.3): *"consider the Moon–Earth case with ε_obs = 3.45·10⁻⁴ and
  e = 0.0549; there exists an invariant torus around the synchronous resonance corresponding to a libration of
  8°.79 for any ε ≤ ε_obs/5.26."* For Rhea–Saturn the observed parameters were reached.
- **Andreu, Celletti, Falcolini (1999)**: numerical breakdown of librational tori (Greene's criterion); not rigorous.
- **Calleja, Celletti, Gimeno, de la Llave (2021–23)**: the dissipative model; numerically validated, not a rigorous
  lunar librational result.

**Accurate novelty claim.**

- As far as we found, no rigorous librational torus has been proved for the Moon at the observed ε. The 1994 result
  needs ε ≤ ε_obs/5.26 and an amplitude of 8.79°.
- A certificate at ε = 69/200000 and e = 549/10000 in the seven-term model would therefore be:
  - the first lunar "locked forever" theorem at the true asphericity;
  - with amplitudes 28–74°, far beyond 8.79°;
  - the first kernel-checked one.
- The search was not exhaustive. Before any public claim, read the 1994 papers and the Celletti–Chierchia KAM
  surveys in full, and check citing works since 1994.
- The model caveats of the rotational band apply unchanged: a truncated Fourier model, a planar fixed Kepler orbit,
  and no tides.

## 5. Recommendation and owner questions

**Recommendation.** Scope SO-LOCK as route (a′):

1. one certified librational torus at N = 40 as the pilot;
2. N = 65 (≈ 74°) as the headline;
3. statement L1.

The first packages are:

- **LOCK-GEN**: high-precision polar-coordinate generator and certificate data at N = 40;
- **LOCK-SQRT**: `HamExpr.sqrt` plus an audit;
- **LOCK-COORDS**: the symplectic map and conjugacy;
- **LOCK-CONF**: the solid-torus confinement;
- then the assembly.

LOCK-GEN and LOCK-SQRT can run in parallel.

**Owner questions** (each with the recommended answer):

1. *Statement:* single-torus solid-torus confinement (L1), or a shell between two tori (L2)?
   **Recommended: L1.**
2. *Centre:* state the bounds around an explicit rational trigonometric c(φ), or around a certified periodic orbit
   (L3)? **Recommended: rational c(φ).** It differs from ψ* by < 10⁻⁵ turns, and certifying the periodic orbit is
   extra work for no content.
3. *Trusted-engine extension:* allow `HamExpr.sqrt` (route a′), or freeze a new G1 for non-primary embeddings
   (route b)? **Recommended: sqrt.** It is local, it leaves the frozen statements untouched, and it is audited like
   the sharp certifier.
4. *Target amplitude:* N = 40 (28.5°, |p − 1| ≤ 1.26 %, ≈ R2 cost) first, then N = 65 (≈ 74°, ≈ 10× R2 checker
   cost)? **Recommended: yes**, the pilot first, the headline second. The same Diophantine lemmas serve both.
5. *Normal form:* skip Birkhoff normalization entirely? **Recommended: skip.** The sharp a-posteriori certifier does
   not need it.
6. *Novelty wording:* "first rigorous librational confinement for the Moon at the observed asphericity, and first
   kernel-checked", made conditional on reading the 1994 papers in full? **Recommended: yes, conditional on that
   reading.**

## Errata and deviations

- **Erratum candidate (exploration doc).** `docs/explorations/lunar-band-2p8-2p9.md`, "Beyond the floor", says the
  route "needs … the same two-barrier confinement argument". One librational torus already confines (§1); two
  barriers are needed only for rotational graphs. This is a statement in a non-pinned note.
- **Brief deviation (wording).** The brief asks for "the smallest libration amplitude band". The theorem's
  initial-data set grows with the *outer* torus, so I report the certifiable range of outer tori (18.6°–≈76° in the
  noble family) and the corresponding initial-data tubes.

## Reproduce

    cd scripts/spin_orbit; export OMP_NUM_THREADS=1
    python3 lock_tori.py OUT_A.json 96 16 0.02,0.05,0.1,0.2,0.3,0.4,0.5,0.6,0.7     # ~25 min
    python3 lock_tori.py OUT_B.json 96 16 0.8,0.9,1.0,1.1,1.2,1.3,1.4,1.45,1.5
    python3 lock_analyze.py OUT_A.json OUT_B.json

Each run is about 25 minutes, single thread.

## Sources

- [Celletti, Perturbation theory in celestial mechanics (survey, mp_arc 07-303)](https://web.ma.utexas.edu/mp_arc/c/07/07-303.pdf), §6.3
- [Celletti, Construction of librational invariant tori in the spin-orbit problem, ZAMP (1994)](https://link.springer.com/doi/10.1007/BF00942847)
- [Celletti, Stability of the synchronous spin-orbit resonance by librational trapping tori, Cel. Mech.](https://link.springer.com/article/10.1007/BF00692482)
- [Andreu, Celletti, Falcolini, breakdown of librational tori (mp_arc 98-470)](https://web.ma.utexas.edu/mp_arc/a/98-470)
