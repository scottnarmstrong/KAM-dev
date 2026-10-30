# W7 delta and W8 assembly: independent review 1

**ITEM A — W7 tight delta: ACCEPT.** The beta = 1/4 measure revision is correct as a conditional measure theorem about admissible frequency families. No new finding in the assigned delta.

**ITEM B — W8 full round 1: REVISE for the claim of an established headline proof.** The local assembly arguments pass, subject to two minor corrections below, but the preparatory estimate consumed by `sharp-prep` remains an unverified input under the already reported W56-R1. This is an inherited dependency stop, not a new review or refutation of W6. Conditional on the required W6 outputs with the displayed constants, W8 covers the frozen statement without weakening any clause. No new major mathematical defect was found in W8's shell, embedding, uniqueness, winding or injectivity arguments.

Reviewer provenance: **GPT-6.1-Sol, codex-1, reasoning effort medium** (launch identifier overrides the generic brief's codex-3). Independent, refute-first, tier-2 source/statement audit; no manuscript repairs or subagents.

## Snapshot, permissions and evidence

Reviewed commit: `1edb81f0564fdba6efb96a9647f84c8063b5acf4`. Item A comparison: `git diff a1654adc 1edb81f0 -- blueprint-W/parts/w7-measure.tex`. All manuscript line numbers below refer to the pristine archive of that commit, exported under `.drafts/W/review-w78/`, not to later worktree changes.

| File | Lines / bytes | SHA-256 |
|---|---:|---|
| `blueprint-W/parts/w7-measure.tex` | 791 / 60512 | `191c061b8e8d72edf8d1cfab18c964ecff1aa4a05edd285400fd3862bed7952d` |
| `blueprint-W/parts/w8-assembly.tex` | 655 / 58089 | `edc00b79c1ba626c01c6dcd7846a2ffb8a8adf291ed7e2d0f4ac0a07c2c3a750` |
| authoritative main `KAM/Frozen/Wave/Theorems/Nlw2.lean` | read directly | `9ce65519e3108c55e50565b268e7138d5a47ed68fbfade07166d0641b2e2dde6` |
| authoritative main `Defs/IsAnalyticTorusEmbedding.lean` | read directly | `6fb4f36f9df08069dbdbb555bba9e758c607a58f34327b975b55a13ed108b4ef` |

Permission envelope: write this report and the named scratch directory only; no git mutation, lint, Lake or Lean process. The launch's explicit prohibition of lint/Lake controls over the generic repository handoff rule. No commit or push. The report is a mathematical blueprint review, not a kernel or axiom certificate; no `#print axioms` was run and no new Lean result was produced. The authoritative theorem still has `by sorry`.

Read the supplied AGENTS instructions and on-disk AGENTS, docs PLAN/DECISIONS, both review briefs, W writer conventions, W PLAN/preamble, W0 conventions and normalization interfaces, headline, W-STATEMENTS and BP0 handoff, round-1 W7 report, and W56 report. Checked W8 in full, the entire assigned W7 diff and its surrounding estimates, and consumed W1/W2/W3/W5/W6 interfaces. W0--W6 were not independently re-audited. Main frozen `nlw2`, embedding, `lam`, `coeff`, `cubicGrad`, `linearTorus`, `WaveSpace`, reconstruction and classical-solution definitions were read directly. Scratch `check_review.py` records hashes of all eleven frozen definition files.

Pinned-source reads: P96-K pp. 140--142 (PDF 23--25; also inspected all three page images), KP96 author pp. 26--31, P96-W pp. 271--273 and 288--291 (PDF 4--6 and 21--24). Source extracts are in scratch. These confirm the measure optimization and the shell construction, and distinguish the source's Lipschitz-family route from W8's new orbit/winding route. The latter is audited here as our own argument, not attributed to a published uniqueness theorem.

## Findings and retained dependency stop

| ID | Location / immutable anchor | Severity | Evidence and disposition | Exact proposed fix / closure criterion |
|---|---|---|---|---|
| W78-B-D1 | W8 lines 174--193, `bpW:w8:sharp-prep`, especially “holds for the full lambda-norm”; consumers `w6-general`, `nlw2-proof` | **major, inherited W56-R1** | W56 identifies the unpaid modified quadratic action-component estimate upstream of the displayed bound `2 C_2 epsilon^(4/3) (hatalpha sigma_P^52)^(-1/3)`. W8's scale algebra does not pay that estimate. This row only records the dependency; it does not repeat or upgrade the W56 source-counterexample claim. | Keep headline proof status conditional until the W56-R1 repair delivers this exact full-norm estimate, or recheck W8 with the repaired constants and strip powers. Do not label the frozen theorem closed from this report. |
| W78-B-1 | W8 lines 18--23, 191--198, 232--233 and 637--642, especially “W6 records only the weaker bound” and “W6 should state ... with epsilon_0 a parameter” | minor | Stale description: pinned W6 `prep-step(v)`, `wave-iteration` and `to-w8` already record the sharp lower bound and the admissible starting-size interval. Tried to read this as a different needed uniformity; W8's chosen value fits precisely the interval already supplied. | Describe W8 as selecting an existing W6 parameter. Remove the obsolete extension request; retain W8's explicit positive choice and sharp comparison. This editorial update does not close D1. |
| W78-B-2 | W8 lines 70--73, `bpW:w8:ext-exp`: `Complex.abs_exp_ofReal_mul_I` | minor | The mathematical identity is correct, but this literal name was not found in current main Mathlib. The available declaration is `Complex.norm_exp_ofReal_mul_I`, `Analysis/Complex/Trigonometric.lean:952`. The other cited bound `Real.norm_exp_I_mul_ofReal_sub_one_le` does exist (`SpecialFunctions/Trigonometric/Bounds.lean:286`). | Replace only the nonexistent API name by `Complex.norm_exp_ofReal_mul_I` and express complex modulus by the norm. For constancy of an integer-valued real map, use the continuous integer-valued factorization (or `IsPreconnected.constant_of_mapsTo`), so the discrete-codomain guard is explicit. |

W56-R2 is also retained as an upstream issue, without re-review. It does **not** cause a new W8 endpoint failure: here `epsilon^sharp_n = E_3 t_n^(3/2) > 0`, hence `kappa_n > 0`, `epsilon_(0,n) > 0`, and the preparatory radius is positive even if the actual perturbation vanishes. A W6 repair restricting to positive chosen majorants is compatible with these data.

## Item A: recomputations and refutation pass

Set kappa = 2, loss varpi = 1/2, and divisor weight beta = 1/4. The weight and loss are different parameters; only the weight enters the preparatory zone count. Exact rational arithmetic gives

```
w = beta / (4 kappa + 4 - beta) = 1/47
1 - 3w = 44/47,                    1 + w = 48/47
kappa / (kappa + 1 - beta) = 8/11
(44/47)(8/11) = (48/47)(2/3) = 32/47
4/3 - (44/47)/3 = 48/47.
```

Thus `hatalpha = alpha^(44/47)`, `checkalpha = alpha^(48/47)`, and the combined exponent is `mu = 32/47`. In particular the revised alpha threshold exponent `47/44` makes `hatalpha <= min{1/27, beta_*/4, vartheta c_X/(4 K_* (K_*+4))}` exactly as needed. All thresholds remain independent of shell or parameter domain. The reindexing comparison is `j^(-1/4) <= (j-2)^(-1/4) <= 3^(1/4) j^(-1/4)` for j >= 3.

For the Lambda-minus estimate (lines 474--506), put `x = hatalpha/A_k` and `j_0 = ceil(x^(-4/11))`. The tail slab decreases with j. Its width is `n(x j_0^(-1/4) + a_kappa j_0^(-2))`. The finite zones and the tail's first term fit inside `x sum_(j<=j_0) j^(-1/4)`; the finite sum includes the j_0 term and extra low indices, so there is no missing additional tail term. Using

```
sum_(j<=j_0) j^(-1/4) <= (4/3) j_0^(3/4),
j_0 <= 2 x^(-4/11),  j_0^(-2) <= x^(8/11),
(4/3) 2^(3/4) < 3,
```

gives exactly `(3+a_kappa) x^(8/11)` times `8 rho_zeta n/(|k| D_A)`. Also `hatalpha <= 1/27 < 3^(-11/4)` ensures `j_0 >= 3`. Summing n <= |k|/vartheta and doubling signs gives the stated `16(3+a_kappa) vartheta^(-2)` contribution. Exceptional-zone estimates are unaffected because the modified weight is bounded by the ordinary weight.

With tau = 24 the new preparatory lattice term is `|k| A_k^(-8/11) <= |k|^(1-192/11)`, faster than `|k|^(-3)`. The unchanged iteration term `|k| A_k^(-1/6) <= |k|^(-3)` is still the slowest. Counting `4N` vectors on each integer l1 sphere leaves a convergent sum of N^(-2). No larger tau is needed.

The density requirement is `alpha^(32/47)/t -> 0`, equivalently `alpha = o(t^(47/32))`; smallness requires `t^(3/2) <= constant * alpha`. Since `47/32 < 95/64 < 3/2`, the choice `alpha=t^(95/64)` satisfies both, with

```
alpha^(32/47)/t = t^(1/94),
t^(3/2)/alpha = t^(1/64),       alpha <= t (0<t<=1).
```

The former `alpha=t^(47/32)` would give ratio 1 and was correctly removed. Attempted counterchecks using the old optimization, the j_0 rounding, the tail slab, and the slow lattice term found no defect. This accepts the revised **conditional measure calculation**, not the upstream construction of an admissible family. Separating beta from varpi does not itself certify the full preparatory solver.

## Item B: frozen-contract ledger

The following checks are conditional on the named analytic inputs; they establish the assembly's fidelity, not those inputs' proof closure.

| Frozen requirement | W8 location | Audit result |
|---|---|---|
| `{m : Real} (hm : 0 < m)`; witnesses `r0 C tau eta Gamma nu K` | `const`, `patch`, `nlw2-proof` | Correct order at existential introduction. All witnesses depend on m and fixed earlier constants only, before I, angles or orbit initial phase. Numerical tau = 24 is a real witness. No uniformity in m is smuggled in. |
| `0<r0`, `0<C`, `1<tau`; eta nonnegative on `(0,r0)` and right limit zero | `p-pos`--`p-etalim` | t0 is a finite minimum of positive constants; eta is the total function `2^(33/64) E_7 r^(1/32)`. Only positive r is used. The limit is `nhdsWithin 0 (Ioi 0)`, not a claim about an unspecified partial eta. |
| Gamma measurable; positive coordinates and `sqrt(I0+I1)<r0` | `patch-cont` | Countable Borel union; `I_i<t0` strictly gives `I0+I1<2t0=r0^2`. Frozen Fin-2 indices correspond to Dirichlet modes 1,2. |
| `ContinuousOn nu Gamma`; `ContinuousOn (uncurry K) (Gamma x univ)` | `patch-local`, `patch-cont` | Correct local-on-Gamma continuity, including the angle variable. Total nu and K are explicitly zero outside Gamma; continuity outside Gamma is neither required nor used. |
| (1) ENNReal density quotient, positive-quadrant denominator | `p-dens`, W7 `density` | Denominator is `volume(P inter ball 0 h)=h^2`, nonzero and finite for h>0 in the ambient max norm. Numerator is the frozen `Gamma inter ball`. No full-ball or Euclidean-ball replacement. Shell defect is at most `(4/3)(7+C_7)t_n^(1/94)`; W7 controls arbitrary h between scales. The final quotient and limit are in ENNReal. |
| (2) gamma chosen after I; exact `IsDiophantine`; frequency limit | `p-dioph`, `p-lim` | `gamma_I=checkalpha_n/(8 pi)>0` is allowed to depend on the shell containing I. With `S=sum_i |k_i|>=1`, `1+S^24<=2 S^24`, division by `2 pi` gives exactly the frozen inequality. The frequency limit uses `nhdsWithin Gamma 0` and target `lam m hm (i:Nat).succPNat/(2 pi)`. |
| (3) `forall I (hI : forall i, 0<I i), I in Gamma -> ...` | `p-emb`, `p-close`, `p-size` | hI is arbitrary; frozen `linearTorus` ignores the proof argument. Closeness is pointwise for every theta at the same angle, with eta(r)r; the norm bound uses the same existential C as (5). |
| (3a) periodicity | `shell-embedding/se-per` | K(theta+k)=K(theta) for every integer vector k, by periodicity before the fixed coordinate maps. |
| (3b) `AnalyticOnNhd Real K univ` | `se-an` | Exactly the Banach-valued real-analytic predicate, obtained from W6's holomorphic strip and continuous linear transport. Not merely scalar coefficient analyticity. |
| (3c) injectivity modulo integer vectors | `se-inj` | Positivity of tangential radii and injectivity of Gamma-real reduce equality to the angular lift. Periodicity of X and Lip(X)<=1/2 force theta-theta' to be the integer lift. |
| (3d) injective `fderiv Real K theta` for every theta | `se-der` | Analyticity supplies differentiability, so fderiv is not used off its locus. Chain rule, reality, injective coordinate transport and invertible D Gamma reduce a kernel vector to `h=-DX h`; norm(DX)<=1/2 forces h=0. No immersion assumption replaces the proof. |
| (4) coordinatewise two `HasDerivAt` statements at zero | `shell-inv`, `p-inv` | Weak Birkhoff invariance is transported by the explicit W3 weak-transport corollary. The displayed equations use exactly frozen coeff, lam and cubicGrad, with the negative sign in the momentum equation and no missing 2 pi. Unbounded linear fields are not assumed bounded on the base space. |
| (5) all four PDE conjuncts with one C | `p-pde`, W2 `clause5` | W2 provides joint `AnalyticAt` at all points of `univ x Icc 0 pi`, the frozen classical-solution predicate including endpoints and boundary conditions, time `HasDerivAt` at every t with reconV, and the pointwise sum bound using `derivWithin` on Icc. `C=max(1,M_m)C_3` is fixed before I and serves both clauses (3) and (5). |
| (6) all I,I' in Gamma, all angles | `injective` | Orbit equality, winding and frequency injectivity force I=I'; the single-torus embedding then supplies the existential integer vector. No claim only for same-shell pairs or nearby angles is substituted. |

### Shell geometry and constants

Each `Gamma_n` lies inside the **open** trimmed shell `O_n=Pi_n`, and the raw shells are disjoint. For I in Gamma_n, `Gamma inter O_n=Gamma_n`, so continuity is locally that of a single shell; no sequence from another shell can approach this I. The shells only accumulate at 0, which is outside Gamma. The removed boundary layer costs at most `7 alpha_n t_n`; it is already included in W7's density estimate. Pairwise separation is sufficient; no uniform positive separation of the entire infinite union is claimed.

The explicit t0 bounds imply `r_n^2/alpha_n=t_n^(1/64)<=1/4`, `kappa_n<=1`, `rho_n^2<=rho_1^2/4<r_1^2`, and `e_tor<=7/256`. The complex parameter neighborhood has `Re zeta_i>alpha_n/2>=2r_n^2`, and `|zeta_i|<t_n`; the initial square-root branches and parameter Cauchy bounds therefore apply. In `sd-init`, the coefficient `3+2 sqrt(2)<6` validates E1. These are native domain attachments, not just exponent comparisons.

Subject to D1, the sharp choice gives

`epsilon_(0,n)/checkalpha_n = gamma_1 kappa_n^(4/3)`, with `kappa_n=(E_3/gamma)t_n^(1/64)>0`.

Its comparison with the sharp preparatory lower bound uses the exact identity `4/3-(44/47)/3=48/47` and the stipulated choice of gamma. Thus the chosen epsilon_0 is inside W6's already parameterized interval. Uniform estimates require only the upper bound `epsilon_0<=gamma_1 checkalpha`; lowering it does not change frequency Lipschitz budgets or exclusion thresholds. Consequently `e_tor<=E_5 t_n^(1/64)`.

For real angles the tangential radii stay positive. The Cauchy radius is `s0/2=7/128`, giving `||DX||<=128 e_tor/7<=1/2`. The full phase-space distance is bounded by `162 sqrt(t_n)e_tor`; numerically `22(1+2 pi)+1<162`. The normal-form displacement is at most `E_6 t_n^(3/2)`. Therefore the same-angle distance is `<=E_7 t_n^(33/64)`. Since `t_n<=2r(I)^2`, this is precisely `eta(r(I))r(I)` with eta from `const`. The separate size estimate gives `C_3=4 sqrt(c_A)`; no shrinking action coordinate or vanishing individual I_i is assumed comparable to t_n beyond the explicit trim margin.

### Refutation of the injectivity route

I tried the main possible obstructions separately:

1. **Unbounded lambda invalidates the energy cancellation.** It does not: analytic coefficient solutions are differentiable into lp2 by W2 `curve-deriv`. Multiplying the frozen coordinate identities by the positive weight gives `Y1'=lambda Y2` and `Y2'=-lambda Y1-g(Y1)` in weighted coordinates. The cubic bound gives `g(Y1)` in lp2, hence both lambda-multiplied components lie in lp2. Each inner-product series is absolutely summable. Their equal lambda cross terms cancel legitimately.
2. **The nonlinearity is controlled in the wrong weight.** Here `g(y)_j=omega_(1,1)(j)cubicGrad(y)_j=j^(-1) G^w(y)_j`. The diagonal multiplier has norm <=1. W1's Lipschitz bound for G^w therefore gives exactly the needed `3 C_m R^2` bound in raw lp2 coordinates. For `f=||D1||^2+||D2||^2`, `|f'|<=L f`. Forward and backward integrating factors on every compact interval establish equality on all real time. No general existence theorem for an ambient bounded vector field is being used.
3. **Meeting orbits could have different parametrization frequencies.** Positivity of both tangential amplitudes and global injectivity of the same Gamma-real undo the Birkhoff map for both shells. Equality of their complex tangential modes gives continuous phase differences in Z; these are constant. Bounded periodic X then forces the winding rates nu_i to coincide. The argument needs neither a dense-orbit assertion nor an unproved uniqueness theorem for lower-dimensional tori.
4. **Equal frequencies on different shells might survive.** The frequency drift is at most `alpha_n/(70 L_A)`: `14 pi/3400<1/70`. Different shells have `|I-I'|>max(alpha_n,alpha_n')`, so affine separation minus the two drifts is strictly positive. On the same shell the lower Lipschitz bound is `7/(8 L_A)`. Thus nu is injective throughout Gamma, not merely on each shell.

All four attempted objections fail given the cited inputs. This supports the new injectivity proof while preserving the upstream dependency stop.

## Source status, verification and closeout

No new pinned-source erratum or frozen-statement defect is alleged. Retained deviations are explicit: separate beta and smoothing loss; rounded cutoffs and explicit constants; shell-wise sharp majorants; same-angle rather than radial-map closeness; uniqueness/winding rather than the source's Lipschitz-family injectivity. The P96-K p. 140 full parameter-Lipschitz estimate remains a **suspected source gap with the qualifications in W56**, not a source theorem disproved by this review. The local normal-operator weight observation `2 beta<=varpi` does not close its remaining full-field obligation.

Verification in the pristine archive:

- `latexmk -pdf -interaction=nonstopmode blueprint.tex`: **exit 0**, **113 pages**. Final log: **0** lines beginning `!`, **0** `Warning:` entries, **0** undefined references. W7 starts p. 86; W8 starts p. 99; headline proof p. 109. Read rendered text extracted by `pdftotext -layout`, including the sharp-size, embedding, uniqueness and assembly passages.
- `python3 .drafts/W/review-w78/check_review.py`: **exit 0**, `CUTOFF, POWER, CONSTANT AND FINITE-SUM CHECKS PASS`; exact exponents printed as `1/47 44/47 48/47 8/11 32/47 density=1/94 smallness=1/64`.
- Mechanical manuscript label/reference scan: **no missing internal ref/eqref targets; no duplicate labels**.
- Mathlib checked read-only for the lp inner-product/summability and local continuity APIs, complex exponential, integer-valued constancy and exponential increment bounds. Two initial guessed source paths did not exist; subsequent rg searches located the actual files. No Lean probe was needed.
- No lint, Lake command, Lean build, theorem axiom probe, generated-root edit, frozen/manifest edit or state-changing git command. Only this report and scratch were written. The closing shared-worktree status also showed concurrent modifications to `blueprint-W/blueprint.pdf`, W5 and W6; these were not made or altered by this reviewer, and the audit remained pinned to the archive.

Item A closes at the requested delta scope. Item B's local assembly has no newly identified major defect, but its unconditional headline-proof claim cannot close until W56-R1 is discharged with compatible constants. Resolve the two minor W8 corrections and retain the positive-majorant guard when consuming W6's R2 repair. No theorem sealing or campaign closure is certified here.
