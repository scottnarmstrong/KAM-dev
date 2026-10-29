# Track W blueprint: plan of milestones W0–W8

Author: W-BP0, 28 October 2026. Track W was adopted by owner decision D30 from
[`docs/explorations/pde-kam-and-leapfrogging.md`](../docs/explorations/pde-kam-and-leapfrogging.md) (the scoping report;
section numbers below refer to it). Target: two-frequency quasi-periodic solutions of `u_tt = u_xx − m u − u³` on
`[0, π]`, Dirichlet, modes `J = {1,2}`, every fixed `m > 0`. **Nothing here is frozen or approved**; the headline
`W-NLW2` (`bpW:wh:nlw2`) is a proposal for statement audit and owner review.

Written: Part 0 (`parts/w0-conventions.tex`, `parts/w0-normalization.tex`) and the proposed headline
(`parts/w-headline.tex`). Labels: `bpW:w<k>:<slug>` (W0 normalization part uses `bpW:w0n:`), steps `stepW:...`,
headline `bpW:wh:`. Labels marked PLANNED do not exist yet. Pinned sources: P96-W (wave), P96-K (abstract KAM), KP96
(author v2.1); locators in `bpW:w0:sources`. Checks: `scripts/wave/w0_checks.py`. Errata verdicts:
`docs/tracks/W/errata-check-W0.md`.

Repository hard rules (verbatim, binding on all later Lean work): 1. Never use `set_option maxHeartbeats` (or any
heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof,
not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design
signal. 2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
preserving public import paths as cheap facades.

## Normalization rulings (fixed in Part 0; do not reopen without an owner ruling)

- Real coordinates `q_j = sqrt(λ_j) x_j`, `p_j = y_j / sqrt(λ_j)`; `H = ½ Σ λ_j (q_j² + p_j²) + ¼ ∫ U_m(q)⁴`;
  `q̇ = λp`, `ṗ = −λq − G_q(q)`.
- Actions `I_j = (q_j² + p_j²)/2 = |z_j|²`, `z = (q + ip)/√2`, `ż = −iλz` linearly; angles `q = √(2I) cos φ`,
  `p = −√(2I) sin φ`; campaign angles period one, `φ = 2πθ`, `ν = ω/2π`.
- Normal-form coefficients `A_ii = 9/(8πλ_i²)`, `A_ij = B_ji = 3/(2πλ_iλ_j)`, `det A = −63/(64π²(1+m)(4+m))`. The
  printed P96-W values are 16 times larger (E-PDE-W-1) and must not be used.
- Weights `a = p = 1` for the headline.

## Milestones

| Milestone | Content | Status | Main sources |
|---|---|---|---|
| W0 | Normalization, cubic attachment, quartic coefficients, `A`, `B`, nondegeneracy, Duffing | **blueprint written** (this package) | P96-W §2–3, pp. 277–284, 287–293 |
| W1 | Weighted sequence calculus | planned (nodes below) | P96-W Lemma 2, App. A; KP96 App. A |
| W2 | PDE reconstruction (analytic, all time) | planned | P96-W Lemma 1 |
| W3 | Partial Birkhoff normal form (analytic map, remainder) | planned | P96-W Main Prop., Lemma 4, pp. 281–286 |
| W4 | Normal homological equation (operator solve, Lipschitz) | planned | P96-K Lemma 1, App. A Lemma A.1 |
| W5 | One KAM step | planned | P96-K §3 |
| W6 | Iteration, convergence, invariance | planned | P96-K §4 |
| W7 | Wave measure estimate (Theorem D) | planned | P96-K §5–6 |
| W8 | Action family, density one, family injectivity, headline assembly | planned | KP96 §7; P96-W pp. 289–291 |

## W0 nodes (written)

Definitions (Part 0, conventions): `bpW:w0:mass` (standing `m > 0`), `bpW:w0:nlw` (classical solution, equation
`bpW:w0:eq`), `bpW:w0:basis`, `bpW:w0:ellap`, `bpW:w0:weights`, `bpW:w0:twosided`, `bpW:w0:reconstruction`,
`bpW:w0:H`, `bpW:w0:Gq`, `bpW:w0:eqmotion` (system `bpW:w0:coeffsys`), `bpW:w0:z`, `bpW:w0:actions`,
`bpW:w0:periodone`; comparison table `bpW:w0:table`, remark `bpW:w0:harmless`.

| Node | Statement | Proof status | Depends on |
|---|---|---|---|
| `bpW:w0n:recon-bounded` | `U_m`, `V_m` bounded `ℓ^{a,p} → C^k[0,π]` for `a > 0`, all `p`, `k` | proved | `bpW:w0:ellap`, `bpW:w0:basis` |
| `bpW:w0n:quartic-coeff` | closed form of `g_ijkl`, signed form `bpW:w0n:g-signed` (deliverable c) | proved | `bpW:w0:basis` |
| `bpW:w0n:gradient` | `G`, `G_q` as absolutely convergent sums; `∂G/∂q_l = G_q(q)_l` | proved | `recon-bounded`, `quartic-coeff` |
| `bpW:w0n:algebra` | `‖c*d‖_{a,s} ≤ K_s ‖c‖‖d‖`, `K_s = 2^s (1+2ζ(2s))^{1/2}`, `s ≥ 1` (also W1) | proved | `bpW:w0:twosided` |
| `bpW:w0n:cubic-bound` | `G_q : ℓ^{1,1} → ℓ^{1,2}` bounded cubic polynomial, `C_m = 8(1+2ζ(3))/π` (deliverable b) | proved | `quartic-coeff`, `algebra`, `gradient` |
| `bpW:w0n:pde-equiv` | coefficient system ⇔ classical PDE, force identity `bpW:w0n:force` (deliverable a) | proved (uses `L²` completeness of sines, external) | `recon-bounded`, `gradient`, `cubic-bound` |
| `bpW:w0n:nonres` | qualitative quartic nonresonance, all indices, all `m > 0` | proved | `quartic-coeff` |
| `bpW:w0n:AB` | `Ḡ = ½⟨AI,I⟩ + ⟨BI,Z⟩`, formula `bpW:w0n:avgG` (deliverable d) | proved | `nonres`, `quartic-coeff`, `bpW:w0:actions` |
| `bpW:w0n:formal-birkhoff` | formal Lie transform: quartic part `Λ + Ḡ + G^nor` | proved formally; analytic version is W3 | `nonres`, `AB` |
| `bpW:w0n:nondeg` | `det A ≠ 0`, (A₂), (A₃) for every `m > 0` (deliverable e) | proved | `AB` |
| `bpW:w0n:kappa` | `κ = 2` asymptotics with corrected `B` (remark) | proved | `AB` |
| `bpW:w0n:duffing` | Lindstedt shift = `A_jj I_j` (deliverable f) | proved (+ numerical check) | `quartic-coeff`, `AB` |

Expansion/strengthening of the source proof (not a gap): P96-W Lemma 1 (expanded, strengthened to `C¹` curves, in
`pde-equiv`). Source defects recorded: P96-W p. 280 `√2` (N-1); P96-W p. 278 sign typo (N-4); KP96 p. 13 factor 2 (N-5); P96-W p. 282/284
factor 16 (E-PDE-W-1); P96-W pp. 287/290 conventions (E-PDE-W-2).

## W1 nodes (PLANNED): weighted sequence calculus

| Node (PLANNED) | Statement | Depends on |
|---|---|---|
| `bpW:w1:space` | `ℓ^{a,p}` (real, complex) as a Hilbert space: transport of `lp 2` via `w_j ↦ j^p e^{aj} w_j`; coordinate evaluation continuous; completeness; separability | `bpW:w0:ellap` |
| `bpW:w1:embed` | `ℓ^{a,p} ⊂ ℓ^{a',p'}` continuously for `a ≥ a'`, `p ≥ p'`; finite truncations converge | `space` |
| `bpW:w1:diag` | diagonal multipliers `(λ_j^r)` bounded `ℓ^{a,p+r} → ℓ^{a,p}`, norm `≤ (1+m)^{r/2}` for `r ≥ 0` (for real `r`: `≤ (1+m)^{max(r,0)/2}`; for `r < 0` the norm is `sup_j λ_j^r j^{-r}` ≤ 1); phase rotations `e^{iλt}` isometric | `space` |
| `bpW:w1:twosided` | two-sided space `ℓ^{a,s}_b`, odd/even extension maps `ℓ^{a,p} → ℓ^{a,p+1/2}_b` with norm `≤ √2` (after the `λ^{-1/2}` weight) | `space`, `bpW:w0:twosided` |
| `bpW:w1:young` | `ℓ² * ℓ¹ ⊂ ℓ²` (Young) and `ℓ¹` control by weighted `ℓ²` (Cauchy–Schwarz, `Σ_{l∈ℤ} ⟨l⟩^{-2s} = 1 + 2ζ(2s) < ∞` for `s > 1/2`) | `twosided` |
| `bpW:w1:algebra` | = `bpW:w0n:algebra` (moved here in Lean) | `young` |
| `bpW:w1:trilinear` | the cubic map as a `ContinuousMultilinearMap` `(ℓ^{a,p}_ℂ)³ → ℓ^{a,p+1}_ℂ` for `a ≥ 0`, `p ≥ 1/2` (track uses `p = 1`), real structure | `algebra`, `bpW:w0n:quartic-coeff` |
| `bpW:w1:cubic-analytic` | `G_q` analytic (from multilinearity), Lipschitz bound `‖G_q(q) − G_q(q')‖ ≤ 3C‖q−q'‖ max(‖q‖,‖q'‖)²` | `trilinear` |
| `bpW:w1:hamfield` | the Hamiltonian field `X_H = (λp, −λq − G_q)` as a map `E_{a,p+1} → E_{a,p}`; `X_G : E_{a,p} → E_{a,p+1}` (one-smoothing) | `diag`, `cubic-analytic` |
| `bpW:w1:gradient-identity` | `G_q` is the gradient of `G` w.r.t. the unweighted pairing `Σ q_j q'_j` (not the weighted Riesz gradient) | `bpW:w0n:gradient`, `trilinear` |
| `bpW:w1:sine-completeness` | sine system complete in `L²(0,π)` (from Mathlib's Fourier Hilbert basis on `AddCircle` via odd extension) | external (Mathlib) |

## Intended dependency edges beyond W1 (coarse)

- W2 (`bpW:w2:*`): `pde-equiv` + time-analyticity of a torus orbit ⇒ real-analytic all-time classical solution; uses
  `recon-bounded`, `w1:hamfield`.
- W3 (`bpW:w3:*`): `formal-birkhoff` + P96-W Lemma 4 (quantitative divisors, to be proved) + W1 ⇒ analytic symplectic
  `Γ` with `H∘Γ = Λ + Ḡ + G^nor + K`, `K = O(‖z‖⁶)`, smoothing fields. Consumes `AB`.
- W4–W6: P96-K Theorem A specialised to `d = 1`, `δ = −1`, `p̄ − p = 1`; consumes `nondeg`, `kappa`, W1, W3.
- W7: P96-K Theorem D with `κ = 2`, `Δ = 1`, `g = 6` (`6 > 11/2`); consumes `nondeg` ((A₃)), `kappa`.
- W8: KP96 §7 shell patching ⇒ `bpW:wh:nlw2` (the D30 first headline, a declared weakening of P96-W's Main Theorem
  for `J = {1,2}`); also proves its family-level injectivity conclusion (item (6): `K_I(θ) = K_{I'}(θ')` ⇒ `I = I'`,
  `θ ≡ θ'` mod 1) from the action/frequency parametrization of the family (P96-W pp. 272–273, 288–289); consumes W2,
  W6, W7. Lipschitz (Cantor-manifold) regularity of the family is deferred with Whitney regularity and stability (D30 Q3).

## Open questions for the owner (from this package)

1. Accept the normalization rulings above as the track-W conventions (they repair E-PDE-W-1/2 rather than copy
   P96-W)?
2. W0's `C_m` is uniform in `m > 0` (only `λ_j ≥ j` is used). Keep the headline's "for every `m > 0`, constants depend
   on `m`" (recommended, since later milestones do depend on `m`)?
