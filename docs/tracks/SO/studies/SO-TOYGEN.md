# SO-TOYGEN: passing data for the toy certificates T2, T2d, T3 and the checker-only toy TR (track SO)

Branch `inp-sotoygen`. This package is Python and generated data only: no Lean file is added to the repository. The
inputs are design Revision 7 (`docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §1, §4, §8), the signatures
`.drafts/design/SOSignatures.lean` (§C, §D, §F, §G, §J), design audit 1 finding F4, and the landed Lean modules under
`KAM/Certificate/`.

## Verdict

**All four toys pass, and none hits an obstruction.** For each toy, the generator writes the complete
`TorusCertificate n ℚ` as exact data. That covers the parameter package, Hamiltonian, domain, frequency box,
embedding, witnesses, Gram and torsion witnesses, `ModelConfig`s with `direct` advice, π enclosure and weight
controls. A Python mirror of `checkTorusCertificate` then runs on it, and all eight sub-checks pass with margin.

| Toy | n, τ | γ | threshold `γ⁴ρ^{4τ}/isoC1Q` | `err` | `isoC1Q·err / (γ⁴ρ^{4τ})` | `disp` | `|ν̃ − ν*|`, `N` |
|---|---|---|---:|---:|---:|---:|---|
| T2 | 2, 1 | 1/42 | 10^−38.23 | 10^−42.49 | 5.4e-5 | 1.88e-26 | ≤ 2·10^−43.1, `N = 43` |
| T2d | 2, 1 | 1/42 | 10^−188.79 | 10^−192 | 6.1e-4 | 1.96e-102 | ≤ 2·10^−198.1, `N = 197` |
| T3 | 3, 2 | 1/12 | 10^−59.30 | 10^−63.60 | 5.0e-5 | 1.94e-38 | ≤ 2·10^−64.2 (both coordinates), `N = 63` |
| TR | 2, 1 | 1/42 | 10^−30.06 | 0 | 0 | 0 | exact (`ν = 1/2`) |

- **TR passes the checker and is not Diophantine, which is what the design states.** Its reference vector
  `(1/4, 1/2)` is the box centre with radius 0. For `k = (2, −1)`, `k·ω = 0`, so `IsDiophantine γ τ ω` fails for
  every `γ > 0`. TR therefore supports only `toyRatCert_passes` and no `CertifiedTorus` (§3.4).
- **Negative tests.** 16 mutations of the passing data each fail their intended sub-check (§6). They cover all the
  §8 negative items that apply to ℚ toys. Three Lean controls of landed predicates evaluate to `false`.
- **Landed Lean code was checked exactly against the data, in Lean.** This was done by `lake env lean` on a scratch
  file outside the repository (§5):
  - the jet programs are those of the landed `HamExpr.jet`;
  - the Python ball mirror equals the landed `Slp.balls` slot by slot on every toy's domain;
  - `checkWeight` (both weights), `checkPiEnclosure`, `checkRootEnclosure`, `checkAlgBox` and both smallness
    inequalities `isoC1Q e < γ⁴ρ^{4τ}` and `isoC2Q e ≤ disp γ²ρ^{2τ}` all evaluate to `true`.
- **Main caveat.** Six of the eight sub-check bodies are still `sorry` in the signatures (`checkStatic` partly, and
  `checkEmbedding`, `checkInvariance`, `checkEnergy`, `checkGram`, `checkTorsion`, together with `Slp.compose`,
  the model operations and the witness radii). The mirror implements them from the docstrings and the design. Every
  reading is listed in §4. For T2, T3 and TR every composed model is exact (radius 0), so the outcome does not
  depend on those readings beyond the conventions in §4.
- **Design signal (T2d, kernel cost of the `direct` route).** T2d as specified needs a reciprocal witness of 531
  terms (`|k| ≤ 265`, 682-bit dyadic coefficients). The reason is M. The ball pass bounds `‖D²X_H‖` by 1,523 on
  every admissible domain, so `mSize ≈ 1,600`, and the threshold is 10^−188.8. The direct product `Q·Q` then has
  281,961 coefficient pairs, and it is needed at both precisions. At SO-REPLAY's measured direct-product rates this
  is far beyond a kernel replay. §7 gives the levers.

## 1. Pipeline (`scripts/spin_orbit/toy_*.py`)

| Script | Role |
|---|---|
| `toy_constants.py` | Exact mirror of `KAM/Certificate/Constants.lean` (`cRUpQ`, the mirror chain, `isoC1Q`, `isoC2Q`) for general `n`, `τ`, with Lean's `x / 0 = 0`. It is cross-checked against `exact_constants.py` at `n = 2`, `τ = 1`. |
| `toy_arith.py` | Exact mirror of the landed arithmetic: `ratExpUp`, `checkWeight`, `atanS`/`piLowRat`/`piUpRat`, `checkPiEnclosure` (ℚ), `checkRootEnclosure`, `checkAlgBox`, `CertBall` ops, `certCExp`, `certCExpReduced`, `cexpHalvings`, `constBall`, `ballStep` and `Slp.balls` |
| `toy_lean_extract.py` | Writes a scratch Lean file in a temporary directory and runs it with `nice -n 5 lake env lean` in an existing build. It extracts the landed `HamExpr.jet` programs, and optionally the landed `Slp.balls` and closed `Bool` predicates. |
| `toy_model.py` | Exact ℚ Fourier models: polynomials over a common integer denominator, weighted norms, `supBound`, `toDeg`, products on the `direct` route, `ofDeriv`, `shift`, and the exp and reciprocal witness radii |
| `toy_check.py` | The mirror of the eight sub-checks, `Slp.compose`, `gramCheck`, `torsionModels` and `torsionAvgCheck` |
| `toy_gen.py` | Builds the four certificates, sizes their precision against the threshold, runs the mirror, and writes `<toy>.json` and `summary.json` |
| `toy_crosscheck.py` | Compares jets and balls with Lean, and evaluates the landed predicates on the data in Lean |
| `toy_negative.py` | The negative tests (§6) |

Outputs (`certificates/so-toys/`): `jets.json` (the landed jet programs), `T2.json`, `T2d.json`, `T3.json`, `TR.json`
(each holds `certificate` and `verification`), `summary.json`, `lean_crosscheck.json` and `negative.json`.
Rationals are strings `p/q`, and polynomials are lists `[key, [re, im]]`.

Reproduce (about 10 s of Python, plus two Lean runs of about 30 s each):

```
cd scripts/spin_orbit
python3 toy_constants.py
python3 toy_lean_extract.py BUILD_DIR ../../certificates/so-toys/jets.json
python3 toy_gen.py ../../certificates/so-toys/jets.json ../../certificates/so-toys
python3 toy_crosscheck.py BUILD_DIR ../../certificates/so-toys/jets.json ../../certificates/so-toys
python3 toy_negative.py ../../certificates/so-toys/jets.json ../../certificates/so-toys BUILD_DIR
```

`BUILD_DIR` was the shared `inp` checkout `/root/code/KAM-inp`, used read-only through `lake env lean`. Its Lean
sources for `KAM/Certificate/{Expr,Arith,Model,Poly}/*` were byte-identical to this branch's.

## 2. The toys (data choices)

Common choices:
- `s = 2`, `σω = 3`, `γbar = γ`, `E0 = 0`.
- `ModelConfig.taylorN = 24`, `halvings = 8`, and `toMant` is unused on the direct route.
- `piEnc` is the Machin pair `(4, 4)` as centre ± half-width. No toy ever uses `toDeg`.
- Weights are the least multiple of 10^−6 that is `≥ ratExpUp(2·piUpQ·ρ, s, N)`.
- The embedding is `K(θ) = (θ, A)` with the actions `A` constant. It is stored as length-`n` lists of
  `CertRealPoly` with `zero = A_i`, `half = []`, and the angles zero (`zero = 0`, `half = []`).
- The Gram witness is `B = I`, so `G = I`, `δ = 0` and `β = 1`.
- The torsion witness `S` is the exact rational inverse of the averaged centre matrix.
- `M`, `σK`, `σB` and `σT` are all set to `mSize`, the largest requirement among them. Only
  `mSize = max(1, M, σK, σB, σT)` enters the constants. `M` carries a 5% margin over its ball bound, and `σT` carries
  1% over `‖S‖/(1 − δ_T) + μ`.
- `err` is the largest power of ten `≤ 10^−3 ×` threshold. For T2 and T3 it is 4 box radii, which is below that power.
- `disp` is `isoC2Q·err/(γ²ρ^{2τ})`, rounded up with a 0.1% margin.

### 2.1 Hamiltonians (`HamExpr` literals; `p = I₀`, `J = I₁`, `q = θ₀`)

- T2 and TR: `.add (.action 1) (.mul (.const (1 / 2)) (.pow (.action 0) 2))`. The jet has 20 slots.
- T2d: `.add (.action 1) (.mul (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.div N N))`, where
  `N = .add (.const 3) (.cosMode [1, 0])`. The jet has 156 slots and one `inv` slot (79). The two compiled
  characters, `[1, 0]` and `[-1, 0]`, both normalize to `(0, 0)` because `U ≡ 0`.
- T3: `toyHam3`, verbatim from A-E §J. The jet has 37 slots.

### 2.2 Per-toy data

| | T2 | T2d | T3 | TR |
|---|---|---|---|---|
| `ρ`, `ρ∞`, `δ₀` | 9, 1, 1 | 1/125, 1/1250, 9/10000 | 9, 1, 1 | 9, 1, 1 |
| `D`: `ρ_H`; action centre; radius | 451/50; `A`; 1/50 | 1/100; `A`; 3/2000 | 451/50; `A`; 1/50 | 451/50; `A`; 1/50 |
| `μ`, `ν` | 1/100, 49/100 | 1/1000, 49/100 | 1/100, 39/50 | 1/100, 49/100 |
| `M = σK = σB = σT` | 297/100 | 39969/25 | 161/20 | 89/50 |
| frequency provider | `checkRootEnclosure 2 5`, 43 digits | `checkRootEnclosure 2 5`, 193 digits | `checkRootEnclosure 3 2`, 65 digits | exact box |
| box | `(ν₋/2 ± 10^−43.1, 1/2 ± 0)` | `(ν₋/2 ± 10^−198.1, 1/2 ± 0)` | `(∛2/2 ± 10^−64.6, ∛4/2 ± 10^−64.2, 1/2 ± 0)` | `(1/4 ± 0, 1/2 ± 0)` |
| `A` (actions) | `(ν̃, −ν̃²/2)`, `ν̃ = 2·c₀` | same, 193-digit `ν̃` | `(a, b, −(a² + b²)/2)`, `a = 2c₀`, `b = 2c₁` | `(1/2, −1/8)` |
| witnesses | none | `invWit = [Q]`, `charWit = [((0, 0), E = 1, s = 0, N = 400)]` | none | none |
| cutoffs (full / low) | 0 / 0 | 532 / 30 | 0 / 0 | 0 / 0 |
| JSON size | 23 KB | 247 KB | 63 KB | 21 KB |

Notes on these choices:
- **Large strip for T2, T3 and TR.** The check `isoC1Q·e < γ⁴ρ^{4τ}` cancels `ρ^{4τ}`. That leaves `δ₀ = min(1,
  (ρ − ρ∞)/8)`, which is maximal (`= 1`) at `ρ − ρ∞ ≥ 8`. Those three toys have no angle dependence, so the
  large strip costs nothing. This is the design's "larger `ρ` (the toy is entire)" lever.
- **Small strip for T2d.** The denominator ball must exclude 0, which needs `w_H < 3`, and `M` grows quickly with
  `w_H`. A scan over `ρ_H ∈ [1/100, 1/25]` and `μ` moved the threshold by only 10^±3. The chosen point is
  `ρ_H = 1/100`, `μ = 1/1000`, action radius `3μ/2`.
- **The box drives the residual.** `ν̃ = 2c₀` (twice the box centre), so the invariance error over the whole box is
  exactly `2r₀`. The energy is `H∘K = 0` exactly for T2, T3 and TR.
- **The reciprocal witness Q (T2d)** is `c_k = (−r)^{|k|}/√8` with `r = 3 − 2√2`, for `|k| ≤ 265`, rounded to
  `2^−682`. Its sizing makes the truncation tail and the rounding each about `10^−5·err` on `T_ρ`. The check gives
  `δ = sup|1 − Q(3 + cos 2πq)| ≈ 10^−197`.

## 3. Margins (Python mirror)

### 3.1 HamBounds: the five ball bounds against `M`

| | `‖DH‖` | `‖X_H‖` | `‖DX_H‖` | `‖D²X_H‖` | `‖D²H‖` | `M` |
|---|---:|---:|---:|---:|---:|---:|
| T2 | 1.995 | 1 | 1 | 0 | 1 | 2.97 |
| T2d | 8.17 | 5.11 | 77.98 | **1522.6** | 90.55 | 1598.8 |
| T3 | 3.887 | 1.607 | 1 | 0 | 2 | 8.05 |
| TR | 1.52 | 1 | 1 | 0 | 1 | 1.78 |

T2d's `‖D²X_H‖` comes from the ball arithmetic of `∂³_q(N·N⁻¹)`. That function is exactly 0, but the ball pass
loses the correlation between `N` and `N⁻¹`. As `w_H → 1` the bound floors at about 1,520. The other toys are
polynomial, and their balls are exact.

### 3.2 The other checks

| | invariance bound / `err` | energy bound | `‖DK‖` / `σK − μ` | Gram `δ`, `β` | torsion `δ_T`; `‖S‖/(1 − δ_T)` / `σT − μ` | `ν` / `ν_max` |
|---|---|---|---|---|---|---|
| T2 | 1.6e-43 / 3.2e-43 | 0 | 1 / 2.96 | 0, 1 | 4.7e-43; 2.927 / 2.96 | 0.49 / 0.5 |
| T2d | 3.7e-197 / 1e-192 | 3.9e-198 | 1 / 1598.8 | 0, 1 | 4.0e-197; 2.927 / 1598.8 | 0.49 / 0.5 |
| T3 | 1.26e-64 / 2.5e-64 | 0 | 1 / 8.04 | 0, 1 | 1.0e-63; 7.955 / 8.04 | 0.78 / 0.7937 |
| TR | 0 / 0 | 0 | 1 / 1.77 | 0, 1 | 0; 1.75 / 1.77 | 0.49 / 0.5 |

Embedding margins:
- **Strip.** `ρ + ι + μ ≤ ρ_H` holds with slack `μ`, since `ι = 0`.
- **Action.** `dist + μ ≤ radius` holds with slack `μ` (T2, T3, TR) or `μ/2` (T2d).

### 3.3 Smallness

`checkSmallness` passes for all four toys, both in Python and in Lean (§5); see the Verdict table for the ratios. In
every toy the active term of `hatcStarQ` is `2^{2a}·hatCE` (the "E" term).

### 3.4 TR: why there is no torus

TR's box is exact: `(1/4, 1/2)`, radius 0, and the black box's `FreqEncloses` forces `ω* = (1/4, 1/2)`.
`k = (2, −1) ≠ 0` gives `k·ω* = 0 < γ/|k|₁^τ` for every `γ > 0`. So `IsDiophantine γ τ ω*` is false and
`checkTorusCertificate_sound` cannot be applied. The checker itself passes, with zero invariance and energy error,
so the zero-error case of the arithmetic is exercised. This is exactly the design's labelling: "Checker-only test
TR … Only `toyRatCert_passes`". The check is recorded in `TR.json` (`verification.resonance`).

## 4. Readings (bodies still `sorry`; SO-EMB, SO-MAT, SO-TORS, SO-DEFS should confirm or correct)

Each reading is one function in `toy_check.py` or `toy_model.py`.

1. **`checkStatic`.** It checks the `StaticFacts` list. It also checks shapes: `box.length = n`, `centre`/`radius`
   of length `n`, and the four embedding lists of length `n`. The box must exclude 0: `L := max_i (|c_i| − r_i) > 0`.
   The ray margins are `ν ≤ (s − 1)L` and `ν ≤ (σω − s)L`.
2. **`checkHamBounds`.** It runs `Slp.balls n ham.jet.prog weightH centre radius cfgFull.taylorN`. Each slot is
   bounded by `normUp(centre) + radius`. The five bounds are:
   - `Σ_a d1[a]`;
   - `max_a d1[swap a]`;
   - `max_a Σ_b d2[swap a][b]`;
   - `max_a Σ_{b,c} d3[swap a][b][c]`;
   - `Σ_{a,b} d2[a][b]`.

   They follow the `NormBridge` lemmas, and each must be `≤ M`. No toy has an `exp` slot, so `taylorN` is unused.
3. **`checkEmbedding`.** It uses `ι_i = min(sup|U_i|, ρ Σ_j sup|∂_j U_i|)` and requires `ρ + ι_i + μ ≤ ρ_H` and
   `sup|A_i − c_i| + μ ≤ r_i`, all as `supBound` of models. It also requires `max` row sum of `supBound(DK_{ij})`
   `≤ σK − μ`.
4. **`Slp.compose`.** It computes models in program order over the dependency closure of the wanted slots.
   Witnesses are consumed in slot order among the `exp` and `inv` slots of the whole program.
   - **Character slot `χ_k`.** The index is normalized by zeroing the coordinates whose `U_j` is syntactically zero
     (`zero = 0`, `half = []`). The witness is looked up by the normalized key, padded to length `n`. The model is
     `⟨0, shift_k E, r_E · w^{|k|₁}⟩`. **An all-zero normalized index still requires a witness.** T2d supplies
     `E = 1` at `(0, 0)`. If SO-EMB instead treats that case as the exact constant 1, the entry goes unused and the
     margins only improve.
5. **`CertModel.mul` (direct).** It forms the exact product, then moves terms with `|k|₁ > cutoff` into the radius at
   their weighted size. The cross terms are `|P_a|_w r_b + |P_b|_w r_a + r_a r_b`, with weighted norms that leave out
   the `(2π)^deg` factor.
6. **`CertModel.add` across degrees.** An exactly zero model takes the other operand's degree; otherwise `toDeg`
   goes through the π enclosure. No toy uses `toDeg`: the count is 0.
7. **`expWitnessRadius`.** It follows design §1.7 literally:
   - `B = |g₀|_w`;
   - `ε₀ = normUp(E(0) − out.c) + out.r`, with `out = certCExpReduced(Σ ĝ₀, 0, pinHalvings, pinOrder)`;
   - residual `r_j = supBound(∂_j E − (∂_j g₀)E)` at degree 1;
   - radius `ratExpUp(2B)(ε₀ + Σ_j (1/2 + ρ) r_j) + ratExpUp(B)(ratExpUp(η) − 1)`.
8. **`invWitnessRadius`.** It uses `δ = |1 − Q·P|_w + |Q|_w·rad_b` and requires `δ < 1`. The radius is
   `|Q|_w δ/(1 − δ)` and the model is `⟨−deg_b, Q, r⟩`.
9. **`checkInvariance`.** It evaluates the components `X_H(K) − DK(sω)` in `sumVec` order, with `sω_j` the ball
   `(s c_j, s r_j)`, and requires `max` of their `supBound` `≤ err`. It uses `cfgFull`. **`checkEnergy`** requires
   `normUp(coef₀ − E0) + rad ≤ err` on the degree-0 model of `v0∘K`.
10. **`gramCheck`.** It forms `G = DKᵀDK` from model products under `cfgLow`. Then `δ` is the `max` row sum of
    `supBound(I − BG)` and `β` the `max` row sum of `|B_ij|_w`. It requires `δ < 1` and `β/(1 − δ) ≤ σB − μ`.
11. **`torsionModels`.** It uses `G⁻¹ ≈ B` with entrywise radius `δβ/(1 − δ)`, and `N = Ω₀ DK G⁻¹`. The derivative
    term is `DN[v] = Ω₀(D²K[v] G⁻¹ − DK G⁻¹ DG[v] G⁻¹)`, with `DG[v]` built from `DK` and `D²K[v]`. Then
    `T = Nᵀ Ω₀ (DX_H(K) N − DN[v])`, where `DX_H(K)_{ab} = hamSign(a)·d2[swap a][b]∘K`. The border column is `v_a`,
    the last row is `DH(K) N`, and the corner is 0. It uses `cfgLow`.
12. **`torsionAvgCheck`.** It first checks the `(n+1) × (n+1)` shapes of `T` and `S`. Each entry is taken to degree
    0, giving `C = coef₀` and `R = rad`. Complex norms use `normUp`. It requires
    `δ_T = ‖I − SC‖ + ‖S‖‖R‖ < 1` and `‖S‖/(1 − δ_T) ≤ σT − μ`.
13. **Product keys (proposed, as in SO-DATA-PY §1.3).**
    - compose: `[0, slot]`;
    - character-witness residual: `[1, 1, slot, j]`;
    - reciprocal: `[2, inv]`;
    - Gram: `[3, 0|1, i, j, k]`;
    - torsion: `[4, sub, i, j, k]`.

    Each config's advice book lists every distinct key with `direct`. For the ℚ toys, a default-`direct` policy
    would make the book unnecessary.

## 5. Cross-checks against landed Lean (`lean_crosscheck.json`)

These were run with `lake env lean` on a scratch file, in the shared build (read-only), one process at a time.

- **Jets.** The re-extracted `HamExpr.jet` programs of T2, T2d and T3 are identical to `jets.json`.
- **Balls.** The landed `Slp.balls` on each toy's certificate domain (`weightH`, `centre`, `radius`) equals the
  Python mirror exactly, for every slot: 20, 156, 37 and 20 slots.
- **Landed predicates on the emitted data.** Each one evaluates to `true` for all four toys:
  - `checkWeight weight` and `checkWeight weightH`;
  - `checkPiEnclosure`;
  - `checkRootEnclosure` and `checkAlgBox`, for T2, T2d and T3;
  - `decide (isoC1Q … * err < γ ^ 4 * ρ ^ (4τ))`;
  - `decide (isoC2Q … * err ≤ disp * γ ^ 2 * ρ ^ (2τ))`.

## 6. Negative tests (`negative.json`)

Every mutation fails in its intended sub-check. Failures that follow from it are listed as well.

| Mutation | Design | Toy | Fails |
|---|---|---|---|
| false residual bound (`err` = half the invariance bound) | §8.1 | T2 | checkInvariance |
| Gram witness `B = 0` | §8.2 | T2 | checkGram (and checkTorsion) |
| torsion witness `S = 0` | §8.2 | T2 | checkTorsion |
| `μ = 0` | §8.3 | T2 | checkStatic |
| character witness with wrong mean (`E = 2`) | §8.4 | T2d | checkInvariance (and Energy, Torsion) |
| `w = 1 < e^{2πρ}` | §8.5 | T2 | checkStatic |
| denominator ball contains 0 (`ρ_H = 1/5`, `w_H ≥ 3`) | §8.6 | T2d | checkHamBounds |
| reciprocal witness `Q = 0` (`δ = 1`) | §8.6 | T2d | checkInvariance (and Energy, Torsion; compose fails closed) |
| box not excluding 0 | §8.7 | T2 | checkStatic (and Invariance, Torsion) |
| ray margin `ν = 6/10 > (s − 1)·1/2` | §8.7 | T2 | checkStatic |
| π enclosure narrowed below the Machin bounds | §8.8 | T2 | checkStatic |
| torsion witness of shape 4 × 4 at `n = 2` (F7 analogue) | §8.9 | T2 | checkTorsion |
| `err = 10^6 ×` threshold | control | T2 | checkSmallness |
| `M = 1` | control | T2 | checkHamBounds |
| `σK = 1 + μ/2` | control | T2 | checkEmbedding |
| action centre shifted by the radius | control | T2 | checkEmbedding |

Lean controls, all `false`: `checkWeight ⟨9, 1⟩`, the narrowed `checkPiEnclosure`, and the smallness inequality at
`err = 10^6 ×` threshold.

Two §8 items are not covered here:
- §8.9 at `n = 1` proper, because no toy has `n = 1`;
- §8.10, the character pin with `|2πk·U(0)| > 1`, because it needs a nonzero `U`. SO-CEXP's `Tests/ComplexExp`
  covers the reduction itself.

## 7. Design signal: T2d on the direct route

The product counts are those of the mirror, in coefficient pairs.

| | distinct products | pairs | largest |
|---|---:|---:|---|
| T2, TR | 7 full + 184 low (most with a zero factor) | 25 | 1 × 1 |
| T3 | 14 + 601 | 46 | 1 × 1 |
| **T2d** | 37 full + 237 low | **294,568 + 321,471** | `Q·Q`: 531 × 531 = 281,961 (in both configs); `Q·Q²` (low, cut at 30): 531 × 61 = 32,391 |

**Cost.** SO-REPLAY measured naive direct products in the kernel at about 2.3 ms and 190 KB per coefficient pair, at
450 bits. T2d's coefficients are 682-bit dyadics, about 400 bits after products. On those rates, T2d's two `Q·Q`
products alone come to about 0.56 M pairs, roughly 20 min and about 100 GB. **T2d as specified is therefore not
replayable on the `direct` route.** T2, T3 and TR are trivial.

**Levers** (not taken here; SO-TEST, SO-EMB or the owner decide):
1. `trim` (or a smaller cutoff) of the `inv` slot model before products under `cfgLow`. It would cut the low-precision
   `Q·Q` to about 61² pairs.
2. Reuse the `Q·Q` product between the two configs, or route T2d's two or three large products through `packed`
   advice, as for the lunar data.
3. A larger constant in `(a + cos 2πq)/(a + cos 2πq)`. These are estimates on the same jet with the constant
   replaced, against the same domain (rows in the order `a`, `M`, threshold, `K`, `Q·Q` pairs):

   | `a` | M | threshold | K | `Q·Q` pairs |
   |---:|---:|---:|---:|---:|
   | 3 | 1,524 | 10^−188 | 264 | 2.8e5 |
   | 5 | 336 | 10^−164 | 177 | 1.3e5 |
   | 10 | 84 | 10^−142 | 117 | 5.5e4 |
   | 30 | 18 | 10^−117 | 71 | 2.0e4 |

   The decorrelation of `N·N⁻¹` in the ball pass drives `M`, and through `mSize^{≈38}` the threshold.

## 8. Determinism and input pins

Determinism: two runs of `toy_gen.py` produce byte-identical `<toy>.json`. The pipeline uses no floating point in
any emitted value, no NumPy and no randomness. The environment was Python 3.12.3.

| Input | SHA-256 |
|---|---|
| `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Revision 7) | `4576b12f60f8eec34eac5bd93f14870aa0c1c90dd74c303546b0b06ff1617d8f` |
| `.drafts/design/SOSignatures.lean` (main checkout) | `9a4652019186e914a0ccfdba6e01c903e458b679d0c057ac4cf7b7d353a4c1cc` |
| `KAM/Certificate/Expr/Ball.lean` | `f4cdcef038daadcc979cb01237331e323f2547936ddbb34de45d366583810566` |
| `KAM/Certificate/Expr/Diff.lean` | `100c735b586b3d0f18a95a76ad9d4b05feb45242b2da0462d9b2397cd7905a8c` |
| `KAM/Certificate/Expr/DiffNode.lean` | `521beb43d6723acc8a041fe09c4c547f678cba8615a09bff5ab309745f75d695` |
| `KAM/Certificate/Expr/DiffBuild.lean` | `a8eff5ab88e7fc1378f5815f67f43f663a449a5dc4f0cbc2cc53f74e880ead48` |
| `KAM/Certificate/Expr/Slp.lean` | `b0519678950971fbba6cc487f4abb6753480d0b4f9323d0073b7e497c5964e83` |
| `KAM/Certificate/Constants.lean` | `2c1b094e2f9d40ddb3bf59928556aa9bd3a86111bbe4856fff5ab66d9b8d9530` |
| `KAM/Certificate/Freq.lean` | `57b070e7d6a0298596a1b5c054362a7924874fee82fcc1fb3d2d1b488cd6fca9` |
| `KAM/Certificate/Model/Basic.lean` | `583f95640c2066caddd5742b139e281e396b0987cb4a34c0d4274cf7cc1bdbec` |
| `KAM/Certificate/Arith/{ComplexExp,Roots,PiHigh,Transcendental}.lean` | `66a31cd0…`, `93a799af…`, `0ee583dd…`, `c2fea76c…` |
| `KAM/Certificate/{Quadratic,Cubic}Diophantine.lean`, `KAM/SpinOrbit/Freq.lean` | `511dafeb…`, `fda76dde…`, `d1a484c4…` |
| `certificates/so-toys/jets.json` | `b2017a27ad05ec34a303898e0545bd6a9196cc318e5270e659be7e5b011933fb` |

The output hashes are in `certificates/so-toys/summary.json`.

## 9. Uncertainties, errata and deviations

1. **The readings of §4 are this package's.** The two most likely to differ are 2 (how `checkHamBounds` assembles
   the five norms) and 4 (whether an all-zero normalized character index needs a witness). For T2, T3 and TR, any
   sound implementation gives the same models, because all of them are exact. Only the `M` convention could matter,
   and `M` has 5% slack there (in fact far more, since `M = mSize`). For T2d the slack is 5% on `M` and
   10^4.4 between the invariance bound and `err`.
2. **`toyHam2` and `toyHam2d` are not given verbatim in A-E §J.** The literals of §2.1 are this package's choice:
   `p = I₀` and `q = θ₀`.
3. **Errata:** none suspected in the pinned sources.
4. **Deviations:** none from the design's toy specifications. TR is checker-only, as the design states. "The
   negative toy" of the brief is read as TR's missing Diophantine premise, together with the §8 negative mutations
   of §6.
