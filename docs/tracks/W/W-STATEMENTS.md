# Track W: exact Lean drafts of W-NLW2 and its definitions (W-STMT)

Status: **DRAFT, revision 1 (after audit `docs/tracks/W/audits/W-STMT-audit-1.md`), for independent re-audit and owner approval. Nothing is frozen or manifested.**
Drafts live at `.drafts/W/KAM/Wave/{Defs,Theorems}/*.lean` (not committed), one public declaration per file,
namespace `KAM.Wave`. Proposed final paths (ruling Q5, rev 1): `KAM/Frozen/Wave/Defs/<Name>.lean` and
`KAM/Frozen/Wave/Theorems/Nlw2.lean`, namespace `KAM.Wave`, one individually versioned anchor per declaration
(`WaveSpace` and `coeff` frozen together as separate anchors, Q1). Each draft's header comment records its path.
Section headings below still give the draft module names.

Mathematical source: blueprint-W rev 1 (`blueprint-W/parts/w0-conventions.tex`, `w-headline.tex`), P96-W
(Pöschel, CMH 71 (1996)), owner decision D30, orchestrator ruling W-A2 (declared weakenings).

## Design summary

* **Mode index `ℕ+`**: sequences are `ℕ+ → ℝ`, so `j ≥ 1` is literal (no index shift). Tangential mode
  `i : Fin 2` is Dirichlet mode `j = i + 1` (`(i : ℕ).succPNat`).
* **Phase space in weighted coordinates.** `E_{1,1}` is `lp (fun _ : ℕ+ => ℝ) 2 × lp (…) 2` (Mathlib `lp`,
  product = max norm). A point `(y, y')` stands for `q_j = y_j/(j e^j)`, `p_j = y'_j/(j e^j)`
  (`coeff`). `q ↦ (j e^j q_j)` is an isometric iso `ℓ^{1,1} ≅ ℓ²`, so `‖(y,y')‖ = max(‖q‖_{1,1},‖p‖_{1,1})`
  exactly as in `bpW:w0:ellap`. This gives a genuine Mathlib Banach space (needed for analyticity, `fderiv`,
  continuity) with **no new structure**. Alternative considered: a submodule of `ℕ+ → ℝ` with a hand-built
  norm — rejected (new normed-space instance = new meaning-carrying code).
* **Positive carriers (rev 1).** Every mass-dependent definition takes `(hm : 0 < m)` (W-ST2) and `linearTorus`
  takes `(hI : ∀ i, 0 < I i)` (W-ST1), so no definition can be applied off the source domain.
* **No fallback branches** except the Mathlib total-function convention for `η` (Q3, accepted); every `tsum`
  is over a series that converges absolutely for every input (Lemma `bpW:w0n:recon-bounded`, `a = 1 > 0`).
* **Diophantine**: reuses frozen `KAM.IsDiophantine` (n = 2), as the blueprint prescribes; no new definition.
* **`D_ν`** (`bpW:wh:Dnu`) is not a separate declaration: (4) is stated as `HasDerivAt` of
  `t ↦ coeff (K I (θ + t•ν)) j` at `0`, which is `D_ν` of the coordinate, coordinatewise as in
  `bpW:w0:eqmotion` ("or coordinatewise").
* **Hamiltonian `H_m`, two-sided spaces, actions/angles**: not used by the statement, so not drafted.

## Elaboration (every draft)

Oleans were produced transiently into the scratchpad in dependency order (no `lake build`; the frozen
`KAM/Frozen/Defs/IsDiophantine.lean` was compiled read-only the same way because the worktree has no KAM build):

```
cd /root/code/KAM-w && LEAN_NUM_THREADS=1 nice -n 5 lake env bash -c \
  "LEAN_PATH=\$LEAN_PATH:$S lean -o $S/<Mod path>.olean -i $S/<Mod path>.ilean <file>"
```
Result (rev 1, re-run in dependency order IsDiophantine, Lam, SineMode, EllWeight, WaveSpace, Coeff, ReconU,
ReconV, CubicGrad, LinearTorus, IsAnalyticTorusEmbedding, IsClassicalSolution, Nlw2): all **11 definition
files** and the frozen dependency: no output, exit 0. The **one theorem file** `Theorems/Nlw2.lean`: exit 0, the
only message `warning: declaration uses 'sorry'` (the draft body). No heartbeat options; max file 79 lines.

`#print axioms` (rev 1): `nlw2` depends on `[propext, sorryAx, Classical.choice, Quot.sound]` (`sorryAx`
expected for the draft); all eleven definitions depend only on `[propext, Classical.choice, Quot.sound]`.

## Declarations

### `Lam` (`KAM.Wave.Defs.Lam`)

```lean
namespace KAM.Wave

/-- The linear frequency `λ_j = √(j² + m)` of the Dirichlet mode `j ≥ 1` of
`u_tt = u_xx - m u` on `[0, π]` (P96-W p. 277). The standing convention `0 < m` is part of the
carrier (W-ST2). -/
def lam (m : ℝ) (_hm : 0 < m) (j : ℕ+) : ℝ :=
  Real.sqrt ((j : ℝ) ^ 2 + m)

end KAM.Wave
```

Source: `bpW:w0:basis`; P96-W p. 277. Binders: `m` typing, `_hm : 0 < m` standing convention `bpW:w0:mass` (W-ST2), `j` typing.

### `SineMode` (`KAM.Wave.Defs.SineMode`)

```lean
namespace KAM.Wave

/-- The normalized Dirichlet eigenfunction `φ_j(x) = √(2/π) sin(j x)`, `j ≥ 1`, defined for all
real `x` (P96-W p. 277). -/
def sineMode (j : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.sin ((j : ℝ) * x)

end KAM.Wave
```

Source: `bpW:w0:basis`; P96-W p. 277. Defined for all `x : ℝ` (needed: (5) asks analyticity of `u` near `x=0,π`). Binders typing.

### `EllWeight` (`KAM.Wave.Defs.EllWeight`)

```lean
namespace KAM.Wave

/-- The weight `j ^ p * e ^ (a j)` of `ℓ^{a,p}`: `‖w‖_{a,p}² = Σ_{j ≥ 1} (ellWeight a p j * |w_j|)²`
(P96-W p. 277). It is strictly positive. -/
def ellWeight (a p : ℝ) (j : ℕ+) : ℝ :=
  (j : ℝ) ^ p * Real.exp (a * j)

end KAM.Wave
```

Source: `bpW:w0:ellap`; P96-W p. 277 (source `s` = our `p`). Binders `a p j` typing. Strictly positive, so division by it in `coeff` is exact.

### `WaveSpace` (`KAM.Wave.Defs.WaveSpace`)

```lean
namespace KAM.Wave

/-- The phase space `E_{1,1}` in weighted coordinates (two copies of `ℓ²(ℕ+)`, max norm). -/
abbrev WaveSpace : Type :=
  lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2

end KAM.Wave
```

Source: `bpW:w0:ellap`, `bpW:w0:weights` (ruling: a = p = 1, D30/W-BP0). Weighted-coordinate representation, see design summary.

### `Coeff` (`KAM.Wave.Defs.Coeff`)

```lean
namespace KAM.Wave

/-- The `ℓ^{1,1}` coefficient sequence `q_j = y_j / (j e^j)` represented by `y ∈ ℓ²(ℕ+)`. -/
def coeff (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) : ℝ :=
  y j / ellWeight 1 1 j

end KAM.Wave
```

Source: `bpW:w0:ellap`. Representation map only (meaning: the coefficient sequence of the point).

### `ReconU` (`KAM.Wave.Defs.ReconU`)

```lean
namespace KAM.Wave

/-- The displacement reconstruction `U_m(q)(x) = Σ_{j ≥ 1} q_j / √λ_j · φ_j(x)`, where `q = coeff y` (P96-W p. 277). -/
def reconU (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, coeff y j / Real.sqrt (lam m hm j) * sineMode j x

end KAM.Wave
```

Source: `bpW:w0:reconstruction`; P96-W p. 277 (`u = 𝒮q`, `v = 𝒮'p`). Binders typing, except `hm : 0 < m` (standing convention, W-ST2). `tsum` converges absolutely for every `y`, `x`.

### `ReconV` (`KAM.Wave.Defs.ReconV`)

```lean
namespace KAM.Wave

/-- The velocity reconstruction `V_m(p)(x) = Σ_{j ≥ 1} √λ_j p_j · φ_j(x)`, where `q = coeff y` (P96-W p. 277). -/
def reconV (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, Real.sqrt (lam m hm j) * coeff y j * sineMode j x

end KAM.Wave
```

Source: `bpW:w0:reconstruction`; P96-W p. 277 (`u = 𝒮q`, `v = 𝒮'p`). Binders typing, except `hm : 0 < m` (standing convention, W-ST2). `tsum` converges absolutely for every `y`, `x`.

### `CubicGrad` (`KAM.Wave.Defs.CubicGrad`)

```lean
namespace KAM.Wave

/-- The cubic gradient `𝒢(q)_l = λ_l^{-1/2} ∫₀^π U_m(q)(x)³ φ_l(x) dx`, `l ≥ 1`, i.e.
`∂G/∂q_l` for `G(q) = ¼ ∫₀^π U_m(q)⁴` (blueprint-W `bpW:w0:Gq`, Lemma `bpW:w0n:gradient`). -/
def cubicGrad (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) : ℝ :=
  (∫ x in (0 : ℝ)..Real.pi, reconU m hm y x ^ 3 * sineMode l x) / Real.sqrt (lam m hm l)

end KAM.Wave
```

Source: `bpW:w0:Gq`; P96-W (8)–(9) p. 280. Output as a raw sequence `ℕ+ → ℝ` (only coordinatewise use in (4); membership in `ℓ^{1,2}` is a theorem, `bpW:w0n:cubic-bound`). `intervalIntegral` of a continuous integrand: no default branch. `hm : 0 < m` standing convention (W-ST2).

### `LinearTorus` (`KAM.Wave.Defs.LinearTorus`)

```lean
namespace KAM.Wave

/-- The linear torus of action `I ∈ (0, ∞)²` (positivity is part of the carrier, W-ST1), period-one angle `θ`:
`Q⁰_j = √(2 I_j) cos(2π θ_j)`, `P⁰_j = -√(2 I_j) sin(2π θ_j)` for `j = 1, 2`, and
`Q⁰_j = P⁰_j = 0` for `j ≥ 3` (blueprint-W `bpW:w0:periodone`). -/
def linearTorus (I : Fin 2 → ℝ) (_hI : ∀ i, 0 < I i) (θ : Fin 2 → ℝ) : WaveSpace :=
  (∑ i : Fin 2, lp.single 2 (i : ℕ).succPNat
      (ellWeight 1 1 (i : ℕ).succPNat * (Real.sqrt (2 * I i) * Real.cos (2 * Real.pi * θ i))),
    ∑ i : Fin 2, lp.single 2 (i : ℕ).succPNat
      (ellWeight 1 1 (i : ℕ).succPNat * (-(Real.sqrt (2 * I i) * Real.sin (2 * Real.pi * θ i)))))

end KAM.Wave
```

Source: `bpW:wh:lintorus` = `bpW:w0:periodone`. Binders `I θ` typing; `_hI : ∀ i, 0 < I i` source domain `(0,∞)²` (W-ST1), so `Real.sqrt` is never clamped.

### `IsAnalyticTorusEmbedding` (`KAM.Wave.Defs.IsAnalyticTorusEmbedding`)

```lean
namespace KAM.Wave

/-- `K : ℝ² → E` is an analytic torus embedding: `ℤ²`-periodic, real analytic, injective modulo
`ℤ²`, with injective derivative everywhere (blueprint-W `bpW:wh:embedding`). -/
def IsAnalyticTorusEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : (Fin 2 → ℝ) → E) : Prop :=
  (∀ (k : Fin 2 → ℤ) (θ : Fin 2 → ℝ), K (θ + fun i => (k i : ℝ)) = K θ) ∧
  AnalyticOnNhd ℝ K Set.univ ∧
  (∀ θ θ' : Fin 2 → ℝ, K θ = K θ' → ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ)) ∧
  ∀ θ : Fin 2 → ℝ, Function.Injective (fderiv ℝ K θ)

end KAM.Wave
```

Source: `bpW:wh:embedding`. Real analyticity as `AnalyticOnNhd ℝ` (local power series); equivalent for Banach targets to the blueprint's local holomorphic-extension wording (Q4). Generic in the Banach target `E`.

### `IsClassicalSolution` (`KAM.Wave.Defs.IsClassicalSolution`)

```lean
namespace KAM.Wave

/-- `u` is a classical solution on `ℝ` of `u_tt = u_xx - m u - u³` on `[0, π]` with
`u(t, 0) = u(t, π) = 0` (blueprint-W `bpW:w0:nlw`). -/
-- The standing convention `0 < m` is part of the carrier (W-ST2, uniform mass discipline).
def IsClassicalSolution (m : ℝ) (_hm : 0 < m) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ut ux utt uxx : ℝ → ℝ → ℝ,
    (∀ v ∈ ({Function.uncurry u, Function.uncurry ut, Function.uncurry ux,
        Function.uncurry utt, Function.uncurry uxx} : Set (ℝ × ℝ → ℝ)),
      ContinuousOn v (Set.univ ×ˢ Set.Icc 0 Real.pi)) ∧
    (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
      HasDerivAt (fun s => u s x) (ut t x) t ∧
      HasDerivAt (fun s => ut s x) (utt t x) t ∧
      HasDerivWithinAt (u t) (ux t x) (Set.Icc 0 Real.pi) x ∧
      HasDerivWithinAt (ux t) (uxx t x) (Set.Icc 0 Real.pi) x ∧
      utt t x = uxx t x - m * u t x - u t x ^ 3) ∧
    ∀ t : ℝ, u t 0 = 0 ∧ u t Real.pi = 0

end KAM.Wave
```

Source: `bpW:w0:nlw` with interval `ℝ`; P96-W (1) p. 272, `f(u) = u³` (declared specialization). Derivatives as named witnesses; `u_x,u_xx` within `[0,π]` (one-sided at endpoints), all five continuous on `ℝ × [0,π]`. `_hm : 0 < m` carried for uniform mass discipline (W-ST2 ruling: every definition using `m`).

### `nlw2` (`KAM.Wave.Theorems.Nlw2`)

```lean
namespace KAM.Wave

/-- **W-NLW2 (proposed).** For every `m > 0` the cubic Dirichlet wave equation
`u_tt = u_xx - m u - u³` has a density-one (in the actions, at `0`) Borel family of small analytic
invariant 2-tori with Diophantine frequencies, carrying exact classical PDE solutions, pairwise
disjoint and embedded. -/
theorem nlw2 {m : ℝ} (hm : 0 < m) :
    ∃ (r₀ C τ : ℝ) (η : ℝ → ℝ) (Γ : Set (Fin 2 → ℝ)) (ν : (Fin 2 → ℝ) → Fin 2 → ℝ)
      (K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace),
      0 < r₀ ∧ 0 < C ∧ 1 < τ ∧
      (∀ r ∈ Set.Ioo 0 r₀, 0 ≤ η r) ∧ Tendsto η (𝓝[>] 0) (𝓝 0) ∧
      MeasurableSet Γ ∧ Γ ⊆ {I | (∀ i, 0 < I i) ∧ Real.sqrt (I 0 + I 1) < r₀} ∧
      ContinuousOn ν Γ ∧ ContinuousOn (Function.uncurry K) (Γ ×ˢ Set.univ) ∧
      -- (1) density one in actions
      Tendsto (fun h : ℝ => volume (Γ ∩ Metric.ball 0 h) /
          volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h)) (𝓝[>] 0) (𝓝 1) ∧
      -- (2) two independent frequencies
      (∀ I ∈ Γ, ∃ γ : ℝ, 0 < γ ∧ KAM.IsDiophantine γ τ (ν I)) ∧
      Tendsto ν (𝓝[Γ] 0) (𝓝 fun i => lam m hm (i : ℕ).succPNat / (2 * Real.pi)) ∧
      -- (3) small embedded tori
      (∀ (I : Fin 2 → ℝ) (hI : ∀ i, 0 < I i), I ∈ Γ → IsAnalyticTorusEmbedding (K I) ∧
        (∀ θ, ‖K I θ - linearTorus I hI θ‖ ≤
          η (Real.sqrt (I 0 + I 1)) * Real.sqrt (I 0 + I 1)) ∧
        ∀ θ, ‖K I θ‖ ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (4) exact invariance
      (∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).1 j)
          (lam m hm j * coeff (K I θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).2 j)
          (-(lam m hm j * coeff (K I θ).1 j) - cubicGrad m hm (K I θ).1 j) 0) ∧
      -- (5) PDE solutions
      (∀ I ∈ Γ, ∀ θ₀ : Fin 2 → ℝ,
        (∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi,
          AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (K I (θ₀ + z.1 • ν I)).1 z.2) z) ∧
        IsClassicalSolution m hm (fun t x => reconU m hm (K I (θ₀ + t • ν I)).1 x) ∧
        (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          HasDerivAt (fun s => reconU m hm (K I (θ₀ + s • ν I)).1 x)
            (reconV m hm (K I (θ₀ + t • ν I)).2 x) t) ∧
        ∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          |reconU m hm (K I (θ₀ + t • ν I)).1 x| +
            |derivWithin (reconU m hm (K I (θ₀ + t • ν I)).1) (Set.Icc 0 Real.pi) x| +
            |reconV m hm (K I (θ₀ + t • ν I)).2 x| ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (6) family injectivity
      ∀ I ∈ Γ, ∀ I' ∈ Γ, ∀ θ θ' : Fin 2 → ℝ, K I θ = K I' θ' →
        I = I' ∧ ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) := by
  sorry

end KAM.Wave
```

Source: `bpW:wh:nlw2` rev 1; P96-W Main Theorem pp. 272–273 (J = {1,2}), Cantor Manifold Thm p. 289; D30 Q2–Q3;
ruling W-A2.

**Binder classification.** `m`: typing; `hm : 0 < m`: source premise (`bpW:w0:mass`), threaded into every
mass-dependent definition. No other hypotheses. Counts: SOURCE 1, STANDING 0, TYPING 1, RULED 0, EXCESS 0.
In (3) the bound variable `hI : ∀ i, 0 < I i` is part of the universally quantified conclusion, not a premise:
(3) quantifies over positive `I` with `I ∈ Γ`, which (since `Γ ⊆` the positive quadrant) is the same set of `I`
as `∀ I ∈ Γ`.
Existentials (in the blueprint order, after `m`, before `I`, `θ₀`): `r₀ C τ η Γ ν K`. `γ` is chosen per `I`
inside (2), so it may degenerate as `I → 0` (`bpW:wh:reading`).

**Clause map.** side conditions ↔ preamble of `bpW:wh:nlw2` (`r₀,C > 0`, `τ > 1`, `η ≥ 0` on `(0,r₀)`,
`η → 0⁺`, Γ Borel (`MeasurableSet` for the Borel σ-algebra of `Fin 2 → ℝ`), `Γ ⊆ {I ∈ P : r(I) < r₀}`,
ν continuous on Γ, `(I,θ) ↦ K_I θ` continuous on `Γ × ℝ²`); (1) ratio in `ℝ≥0∞`, `B_h = Metric.ball 0 h`
(sup norm on `Fin 2 → ℝ` = `max |I_i| < h`); (2) `KAM.IsDiophantine γ τ (ν I)` and `ν → (λ₁,λ₂)/(2π)` along
`𝓝[Γ] 0`; (3) embedding, `‖K_I θ − K⁰_I θ‖_E ≤ η(r) r`, `‖K_I θ‖_E ≤ C r` (pointwise ∀θ = sup bound);
(4) coordinatewise invariance for all `j : ℕ+`; (5) analyticity of `(t,x) ↦ u` at every point of `ℝ × [0,π]`,
classical solution, `u_t = V_m(P)`, and `|u| + |u_x| + |u_t| ≤ C r` with `u_x` = `derivWithin` on `[0,π]`
and `u_t` written as `V_m(P)` (equal by the preceding conjunct); (6) family injectivity.

## Declared weakenings (from `bpW:wh:weakenings`, ruling W-A2, D30 Q3)

Deferred: linear stability; Whitney regularity; Lipschitz (Cantor-manifold) regularity of the family — only
continuity of `(I,θ) ↦ K_I θ` is asserted. Also declared: Borel density-one set instead of a Cantor set; `o(r)`
closeness instead of `O(r^σ)`; pure cubic nonlinearity, `a = p = 1`, period-one angles. Retained: analytic
embedding (3) and family injectivity (6). None of the deferred items appears in the draft.

## Deviations introduced by this draft (for audit)

1. Weighted-coordinate encoding of `E_{1,1}` (isometric; changes no statement content).
2. `D_ν` stated as a directional `HasDerivAt` of each coefficient, not via `fderiv` of `K` (equivalent given
   the analyticity in (3)).
3. The `u_t` bound in (5) uses `V_m(P)` rather than a derivative symbol (equal by the conjunct before it).

## Owner questions (rev 1: resolved by orchestrator rulings, adopting audit recommendations; for owner review)

* **Q1** weighted coordinates accepted; `WaveSpace` and `coeff` frozen together as separately versioned anchors.
* **Q2** restricted carrier: `linearTorus` takes `(hI : ∀ i, 0 < I i)` (W-ST1).
* **Q3** total `η` with local constraints accepted.
* **Q4** `AnalyticOnNhd ℝ` / `AnalyticAt ℝ` accepted for the Banach targets; no uniform-strip claim is made.
* **Q5** final paths `KAM/Frozen/Wave/Defs/...`, `KAM/Frozen/Wave/Theorems/Nlw2.lean`, namespace `KAM.Wave`.

## Revision 1 (response to `W-STMT-audit-1`)

| Finding | Fix |
|---|---|
| W-ST1 (BLOCKER) `linearTorus` accepted non-positive actions (`I = (−1,−1)` gave `0`) | Signature `linearTorus (I : Fin 2 → ℝ) (_hI : ∀ i, 0 < I i) (θ : Fin 2 → ℝ)`. Proof argument chosen over a subtype so that `Γ`, the density ratio (1) and `ν` stay on `Fin 2 → ℝ` with Lebesgue `volume`. In `nlw2` (3) now reads `∀ (I) (hI : ∀ i, 0 < I i), I ∈ Γ → …linearTorus I hI θ…`; positivity comes from the existing `Γ ⊆` positive-quadrant clause, no new premise. |
| W-ST2 (BLOCKER) `lam`, `reconU`, `reconV`, `cubicGrad` accepted any real `m` (`m = −1` gave `lam = 0`, `cubicGrad = 0`) | Each takes `(hm : 0 < m)` after `m` (`_hm` in `lam`); `IsClassicalSolution` also takes `_hm` (ruling: every definition using `m`). `nlw2` keeps the single premise `hm : 0 < m` and passes it everywhere. |
| W-ST3 (NOTE) counts / axioms | Counts corrected (11 definition files + 1 theorem); `#print axioms` recorded above. |
| W-ST4 (NOTE) lint ABI stage | Noted only: needs built KAM artifacts; the library is not built in this worktree (rule 8). |

**Counterexample probe (rev 1).** A transient probe importing the rev-1 drafts: `#check_failure (lam (-1) 1)`,
`#check_failure (cubicGrad (-1) 0 1)` and `#check_failure (linearTorus (fun _ => -1) (fun _ => 0))` all fail to
elaborate (a proof of `0 < -1` resp. `∀ i, 0 < -1` is required), and `example : ¬ (0:ℝ) < -1` and
`example : ¬ ∀ i : Fin 2, (0:ℝ) < -1` are proved, so no term `lam (-1) h …` or `linearTorus (fun _ => -1) h …`
exists. Positive instances (`lam 1 one_pos 1`, `linearTorus (fun _ => 1) (fun _ => one_pos) …`) elaborate.
Probe exit 0.
