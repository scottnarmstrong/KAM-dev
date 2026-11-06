# N2-Chart handoff (T2-CONF): the symplectic chart from (η, ξ) to (u, φ)

Worker g2-n2. Status: **complete.** All targets (A)–(E) are proved, plus two additions the consumer N5
needs (a local-inverse regularity layer and an observable/periodicity layer, see "Deviations").
No `sorry`, no `set_option`, every file ≤ 1500 lines, axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Files (namespace `KAM.EffectiveStability.Tube`, directory `KAM/EffectiveStability/Tube/Chart/`)

| file | lines | content |
|---|---:|---|
| `Bracket.lean` | 89 | `bracketSum`; sign formula; generic symplectic transport of rates; germ congruence |
| `Rotation.lean` | 160 | (A): `rotMap`, inverses, symplecticity, rotation transport, regularity of `H ∘ Rinv` |
| `Polar.lean` | 216 | (B), (C): `polar`, `actionPos`, `polarD`, smoothness, symplecticity, polar transport, `polarInv`, coverage |
| `Shift.lean` | 147 | (D): `phiOf`, `shiftChart`, `reducedBracket`, the shift/angle-reduction identity |
| `ShiftSymm.lean` | 51 | the symmetry hypothesis of (D) for a gradient shift `B_l = c_l + ∂_{θ_l} S` |
| `LocalInverse.lean` | 128 | inverse-function theorem for `polar`; regularity of `G` from regularity of `G ∘ Rinv ∘ polar` |
| `Composite.lean` | 124 | (E): `tubeChart`, composite rate formula (three forms) |
| `Observable.lean` | 133 | observables `x ↦ f (tubeChart V B x)`: chart identity from periodicity, `C^k`, rate formula |

Total 1048 lines. Import order: `Bracket` ← {`Rotation`, `Polar`, `Shift`} ← `ShiftSymm`, `LocalInverse` ←
`Composite` ← `Observable`. N5 should import `KAM.EffectiveStability.Tube.Chart.Observable` (it re-exports
everything). Only `KAM.EffectiveStability.Transfer` (core) and narrow Mathlib modules are imported; no application
module.

## Conventions (pinned by computation)

- Phase space `(Fin n → ℝ) × (Fin n → ℝ)`, `x = (q, p)`, `X_H x = (∂H/∂p, -∂H/∂q)` (frozen
  `KAM.hamiltonianVectorField`).
- `polar (I, θ) = (fun j => -√(2 * I j) * sin (θ j), fun j => √(2 * I j) * cos (θ j))`: **actions `I = y.1` are
  positions, angles `θ = y.2` are momenta.** Jacobian determinant per mode `+1`.
- **Sign** (`fderiv_apply_hamiltonianVectorField_eq_bracketSum`, no hypotheses):
  `fderiv ℝ G y (X_H y) = bracketSum G H y := Σ_j (∂_{y.1 j} G · ∂_{y.2 j} H - ∂_{y.2 j} G · ∂_{y.1 j} H)`,
  i.e. in polar variables `Σ_j (∂_{I_j} G ∂_{θ_j} H - ∂_{θ_j} G ∂_{I_j} H)`. Sanity check: for
  `H ∘ polar = Σ ω_j I_j` the flow is `θ̇ = -ω`, matching `q̇ = ω p`, `ṗ = -ω q` from `X_H`.
- `rotMap A x = (A *ᵥ x.1, A *ᵥ x.2)`; `R = rotMap Vᵀ`, `Rinv = rotMap V`, hypothesis `Vᵀ * V = 1`.
- `phiOf θ = ![θ 0 - θ 2, θ 1 - θ 2]`, `shiftChart B (I, θ) = (I - B (phiOf θ), phiOf θ)`,
  `tubeChart V B x = shiftChart B (polarInv (rotMap Vᵀ x))`,
  `polarInv x = (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2, fun j => Complex.arg ⟨x.2 j, -x.1 j⟩)`.
- `∂_{θ_i}` on functions of `φ` is `fderiv ℝ · φ (phiOf (Pi.single i 1))`
  (`= ∂_{φ₀}, ∂_{φ₁}, -∂_{φ₀} - ∂_{φ₁}` for `i = 0, 1, 2`).
- `reducedBracket f h p = Σ_{a : Fin 2} ((∂_{u_a} f - ∂_{u_2} f) · ∂_{φ_a} h - ∂_{φ_a} f · (∂_{u_a} h - ∂_{u_2} h))`
  at `p = (u, φ)`, with `∂_{u_l} = fderiv · p (Pi.single l 1, 0)` and `∂_{φ_a} = fderiv · p (0, Pi.single a 1)`
  (`u_a` is `Pi.single a.castSucc 1`).

## Main theorems (exact statements; binders `{n : ℕ}` implicit, `Phase n` abbreviates `(Fin n → ℝ) × (Fin n → ℝ)` here only)

### Bracket.lean
```lean
theorem fderiv_apply_hamiltonianVectorField_eq_bracketSum (G H : Phase n → ℝ) (y : Phase n) :
    fderiv ℝ G y (hamiltonianVectorField H y) = bracketSum G H y

theorem fderiv_apply_hamiltonianVectorField_comp_symplectic {Ψ : Phase n → Phase n} {G H : Phase n → ℝ} {y}
    (hΨ : DifferentiableAt ℝ Ψ y)
    (hsymp : ∀ u v, symplecticForm (fderiv ℝ Ψ y u) (fderiv ℝ Ψ y v) = symplecticForm u v)
    (hG : DifferentiableAt ℝ G (Ψ y)) (hH : DifferentiableAt ℝ H (Ψ y)) :
    fderiv ℝ G (Ψ y) (hamiltonianVectorField H (Ψ y)) =
      fderiv ℝ (G ∘ Ψ) y (hamiltonianVectorField (H ∘ Ψ) y)
```
(Reuses `fderiv_chart_apply_hamiltonianVectorField` of `KAM/EffectiveStability/Transfer.lean`.)

### (A) Rotation.lean
```lean
theorem rotMap_rotMap_transpose (hV : Vᵀ * V = 1) (x) : rotMap V (rotMap Vᵀ x) = x      -- Rinv ∘ R = id
theorem rotMap_transpose_rotMap (hV : Vᵀ * V = 1) (y) : rotMap Vᵀ (rotMap V y) = y      -- R ∘ Rinv = id
theorem symplecticForm_rotMap (hA : Aᵀ * A = 1) (u v) :
    symplecticForm (rotMap A u) (rotMap A v) = symplecticForm u v
theorem fderiv_comp_rotMap_apply_hamiltonianVectorField (hV : Vᵀ * V = 1)
    (hG : DifferentiableAt ℝ G (rotMap Vᵀ x)) (hH : DifferentiableAt ℝ H x) :
    fderiv ℝ (G ∘ rotMap Vᵀ) x (hamiltonianVectorField H x) =
      fderiv ℝ G (rotMap Vᵀ x) (hamiltonianVectorField (H ∘ rotMap V) (rotMap Vᵀ x))
theorem contDiffAt_comp_rotMap (A) (hH : ContDiffAt ℝ k H (rotMap A y)) : ContDiffAt ℝ k (H ∘ rotMap A) y
theorem contDiffOn_comp_rotMap (A) (hH : ContDiffOn ℝ k H S) : ContDiffOn ℝ k (H ∘ rotMap A) (rotMap A ⁻¹' S)
theorem differentiableAt_comp_rotMap (A) (hH : DifferentiableAt ℝ H (rotMap A y)) :
    DifferentiableAt ℝ (H ∘ rotMap A) y
theorem rotMap_preimage_eq_image (hV : Vᵀ * V = 1) (S) : rotMap V ⁻¹' S = rotMap Vᵀ '' S
```

### (B), (C) Polar.lean
```lean
theorem isOpen_actionPos : IsOpen (actionPos n)              -- actionPos n = {y | ∀ j, 0 < y.1 j}
theorem contDiffOn_polar : ContDiffOn ℝ ∞ (polar (n := n)) (actionPos n)
theorem fderiv_polar_apply (hy : y ∈ actionPos n) (v) : fderiv ℝ polar y v = polarD y v
theorem symplecticForm_fderiv_polar (hy : y ∈ actionPos n) (u v) :
    symplecticForm (fderiv ℝ polar y u) (fderiv ℝ polar y v) = symplecticForm u v
theorem fderiv_apply_hamiltonianVectorField_polar (hy : y ∈ actionPos n)
    (hG : DifferentiableAt ℝ G (polar y)) (hH : DifferentiableAt ℝ H (polar y)) :
    fderiv ℝ G (polar y) (hamiltonianVectorField H (polar y)) =
      fderiv ℝ (G ∘ polar) y (hamiltonianVectorField (H ∘ polar) y)
theorem fderiv_apply_hamiltonianVectorField_polar_eq_bracketSum (hy) (hG) (hH) :
    fderiv ℝ G (polar y) (hamiltonianVectorField H (polar y)) =
      ∑ j, (fderiv ℝ (G ∘ polar) y (Pi.single j 1, 0) * fderiv ℝ (H ∘ polar) y (0, Pi.single j 1) -
        fderiv ℝ (G ∘ polar) y (0, Pi.single j 1) * fderiv ℝ (H ∘ polar) y (Pi.single j 1, 0))
theorem polar_sq_add_sq (hj : 0 ≤ y.1 j) : (polar y).1 j ^ 2 + (polar y).2 j ^ 2 = 2 * y.1 j
theorem polarInv_mem_actionPos (hx : ∀ j, 0 < x.1 j ^ 2 + x.2 j ^ 2) : polarInv x ∈ actionPos n
theorem polar_polarInv (x) : polar (polarInv x) = x                      -- no hypothesis needed
theorem exists_polar_eq (hx : ∀ j, 0 < x.1 j ^ 2 + x.2 j ^ 2) : ∃ y ∈ actionPos n, polar y = x
theorem polarInv_polar (hy : y ∈ actionPos n) :
    (polarInv (polar y)).1 = y.1 ∧ ∀ j, ∃ k : ℤ, (polarInv (polar y)).2 j = y.2 j + 2 * π * k
```

### (D) Shift.lean, ShiftSymm.lean (n = 3)
```lean
theorem bracketSum_comp_shiftChart {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    {y : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hh : DifferentiableAt ℝ h (shiftChart B y))
    (hB : DifferentiableAt ℝ B (phiOf y.2))
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (phiOf y.2) (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (phiOf y.2) (phiOf (Pi.single l 1)) i) :
    bracketSum (f ∘ shiftChart B) (h ∘ shiftChart B) y = reducedBracket f h (shiftChart B y)

theorem shift_symm_of_gradient {B} {S : (Fin 2 → ℝ) → ℝ} {c : Fin 3 → ℝ} {φ} (hS : ContDiffAt ℝ 2 S φ)
    (hB : B =ᶠ[𝓝 φ] fun φ' l => c l + fderiv ℝ S φ' (phiOf (Pi.single l 1))) (i l : Fin 3) :
    fderiv ℝ B φ (phiOf (Pi.single i 1)) l = fderiv ℝ B φ (phiOf (Pi.single l 1)) i
```

### Local inverse (LocalInverse.lean)
```lean
theorem exists_polar_localInverse (hy : y ∈ actionPos n) (hk : k ≠ 0) :
    ∃ ψ, ContDiffAt ℝ k ψ (polar y) ∧ ψ (polar y) = y ∧
      ∀ᶠ z in 𝓝 (polar y), ψ z ∈ actionPos n ∧ polar (ψ z) = z
theorem contDiffAt_of_comp_rotMap_polar (hV : Vᵀ * V = 1) (hk : k ≠ 0)
    (hGg : ∀ y' ∈ actionPos n, G (rotMap V (polar y')) = g y')
    (hy : y ∈ actionPos n) (hxy : polar y = rotMap Vᵀ x) (hg : ContDiffAt ℝ k g y) : ContDiffAt ℝ k G x
theorem differentiableAt_of_comp_rotMap_polar (hV) (hGg) (hy) (hxy) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ G x
```
(and the `polar`-only versions `contDiffAt_of_comp_polar`, `differentiableAt_of_comp_polar`).

### (E) Composite.lean
```lean
theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket {V : Matrix (Fin 3) (Fin 3) ℝ}
    (hV : Vᵀ * V = 1) {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {G H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hGf : ∀ y ∈ actionPos 3, G (rotMap V (polar y)) = f (shiftChart B y))
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    {x y : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hy : y ∈ actionPos 3) (hxy : polar y = rotMap Vᵀ x)
    (hf : DifferentiableAt ℝ f (shiftChart B y)) (hh : DifferentiableAt ℝ h (shiftChart B y))
    (hB : DifferentiableAt ℝ B (phiOf y.2))
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (phiOf y.2) (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (phiOf y.2) (phiOf (Pi.single l 1)) i) :
    fderiv ℝ G x (hamiltonianVectorField H x) = reducedBracket f h (shiftChart B y)

theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket_tubeChart (hV) (hGf) (hHh)
    {x} (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : DifferentiableAt ℝ f (tubeChart V B x)) (hh : DifferentiableAt ℝ h (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2)
    (hsym : ∀ i l : Fin 3, fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single i 1)) l =
      fderiv ℝ B (tubeChart V B x).2 (phiOf (Pi.single l 1)) i) :
    fderiv ℝ G x (hamiltonianVectorField H x) = reducedBracket f h (tubeChart V B x)

theorem fderiv_apply_hamiltonianVectorField_eq_reducedBracket_of_gradient  -- hsym replaced by
    ... (hS : ContDiffAt ℝ 2 S (phiOf y.2))
    (hBS : B =ᶠ[𝓝 (phiOf y.2)] fun φ' l => c l + fderiv ℝ S φ' (phiOf (Pi.single l 1))) : ...
```

### Observable.lean (the form N5 can feed with literal `f`, `h̃`, `B`)
With `hBper : ∀ φ (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ` and
`hfper : ∀ u φ (m : Fin 2 → ℤ), f (u, φ + fun a => 2 * π * m a) = f (u, φ)`:
```lean
theorem comp_tubeChart_rotMap_polar (hV) (hBper) (hfper) (hy : y ∈ actionPos 3) :
    f (tubeChart V B (rotMap V (polar y))) = f (shiftChart B y)
theorem contDiffAt_comp_tubeChart (hV) (hk : k ≠ 0) (hBper) (hfper)
    (hx : ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2)
    (hf : ContDiffAt ℝ k f (tubeChart V B x)) (hB : ContDiffAt ℝ k B (tubeChart V B x).2) :
    ContDiffAt ℝ k (fun x => f (tubeChart V B x)) x
theorem differentiableAt_comp_tubeChart  -- same with DifferentiableAt
theorem fderiv_comp_tubeChart_apply_hamiltonianVectorField (hV) (hBper) (hfper)
    (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y)) (hx) (hf) (hh) (hB) (hsym) :
    fderiv ℝ (fun x => f (tubeChart V B x)) x (hamiltonianVectorField H x) =
      reducedBracket f h (tubeChart V B x)
```

## Approach

- One generic lemma does all transport: a map with symplectic derivative intertwines `X_H` (existing
  `fderiv_chart_apply_hamiltonianVectorField`), so by the chain rule `DG(Ψy)·X_H(Ψy) = D(G∘Ψ)(y)·X_{H∘Ψ}(y)`.
- (A): `rotMap V` is linear and preserves dot products (`Vᵀ V = 1`, `V Vᵀ = 1` by `mul_eq_one_comm`), hence `ω`;
  apply the generic lemma to `Ψ = Rinv` at `R x` with `G ∘ R`.
- (B): `fderiv polar y v` is computed in closed form (`polarD`) by differentiating along the line `t ↦ y + t v`
  and uniqueness of derivatives; symplecticity is `field_simp` plus `sin² + cos² = 1` per mode.
- (C): `polarInv` via `Complex.arg ⟨p, -q⟩`; `‖z‖ cos (arg z) = re z`, `‖z‖ sin (arg z) = im z`
  (holds for all `x`). `polarInv_polar` via `Complex.arg_mul_cos_add_sin_mul_I_sub`.
- (D): explicit derivative `shiftD` of `shiftChart`; a linear functional on `(Fin 3 → ℝ) × (Fin 2 → ℝ)` is
  expanded in coordinates; after expanding `Fin 3`/`Fin 2` sums the residual is exactly
  `Σ (β_{lj} - β_{jl}) · (quadratic in ∂_u f, ∂_u h)`, killed by `linear_combination` with three instances of the
  symmetry hypothesis.
- (E): rotate, polar-transport, replace the germs of `G ∘ Rinv ∘ polar`, `H ∘ Rinv ∘ polar` by those of
  `f ∘ shiftChart B`, `h ∘ shiftChart B` (equal on the open `actionPos`), then (D). Differentiability of `G`, `H`
  at `x` is derived, not assumed: the inverse function theorem gives a `C^k` local inverse of `polar` at `y`
  (derivative bijective because symplectic), so `G = g ∘ ψ ∘ R` near `x`.
- Observables: `polarInv (polar y)` equals `y` up to `2πk` in the angles; `phiOf` maps this to a `2πm` shift of
  `φ`, removed by periodicity of `B` and `f`. So `x ↦ f (tubeChart V B x)` is smooth across the `arg` cut.

## Checks run (outputs)

Targeted builds (each via `.drafts/g2/g2lake build`, final state):
```
✔ Built KAM.EffectiveStability.Tube.Chart.Bracket       Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.Rotation      Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.Polar         Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.Shift         Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.ShiftSymm     Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.LocalInverse  Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.Composite     Build completed successfully
✔ Built KAM.EffectiveStability.Tube.Chart.Observable    Build completed successfully
```
No warnings in the final builds.

`#print axioms` (scratch `.drafts/g2/scratch/n2/Axioms.lean`, output `axioms.out`): all 26 listed theorems
(every theorem named above) report `[propext, Classical.choice, Quot.sound]`; none other.

`wc -l`: Bracket 89, Rotation 160, Polar 216, Shift 147, ShiftSymm 51, LocalInverse 128, Composite 124,
Observable 133 (total 1048); max 216 ≤ 1500.

Lint: `.drafts/g2/lint_noabi.sh` (per the WORKER-RULES 'Lint' section; **the `abi_hashes` step was skipped**).
An earlier full `scripts/lint_sources.sh` run was stopped by exact PID at kam-g2's request; it had flagged 9 lines
over 100 characters in my files, which were fixed and rebuilt. Final `lint_noabi.sh` output: exit 1, with **no
finding under `KAM/EffectiveStability/Tube/Chart/`**. The failures all come from outside my package: lines over
100 characters in other packages' files (`SJSU/Ecc/*`, …) and `KAM.lean is out of date; run
scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)`, because the new modules aren't in the
generated roots yet (orchestrator-owned). Other steps: `check_lean_modules: PASS (18362 Lean files)`, unit tests
`Ran 29 tests … OK`, `Ran 8 tests … OK`, `FROZEN-ANCHOR GUARD OK`. Forbidden-pattern checks (sorry, axiom,
set_option, EuclideanSpace, …): no hits in my files.

## Design signals

None. Every module elaborates in a few seconds at default heartbeats.

## Uncertainties

- `reducedBracket` uses `Pi.single a.castSucc 1` for `u_a` (`a : Fin 2 ↦ 0, 1 : Fin 3`); N5's evaluator should
  match it (`Fin.castSucc 0 = 0`, `Fin.castSucc 1 = 1`, by `rfl`/`simp`).
- The symmetry hypothesis is stated with `phiOf (Pi.single i 1)` as the direction (`= ![1,0]`, `![0,1]`,
  `![-1,-1]` for `i = 0, 1, 2`); `shift_symm_of_gradient` discharges it when `B` is (near `φ`) literally
  `c + ∂_θ S` with `fderiv` of `S`. If N5's `B` uses a separately written literal derivative of `S`, N5 must
  prove that it equals `fderiv ℝ S` (or prove the symmetry directly).
- Periodicity in `Observable.lean` is stated per integer vector (`φ + fun a => 2π m a`); a literal trigonometric
  polynomial satisfies it, but N5 must prove it for its literal `f`, `h̃`, `B`.

## Deviations from the brief

- (E) has **fewer** hypotheses than the brief allowed: differentiability of `G`, `H` at `x` is derived (via
  `LocalInverse.lean`) rather than assumed.
- Additions not in the brief: `LocalInverse.lean` (regularity through the polar chart, which also gives N5 the
  consumer's `DifferentiableOn (F j) W` for observables defined through `tubeChart`), `Observable.lean`
  (chart identity from periodicity, so `G := fun x => f (tubeChart V B x)` discharges `hGf`), `ShiftSymm.lean`
  (symmetry hypothesis for gradient shifts), `polarInv_polar`, `polar_sq_add_sq`.
- `polar_polarInv` holds for all `x` (no hypothesis); positivity is needed only for `polarInv x ∈ actionPos`.
- No facade `KAM/EffectiveStability/Tube/Chart.lean` (outside my directory); `Observable` is the umbrella import.
- The rotation is not specialized to a Cayley-rational `V`; any real `V` with `Vᵀ * V = 1`.

## Suspected errata

None in pinned sources. Brief check: (B)'s "equivalently" formula
`Σ_j (∂_{I_j}(G∘polar) ∂_{θ_j}(H∘polar) − ∂_{θ_j}(G∘polar) ∂_{I_j}(H∘polar))` is confirmed with the stated
sign (I as positions); (D)'s reduced formula is confirmed with `D_a = ∂_{u_a} − ∂_{u_2}`.
