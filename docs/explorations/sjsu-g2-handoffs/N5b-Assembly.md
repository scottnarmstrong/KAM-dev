# N5b-Assembly handoff (T2-CONF, worker g2-n5b): phase A, the generic assembly

6 November 2026, branch `inp-sjsu-g2`, shared worktree; nothing committed by me. Brief
`.drafts/g2/BRIEF-N5b-Assembly.md`.

**Status.**
- **Phase A is complete:** the generic tube-checker assembly in `KAM/EffectiveStability/Tube/Check/`. Every literal
  check is an abstract numeric hypothesis on functions of `(u, φ)` or on the ball `Q`.
- **Phase B is not started:** the SJSU instance in `KAM/EffectiveStability/SJSU/Confinement/`. It needs:
  - N5a's `h̃` tube model;
  - the literal observables `f_j` (F-v1);
  - the η / face / partial-bound checkers;
  - N5c-Q's ball discharges.
- No `sorry`, `axiom` or `set_option`; every file ≤ 1500 lines. The axioms are only `propext`, `Classical.choice`
  and `Quot.sound`.

The files `Confine.lean` and `Solution.lean` were drafts by the previous N5b session. I kept and checked them, and
generalized nothing in them.

## The interface for the instance (exact hypothesis form; N5c-Q should match this)

The main theorem, `KAM.EffectiveStability.Tube.tubeChart_confinement` (`Tube/Check/TubeChart.lean`):

```lean
theorem tubeChart_confinement {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {bmin bmax β ct ε γ η μ A a : Fin 3 → ℝ} {Fu : Fin 3 → Fin 3 → ℝ}
    {Fφ : Fin 3 → Fin 2 → ℝ} {δ ρ T Nv r : ℝ} {z : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    {Pγ : Fin 3 → ℝ → Prop}
    -- the shift `B`
    (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B) (hρ : ∀ j, ρ < bmin j)
    (hBmin : ∀ φ j, bmin j ≤ B φ j) (hBmax : ∀ φ j, B φ j ≤ bmax j)
    (hβ : ∀ φ (b : Fin 2) (l : Fin 3), |fderiv ℝ B φ (Pi.single b 1) l| ≤ β l)
    (hsym : ∀ φ (i l : Fin 3), fderiv ℝ B φ (phiOf (Pi.single i 1)) l =
      fderiv ℝ B φ (phiOf (Pi.single l 1)) i)
    -- the Hamiltonian
    (hH : ContDiff ℝ 2 H) (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ ρ) → DifferentiableAt ℝ h (u, φ))
    -- the observables
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    -- rates, faces, centre
    (hη : ∀ j u φ, (∀ l, |u l| ≤ ρ) → |reducedBracket (f j) h (u, φ)| ≤ η j)
    (hT : 0 ≤ T) (hTη : ∀ j, T * η j < δ / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ ρ) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hc : ∀ j, |f j (tubeChart V B z) - ct j| ≤ γ j) (hερ : ∀ j, δ + ε j + γ j < ρ)
    -- the ball `Q = closedBall z r`
    (hN : ∀ j, ∑ k, |V k j| ≤ Nv)
    (hAb : ∀ y ∈ Metric.closedBall z r, ∀ j, |(rotMap Vᵀ y).1 j| + |(rotMap Vᵀ y).2 j| ≤ A j)
    (ha : ∀ j, 0 < a j) (hab : ∀ y ∈ Metric.closedBall z r, ∀ j, a j ≤ modeSq V y j)
    (hμ : ∀ j, |tubeU V B z j| ≤ μ j)
    (hμρ : ∀ j, μ j + chartLip Nv A a β (Pi.single j 1) 0 * r < ρ)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ ρ) → ∀ l, |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ Fu j l)
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ ρ) → ∀ b, |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ Fφ j b)
    (hLF : ∀ j, chartLip Nv A a β (Fu j) (Fφ j) * r ≤ δ / 2)
    -- the planet actions on the tube
    (hG : ∀ (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ), (∀ k, |I k - B φ k| ≤ ρ) → ∀ j,
      Pγ j (chartGamma V I φ j))
    {z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hz₀ : z₀ ∈ Metric.closedBall z r) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ x : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), x 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, HasDerivAt x (KAM.hamiltonianVectorField H (x t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = x t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, Pγ j (KAM.Planetary.oscillatorAction (x t).2 (x t).1 j)
```

Definitions it uses (all in namespace `KAM.EffectiveStability.Tube`):
- `ShiftPeriodic B := ∀ φ (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ` (abbrev).
- `ObsPeriodic f := ∀ u φ (m : Fin 2 → ℤ), f (u, φ + fun a => 2 * π * m a) = f (u, φ)` (abbrev).
- `modeSq V x j := (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2`.
- `modesPos V := {x | ∀ j, 0 < modeSq V x j}`; this is `W`.
- `tubeU V B x := (tubeChart V B x).1`.
- `tubeK V B ρ := {x | x ∈ modesPos V ∧ ∀ j, |tubeU V B x j| ≤ ρ}`; this is `K`.
- `thetaW A a b := A b.castSucc / a b.castSucc + A 2 / a 2`.
- `chartLip Nv A a β Fu Fφ := Nv * (Σ_l Fu l * (A l + β l * (thetaW A a 0 + thetaW A a 1)) + Σ_b Fφ b * thetaW A a b)`.
- `chartGamma V I φ j := (Σ_k V j k * √(I k) * cos (![φ 0, φ 1, 0] k))^2 + (Σ_k … sin …)^2`.
  - It has the same body as N6's `eccGamma`, with a real matrix in place of `ℚ` entries.
  - So `chartGamma (Matrix.of fun j k => (V' j k : ℝ)) I φ j = eccGamma V' I φ j` holds **by `rfl`** (checked:
    `.drafts/g2/scratch/n5b/Rfl.lean`).
  - N6's `sjsu_tube_ecc` then gives `hG`, with `Pγ j g := lo j ≤ √(1 - (1 - g/Λ j)²) ∧ √(…) ≤ hi j`.
- `reducedBracket` (N2), `phiOf`, `rotMap`, `polar`, `shiftChart`, `tubeChart`, `actionPos` (N2).

**Ball in coordinates.** `mem_closedBall_iff_coords (hr : 0 ≤ r) : z₀ ∈ Metric.closedBall z r ↔ ∀ j, |z₀.2 j -
z.2 j| ≤ r ∧ |z₀.1 j - z.1 j| ≤ r` is exactly the `hz₀` of `sjsu_secular_confinement` (`ξ = x.2` first).

**Helper for `hAb`, `hab`.** `modeBounds_of_mem_closedBall (hN) (hy : y ∈ closedBall z r) j` gives two bounds:
- `|q_j| + |p_j| ≤ |q*_j| + |p*_j| + 2 (Nv r)`;
- `q*_j² + p*_j² − 2 (|q*_j| + |p*_j|) (Nv r) ≤ modeSq V y j`.

Here `(q, p) = Vᵀy` and `(q*, p*) = Vᵀz`.

**How the Q hypotheses are used.**
- `|u_j(y) − u_j(z)| ≤ chartLip … (Pi.single j 1) 0 · r` (mean value), so `|u_j| < ρ` on `Q`.
- Then `|F_j(y) − F_j(z)| ≤ chartLip … (Fu j) (Fφ j) · r ≤ δ/2`, with `Fu`, `Fφ` bounds on the `u`-box `ρ`.
- `c_j := F_j(z)` exactly. A literal `ct j` enters only through `hc` and `hface`, so `γ_j := ε_j + μ_j` (N5c's
  proposal (6)) is a valid instantiation, given `μ_j ≤ ρ`.

## Files (`KAM/EffectiveStability/Tube/Check/`, namespace `KAM.EffectiveStability.Tube`, core)

| file | lines | content |
|---|---:|---|
| `Solution.lean` | 70 | `hamiltonian_solution_of_maximal`: `IsMaximalSolution` in `W` → existence on `(-T₁, T₁)` and uniqueness among all solutions (generic part of the Hénon–Heiles conversion) |
| `Confine.lean` | 185 | `tubeDomain`, `isOpen_tubeDomain`, `le_of_mem_closure_tubeDomain`, `exists_ge_of_mem_frontier` (frontier separation from a face bound), `tube_confinement`, `tube_confinement_observable` |
| `Domain.lean` | 161 | `ShiftPeriodic`, `ObsPeriodic`, `modeSq`, `modesPos`, `tubeU`, `tubeK`; `isOpen_modesPos`, `differentiableAt_tubeU`, `continuousOn_tubeU`, `isCompact_tubeK` |
| `Gamma.lean` | 97 | `chartGamma`, `sum_cos_sin_sub_sq`, `oscillatorAction_eq_chartGamma`, `oscillatorAction_prop_of_tube` |
| `Deriv.lean` | 140 | `polarInvD`, `polarD_polarInvD`, `fderiv_polar_polarInvD`, `fderiv_localInverse_eq`, `fderiv_comp_tubeChart_apply` |
| `Lip.lean` | 250 | `thetaW`, `chartLip`, `norm_rotMap_transpose_le`, `abs_polarInvD_fst/snd_le`, `abs_fderiv_comp_tubeChart_le`, `abs_sub_le_of_closedBall`, `modeBounds_of_mem_closedBall` |
| `TubeChart.lean` | 205 | `mem_closedBall_iff_coords`, `chartLip_nonneg`, **`tubeChart_confinement`** |
| `Bracket.lean` | 96 | `sliceBracket`, `reducedBracket_eq_sliceBracket`, `abs_sliceBracket_sub_le` (for the η checker) |

Total 1,204 lines. Imports:
- Core only: N2's `Chart.Observable` / `Chart.Shift`, N3's `Trig.TubeClose` (from `Bracket`),
  `KAM.Application.Confinement.ApproxIntegral`, `KAM.ODE.*`, and the frozen `Planetary.Defs.OscillatorAction`.
- No application module. `TubeChart` imports everything except `Bracket`.

## Other main statements

```lean
theorem tube_confinement_observable (hH : ContDiff ℝ 2 H) (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWK : ∀ x ∈ W, (∀ j, |u j x| ≤ ρ) → x ∈ K) (hF : ∀ j, DifferentiableOn ℝ (F j) W)
    (hu : ∀ j, ContinuousOn (u j) W)
    (hη : ∀ j, ∀ x ∈ K, |fderiv ℝ (F j) x (KAM.hamiltonianVectorField H x)| ≤ η j)
    (hface : ∀ j, ∀ x ∈ K, |F j x - c j - u j x| ≤ ε j) (hερ : ∀ j, δ + ε j < ρ)
    (hT : 0 ≤ T) (hTη : ∀ j, T * η j < δ / 2)
    (hQ : ∀ x ∈ Q, x ∈ W ∧ (∀ j, |F j x - c j| ≤ δ / 2) ∧ ∀ j, |u j x| < ρ)
    {P} (hP : ∀ x ∈ K, P x) (hz₀ : z₀ ∈ Q) :
    ∃ T₁, T < T₁ ∧ ∃ z, z 0 = z₀ ∧ (existence on Ioo) ∧ (uniqueness) ∧ ∀ t, |t| ≤ T → P (z t)
-- (`tube_confinement`: same hypotheses; conclusion z t ∈ tubeDomain, z t ∈ K, drift ≤ η_j |t|)

theorem isCompact_tubeK (hV : Vᵀ * V = 1) (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B)
    (hρ : ∀ j, ρ < bmin j) (hmin : ∀ φ j, bmin j ≤ B φ j) (hmax : ∀ φ j, B φ j ≤ bmax j) :
    IsCompact (tubeK V B ρ)

theorem oscillatorAction_eq_chartGamma (hV : Vᵀ * V = 1) (B) (x) (j) :
    KAM.Planetary.oscillatorAction x.2 x.1 j =
      chartGamma V (tubeU V B x + B (tubeChart V B x).2) (tubeChart V B x).2 j

theorem fderiv_comp_tubeChart_apply (hV) (hBper : ShiftPeriodic B) (hfper : ObsPeriodic f)
    (hx : x ∈ modesPos V) (hf : DifferentiableAt ℝ f (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2) (v) :
    fderiv ℝ (fun x => f (tubeChart V B x)) x v =
      fderiv ℝ f (tubeChart V B x)
        (shiftD (fderiv ℝ B (tubeChart V B x).2) (polarInvD (rotMap Vᵀ x) (rotMap Vᵀ v)))

theorem abs_fderiv_comp_tubeChart_le (hV) (hBper) (hfper) (hx : x ∈ modesPos V) (hf) (hB)
    (hN : ∀ j, ∑ k, |V k j| ≤ Nv) (hA : ∀ j, |(rotMap Vᵀ x).1 j| + |(rotMap Vᵀ x).2 j| ≤ A j)
    (ha : ∀ j, 0 < a j) (haw : ∀ j, a j ≤ modeSq V x j)
    (hβ : ∀ b l, |fderiv ℝ B (tubeChart V B x).2 (Pi.single b 1) l| ≤ β l)
    (hFu : ∀ l, |fderiv ℝ f (tubeChart V B x) (Pi.single l 1, 0)| ≤ Fu l)
    (hFφ : ∀ b, |fderiv ℝ f (tubeChart V B x) (0, Pi.single b 1)| ≤ Fφ b) (v) :
    |fderiv ℝ (fun x => f (tubeChart V B x)) x v| ≤ chartLip Nv A a β Fu Fφ * ‖v‖

theorem reducedBracket_eq_sliceBracket (hf : DifferentiableAt ℝ f (u, φ)) (hh : DifferentiableAt ℝ h (u, φ)) :
    reducedBracket f h (u, φ) = sliceBracket (fun v ψ => f (v, ψ)) (fun v ψ => h (v, ψ)) u φ
theorem abs_sliceBracket_sub_le (hc : TubeClose G Ĝ r e₀ e₁ e₂) (hu : InBox r u) (φ) :
    |sliceBracket F G u φ - sliceBracket F Ĝ u φ| ≤
      ∑ a : Fin 2, (|upd F u φ a.castSucc - upd F u φ 2| * e₁ + |pderiv (F u) φ a| * (2 * e₂))
```

## Approach

- **Assembly.** `tubeChart_confinement` instantiates `tube_confinement_observable` with:
  - `W = modesPos V`, `K = tubeK V B ρ`, `Q = closedBall z r`;
  - `F_j = f_j ∘ tubeChart V B`, `u_j = tubeU`, `c_j = F_j(z)`;
  - face error `ε_j + γ_j`, and `P = Pγ` of `Γ`.

  The abstract theorem applies `hamiltonian_approxIntegrals_confinement` with `a = c − δ/2`, `b = c + δ/2` and
  `D = tubeDomain`; then `hamiltonian_solution_of_maximal`.
- **Frontier.**
  - `D` is open, and `closure D ⊆ K` because `K` is closed.
  - A frontier point is in `W`. If all `|F_j − c_j| < δ`, some `|u_j| = ρ` (else the point would be in `D`).
  - The face bound then gives `|F_j − c_j| ≥ ρ − ε_j > δ`, a contradiction. So some `|F_j − c_j| ≥ δ > δ/2 + Tη_j`.
- **Compactness.**
  - `u_j = modeSq/2 − B_j(φ)`, so on `K` every `modeSq_j ∈ [2(bmin_j − ρ), 2(bmax_j + ρ)]`.
  - `K = S ∩ u⁻¹(box)`, with `S` closed inside `W` and `u` continuous on `S`; the continuity comes from N2's
    periodic-observable regularity.
  - `K ⊆ rotMap V '' closedBall 0 M`.
- **Γ.** `x = rotMap V (polar (polarInv (Vᵀx)))`, then a direct expansion. The common phase `θ₂` drops out by
  `sin² + cos² = 1`.
- **Derivative on Q** (SR-7 chain).
  - Near `x`, `F = (f ∘ shiftChart B) ∘ ψ ∘ Vᵀ`, with `ψ` N2's local inverse of `polar` and periodicity across
    the `arg` cut.
  - `Dψ = polarInvD`, because `Dpolar ∘ Dψ = id` and `polarD (polarInvD dw) = dw` (algebra), and `Dpolar` is
    injective.
  - The bounds `|dI_j| ≤ A_j ‖dw‖` and `|dθ_j| ≤ (A_j / a_j) ‖dw‖` hold, and `‖Vᵀv‖ ≤ N_V ‖v‖`.
  - The mean value inequality applies on the convex ball.

## Checks run

- Targeted builds through `.drafts/g2/g2lake build`, final state:
  - `KAM.EffectiveStability.Tube.Check.TubeChart`: `Build completed successfully (9092 jobs)`. This builds
    `Solution`, `Confine`, `Domain`, `Gamma`, `Deriv` and `Lip` as dependencies.
  - `KAM.EffectiveStability.Tube.Check.Bracket`: `Build completed successfully (2764 jobs)`.
  - No warnings in my files. The only warnings are from other modules: `KAM/ODE/Exit.lean`'s unused section
    variable, and a deprecated import in N3's `Algebra/Bounds.lean`.
- `#print axioms` (`.drafts/g2/scratch/n5b/Axioms.lean`, output in `axioms.out`), via `g2lake env lean`:
  `[propext, Classical.choice, Quot.sound]` for each of the following:
  - `hamiltonian_solution_of_maximal`, `isOpen_tubeDomain`, `exists_ge_of_mem_frontier`, `tube_confinement`,
    `tube_confinement_observable`;
  - `isOpen_modesPos`, `continuousOn_tubeU`, `isCompact_tubeK`, `oscillatorAction_eq_chartGamma`,
    `oscillatorAction_prop_of_tube`;
  - `polarD_polarInvD`, `fderiv_localInverse_eq`, `fderiv_comp_tubeChart_apply`, `norm_rotMap_transpose_le`,
    `abs_fderiv_comp_tubeChart_le`, `abs_sub_le_of_closedBall`, `modeBounds_of_mem_closedBall`;
  - `mem_closedBall_iff_coords`, `tubeChart_confinement`, `reducedBracket_eq_sliceBracket`,
    `abs_sliceBracket_sub_le`.
- `wc -l`: see the table; max 250.
- Lines over 100 characters (as the lint counts them): none.
- Forbidden patterns (`sorry`, `axiom`, `set_option`, `admit`, `EuclideanSpace`): no hits.
- Lint `.drafts/g2/lint_noabi.sh`: see "Lint" below. **The `abi_hashes` step was skipped.**

## Design signals

None at heartbeats; every module elaborates in a few seconds. One elaboration note:
- `simp` refuses goals that contain `V j k` for `V : Matrix …` ("not type-correct under the implicit transparency
  level: function expected `V j`").
- `Gamma.lean` therefore uses `rw` with `Fin.sum_univ_three` and `linear_combination` instead of `simp`.

## N3 audit 1 safeguards (kam-g2 note), for phase B

- **N3-N1.** `TP.mul` is the raw convolution without `psgn (p && q)`. The η checker must use `evalK_mul`/`TP.eval_mul`
  with the sign, and recheck `ok`/`symOk` on every product (no preservation lemmas are exported).
- **N3-N2.** The dropped-product budget for a `TubeClose` model needs three parts:
  - the value bound of `abs_dropped_le`;
  - the angle budget `Σ (A1_d B_e + A_d B1_e) r^(d+e)`;
  - the action budget `Σ (d+e) A_d B_e r^(d+e−1)`.
- **N3-N3.** `TubeClose` gives slice regularity only. My `reducedBracket_eq_sliceBracket` therefore takes **joint**
  differentiability of `f` and `h̃` at `(u, φ)` as explicit hypotheses. They come from the polynomial structure
  (`f`) and from N5a (`h̃`), never from `TubeClose`.

## Remaining (phase B, the SJSU instance in `SJSU/Confinement/`)

- **Ownership.** I own the definition of the literal observables `sjsuObs j : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ`.
  - Planned form: `sjsuObs j p = tmEval s μ (g j) p.1 p.2` (N3's `tmEval`), with `g j i = TP.eval S (x j i)` (N3
    scaled models, even parity), from F-v1 via N7's literal format.
  - `hfd` (joint differentiability) and `hfper` follow from the polynomial-in-`u` / trig-in-`φ` structure.
- **Checks still to be written:**
  - `hη`: the bracket of `sjsuObs` with N5a's `h̃` model, via `reducedBracket_eq_sliceBracket` and
    `abs_sliceBracket_sub_le`;
  - `hface`; `hFu`/`hFφ` (l1/wl1 norms; N5c's generic lemma (5));
  - `hB…` and `hsym` from N5a's `B`.
- **N5c-Q supplies** `hN`, `hAb`, `ha`, `hab`, `hβ`, `hμ`, `hμρ`, `hLF` (numerics) and `γ := ε + μ`.
- **The final step:**
  - instantiate `tubeChart_confinement` with `V = V′`, `B = sjsuB`, `H = sjsu18O2`, `δ = 10⁻⁶`, `ρ = 2·10⁻⁶`,
    `r = 10⁻⁶`, `T = 5·10⁹`;
  - take `hG` from `sjsu_tube_ecc` and `hz₀` from `mem_closedBall_iff_coords`;
  - prove `ContDiff ℝ 2 sjsu18O2` (a polynomial).

## Uncertainties

- `hhd` asks for joint differentiability of `h̃` on the whole `u`-box. If N5a's `h̃` uses `rpow` of `B + u`, this
  needs `B + u > 0` on the box, which holds since `ρ < bmin`.
- `hsym` is required at every `φ`. N2's `shift_symm_of_gradient` gives it if N5a's `B` is literally
  `c + fderiv S`.

## Deviations from the brief

- **`D` and `K`.**
  - `D = {x ∈ W : |F_j − c_j| < δ ∧ |u_j| < ρ}` and `K = {x ∈ W : |u_j| ≤ ρ}`, with `ρ` a parameter (`κδ` in the
    instance).
  - The face condition is `δ + ε_j + γ_j < ρ`, with a literal `ct` and `γ ≥ |F_j(z*) − ct_j|`.
- **`F_j` form.** `F_j = f_j ∘ tubeChart V B`, N2's chart through `polarInv`/`arg` plus periodicity, rather than an
  explicit `e_j = w_j/|w_j|` formula.
  - This is equivalent for periodic `f`, and it is differentiable on `W` by N2's `LocalInverse`.
  - The `x`-derivative is in closed form (`polarInvD`), so the unit complex numbers are not needed.
- **Eccentricity.** It is generalized to an arbitrary per-planet predicate `Pγ` of `Γ_j`, so that N6's
  `sjsu_tube_ecc` plugs in directly.
- **`Bracket.lean`** is an addition, for the η checker.

## Suspected errata

None in pinned sources.

## Lint

`.drafts/g2/lint_noabi.sh` (output `.drafts/g2/scratch/n5b/lint.out`): exit 1, with **no finding under
`KAM/EffectiveStability/Tube/Check/`**. **The `abi_hashes` step was skipped.** The failures come from outside this
package:
- lines over 100 characters in `SJSU/Model/SJSU18O2Part5.lean`, `Tube/Engine/{Lit,Spread}.lean` and
  `Tube/Poly/{Compose,Polar,Sparse}.lean`;
- `KAM.lean is out of date` (new modules are not in the generated roots; orchestrator-owned).

Everything else passed: `check_lean_modules: PASS`, unit tests `Ran 29 tests … OK` and `Ran 8 tests … OK`,
`FROZEN-ANCHOR GUARD OK`.
