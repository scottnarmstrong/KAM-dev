# N5b-Assembly handoff (T2-CONF, worker g2-n5b): phases A and B(i)–(iii)

6 November 2026, branch `inp-sjsu-g2`, shared worktree; nothing committed by me. Brief
`.drafts/g2/BRIEF-N5b-Assembly.md`.

**Status.**
- **Phase A is complete** (committed by kam-g2 as `c2a92e9d1`): the generic tube-checker assembly in
  `KAM/EffectiveStability/Tube/Check/`.
- **Phase B (i)–(iii) is complete** (16:47 UTC); see the section "Phase B" right below.
  - The exact D76 conclusion is derived from `tubeChart_confinement`. The literal checks still pending are
    hypotheses of an intermediate lemma.
  - The properties of N5a's `B` are proved, and so is `ContDiff ℝ 2 sjsu18O2`.
- **Not yet possible:** the ordinary theorem `KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof` itself.
  It waits for N5a's `h̃` (`hHh`, `hhd`) and N7's observables and checks. Once they land, it is a one-line
  application of `sjsu_secular_confinement_of_obs` (template below).
- No `sorry`, `axiom` or `set_option`; every file ≤ 1500 lines. The axioms are only `propext`, `Classical.choice`
  and `Quot.sound`.

## Phase B: the SJSU instance (`KAM/EffectiveStability/SJSU/Confinement/`, namespace `KAM.EffectiveStability.SJSU`, opt-in `KAMSJSU`)

| file | lines | content |
|---|---:|---|
| `Shift.lean` | 105 | (ii) `sjsuBmin`, `sjsuBmax`, `sjsuB_eq_eccCenter` (`rfl`), `shiftPeriodic_sjsuB`, `differentiable_sjsuB`, `sjsuB_bounds`, `sjsu_rho_lt_bmin`; (iii) `contDiff_polyRe`, `contDiff_sjsu18O2` |
| `Statement.lean` | 163 | (i) `chartGamma_sjsuV`, `sjsu_hG`, **`sjsu_secular_confinement_of_checks`**, **`sjsu_secular_confinement_of_obs`** |

There is also one new core file, `KAM/EffectiveStability/Tube/Check/Center.lean` (87 lines):
- `abs_modeK_mul_le`;
- `abs_tubeCenter_sub_le : |tubeCenter modes Ibar k φ - Ibar k| ≤ ((lipSum₁ modes k + lipSum₂ modes k : ℚ) : ℝ)`;
- `tubeCenter_bounds_of_globalOK (hg : globalOK d = true) k φ`, which gives
  `↑(d.Ibar k - (d.L₁ k + d.L₂ k)) ≤ tubeCenter d.modes d.Ibar k φ ≤ ↑(d.Ibar k + (d.L₁ k + d.L₂ k))`.

### (ii) The shift `B = sjsuB` (N5a)

```lean
def sjsuBmin (k : Fin 3) : ℚ := sjsuEccIbar k - (sjsuEccData.L₁ k + sjsuEccData.L₂ k)
def sjsuBmax (k : Fin 3) : ℚ := sjsuEccIbar k + (sjsuEccData.L₁ k + sjsuEccData.L₂ k)
theorem sjsuB_eq_eccCenter (φ : Fin 2 → ℝ) (k : Fin 3) : sjsuB φ k = sjsuEccCenter k φ := rfl
theorem shiftPeriodic_sjsuB : ShiftPeriodic sjsuB
theorem differentiable_sjsuB : Differentiable ℝ sjsuB
theorem sjsuB_bounds (φ : Fin 2 → ℝ) (k : Fin 3) :
    (sjsuBmin k : ℝ) ≤ sjsuB φ k ∧ sjsuB φ k ≤ (sjsuBmax k : ℝ)
theorem sjsu_rho_lt_bmin (k : Fin 3) : (2 / 10 ^ 6 : ℝ) < (sjsuBmin k : ℝ)
```

- **No new kernel check.**
  - `|B_k − Ī_k| ≤ Σ|m_k σ| ≤ Σ|m_k σ|(|m₁| + |m₂|) = lipSum₁ + lipSum₂ ≤ L₁ + L₂`, using N6's `globalOK`.
  - A mode with `m₁ = m₂ = 0` has `m_k = 0`; every other mode has `|m₁| + |m₂| ≥ 1`.
  - Values: `bmin ≈ (2.63·10⁻⁴, 6.19·10⁻⁴, 2.34·10⁻⁵)`, far above `ρ = 2·10⁻⁶`.
- **Symmetry:** N5a's `sjsuB_symm` (from `tubeCenter_symm`, N2's `shift_symm_of_gradient`), used as is.
- **`β`:** N5c's `sjsu_hβ` (`β = sjsuBeta ≥ max(L₁, L₂)`), used as is. I did not duplicate it.
- **`B` is N6's centre:** N5a's `sjsuB φ k` is literally `tubeCenter sjsuEccModes sjsuEccIbar k φ`, which is N6's
  `sjsuEccCenter k φ` by `rfl`. N6's `sjsu_tube_ecc` therefore applies to `sjsuB` with no conversion.

### (iii) `hH`

```lean
theorem contDiff_polyRe {n : WithTop ℕ∞} (L : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)) :
    ContDiff ℝ n (fun x => let z := …; ((L.map fun t => …).sum).re)   -- the body of `sjsu18O2`
theorem contDiff_sjsu18O2 {n : WithTop ℕ∞} : ContDiff ℝ n sjsu18O2 := contDiff_polyRe sjsu18O2Terms
```

- The proof is by induction over an arbitrary term list, so the 7,941 rows are never unfolded. The last step is a
  definitional match of the body; it elaborates in seconds.
- Ingredients: `z_j` is real-affine into `ℂ` (`Complex.ofRealCLM`); `star` is `Complex.conjCLE`; `Re` is
  `Complex.reCLM`; `ContDiff.mul`, `ContDiff.pow` in the normed `ℝ`-algebra `ℂ`.

### (i) The D76 statement

Both lemmas conclude **the exact conclusion of `sjsu_secular_confinement` (draft v2)** for every `z₀` satisfying
its `hz₀`. The text is copied verbatim and differs only in line breaks.

They discharge:
- `hV` (N5a's `sjsuV_orth`);
- the shift (ii) and `hH` (iii);
- `hT`;
- `hz₀ ↔ z₀ ∈ Metric.closedBall sjsuZStar (1/10^6)` (`mem_closedBall_iff_coords`; N5c's `sjsuZStar` uses the
  statement's decimals verbatim, so this is definitional);
- `Pγ`, the eccentricity intervals, via `sjsu_hG`. That is N6's `sjsu_tube_ecc` after
  `chartGamma_sjsuV : chartGamma sjsuV I φ j = eccGamma sjsuEccV I φ j`, from N5c's `sjsuV_eq_eccV` and `rfl`.

Fixed values: `δ = r = 1/10^6`, `ρ = 2/10^6`, `T = 5 * 10^9`, `z = sjsuZStar`, `V = sjsuV`, `B = sjsuB`,
`H = sjsu18O2`.

```lean
theorem sjsu_secular_confinement_of_checks
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {β ct ε γ η μ A a : Fin 3 → ℝ} {Fu : Fin 3 → Fin 3 → ℝ} {Fφ : Fin 3 → Fin 2 → ℝ} {Nv : ℝ}
    -- N5a: the Hamiltonian in tube coordinates
    (hHh : ∀ y ∈ actionPos 3, sjsu18O2 (rotMap sjsuV (polar y)) = h (shiftChart sjsuB y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → DifferentiableAt ℝ h (u, φ))
    -- N7: the observables, rates and faces
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |reducedBracket (f j) h (u, φ)| ≤ η j)
    (hTη : ∀ j, 5 * 10 ^ 9 * η j < 1 / 10 ^ 6 / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hc : ∀ j, |f j (tubeChart sjsuV sjsuB sjsuZStar) - ct j| ≤ γ j)
    (hερ : ∀ j, 1 / 10 ^ 6 + ε j + γ j < 2 / 10 ^ 6)
    -- N5c: the ball `Q = closedBall z* 10⁻⁶`
    (hN : ∀ j, ∑ k, |sjsuV k j| ≤ Nv)
    (hAb : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
      |(rotMap sjsuVᵀ y).1 j| + |(rotMap sjsuVᵀ y).2 j| ≤ A j)
    (ha : ∀ j, 0 < a j)
    (hab : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j, a j ≤ modeSq sjsuV y j)
    (hβ : ∀ φ (b : Fin 2) (l : Fin 3), |fderiv ℝ sjsuB φ (Pi.single b 1) l| ≤ β l)
    (hμ : ∀ j, |tubeU sjsuV sjsuB sjsuZStar j| ≤ μ j)
    (hμρ : ∀ j, μ j + chartLip Nv A a β (Pi.single j 1) 0 * (1 / 10 ^ 6) < 2 / 10 ^ 6)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ l,
      |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ Fu j l)
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ b,
      |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ Fφ j b)
    (hLF : ∀ j, chartLip Nv A a β (Fu j) (Fφ j) * (1 / 10 ^ 6) ≤ 1 / 10 ^ 6 / 2)
    (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz₀ : …the D76 hz₀…) : …the D76 conclusion…

theorem sjsu_secular_confinement_of_obs
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {ct ε η : Fin 3 → ℝ}
    (hHh : ∀ y ∈ actionPos 3, sjsu18O2 (rotMap sjsuV (polar y)) = h (shiftChart sjsuB y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → DifferentiableAt ℝ h (u, φ))
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |reducedBracket (f j) h (u, φ)| ≤ η j)
    (hTη : ∀ j, 5 * 10 ^ 9 * η j < 1 / 10 ^ 6 / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hερ : ∀ j, 1 / 10 ^ 6 + ε j + (ε j + (sjsuMu : ℝ)) < 2 / 10 ^ 6)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ l,
      |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ (sjsuFuMax j l : ℝ))
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ b,
      |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ (sjsuFphiMax j b : ℝ))
    (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz₀ : …the D76 hz₀…) : …the D76 conclusion…
```

- **`of_obs`** plugs in N5c's ball discharges: `sjsu_hN`, `sjsu_hAb`, `sjsu_ha`, `sjsu_hab`, `sjsu_hβ`, `sjsu_hμ`,
  `sjsu_hμρ` and `sjsu_hLF`, with N5c's ceilings `sjsuFuMax` and `sjsuFphiMax`.
- **`hc`** is discharged with `γ_j = ε_j + μ` through N5c's `abs_obs_sub_le_of_face`.
- **What remains:**
  - N5a: `h` with `hHh`, `hhd`;
  - N7: the literal observables `f` with `hfper`, `hfd`, `hη`, `hTη`, `hface`, `hερ` (a face margin
    `2ε + 10⁻⁹ < 10⁻⁶`; phase 1 had `ε ≈ 0.423δ`), and the partial ceilings `hFu`/`hFφ`.
  - N5c's `Tube/Initial/Partials` (`abs_fderiv_tmEvalPair_u_le`/`_φ_le`, `differentiable_tmEvalPair`,
    `tmEvalPair_add_two_pi`) gives `hFu`, `hFφ`, `hfd`, `hfper` from coefficient norms if
    `f j = tmEvalPair s μ (g j)`.
- **Using `of_checks` directly:** if N5c's ceilings change, `of_obs` changes, and `of_checks` does not.

**Template for the ordinary theorem**, once N5a and N7 land:

```lean
theorem sjsu_secular_confinement_proof (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz₀ : …D76…) : …D76… :=
  sjsu_secular_confinement_of_obs (h := sjsuHTilde) (f := sjsuObs) sjsu_hHh sjsu_hhd sjsu_hfper sjsu_hfd
    sjsu_hη sjsu_hTη sjsu_hface sjsu_hερ sjsu_hFu sjsu_hFφ z₀ hz₀
```

It must be stated in the verbatim D76 text. The binders of `of_obs` elaborate to the same term (copied text;
`exact` closed `of_obs` from `of_checks`).

**Phase-B checks.**
- **Builds** (`g2lake build`):
  - `KAM.EffectiveStability.SJSU.Confinement.Statement`: `Build completed successfully (9125 jobs)`. This builds
    `Shift`, `Tube.Check.Center`, N5c's `SJSU.Initial.Main`, N6's `SJSU.Ecc.Main` and N5a's `SJSU.Ham.Center` and
    `Rot`.
  - `KAM.EffectiveStability.Tube.Check.Bracket` rebuilt after N6's rename (`treeSum` → `treeSumQ`):
    `Build completed successfully`.
  - No warnings in my files.
- **`#print axioms`** (`.drafts/g2/scratch/n5b/Axioms2.lean`, output `axioms2.out`):
  `[propext, Classical.choice, Quot.sound]` for each of the following:
  - `abs_tubeCenter_sub_le`, `tubeCenter_bounds_of_globalOK`;
  - `sjsuB_eq_eccCenter`, `shiftPeriodic_sjsuB`, `differentiable_sjsuB`, `sjsuB_bounds`, `sjsu_rho_lt_bmin`;
  - `contDiff_polyRe`, `contDiff_sjsu18O2`;
  - `chartGamma_sjsuV`, `sjsu_hG`, `sjsu_secular_confinement_of_checks`, `sjsu_secular_confinement_of_obs`.
- **Line counts:** `Shift` 105, `Statement` 163, `Center` 87. No line is over 100 characters.
- **Lint:** see "Lint (phase B)" at the end.

**Phase-B dependencies on in-progress packages.**
- `Statement.lean` imports N5c's `SJSU.Initial.Main`. N5c's package audit is pending.
- `Center.lean` uses N6's `treeSumQ_eq`, which N6 renamed during this session.
- A rename in either package breaks these imports, and the fix is a one-line edit on my side.

**Audit 1 fix N1** (`docs/explorations/sjsu-g2-audits/N5b-Assembly-AUDIT-1.md`, applied).
- The `polarInvD` docstring (`Tube/Check/Deriv.lean`) now reads: "the inverse of the polar derivative at
  `polarInv w` (equivalently, the derivative of a smooth local inverse of `polar` through that lift), for nonzero
  modes". It adds that it is not a derivative of `polarInv` itself, whose `arg` lift is discontinuous on
  `q = 0, p < 0`.
- The change is documentation only. `Statement` and its whole import chain rebuild: `Build completed successfully
  (9125 jobs)`.

**Phase-B design signals.** None. Higher-order unification could not infer `Pγ` from `sjsu_hG`, so it is passed
explicitly.

The files `Confine.lean` and `Solution.lean` were drafts by the previous N5b session. I kept and checked them, and
generalized nothing in them.

## Phase A: the interface for the instance (exact hypothesis form; N5c-Q should match this)

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

## Remaining (as of phase A; superseded by "Phase B" above)

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

## Lint (phase B)

`.drafts/g2/lint_noabi.sh` (output `.drafts/g2/scratch/n5b/lint3.out`; **the `abi_hashes` step was skipped**).

Result: exit 1, with **no finding under `KAM/EffectiveStability/Tube/Check/` or `KAM/EffectiveStability/SJSU/Confinement/`**.

The failures come from outside this package:
- lines over 100 characters in `SJSU/Ham/*`, `SJSU/Model/SJSU18O2Part*`, `Tube/Engine/*` and `Tube/Poly/*`;
- `KAM.lean is out of date` (orchestrator-owned roots).

Everything else passed: `check_lean_modules: PASS`, unit tests `Ran 29 tests … OK` and `Ran 8 tests … OK`,
`FROZEN-ANCHOR GUARD OK`.

An earlier run (`lint2.out`) crashed when another worker deleted `SJSU/Ham/Hw/D3P0.lean` during the run. That is a
race in the shared worktree, not a finding.

**Freeze-prep note (for N6's staging).** The ordinary theorem will live in the module
`KAM.EffectiveStability.SJSU.Confinement.Proof` (file `SJSU/Confinement/Proof.lean`, not yet written).
- Its type is the v2 text verbatim.
- It will import `SJSU.Confinement.Statement` plus the N5a/N7 instance modules, and nothing under `KAM/Frozen/` and
  no provider.

I confirmed this to g2-n6.

## Final step staged (scratch; promote once N5a is committed and N7 lands)

`.drafts/g2/scratch/n5b/Proof.lean` (not in the package).

**Part 1** is type-checked with `g2lake env lean` (17:1x UTC, against N5a's built oleans).
- `sjsu_hhd`: `h̃ = sjsuHTilde sjsuB` is differentiable on the whole box. It uses N5a's `differentiableAt_hTildeOf`;
  on the box `B_j + u_j ≥ bmin_j − ρ > 0`.
- `sjsu_secular_confinement_of_N7` is `of_obs` with `h := sjsuHTilde sjsuB`, `hHh := sjsu18O2_chart` (N5a) and
  `hhd := sjsu_hhd`. Its only hypotheses are N7's: `hfper`, `hfd`, `hη` (bracket with `sjsuHTilde sjsuB`), `hTη`,
  `hface`, `hερ`, `hFu`, `hFφ`.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for both.

**Part 2** (commented out) is `sjsu_secular_confinement_proof`.
- It follows kam-g2's width ruling: the text is reflowed to ≤ 100 columns, the same Expr as v2. The frozen anchor
  stays byte-identical and gets `scripts/lint-width-allow.txt` entries at freeze.
- It calls `of_N7` with placeholder N7 names: `sjsuObs`, `sjsuObsCt`, `sjsuObsEps`, `sjsuEta`, `sjsu_hfper`, …,
  `sjsu_hFφ`.
- Its target is `KAM/EffectiveStability/SJSU/Confinement/Proof.lean` (module
  `KAM.EffectiveStability.SJSU.Confinement.Proof`).

**Update (N8-Obs plugged in; scratch, type-checked).**
- `sjsu_secular_confinement_of_rate` instantiates `of_N7` with N8's `sjsuObs`, `sjsuObsCt`, `sjsuObsEps`,
  `sjsu_hfper`, `sjsu_hfd`, `sjsu_hface`, `sjsu_hερ`, `sjsu_hFu`, `sjsu_hFφ` (module
  `KAM.EffectiveStability.SJSU.Obs.Main`).
- Its **only** hypotheses are the rate check:
  - `hη : ∀ j u φ, (∀ l, |u l| ≤ 2/10^6) → |reducedBracket (sjsuObs j) (sjsuHTilde sjsuB) (u, φ)| ≤ η j`;
  - `hTη : ∀ j, 5·10^9 · η j < 1/10^6/2`.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Part 2 now reads `sjsu_secular_confinement_of_rate (η := sjsuEta) sjsu_hη sjsu_hTη z₀ hz₀`. The placeholders left
  are N7's η checker only.

## N9-Bracket (worker g2-n5b; brief `.drafts/g2/BRIEF-N9-Bracket.md`)

**Status (17:40 UTC): (A) and (B) are built (interim `READY g2-n9a`); (C), the SJSU instance, is next.**

### Files (core, `KAM/EffectiveStability/Tube/Check/`, namespace `KAM.EffectiveStability.Tube`)

| file | lines | content |
|---|---:|---|
| `BracketList.lean` | 135 | (A) `natCast_mul_umon_sub_mul_umon`, `natCast_mul_umon_mul_umon_sub`, `sum_map_flatMap`, `list_sum_mul_list_sum`, `list_sum_sub`, `list_sum_add`, **`reducedBracket_listObs`** |
| `BracketBound.lean` | 246 | (B) `mem_truncSet_iff`, `list_sum_split_fiber`, `list_sum_split_truncSet`, `reducedBracket_add`, `abs_reducedBracket_le`, `bracketKept/Drop/Err/Tail`, `abs_reducedBracket_listObs_le`, `listObs_add_sub`, **`reducedBracket_bound`** |

Imports: N7's `Engine/BTerm`, N8's `Obs/ListObs`, N2's `Chart/Shift`, my `Check/Bracket`, and N4's
`Witness/BinomialProd`.

### (A), exactly as the brief states it

```lean
theorem reducedBracket_listObs {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ) (k : κ → (Fin 2 → ℝ) → ℝ)
    (hg : ∀ i ∈ Fl, Differentiable ℝ (g i)) (hk : ∀ e ∈ Hl, Differentiable ℝ (k e))
    (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) :
    reducedBracket (listObs Fl μ g) (listObs Hl ν k) (u, φ) =
      ((bterms Fl Hl).map fun b => (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ).sum
```

- Both sides are expanded to `Σ_a Σ_i Σ_e T(a, i, e)`.
- The bracket side uses N8's `fderiv_listObs_u/φ` and list distributivity; the `bterms` side uses flatMap sums.
- Term by term, `linear_combination` closes the goal with `m_x u^{m−e_x} u^n = m_x u^{m+n−e_x}` (natural
  subtraction; both sides are 0 when `m_x = 0`). This also verifies N7's `BTerm` table.

### (B)

```lean
def bracketKept (L : ℕ) (r : ℝ) (G : (Fin 3 → ℕ) → ℝ) : ℝ := ∑ p ∈ truncSet (Fin 3) L, r ^ mdeg p * G p
def bracketDrop (Fl) (μ) (Hl) (ν) (L : ℕ) (r : ℝ) (V : BT ι κ → ℝ) : ℝ :=
  (((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon μ ν))).map fun b =>
    |(b.coef μ ν : ℝ)| * r ^ mdeg (b.mon μ ν) * V b).sum
def bracketErr (Hl) (ν) (r : ℝ) (e₀ e₁ : κ → ℝ) (Fd Fp : Fin 2 → ℝ) : ℝ :=
  ∑ a : Fin 2, (Fd a * (Hl.map fun e => r ^ mdeg (ν e) * e₁ e).sum +
    Fp a * ((Hl.map fun e => (ν e a.castSucc : ℝ) * r ^ mdeg (ν e - Pi.single a.castSucc 1) * e₀ e).sum +
      (Hl.map fun e => (ν e 2 : ℝ) * r ^ mdeg (ν e - Pi.single 2 1) * e₀ e).sum))
def bracketTail (Fd Fp : Fin 2 → ℝ) (Ru : Fin 3 → ℝ) (Rp : ℝ) : ℝ :=
  ∑ a : Fin 2, (Fd a * Rp + Fp a * (Ru a.castSucc + Ru 2))

theorem reducedBracket_bound {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ)
    (k hc : κ → (Fin 2 → ℝ) → ℝ) (hg : ∀ i ∈ Fl, Differentiable ℝ (g i))
    {e₀ e₁ : κ → ℝ} (hcert : ∀ e ∈ Hl, C1Close (hc e) (k e) (e₀ e) (e₁ e))
    {h R : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} (hdec : ∀ p, h p = listObs Hl ν hc p + R p)
    {L : ℕ} {r : ℝ} {G : (Fin 3 → ℕ) → ℝ} {V : BT ι κ → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L, ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ ν = p)).map (fun b => (b.coef μ ν : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    (hV : ∀ b ∈ bterms Fl Hl, ∀ φ, |b.val g k φ| ≤ V b)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ)
    {Fd Fp : Fin 2 → ℝ}
    (hFd : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single a.castSucc 1, 0) -
      fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single 2 1, 0)| ≤ Fd a)
    (hFp : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (0, Pi.single a 1)| ≤ Fp a)
    {Ru : Fin 3 → ℝ} {Rp : ℝ} (hRd : DifferentiableAt ℝ R (u, φ))
    (hRu : ∀ l, |fderiv ℝ (fun v => R (v, φ)) u (Pi.single l 1)| ≤ Ru l)
    (hRp : ∀ a, |fderiv ℝ (fun ψ => R (u, ψ)) φ (Pi.single a 1)| ≤ Rp) :
    |reducedBracket (listObs Fl μ g) h (u, φ)| ≤
      bracketKept L r G + bracketDrop Fl μ Hl ν L r V + bracketErr Hl ν r e₀ e₁ Fd Fp +
        bracketTail Fd Fp Ru Rp
```

- **Splitting `h`.** `h = model + (true − model) + R` as functions (`hdec` is global, like N5a's `hTildeOf_taylor`).
  Additivity gives three brackets:
  - the model part, ≤ `KEPT + DROP`: (A), then a fibre split over N4's `truncSet (Fin 3) L`;
  - the certificate part, ≤ `ERR`: N8's `abs_fderiv_listObs_u/φ_le` applied to `d_e = h_e − k_e`;
  - the remainder, ≤ `TAIL`: slice-to-joint partials of `R` through `Check/Bracket`, using the joint
    differentiability `hRd`.
- **Regularity.**
  - `hG` is N7's per-`p` form verbatim (filter by `decide (b.mon μ ν = p)`). For `p` with no terms the sum is
    `0`.
  - `V` is any bound of `|val b|`: for the SJSU, `if kind then sup|∂g|·sup|k| else sup|g|·sup|∂k|`.
  - Joint differentiability: the models `k` and the true `h_e` come from `C1Close` (both sides differentiable);
    for `R`, it is the hypothesis `hRd`.
- **Checks.**
  - Builds: `KAM.EffectiveStability.Tube.Check.BracketList` and `.BracketBound` both report
    `Build completed successfully`. No warnings in my files; no line over 100 characters.
  - `#print axioms` (`.drafts/g2/scratch/n5b/axioms3.out`): `[propext, Classical.choice, Quot.sound]` for
    `reducedBracket_listObs`, `list_sum_split_truncSet`, `reducedBracket_add`, `abs_reducedBracket_le`,
    `abs_reducedBracket_listObs_le` and `reducedBracket_bound`.
- **Design signals:** none.

