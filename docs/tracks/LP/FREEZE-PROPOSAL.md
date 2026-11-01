# Track LP: freeze proposal (DRAFT 4, for the owner's morning review)

Status: 2026-11-01, overnight. **Nothing is frozen.** This file proposes the exact Lean text of the LP anchors.
**Draft 2** applies the independent refute-first statement review
[`freeze/STATEMENT-REVIEW-1.md`](freeze/STATEMENT-REVIEW-1.md) (codex-2, Sol medium; verdict RETURN FOR REVISION of
draft 1: no false statement and no conclusion-shaped premise, but source-scope omissions F1–F2 and definition-carrier
issues F3–F4). The texts below are the reviewer's replacements, elaborated transiently against the current LP code
(`freeze/elaboration-draft-2.lean.txt`, proof placeholders only, outside the library; capped `lp_lean.sh`, exit 0).
Draft 1 is kept in `freeze/elaboration-draft-1.lean.txt` for comparison.

**Review status.** Draft 3 adds only §3b (the OD-11 (b) text, proved); its delta review
[`freeze/STATEMENT-REVIEW-3.md`](freeze/STATEMENT-REVIEW-3.md) is **PASS** (F4 resolved for the source-facing
definitions on their whole carriers; §3b faithful to draft-2 LP1). **With option (b), the freeze package has no open
technical blocker**: what remains is the owner's decisions OD-1…OD-11. (Code blocks show statements only; the proofs
are the LP-PS / LP-SRC theorems, see §1.) Delta review [`freeze/STATEMENT-REVIEW-2.md`](freeze/STATEMENT-REVIEW-2.md) (codex-2): **PASS for the
draft-2 theorem types** (F1, F2, F5 resolved; F3 repaired in LP-THR2, landing; no conclusion-shaped input; sorry-free
producers independently verified). **Freeze package NOT READY** only because of the open owner decision **OD-11**
(F4: how the new physical formulas are frozen; orchestrator recommendation (b), source subtypes). After the owner
rules on OD-1…OD-11, the exact final anchor and definition text is generated and re-reviewed before any freeze. Approval objects are
these exact texts; the decisions they depend on are in [`OWNER-DECISIONS.md`](OWNER-DECISIONS.md) (OD-1…OD-9).

Source: [`source/MAIN.md`](source/MAIN.md) as amended by [`source/AMENDMENTS.md`](source/AMENDMENTS.md)
(audit PROOF-AUDIT-1, PASS WITH NOTES).

## 1. Proposed anchors

| Anchor | Lean name | MAIN | Lean proof status (2026-11-01 overnight) |
|---|---|---|---|
| LP0 | `planar_strongAMD_barrier` | L5 in full (with L2–L4) | **proved (draft-2 text, exactly)** by LP-PS `lp0_planar_barrier` from GEOMOD (landed); same verification file |
| LP1 | `planar_strongAMD_exponentialSafety` | Theorem 15 (+ L16) | **proved (draft-2 text, exactly)** by LP-PS `lp1_planar_strongAMD_safety_normalized` (branch `inp-lp-ps` 74ebebb1; audit pending). Verification: `freeze/verification-draft-2.lean.txt` states the draft-2 LP0 and LP1 verbatim and closes them by the proved theorems; capped `lp_lean`, exit 0, axioms `[propext, Classical.choice, Quot.sound]` |
| LP2 | `spatial_strongAMD_exponentialSafety` | Theorem 19 (+ L16, d = 3) | **proved** by LP-SP-SAFE `lp2_spatial_strongAMD_safety_normalized` (branch `inp-lp-spsafe` c9553935; audit pending); axioms `[propext, Classical.choice, Quot.sound]` (orchestrator re-check); text §3c, not yet statement-reviewed |
| LP-cor | `planar_strongAMD_exponentialSafety_halfInteger` | §1 (τ = n − 1/2) | corollary, exponent `1/(2n+1)` (`scaleExponent_planar`, NRS) |

Definitions entering the statements (all non-frozen today). **Which of them would be frozen as source objects, and in
what form, is governed by §4b (definition freeze inventory) and owner decision OD-11, not by this list**: the list
below is the definition closure the elaborated texts reference, including internal total helpers:
`chamber`, `actionAxis`, `eccDeficit`, `pairFeasible`, `pairObjective`, `pairThreshold` (+ characterization),
`AdjIdx`, `AdjIdx.upperIdx`, `crossThreshold`, `starThreshold`, `strongThreshold`, `OrderedActions`,
`orderedPairThreshold`, `orderedCrossThreshold`, `orderedStrongThreshold` (THR); `strongAMD` (MOM);
`oscVelocity`, `oscParam`, `oscEnergy`, `oscAxis`, `oscEccVector`, `oscEcc`, `oscPeri`, `oscApo`, `keplerPeri`,
`keplerApo` (OSC); and the frozen planar repository definitions (`Phase`, `bodyVector`, `keplerEnergy`,
`keplerAxis`, `keplerAction`, `keplerEccVector`, `planeLength`, `IsMovingSolutionOn`, `MovingUniqueOn`,
`IsNewtonSolutionOn`, `actualMasses`, `barycentricPositions`, `barycentricVelocities`), and
`KAM.Fourier.modeSize` (ℓ¹ mode size).

## 2. LP0: the planar sharp barrier (exact text)

```lean
theorem planar_strongAMD_barrier (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) (hm : 0 < m) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      (∀ I : Fin n → ℝ, ∀ hI : I ∈ U, ∀ e : Fin n → ℝ,
        (∀ i, e i ∈ Set.Icc (0 : ℝ) 1) →
        (∑ i, I i * eccDeficit (e i)) ≤ orderedStrongThreshold hn ⟨I, hUch hI⟩ - m →
        (∀ i, dStar ≤ actionAxis ν I i * (1 - e i)) ∧
        (∀ a : AdjIdx n, dPair ≤ actionAxis ν I a.upperIdx * (1 - e a.upperIdx) -
          actionAxis ν I a.1 * (1 + e a.1))) ∧
      ∃ K : Set (Phase (n * 2)), IsCompact K ∧
        (∀ w ∈ K, NoCollision w.1 ∧ ∀ i, keplerEnergy ν w i < 0) ∧
      ∀ z : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) →
        ∀ hΛ : (fun i => keplerAction ν z i) ∈ U,
        strongAMD ν z ≤ orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - ecc ν z i)) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx * (1 - ecc ν z a.upperIdx) -
            keplerAxis ν z a.1 * (1 + ecc ν z a.1)) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z)
```

Reading: for fixed positive masses, a compact action set `U` inside the ordered chamber and a margin `m > 0`,
there are `d⋆, d_pair > 0` (before the state) such that every negative-energy state with actions in `U` and
strong AMD `≤ B(Λ) − m` has perihelia `≥ d⋆`, adjacent radial-annulus gaps `≥ d_pair`, star distances `≥ d⋆`,
and all pair distances `≥ d_pair`. This is MAIN L5 in full (review F1): also the deficit-list form for every `e ∈ [0,1]ⁿ` on action vectors in `U`,
a compact collision-free set `K` of negative-energy states containing every such state, and the invariable-frame
conclusion `|L_i| ≥ m` with every `L_i` of the sign of `L`. The added items are outputs, not premises.

## 3. LP1: planar strong-AMD exponential safety (exact text)

```lean
theorem planar_strongAMD_exponentialSafety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧ 0 < Aelem ∧
      Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i * (1 - ecc ν (z t) i)) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx * (1 - ecc ν (z t) a.upperIdx) -
                keplerAxis ν (z t) a.1 * (1 + ecc ν (z t) a.1)) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∀ i, oscEnergy ν μ (z t) i < 0 ∧
                  0 < oscAxis ν μ (z t) i ∧ oscEcc ν μ (z t) i < 1 ∧
                  oscPeri ν μ (z t) i ≤ planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤ oscApo ν μ (z t) i ∧
                  |oscAxis ν μ (z t) i - keplerAxis ν (z t) i| +
                    planeLength (oscEccVector ν μ (z t) i - keplerEccVector ν (z t) i)
                      ≤ Aelem * μ) ∧
            (∀ i, |oscPeri ν μ (z t) i - keplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |oscApo ν μ (z t) i - keplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ oscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤ oscPeri ν μ (z t) a.upperIdx - oscApo ν μ (z t) a.1)
```

Reading (MAIN §1 (6)–(9) and Theorem 15): constants `μ₀, c, T₀, A_Λ, A_a, d⋆, d_pair, A_osc` are chosen
before `μ` and the initial state. For every `0 < μ ≤ μ₀` and every negative-energy initial state with axes in
`A`, the Diophantine condition (5) on the initial Kepler frequencies `ω_i = ν_i³/Λ_i³`, and AMD at most
`B(Λ) − δ`, the unique moving solution exists on `|t| ≤ T₀ exp(c μ^{−1/(2(τ+1))})`, reconstructs the actual
Newtonian `(1+n)`-body motion, and along it: ellipticity, AMD `≤ B − δ/2`, `O(√μ)` action/axis drift, AMD drift
`≤ n A_Λ √μ`, perihelia and adjacent gaps bounded below, all star and pair distances bounded below, and the
actual-velocity osculating ellipses: valid ellipses (energy `< 0`, `e < 1`) through the current position, with
MAIN L16's summed element error `≤ A_elem μ`, endpoint errors `≤ A_osc μ` and half the gaps; the N10 smallness
inequalities on `μ₀` are displayed (review F2). **No hypothesis on the secular dynamics.**

## 3b. LP1 under OD-11 option (b): exact text through the source carriers (draft 3 addition)

Option (b) (orchestrator recommendation) is now **concrete and proved**: package LP-SRC (branch `inp-lp-src`
dd0a5ec5; audit pending) defines the source carriers and source-facing definitions of review 1 F4, with their
characterization theorems, and proves LP1 restated through them from `lp1_planar_strongAMD_safety` (capped build,
lint, short names, axioms `[propext, Classical.choice, Quot.sound]`). Full files:
`freeze/odb-SourceCarrier.lean.txt`, `freeze/odb-PlanarSafety-Source.lean.txt`.

Source carriers and source-facing definitions (each with a `_def` equation to its internal total helper, by `rfl`;
characterizations: `sourceStrongAMD_nonneg`, `sum_action_mul_eccDeficit_le_sourceStrongAMD`, `sourceKepler_axis_pos`,
`sourceKepler_ecc_le_one`, `sourceKeplerPeri_le_planeLength`, `planeLength_le_sourceKeplerApo`, `sourceOscAxis_pos`,
`sourceOscPeri_pos`, `sourceOscPeri_le_planeLength`, `planeLength_le_sourceOscApo`):

```lean
abbrev SourceCanonicalPhase (n : ℕ) (ν : Fin n → ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0}

/-- Source osculating phases (`LP:MAIN L16 (510–525)`): positive masses and `μ`, nonzero
positions, and nondegenerate actual-velocity ellipses (`E^osc < 0`, `e^osc < 1`). -/
abbrev SourceOsculatingPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧
      oscEnergy ν μ z i < 0 ∧ oscEcc ν μ z i < 1}

/-- The strong AMD on source canonical phases. -/
def sourceStrongAMD {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) : ℝ := strongAMD ν z.1

/-- Canonical perihelion on source canonical phases. -/
def sourceKeplerPeri {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerPeri ν z.1 i

/-- Canonical aphelion on source canonical phases. -/
def sourceKeplerApo {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerApo ν z.1 i

/-- Actual heliocentric velocity on source osculating phases. -/
def sourceOscVelocity {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    Fin 2 → ℝ := oscVelocity ν μ z.1 i

/-- Gravitational parameter `1 + μ ν_i` on source osculating phases. -/
def sourceOscParam {ν : Fin n → ℝ} {μ : ℝ} (_z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscParam ν μ i

/-- Osculating energy on source osculating phases. -/
def sourceOscEnergy {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscEnergy ν μ z.1 i

/-- Osculating semi-major axis on source osculating phases. -/
def sourceOscAxis {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscAxis ν μ z.1 i

/-- Osculating eccentricity vector on source osculating phases. -/
def sourceOscEccVector {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    Fin 2 → ℝ := oscEccVector ν μ z.1 i

/-- Osculating eccentricity on source osculating phases. -/
def sourceOscEcc {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscEcc ν μ z.1 i

/-- Osculating perihelion on source osculating phases. -/
def sourceOscPeri {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscPeri ν μ z.1 i

/-- Osculating aphelion on source osculating phases. -/
def sourceOscApo {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscApo ν μ z.1 i

/-! ### Defining equations -/
```

LP1 through the source carriers (normalized, i.e. the draft-2 LP1 binders plus the typing binder `h₀`):

```lean
theorem lp1_planar_strongAMD_safety_source (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              |sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) -
                  sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
                n * AΛ * Real.sqrt μ) ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
             ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧
                  oscEnergy ν μ (z t) i < 0 ∧ oscEcc ν μ (z t) i < 1,
              (∀ i, sourceOscEnergy (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  sourceOscEcc (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 1 ∧
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ≤
                    planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  |sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerAxis ν (z t) i| +
                    planeLength (sourceOscEccVector (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
              (∀ i, |sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerPeri (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ ∧
                  |sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerApo (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.upperIdx -
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1))
```

Differences from §3: a typing binder `h₀` (the source-carrier membership of `z₀`, derivable from the physical
premise and `hν`); the initial AMD hypothesis through `sourceStrongAMD ⟨z₀, h₀⟩`; in the conclusion, the AMD
margin/drift clauses as `∃ hs, … sourceStrongAMD ⟨z t, hs⟩ …` and the whole osculating block under `∃ hs ho, …`
with `sourceOsc*` / `sourceKeplerPeri/Apo` (mirroring `∃ hcht` for the thresholds). The frozen planar repository
definitions (`keplerAxis`, `keplerEccVector`, `keplerAction`, …) stay as in §3.

## 3c. LP2: spatial strong-AMD exponential safety (exact text; draft 4 addition, review pending)

The exact spatial twin of §3 (LP1): `Phase (n * 3)`, Euclidean `spaceLength`, the vector angular momentum in
`spatialStrongAMD`, the spatial Newtonian reconstruction and osculating elements. Premises are those of LP1 with the
spatial objects; **no** prograde, inclination, nonzero-total-angular-momentum, alignment or secular premise (MAIN
Theorem 19; roadmap §2): the frame alignment with `L` is done inside the proof by a rotation. Proved by LP-SP-SAFE
(full module: `freeze/lp2-SpatialSafety-Main.lean.txt`). Under OD-11 (b) the spatial physical quantities would be
restated through source carriers (package LP-SP-SRC, in progress; audit LP-W4A-1 note N1).

```lean
theorem lp2_spatial_strongAMD_safety_normalized (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => spatialKeplerAction ν (z t) i) ∈ chamber ν,
              spatialStrongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤ spatialKeplerAxis ν (z t) i *
              (1 - spaceLength (spatialKeplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν (z t) a.upperIdx *
                (1 - spaceLength (spatialKeplerEccVector ν (z t) a.upperIdx)) -
                spatialKeplerAxis ν (z t) a.1 *
                  (1 + spaceLength (spatialKeplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            (∀ i, spatialOscEnergy ν μ (z t) i < 0 ∧ 0 < spatialOscAxis ν μ (z t) i ∧
                  spatialOscEcc ν μ (z t) i < 1 ∧
                  spatialOscPeri ν μ (z t) i ≤ spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤ spatialOscApo ν μ (z t) i ∧
                  |spatialOscAxis ν μ (z t) i - spatialKeplerAxis ν (z t) i| +
                    spaceLength (spatialOscEccVector ν μ (z t) i -
                      spatialKeplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
            (∀ i, |spatialOscPeri ν μ (z t) i - spatialKeplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |spatialOscApo ν μ (z t) i - spatialKeplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ spatialOscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤
              spatialOscPeri ν μ (z t) a.upperIdx - spatialOscApo ν μ (z t) a.1)
```

## 4. Choices embedded in the text (owner decisions)

1. **AMD convention (OD-1, audit N8).** `strongAMD = ΣΛ − |L|` (orientation-free, MAIN (2)); no prograde premise.
   The proof reduces `L < 0` by the reflection (`isMovingSolutionOn_reflectPhase_iff`, MOM, audited). The
   alternative signed `physicalAMD` would make the hypothesis force `L > 0` (a narrower theorem).
2. **Threshold carrier (OD-2; root-b8 recommendation; review F3).** The anchors use `orderedStrongThreshold hn ⟨Λ, h⟩` on
   the source carrier `OrderedActions ν`, with the chamber membership `hch` as typing data (a binder, not a
   source premise: it follows from `a ∈ A` and `ν > 0`). In conclusions the membership is existential
   (`∃ hcht, …`). The total `strongThreshold` stays an internal helper, equal by `rfl`
   (`orderedStrongThreshold_eq`). **Alternative:** the total form (no `hch` binder; simpler text, but the frozen
   definition then has off-source values).
3. **Mass normalization (OD-3; review F5).** The anchor **keeps** MAIN's `max ν = 1` (`hνmax`, `hνle`), as the
   reviewer recommends. Dropping them is a valid generalization of the *equation* (the Lean proof does not use
   them), but it changes the meaning of `μ` from "largest planet-to-star mass ratio" to a mass *scale* (the ratio
   is `μ · max ν`), and the constants transform (review F5 gives the explicit rescaling). The general version is
   proved as an ordinary theorem (LP-PS) and can be frozen later as a separately approved successor. LP0 has no `μ`
   and is stated for arbitrary positive `ν` (a static generalization; review F5 notes it).
4. **Arithmetic (OD-4).** `τ > n − 1` free, `γ > 0`, condition on the initial radian frequencies with ℓ¹ mode
   size; the corollary fixes `τ = n − 1/2`.
5. **Crossing notion (OD-5).** Canonical annuli + all-pair distances + actual-velocity osculating annuli (N10:
   half gaps; the `μ₀` ordering is internal).
6. **Uniqueness.** Exported in the repository's `MovingUniqueOn` form (as P-EXP-SAFE), plus the Newtonian
   reconstruction `IsNewtonSolutionOn`.
7. **New anchors only (OD-6).** P-EXP-SAFE is untouched.

## 4b. Definition freeze inventory (review F3, F4)

- **Thresholds (F3).** Freeze the source-facing `OrderedActions`, `orderedPairThreshold` (with `i < j`) together with
  its attained-minimum / unique-value characterization (`orderedPairThreshold_isLeast`,
  `orderedPairThreshold_existsUnique_value`), `orderedCrossThreshold` **with `2 ≤ n`** and `orderedStrongThreshold`
  with `2 ≤ n`. The raw total formulas (`pairThreshold`, `crossThreshold`, `starThreshold`, `strongThreshold`) stay
  internal implementation helpers in the definition closure, not certified as MAIN's objects off the chamber. The
  missing `2 ≤ n` on `orderedCrossThreshold` is being repaired in code (package LP-THR2, in progress); the anchors
  already carry `hn`, so their text is unchanged.
- **New physical expressions (F4; owner decision OD-11).** `strongAMD`, `keplerPeri/Apo`, and the osculating
  `oscVelocity/oscParam/oscEnergy/oscAxis/oscEccVector/oscEcc/oscPeri/oscApo` are literal total formulas. They are
  physically meaningful only where the anchors state or prove their guards (negative energy; for the osculating
  elements, `oscEnergy < 0` and `oscEcc < 1`, which LP1 now exports). Two conventions are possible:
  (a) register them as total algebraic expressions with guarded physical interpretation (the anchors unchanged); or
  (b) freeze source-facing restrictions on subtypes (`SourceCanonicalPhase`, `SourceOsculatingPhase`, and
  `sourceStrongAMD`, `sourceOscAxis`, …; exact text in the review, F4), keeping the totals as internal helpers.
  The review does not choose; the owner rules (OD-11). **Orchestrator recommendation: (b)**, for every frozen
  meaning-carrying definition, each with its characterization theorem (the frozen-definition rules reject
  off-carrier junk values). Under (b), the anchors' occurrences of these formulas are restated through the source
  restrictions (the guards `oscEnergy < 0`, `oscEcc < 1` and negative canonical energy, which LP1 exports, supply
  the subtype proofs); the exact restated text is generated once the owner rules, and re-reviewed.

## 5. What a freeze would require next

Owner approval of the exact text (with the OD choices) → independent statement audit (lean-statement-audit) →
freeze under `KAM/Frozen/` with manifest entries (DRAFT_SORRY until sealed) → source dependency graph
(build-proof-dependency-graph skill) → seal by providers from the proved packages (LP0 immediately; LP1 after
LP-LIFT and LP-PS).
