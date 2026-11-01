# Track LP: freeze proposal (DRAFT 7, the approval object)

Status: 2026-11-01. **Nothing is frozen.** This draft is the exact freeze text of the LP anchors under the rulings
the owner approved in D59 (OD-1…OD-6, OD-9, OD-11 option (b), with OD-2 and review 4 resolution (A)). D59 approves
the rulings, not the freeze: this text goes to an independent statement audit and then to the owner for approval of
the exact text, before anything enters `KAM/Frozen/` or `manifest/`. The body below has exactly one text per item;
earlier drafts, alternatives that were not chosen, and the review history are in Appendix A.

Source: [`source/MAIN.md`](source/MAIN.md) (sha256 `68e9167f…48c1b`) as amended by
[`source/AMENDMENTS.md`](source/AMENDMENTS.md) (sha256 `c887d1e2…51881`); cited as `LP:MAIN <item> (<lines>)`.

**What is approved, exactly.** The approval object is the set of 127 frozen file texts under
[`freeze/draft7/`](freeze/draft7/) (one public declaration per file, path `freeze/draft7/<frozen path>.txt`), together
with the manifest entry drafts [`freeze/draft7/manifest-entries.json`](freeze/draft7/manifest-entries.json). Every Lean
code block in this document is a byte-identical excerpt of those files (generated from the same records and
re-checked by script). The only bytes that change at freeze are the two placeholders `<APPROVAL-DATE>` and
`<DECISION>` in each module docstring, filled from the owner decision that approves this text, and the
`TBD at freeze` hash fields of the manifest entries.

**Counts.** 5 theorem anchors (LP0, LP1, LP1-H, LP2, LP2-H), 88 new definitions and
34 characterization theorems: 127 new frozen files. 19 already-frozen definitions are referenced
directly and reused unchanged.

**Verification** (details in [`freeze/verification-draft-7.txt`](freeze/verification-draft-7.txt)):
- **Closure** (Lean meta computation from the proved theorems): exactly the 85 new definitions of §4.2 that are in
  an anchor or characterization closure, plus the reused frozen ones of §4.1.
- **(a) Text elaborates:** each of the 127 files, in a scratch module whose imports are exactly the Mathlib and
  already-frozen imports of the file and of its draft dependencies (dependencies inlined in import order): 127/127
  exit 0; the only messages are the 39 expected "declaration uses `sorry`" warnings, one per theorem file.
- **(b) Bodies equal:** for all 88 definitions, the draft text read against the implementation names is `rfl`-equal
  to the implementation definition; all 88 types are alpha-equivalent with the same reducibility; 77 values are
  alpha-equivalent and the other 11 differ only in auxiliary proof constants (and, for `orderedCrossThreshold`, the
  inlined proof of `i < i + 1`).
- **(c) Verification:** all 39 theorems (5 anchors, 34 characterizations), stated verbatim, close by `exact` of the
  proved implementation theorem; their elaborated types are alpha-equivalent to the implementation statements; `#print
  axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for all 39.

## 1. The rulings in the text (D59)

| Ruling | Where it shows in the text |
|---|---|
| **OD-1** `C = ΣΛ − |L|`, no prograde premise | `strongAMD` (planar, `|totalMomentum|`) and `spatialSourceStrongAMD` (Euclidean `|L|`); no anchor has a sign, prograde, inclination or `L ≠ 0` premise. |
| **OD-2 + OD-11 (b)** source carriers | Thresholds only through `orderedStrongThreshold hn ⟨I, h⟩` on `OrderedActions ν` (with `2 ≤ n`); the strong AMD only through `sourceStrongAMD` / `spatialSourceStrongAMD`; canonical annulus radii and osculating elements only through `source*` / `spatialSource*` on `SourceCanonicalPhase`, `SourceOsculatingPhase`, `SpatialSourceCanonicalPhase`, `SpatialSourceOsculatingPhase`. Each carrier membership is a typing binder (`h₀`, `h`) or an existential output (`∃ hs`, `∃ ho`, `∃ hcht`). The total formulas are internal helpers in the definition closure (§4). The spatial anchors use the review-4 resolution (A) text. |
| **OD-3** `max ν = 1` kept | LP1, LP1-H, LP2, LP2-H carry `hνmax : ∃ i, ν i = 1` and `hνle : ∀ i, ν i ≤ 1`. LP0 has no `μ` and is stated for arbitrary positive `ν` (statement review 1, F5). The general-mass versions (`lp1_planar_strongAMD_safety_source_general`, `lp2_spatial_strongAMD_safety_source_general`) stay ordinary theorems. |
| **OD-4** `τ > n − 1` free, plus `τ = n − 1/2` | LP1, LP2 have `hτ : (n : ℝ) - 1 < τ` and horizon `T₀ exp (c μ^(−1/(2(τ+1))))`; LP1-H, LP2-H fix `τ = n − 1/2` and state the exponent explicitly as `μ ^ (-(1 / (2 * (n : ℝ) + 1)))`. |
| **OD-5 + OD-9** crossing notion | Canonical annuli (`dStar ≤` perihelion, adjacent gap `≥ dPair`), all star and all pair distances, and the actual-velocity osculating annuli with half gaps `dStar / 2`, `dPair / 2`; the N10 inequalities `Aosc * μ₀ ≤ dStar / 2`, `2 * (Aosc * μ₀) ≤ dPair / 2` are displayed outputs; the order in which `μ₀` is chosen is internal to the proof. |
| **OD-6** new anchors only | All anchors are new; `KAM.Planetary.planetaryExponentialSafety` (P-EXP-SAFE) is untouched, as is every existing frozen file. |

## 2. Anchors

| Id | Lean name | Frozen path | Provider (module; export) | Closed by (implementation theorem; module) | MAIN |
|---|---|---|---|---|---|
| LP0 | `KAM.Planetary.StrongAMD.planar_strongAMD_barrier` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean` | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDBarrier`; `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier` | `KAM.Planetary.StrongAMD.lp0_planar_barrier_source`; `KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary` | L5 (162–166), with L2–L4 (110–160); N11 |
| LP1 | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean` | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafety`; `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` | `KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source`; `KAM.Planetary.StrongAMD.PlanarSafety.Source` | T15 (502–506) with §1 (6)–(9) (69–93), L16 (508–529); N8, N10 |
| LP1-H | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean` | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyHalfInteger`; `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` | `KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source_halfInteger`; `KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary` | §1 (93) (τ = n − 1/2), T15 (502–506), L16 (508–529) |
| LP2 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean` | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafety`; `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source`; `KAM.Planetary.Spatial.SpatialSafety.Source` | T19 (599–603) with §1 (6)–(9) (69–93), L16 (508–529), d = 3 |
| LP2-H | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean` | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyHalfInteger`; `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` | `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_halfInteger`; `KAM.Planetary.Spatial.SpatialSafety.SourceCorollary` | §1 (93) (τ = n − 1/2), T19 (599–603), L16 (508–529), d = 3 |

Namespaces and paths follow the repository rule that the frozen path and the provider path mirror the namespace
(`KAM.X.Y.name` in `KAM/Frozen/X/Y/{Defs,Theorems}/Name.lean`, provider `KAM.Provider.X.Y.name` in
`KAM/Provider/X/Y/Name.lean`). Every anchor is sealed by the one-line body `by exact <provider export> <explicit
binders>` (the anchor guard's sealed-body rule); each provider is a one-line application of the proved
implementation theorem in the last column.

**The corollaries LP1-H and LP2-H.** Each is LP1 (resp. LP2) at `τ = n − 1/2` (admissible since `n − 1 < n − 1/2`)
together with the identity `2((n − 1/2) + 1) = 2n + 1`: it adds no mathematical content and no definition. I still
recommend freezing both as anchors, because OD-4 rules the corollary in and the headline exponent `1/(2n+1)` (D56) is
otherwise only implicit in the frozen record. Dropping them would lose nothing provable. Their texts are drafted in
any case (§3.3, §3.5). "Zohar's headline form" is used: the horizon is written with the explicit exponent
`μ ^ (-(1 / (2 * (n : ℝ) + 1)))`, not through `scaleExponent`, and the Diophantine exponent is `-((n : ℝ) - 1 / 2)`.

## 3. Anchor texts (exact)

Each block is the declaration region of the frozen file (from `namespace` to the end marker of the proof body).

### 3.1 LP0: the planar sharp barrier (`LP:MAIN L5 (162–166)` with L2–L4)

```lean
namespace KAM.Planetary.StrongAMD

/-- **LP0** (`LP:MAIN L5 (162–166), with L2–L4 (110–160); N11`): the planar sharp strong barrier
(full MAIN Lemma 5). -/
theorem planar_strongAMD_barrier {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
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
        ∀ h : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0,
        sourceStrongAMD (⟨z, h⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx *
            (1 - planeLength (keplerEccVector ν z a.upperIdx)) -
            keplerAxis ν z a.1 * (1 + planeLength (keplerEccVector ν z a.1))) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Reading: for fixed positive masses, a compact action set `U` inside the chamber and a margin `m > 0`, there are
`d⋆, d_pair > 0` (before the state) such that (i) every action vector `I ∈ U` and eccentricity list `e ∈ [0,1]ⁿ`
with `Σ I_i D(e_i) ≤ B(I) − m` has perihelia `≥ d⋆` and adjacent radial gaps `≥ d_pair`; (ii) there is a compact
collision-free set `K` of negative-energy states; and (iii) every negative-energy state with actions in `U` and strong
AMD `≤ B(Λ) − m` has perihelia `≥ d⋆`, adjacent annulus gaps `≥ d_pair`, star distances `≥ d⋆`, all pair distances
`≥ d_pair`, lies in `K`, and satisfies `|L_i| ≥ m` with every `L_i` of the sign of `L` (the invariable-frame
conclusion). This is MAIN L5 in full (statement review 1, F1). Under OD-11 (b) the strong AMD of the physical
state is `sourceStrongAMD ⟨z, h⟩` with the typing binder `h` placed after `hΛ`, exactly as §3.2 does for LP1; the
canonical radii use the frozen planar `keplerAxis`, `keplerEccVector` (inherited conventions; review 5, R5.4). The
deficit-list clause applies the literal threshold-unit formulas `actionAxis`, `eccDeficit` to an abstract `I ∈ U`
(`⊆` chamber) and `e ∈ [0,1]ⁿ`, never to a physical state.

### 3.2 LP1: planar strong-AMD exponential safety (`LP:MAIN T15 (502–506)`, §1 (6)–(9), L16)

```lean
namespace KAM.Planetary.StrongAMD

/-- **LP1** (`LP:MAIN T15 (502–506) with §1 (6)–(9) (69–93), L16 (508–529); N8, N10`): planar
strong-AMD exponential safety. -/
theorem planar_strongAMD_exponentialSafety {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
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
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

This is the §3b text of draft 6 (delta review 3: PASS) with the anchor name of §1 and the binder names `hνmax`,
`hνle` (review 4, R4.2). Reading (MAIN §1 (6)–(9), T15, L16, N10): the constants `μ₀, c, T₀, A_Λ, A_a, d⋆,
d_pair, A_osc, A_elem` are chosen before `μ` and the initial state; for every `0 < μ ≤ μ₀` and every initial state
with nonzero positions, negative energies, axes in `A`, the Diophantine condition (5) on `ω_i = ν_i³/Λ_i³` with the
ℓ¹ mode size, and strong AMD `≤ B(Λ) − δ`, the unique moving solution exists on `[−T, T]`,
`T = T₀ exp(c μ^(−1/(2(τ+1))))`, reconstructs the Newtonian `(1+n)`-body motion, and along it: ellipticity, chamber
membership with AMD `≤ B − δ/2`, `O(√μ)` action and axis drift, AMD drift `≤ n A_Λ √μ`, canonical perihelia and
adjacent gaps, all star and pair distances, and valid actual-velocity osculating ellipses through the current
position with L16's summed element error, endpoint errors `≤ A_osc μ` and half gaps. No hypothesis on the secular
dynamics.

### 3.3 LP1-H: the planar corollary at `τ = n − 1/2` (`LP:MAIN §1 (93)`)

```lean
namespace KAM.Planetary.StrongAMD

/-- **LP1-H** (`LP:MAIN §1 (93) (τ = n − 1/2), T15 (502–506), L16 (508–529)`): planar strong-AMD
exponential safety at τ = n − 1/2 (exponent 1/(2n+1)). -/
theorem planar_strongAMD_exponentialSafety_halfInteger {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-((n : ℝ) - 1 / 2)) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (n : ℝ) + 1))))
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
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Exactly the LP1 text with the binders `τ`, `hτ` removed, `-τ` replaced by `-((n : ℝ) - 1 / 2)` in the Diophantine
condition, and `-(1 / (2 * (τ + 1)))` replaced by `-(1 / (2 * (n : ℝ) + 1))` in the horizon (four textual changes;
see `diff` in the verification file).

### 3.4 LP2: spatial strong-AMD exponential safety (`LP:MAIN T19 (599–603)`, `d = 3`)

```lean
open KAM.Planetary.StrongAMD

namespace KAM.Planetary.Spatial

/-- **LP2** (`LP:MAIN T19 (599–603) with §1 (6)–(9) (69–93), L16 (508–529), d = 3`): spatial
strong-AMD exponential safety. -/
theorem spatial_strongAMD_exponentialSafety {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 /
              spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3)|) →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∧
            (∀ a : AdjIdx n, dPair ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.upperIdx -
                  spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.1) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                  spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1,
              (∀ i, spatialSourceOscEnergy (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  spatialSourceOscEcc (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 1 ∧
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ≤
                    spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  |spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerEccVector
                        (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ≤ Aelem * μ) ∧
              (∀ i, |spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ ∧
                  |spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ)
                      a.upperIdx -
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

This is the §3d text of draft 6 (review 4, R4.1 resolution (A); delta review 5: PASS WITH NOTES) with the anchor name
of §1. Premises are those of LP1 with the spatial objects; **no** prograde, inclination, nonzero-total-angular-momentum,
alignment or secular premise (MAIN T19; the frame alignment with `L` is a proof step). Every canonical element at
`z₀` and `z t` (axis, action, eccentricity vector, strong AMD, perihelion, aphelion) is a `spatialSource*`
restriction; the only raw total helpers in the text are `spatialKeplerEnergy`, `spatialOscEnergy` and
`spatialOscEcc`, each only as a sign condition inside a guarded predicate (§4.4).

### 3.5 LP2-H: the spatial corollary at `τ = n − 1/2` (`LP:MAIN §1 (93)`, T19)

```lean
open KAM.Planetary.StrongAMD

namespace KAM.Planetary.Spatial

/-- **LP2-H** (`LP:MAIN §1 (93) (τ = n − 1/2), T19 (599–603), L16 (508–529), d = 3`): spatial
strong-AMD exponential safety at τ = n − 1/2 (exponent 1/(2n+1)). -/
theorem spatial_strongAMD_exponentialSafety_halfInteger {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-((n : ℝ) - 1 / 2)) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 /
              spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3)|) →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (n : ℝ) + 1))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∧
            (∀ a : AdjIdx n, dPair ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.upperIdx -
                  spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.1) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                  spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1,
              (∀ i, spatialSourceOscEnergy (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  spatialSourceOscEcc (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 1 ∧
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ≤
                    spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  |spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerEccVector
                        (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ≤ Aelem * μ) ∧
              (∀ i, |spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ ∧
                  |spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ)
                      a.upperIdx -
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Exactly the LP2 text with the same four textual changes as LP1-H.

## 4. Definition freeze inventory under OD-11 (b)

### 4.1 Already frozen (reused; no new file)

Directly referenced by the draft texts:

- `KAM.Planetary.IsMovingSolutionOn` — `KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean`
- `KAM.Planetary.IsNewtonSolutionOn` — `KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean`
- `KAM.Iso.IsHamiltonianSolutionOn` — `KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean`
- `KAM.Planetary.MovingUniqueOn` — `KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean`
- `KAM.Planetary.NoCollision` — `KAM/Frozen/Planetary/Defs/NoCollision.lean`
- `KAM.Planetary.Phase` — `KAM/Frozen/Planetary/Defs/Phase.lean`
- `KAM.Planetary.actualMasses` — `KAM/Frozen/Planetary/Defs/ActualMasses.lean`
- `KAM.Planetary.barycentricPositions` — `KAM/Frozen/Planetary/Defs/BarycentricPositions.lean`
- `KAM.Planetary.barycentricVelocities` — `KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean`
- `KAM.Planetary.bodyVector` — `KAM/Frozen/Planetary/Defs/BodyVector.lean`
- `KAM.Planetary.keplerAction` — `KAM/Frozen/Planetary/Defs/KeplerAction.lean`
- `KAM.Planetary.keplerAxis` — `KAM/Frozen/Planetary/Defs/KeplerAxis.lean`
- `KAM.Planetary.keplerEccVector` — `KAM/Frozen/Planetary/Defs/KeplerEccVector.lean`
- `KAM.Planetary.keplerEnergy` — `KAM/Frozen/Planetary/Defs/KeplerEnergy.lean`
- `KAM.Planetary.planeCross` — `KAM/Frozen/Planetary/Defs/PlaneCross.lean`
- `KAM.Planetary.planeDot` — `KAM/Frozen/Planetary/Defs/PlaneDot.lean`
- `KAM.Planetary.planeLength` — `KAM/Frozen/Planetary/Defs/PlaneLength.lean`
- `KAM.Planetary.planeSq` — `KAM/Frozen/Planetary/Defs/PlaneSq.lean`
- `KAM.Planetary.totalMomentum` — `KAM/Frozen/Planetary/Defs/TotalMomentum.lean`

Through them the semantic closure also contains the frozen `KAM.Planetary.movingHamiltonian` and
`KAM.hamiltonianVectorField` (21 already-frozen definitions in all; verification §1).

These planar repository definitions are inherited conventions (D20/D25). In particular `keplerAxis`, `keplerAction`,
`keplerEccVector` and `keplerEnergy` are frozen total formulas whose physical meaning holds under their guards; the
planar anchors use them directly (review 1, F4; review 5, R5.4), while every **new** physical quantity goes through a
source carrier.

### 4.2 New definitions

Roles: **literal** = a literal formula or predicate of the source, faithful on its whole carrier; **carrier** = a
source carrier (subtype or its predicate); **source** = a source-facing definition on its carrier, one semantic unit
with its characterization theorems (§5); **internal** = a total helper that enters the frozen closure because a
source-facing definition or a literal predicate unfolds to it, certified as MAIN's object only on its carrier (OD-11
(b): "the total formulas stay internal helpers").

| # | Lean name | Role | Frozen path | Defined today in | Characterizations |
|---|---|---|---|---|---|
| 1 | `KAM.Fourier.modeSize` | literal | `KAM/Frozen/Fourier/Defs/ModeSize.lean` | `KAM.Fourier.Derivative` | — |
| 2 | `KAM.Planetary.StrongAMD.actionAxis` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/ActionAxis.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 3 | `KAM.Planetary.StrongAMD.chamber` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/Chamber.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 4 | `KAM.Planetary.StrongAMD.eccDeficit` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/EccDeficit.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 5 | `KAM.Planetary.StrongAMD.pairFeasible` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/PairFeasible.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 6 | `KAM.Planetary.StrongAMD.pairObjective` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/PairObjective.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 7 | `KAM.Planetary.StrongAMD.pairThreshold` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/PairThreshold.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | `orderedPairThreshold_isLeast`, `orderedPairThreshold_existsUnique_value` |
| 8 | `KAM.Planetary.StrongAMD.AdjIdx` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdx.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 9 | `KAM.Planetary.StrongAMD.AdjIdx.upperIdx` | literal | `KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 10 | `KAM.Planetary.StrongAMD.OrderedActions` | carrier | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedActions.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | — |
| 11 | `KAM.Planetary.StrongAMD.orderedPairThreshold` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedPairThreshold.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | `orderedPairThreshold_isLeast`, `orderedPairThreshold_existsUnique_value` |
| 12 | `KAM.Planetary.StrongAMD.orderedCrossThreshold` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | `orderedCrossThreshold_isLeast` |
| 13 | `KAM.Planetary.StrongAMD.orderedStrongThreshold` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean` | `KAM.Planetary.StrongAMD.Threshold.Defs` | `orderedStrongThreshold_isLeast` |
| 14 | `KAM.Planetary.StrongAMD.strongAMD` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/StrongAMD.lean` | `KAM.Planetary.StrongAMD.Momentum` | — |
| 15 | `KAM.Planetary.StrongAMD.keplerPeri` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/KeplerPeri.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 16 | `KAM.Planetary.StrongAMD.keplerApo` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/KeplerApo.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 17 | `KAM.Planetary.StrongAMD.oscVelocity` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscVelocity.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 18 | `KAM.Planetary.StrongAMD.oscParam` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscParam.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 19 | `KAM.Planetary.StrongAMD.oscEnergy` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEnergy.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 20 | `KAM.Planetary.StrongAMD.oscAxis` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscAxis.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 21 | `KAM.Planetary.StrongAMD.oscEccVector` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEccVector.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 22 | `KAM.Planetary.StrongAMD.oscEcc` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscEcc.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 23 | `KAM.Planetary.StrongAMD.oscPeri` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscPeri.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 24 | `KAM.Planetary.StrongAMD.oscApo` | internal | `KAM/Frozen/Planetary/StrongAMD/Defs/OscApo.lean` | `KAM.Planetary.StrongAMD.Osculating.Basic` | — |
| 25 | `KAM.Planetary.StrongAMD.SourceCanonicalPhase` | carrier | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `sourceKepler_axis_pos`, `sourceKepler_ecc_le_one` |
| 26 | `KAM.Planetary.StrongAMD.SourceOsculatingPhase` | carrier | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 27 | `KAM.Planetary.StrongAMD.sourceStrongAMD` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceStrongAMD.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `sourceStrongAMD_nonneg`, `sum_action_mul_eccDeficit_le_sourceStrongAMD` |
| 28 | `KAM.Planetary.StrongAMD.sourceKeplerPeri` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerPeri.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `sourceKeplerPeri_le_planeLength` |
| 29 | `KAM.Planetary.StrongAMD.sourceKeplerApo` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerApo.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `planeLength_le_sourceKeplerApo` |
| 30 | `KAM.Planetary.StrongAMD.sourceOscVelocity` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscVelocity.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 31 | `KAM.Planetary.StrongAMD.sourceOscParam` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscParam.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 32 | `KAM.Planetary.StrongAMD.sourceOscEnergy` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEnergy.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 33 | `KAM.Planetary.StrongAMD.sourceOscAxis` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscAxis.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `sourceOscAxis_pos` |
| 34 | `KAM.Planetary.StrongAMD.sourceOscEccVector` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEccVector.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 35 | `KAM.Planetary.StrongAMD.sourceOscEcc` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEcc.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | — |
| 36 | `KAM.Planetary.StrongAMD.sourceOscPeri` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscPeri.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `sourceOscPeri_pos`, `sourceOscPeri_le_planeLength` |
| 37 | `KAM.Planetary.StrongAMD.sourceOscApo` | source | `KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscApo.lean` | `KAM.Planetary.StrongAMD.SourceCarrier` | `planeLength_le_sourceOscApo` |
| 38 | `KAM.Planetary.Spatial.spaceDot` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean` | `KAM.Planetary.Spatial.Vector` | — |
| 39 | `KAM.Planetary.Spatial.spaceSq` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean` | `KAM.Planetary.Spatial.Vector` | — |
| 40 | `KAM.Planetary.Spatial.spaceLength` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean` | `KAM.Planetary.Spatial.Vector` | — |
| 41 | `KAM.Planetary.Spatial.spaceCross` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean` | `KAM.Planetary.Spatial.Vector` | — |
| 42 | `KAM.Planetary.Spatial.bodyVector3` | literal | `KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean` | `KAM.Planetary.Spatial.Vector` | — |
| 43 | `KAM.Planetary.Spatial.planetAngularMomentum3` | literal | `KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 44 | `KAM.Planetary.Spatial.angularMomentum3` | literal | `KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 45 | `KAM.Planetary.Spatial.spatialHamiltonian` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean` | `KAM.Planetary.Spatial.Model` | — |
| 46 | `KAM.Planetary.Spatial.SpatialNoCollision` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean` | `KAM.Planetary.Spatial.Model` | — |
| 47 | `KAM.Planetary.Spatial.IsSpatialMovingSolutionOn` | literal | `KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean` | `KAM.Planetary.Spatial.Model` | — |
| 48 | `KAM.Planetary.Spatial.SpatialMovingUniqueOn` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean` | `KAM.Planetary.Spatial.Model` | — |
| 49 | `KAM.Planetary.Spatial.spatialBarycentricPositions` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean` | `KAM.Planetary.Spatial.Newton` | — |
| 50 | `KAM.Planetary.Spatial.spatialBarycentricVelocities` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean` | `KAM.Planetary.Spatial.Newton` | — |
| 51 | `KAM.Planetary.Spatial.spatialMasses` | literal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean` | `KAM.Planetary.Spatial.Newton` | — |
| 52 | `KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn` | literal | `KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean` | `KAM.Planetary.Spatial.Newton` | — |
| 53 | `KAM.Planetary.Spatial.spatialKeplerEnergy` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 54 | `KAM.Planetary.Spatial.spatialKeplerAxis` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 55 | `KAM.Planetary.Spatial.spatialKeplerAction` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 56 | `KAM.Planetary.Spatial.spatialKeplerEccVector` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 57 | `KAM.Planetary.Spatial.SpatialNegativeEnergy` | carrier | `KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 58 | `KAM.Planetary.Spatial.SpatialElliptic` | carrier | `KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean` | `KAM.Planetary.Spatial.Elements` | — |
| 59 | `KAM.Planetary.Spatial.spatialKeplerPeri` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 60 | `KAM.Planetary.Spatial.spatialKeplerApo` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 61 | `KAM.Planetary.Spatial.spatialOscVelocity` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 62 | `KAM.Planetary.Spatial.spatialOscParam` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 63 | `KAM.Planetary.Spatial.spatialOscEnergy` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 64 | `KAM.Planetary.Spatial.spatialOscAxis` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 65 | `KAM.Planetary.Spatial.spatialOscEccVector` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 66 | `KAM.Planetary.Spatial.spatialOscEcc` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 67 | `KAM.Planetary.Spatial.spatialOscPeri` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 68 | `KAM.Planetary.Spatial.spatialOscApo` | internal | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 69 | `KAM.Planetary.Spatial.SpatialOscPhase` | carrier | `KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 70 | `KAM.Planetary.Spatial.SpatialSourceCanonicalPhase` | carrier | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean` | `KAM.Planetary.Spatial.SourceCarrier` | — |
| 71 | `KAM.Planetary.Spatial.SpatialSourceOsculatingPhase` | carrier | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean` | `KAM.Planetary.Spatial.SourceCarrier` | — |
| 72 | `KAM.Planetary.Spatial.spatialSourceKeplerAxis` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean` | `KAM.Planetary.Spatial.SourceCarrier` | `spatialSourceKeplerAxis_pos` |
| 73 | `KAM.Planetary.Spatial.spatialSourceKeplerAction` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean` | `KAM.Planetary.Spatial.SourceCarrier` | `spatialSourceKeplerAction_pos`, `spatialSourceKeplerAction_sq` |
| 74 | `KAM.Planetary.Spatial.spatialSourceKeplerEccVector` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean` | `KAM.Planetary.Spatial.SourceCarrier` | — |
| 75 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean` | `KAM.Planetary.Spatial.SourceCarrier` | `spatialSourceKeplerEcc_sq`, `spatialSourceKeplerEcc_nonneg`, `spatialSourceKeplerEcc_le_one` |
| 76 | `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean` | `KAM.Planetary.Spatial.SourceCarrier` | `spatialSourceKeplerEcc_sq`, `spatialSourcePlanetAngularMomentum_length`, `spatialSourcePlanetAngularMomentum_length_le` |
| 77 | `KAM.Planetary.Spatial.spatialSourceAngularMomentum` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean` | `KAM.Planetary.Spatial.SourceCarrier` | — |
| 78 | `KAM.Planetary.Spatial.spatialSourceStrongAMD` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean` | `KAM.Planetary.Spatial.SourceCarrier` | `spatialSourceStrongAMD_nonneg`, `spatialSourceAction_mul_eccDeficit_le` |
| 79 | `KAM.Planetary.Spatial.spatialSourceKeplerPeri` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceKeplerPeri_le_length` |
| 80 | `KAM.Planetary.Spatial.spatialSourceKeplerApo` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceKeplerApo_ge_length` |
| 81 | `KAM.Planetary.Spatial.spatialSourceOscVelocity` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscVelocity.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 82 | `KAM.Planetary.Spatial.spatialSourceOscParam` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscParam_pos` |
| 83 | `KAM.Planetary.Spatial.spatialSourceOscEnergy` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscEnergy_neg` |
| 84 | `KAM.Planetary.Spatial.spatialSourceOscAxis` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscAxis_pos` |
| 85 | `KAM.Planetary.Spatial.spatialSourceOscEccVector` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | — |
| 86 | `KAM.Planetary.Spatial.spatialSourceOscEcc` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscEcc_lt_one`, `spatialSourceOscEcc_nonneg` |
| 87 | `KAM.Planetary.Spatial.spatialSourceOscPeri` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscPeri_pos`, `spatialSourceOscPeri_le_length` |
| 88 | `KAM.Planetary.Spatial.spatialSourceOscApo` | source | `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean` | `KAM.Planetary.Spatial.Osculating.Basic` | `spatialSourceOscApo_ge_length` |

Notes.
- **Not in the closure, therefore not frozen.** The raw total thresholds `crossThreshold`, `starThreshold`,
  `strongThreshold` (the carrier definitions do not unfold to them; they occur only in the implementation's `rfl`
  equations `orderedCrossThreshold_eq`, `orderedStrongThreshold_eq`), and the spatial `spatialStrongAMD`,
  `spatialStrongAMDOn` (`spatialSourceStrongAMD` is defined directly from `spatialSourceKeplerAction` and
  `spatialSourceAngularMomentum`). Draft 6 §4b listed them as internal helpers "in the closure"; Lean's closure
  computation shows they are not (verification file, closure listing).
- **Frozen although outside every anchor closure.** `sourceOscVelocity`, `sourceOscParam` (planar) and
  `spatialSourceOscVelocity` are members of the source-facing set of draft 6 §3b/§4b (review 1 F4, review 4 R4.3);
  `spatialSourceOscParam` enters through its characterization `spatialSourceOscParam_pos`. They are frozen with the
  rest of the (b) set; no anchor depends on them.
- **One body differs from the implementation by a proof term.** In `orderedCrossThreshold` the implementation passes
  the theorem `AdjIdx.lt_upperIdx`; a frozen definition file holds exactly one declaration and cannot use an unfrozen
  theorem, so the draft inlines the proof `(Nat.lt_succ_self a.1.val)`. The values are definitionally equal (proof
  irrelevance); check (b) confirms `rfl`.
- **`SpatialElliptic` stays a `def … : Type`** (review 4, R4.7: optional). Changing it to `abbrev` would change
  reducibility for every implementation proof; the anchors use the `abbrev` `SpatialSourceCanonicalPhase` of it.
- **Docstrings.** The frozen docstring of `spatialKeplerAxis` names the canonical (not osculating) semi-major axis
  (review 4, R4.6); the four spatial radial-incidence characterizations are no longer called "tangency" (R4.5).
  Every other docstring is the implementation's.

### 4.3 Definition texts (exact)

**ℓ¹ mode size** (namespace `KAM.Fourier`; files `ModeSize.lean`):

```lean
/-- The ℓ¹ size of an integer Fourier index, as a real number. -/
def modeSize {n : ℕ} (k : Fin n → ℤ) : ℝ := ∑ j, |(k j : ℝ)|
```

**Thresholds (MAIN §1 (3), L4)** (namespace `KAM.Planetary.StrongAMD`; files `ActionAxis.lean`, `Chamber.lean`, `EccDeficit.lean`, `PairFeasible.lean`, `PairObjective.lean`, `PairThreshold.lean`, `AdjIdx.lean`, `AdjIdxUpperIdx.lean`, `OrderedActions.lean`, `OrderedPairThreshold.lean`, `OrderedCrossThreshold.lean`, `OrderedStrongThreshold.lean`):

```lean
/-- `a_i(I) = (I_i / ν_i)²` (`LP:MAIN` §1 (45)). -/
def actionAxis {n : ℕ} (ν I : Fin n → ℝ) (i : Fin n) : ℝ := (I i / ν i) ^ 2

/-- The action chamber `𝒬 = {I : I_i > 0, a_1 < ⋯ < a_n}` (`LP:MAIN` §1 (43)). -/
def chamber {n : ℕ} (ν : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {I | (∀ i, 0 < I i) ∧ ∀ i j, i < j → actionAxis ν I i < actionAxis ν I j}

/-- The eccentricity deficit `D(u) = 1 - √(1 - u²)` (used on `u ∈ [0,1]`). -/
def eccDeficit (u : ℝ) : ℝ := 1 - Real.sqrt (1 - u ^ 2)

/-- The feasible set `{(u,v) ∈ [0,1]² : a_i(1+u) ≥ a_j(1-v)}` of the pair `(i,j)`. -/
def pairFeasible {n : ℕ} (ν I : Fin n → ℝ) (i j : Fin n) : Set (ℝ × ℝ) :=
  {uv | uv.1 ∈ Set.Icc (0 : ℝ) 1 ∧ uv.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    actionAxis ν I j * (1 - uv.2) ≤ actionAxis ν I i * (1 + uv.1)}

/-- The pair objective `I_i D(u) + I_j D(v)`. -/
def pairObjective {n : ℕ} (I : Fin n → ℝ) (i j : Fin n) (uv : ℝ × ℝ) : ℝ :=
  I i * eccDeficit uv.1 + I j * eccDeficit uv.2

/-- The pair threshold `B_ij(I)`, a literal `sInf` of the objective over the feasible set. -/
def pairThreshold {n : ℕ} (ν I : Fin n → ℝ) (i j : Fin n) : ℝ :=
  sInf (pairObjective I i j '' pairFeasible ν I i j)

/-- The index type of adjacent pairs `(i, i+1)` with `i + 1 < n`. -/
abbrev AdjIdx (n : ℕ) : Type := {i : Fin n // i.val + 1 < n}

/-- The upper index `i + 1` of an adjacent pair. -/
def AdjIdx.upperIdx {n : ℕ} (a : AdjIdx n) : Fin n := ⟨a.1.val + 1, a.2⟩

/-- The source carrier: action vectors in the chamber `𝒬`. -/
abbrev OrderedActions {n : ℕ} (ν : Fin n → ℝ) : Type := {I : Fin n → ℝ // I ∈ chamber ν}

/-- `B_ij` on the carrier `𝒬` (OD-2): the total helper `pairThreshold`, with the ordering
proof as typing data. -/
def orderedPairThreshold {n : ℕ} {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n)
    (_hij : i < j) : ℝ :=
  pairThreshold ν I.1 i j

/-- `B_cross` on the carrier `𝒬` (OD-2), for `2 ≤ n` (the hypothesis is typing data: for `n = 1`
the adjacent family is empty and the real `⨅` would return `0`); a literal infimum of carrier pair
thresholds. -/
def orderedCrossThreshold {n : ℕ} {ν : Fin n → ℝ} (_hn : 2 ≤ n) (I : OrderedActions ν) : ℝ :=
  ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx (Nat.lt_succ_self a.1.val)

/-- `B` on the carrier `𝒬` (OD-2), for `2 ≤ n` (the hypothesis is typing data). -/
def orderedStrongThreshold {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) : ℝ :=
  min (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i)
```

**Planar strong AMD, canonical annulus radii, osculating elements (internal helpers)** (namespace `KAM.Planetary.StrongAMD`; files `StrongAMD.lean`, `KeplerPeri.lean`, `KeplerApo.lean`, `OscVelocity.lean`, `OscParam.lean`, `OscEnergy.lean`, `OscAxis.lean`, `OscEccVector.lean`, `OscEcc.lean`, `OscPeri.lean`, `OscApo.lean`):

```lean
/-- The strong AMD `C = Σ_i Λ_i - |L|` (`LP:MAIN §1 (2)`), with `|L|` the absolute value of the
total angular momentum. -/
def strongAMD {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 2)) : ℝ :=
  (∑ i, keplerAction ν z i) - |totalMomentum z|

/-- Canonical perihelion `a_i (1 - e_i)` (`a_i = keplerAxis`, `e_i = |keplerEccVector|`). -/
def keplerPeri {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))

/-- Canonical aphelion `a_i (1 + e_i)`. -/
def keplerApo {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  keplerAxis ν z i * (1 + planeLength (keplerEccVector ν z i))

/-- The actual heliocentric velocity `V_i = p_i/ν_i + μ ∑_j p_j` (`LP:MAIN (10)`, `L16`). -/
def oscVelocity {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : Fin 2 → ℝ :=
  (1 / ν i) • bodyVector z.2 i + μ • ∑ j, bodyVector z.2 j

/-- The gravitational parameter `k_i = 1 + μ ν_i`. -/
def oscParam {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := 1 + μ * ν i

/-- `E_i^osc = |V_i|²/2 - k_i/|q_i|` (`LP:MAIN L16 (42)`). -/
def oscEnergy {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  planeSq (oscVelocity ν μ z i) / 2 - oscParam ν μ i / planeLength (bodyVector z.1 i)

/-- `a_i^osc = -k_i/(2 E_i^osc)` (`LP:MAIN L16 (42)`). -/
def oscAxis {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  -oscParam ν μ i / (2 * oscEnergy ν μ z i)

/-- `𝐞_i^osc = ((|V_i|² - k_i/|q_i|) q_i - (q_i·V_i) V_i)/k_i` (`LP:MAIN L16 (42)`). -/
def oscEccVector {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : Fin 2 → ℝ :=
  (1 / oscParam ν μ i) •
    ((planeSq (oscVelocity ν μ z i) - oscParam ν μ i / planeLength (bodyVector z.1 i)) •
        bodyVector z.1 i -
      planeDot (bodyVector z.1 i) (oscVelocity ν μ z i) • oscVelocity ν μ z i)

/-- `e_i^osc = |𝐞_i^osc|` (`LP:MAIN L16 (42)`). -/
def oscEcc {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  planeLength (oscEccVector ν μ z i)

/-- Osculating perihelion `a^osc (1 - e^osc)`. -/
def oscPeri {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  oscAxis ν μ z i * (1 - oscEcc ν μ z i)

/-- Osculating aphelion `a^osc (1 + e^osc)`. -/
def oscApo {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  oscAxis ν μ z i * (1 + oscEcc ν μ z i)
```

**Planar source carriers and source-facing definitions** (namespace `KAM.Planetary.StrongAMD`; files `SourceCanonicalPhase.lean`, `SourceOsculatingPhase.lean`, `SourceStrongAMD.lean`, `SourceKeplerPeri.lean`, `SourceKeplerApo.lean`, `SourceOscVelocity.lean`, `SourceOscParam.lean`, `SourceOscEnergy.lean`, `SourceOscAxis.lean`, `SourceOscEccVector.lean`, `SourceOscEcc.lean`, `SourceOscPeri.lean`, `SourceOscApo.lean`):

```lean
/-- Source canonical phases (`LP:MAIN §1 (31–37)`): positive masses, and every planet at a
nonzero position with negative Kepler energy. -/
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
def sourceStrongAMD {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) : ℝ := strongAMD ν z.1

/-- Canonical perihelion on source canonical phases. -/
def sourceKeplerPeri {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerPeri ν z.1 i

/-- Canonical aphelion on source canonical phases. -/
def sourceKeplerApo {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerApo ν z.1 i

/-- Actual heliocentric velocity on source osculating phases. -/
def sourceOscVelocity {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : Fin 2 → ℝ := oscVelocity ν μ z.1 i

/-- Gravitational parameter `1 + μ ν_i` on source osculating phases. -/
def sourceOscParam {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (_z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscParam ν μ i

/-- Osculating energy on source osculating phases. -/
def sourceOscEnergy {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscEnergy ν μ z.1 i

/-- Osculating semi-major axis on source osculating phases. -/
def sourceOscAxis {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscAxis ν μ z.1 i

/-- Osculating eccentricity vector on source osculating phases. -/
def sourceOscEccVector {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : Fin 2 → ℝ := oscEccVector ν μ z.1 i

/-- Osculating eccentricity on source osculating phases. -/
def sourceOscEcc {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscEcc ν μ z.1 i

/-- Osculating perihelion on source osculating phases. -/
def sourceOscPeri {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscPeri ν μ z.1 i

/-- Osculating aphelion on source osculating phases. -/
def sourceOscApo {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscApo ν μ z.1 i
```

**Spatial vectors and angular momenta (literal)** (namespace `KAM.Planetary.Spatial`; files `SpaceDot.lean`, `SpaceSq.lean`, `SpaceLength.lean`, `SpaceCross.lean`, `BodyVector3.lean`, `PlanetAngularMomentum3.lean`, `AngularMomentum3.lean`):

```lean
/-- Euclidean scalar product on `Fin 3 → ℝ`. -/
def spaceDot (v w : Fin 3 → ℝ) : ℝ := ∑ k, v k * w k

/-- Squared Euclidean length on `Fin 3 → ℝ`. -/
def spaceSq (v : Fin 3 → ℝ) : ℝ := ∑ k, v k ^ 2

/-- Euclidean length on `Fin 3 → ℝ`, independent of the ambient Pi sup norm. -/
def spaceLength (v : Fin 3 → ℝ) : ℝ := Real.sqrt (spaceSq v)

/-- The standard cross product on `Fin 3 → ℝ`, written out in components. -/
def spaceCross (v w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]

/-- Extract the three Cartesian coordinates of body `i`. -/
def bodyVector3 {n : ℕ} (q : Fin (n * 3) → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  fun k => q (finProdFinEquiv (i, k))

/-- Individual angular momentum `L_i = q_i × p_i`. -/
def planetAngularMomentum3 {n : ℕ} (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)

/-- Total angular momentum `L = Σ_i q_i × p_i`. -/
def angularMomentum3 {n : ℕ} (z : Phase (n * 3)) : Fin 3 → ℝ :=
  ∑ i, spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)
```

**Spatial model and Newtonian reconstruction** (namespace `KAM.Planetary.Spatial`; files `SpatialHamiltonian.lean`, `SpatialNoCollision.lean`, `IsSpatialMovingSolutionOn.lean`, `SpatialMovingUniqueOn.lean`, `SpatialBarycentricPositions.lean`, `SpatialBarycentricVelocities.lean`, `SpatialMasses.lean`, `IsSpatialNewtonSolutionOn.lean`):

```lean
/-- The exact spatial Hamiltonian `H_μ` (`LP:MAIN §1 (1)`, `d = 3`): positions `q_i` and scaled
canonical momenta `p_i` in `Phase (n * 3)`, masses `m_i = μ ν_i`, central Kepler parameter one. -/
def spatialHamiltonian {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) : ℝ :=
  (∑ i, (spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i))) +
    μ * (spaceSq (∑ i, bodyVector3 z.2 i) / 2 -
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j))

/-- The open physical domain of `H_μ`: no planet at the star and no two planets together. -/
def SpatialNoCollision {n : ℕ} (q : Fin (n * 3) → ℝ) : Prop :=
  (∀ i, 0 < spaceLength (bodyVector3 q i)) ∧
  (∀ i j, i ≠ j → 0 < spaceLength (bodyVector3 q i - bodyVector3 q j))

/-- A genuine spatial moving-Sun solution on `J`: the frozen differentiability-guarded Hamiltonian
ODE for `H_μ` together with collision exclusion (`LP:MAIN §1 (1)`). -/
def IsSpatialMovingSolutionOn {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  KAM.Iso.IsHamiltonianSolutionOn (spatialHamiltonian ν μ) Set.univ J z ∧
    ∀ t ∈ J, SpatialNoCollision (z t).1

/-- Agreement with every other local spatial solution on its overlap with the certified interval
(the pattern of the frozen planar `MovingUniqueOn`). -/
def SpatialMovingUniqueOn {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  ∀ (U : Set ℝ) (w : ℝ → Phase (n * 3)), IsOpen U → Convex ℝ U → 0 ∈ U →
    w 0 = z 0 → IsSpatialMovingSolutionOn ν μ U w → ∀ t ∈ U ∩ J, w t = z t

/-- Barycentric positions (star first, then the planets) from heliocentric `q`, with `m₀ = 1`. -/
def spatialBarycentricPositions {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) :=
  let x0 := (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 q i
  Fin.cons x0 (fun i => x0 + bodyVector3 q i)

/-- Barycentric velocities: actual planet momenta are `μ p`, total momentum zero. -/
def spatialBarycentricVelocities {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (p : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) :=
  Fin.cons ((-μ) • ∑ i, bodyVector3 p i) (fun i => (1 / ν i) • bodyVector3 p i)

/-- The masses `(1, μ ν_1, …, μ ν_n)`. -/
def spatialMasses {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 (fun i => μ * ν i)

/-- Finite-interval Newton equations in dimension three, with Euclidean lengths (`G = 1`). -/
def IsSpatialNewtonSolutionOn {N : ℕ} (mass : Fin N → ℝ) (J : Set ℝ)
    (Q V : ℝ → Fin N → (Fin 3 → ℝ)) : Prop :=
  (∀ t ∈ J, ∀ i j, i ≠ j → 0 < spaceLength (Q t j - Q t i)) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => Q s i) (V t i) t) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => V s i)
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      (mass j / spaceLength (Q t j - Q t i) ^ 3) • (Q t j - Q t i)) t)
```

**Spatial canonical elements and carrier** (namespace `KAM.Planetary.Spatial`; files `SpatialKeplerEnergy.lean`, `SpatialKeplerAxis.lean`, `SpatialKeplerAction.lean`, `SpatialKeplerEccVector.lean`, `SpatialNegativeEnergy.lean`, `SpatialElliptic.lean`, `SpatialKeplerPeri.lean`, `SpatialKeplerApo.lean`):

```lean
/-- Total Kepler energy `ν_i E_i` of planet `i` (planar convention). -/
def spatialKeplerEnergy {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i)

/-- Canonical semi-major axis `a_i = −ν_i/(2 ν_i E_i) = −1/(2 E_i)`. -/
def spatialKeplerAxis {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  -ν i / (2 * spatialKeplerEnergy ν z i)

/-- Kepler action `Λ_i = ν_i √a_i`. -/
def spatialKeplerAction {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  ν i * Real.sqrt (spatialKeplerAxis ν z i)

/-- Eccentricity vector `𝐞_i = (|v|² − 1/|q|) q − (q·v) v` with `v = p/ν`. -/
def spatialKeplerEccVector {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  let q := bodyVector3 z.1 i
  let p := bodyVector3 z.2 i
  (spaceSq p / ν i ^ 2 - 1 / spaceLength q) • q - (spaceDot q p / ν i ^ 2) • p

/-- The source carrier of the Kepler elements: positive masses, no planet at the star, negative
energy of every planet. -/
def SpatialNegativeEnergy {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) : Prop :=
  ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0

/-- Phase points of the carrier. -/
def SpatialElliptic {n : ℕ} (ν : Fin n → ℝ) : Type :=
  {z : Phase (n * 3) // SpatialNegativeEnergy ν z}

/-- Canonical perihelion `a_i (1 - e_i)`. -/
def spatialKeplerPeri {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν z i))

/-- Canonical aphelion `a_i (1 + e_i)`. -/
def spatialKeplerApo {n : ℕ} (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialKeplerAxis ν z i * (1 + spaceLength (spatialKeplerEccVector ν z i))
```

**Spatial osculating elements and carrier** (namespace `KAM.Planetary.Spatial`; files `SpatialOscVelocity.lean`, `SpatialOscParam.lean`, `SpatialOscEnergy.lean`, `SpatialOscAxis.lean`, `SpatialOscEccVector.lean`, `SpatialOscEcc.lean`, `SpatialOscPeri.lean`, `SpatialOscApo.lean`, `SpatialOscPhase.lean`):

```lean
/-- The actual heliocentric velocity `V_i = p_i/ν_i + μ ∑_j p_j` (`LP:MAIN (10)`, `L16`, `d = 3`).
-/
def spatialOscVelocity {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3))
    (i : Fin n) : Fin 3 → ℝ :=
  (1 / ν i) • bodyVector3 z.2 i + μ • ∑ j, bodyVector3 z.2 j

/-- The gravitational parameter `k_i = 1 + μ ν_i`. -/
def spatialOscParam {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := 1 + μ * ν i

/-- `E_i^osc = |V_i|²/2 - k_i/|q_i|` (`LP:MAIN L16 (42)`). -/
def spatialOscEnergy {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceSq (spatialOscVelocity ν μ z i) / 2 -
    spatialOscParam ν μ i / spaceLength (bodyVector3 z.1 i)

/-- `a_i^osc = -k_i/(2 E_i^osc)` (`LP:MAIN L16 (42)`). -/
def spatialOscAxis {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  -spatialOscParam ν μ i / (2 * spatialOscEnergy ν μ z i)

/-- `𝐞_i^osc = ((|V_i|² - k_i/|q_i|) q_i - (q_i·V_i) V_i)/k_i` (`LP:MAIN L16 (42)`). -/
def spatialOscEccVector {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3))
    (i : Fin n) : Fin 3 → ℝ :=
  (1 / spatialOscParam ν μ i) •
    ((spaceSq (spatialOscVelocity ν μ z i) -
        spatialOscParam ν μ i / spaceLength (bodyVector3 z.1 i)) • bodyVector3 z.1 i -
      spaceDot (bodyVector3 z.1 i) (spatialOscVelocity ν μ z i) • spatialOscVelocity ν μ z i)

/-- `e_i^osc = |𝐞_i^osc|` (`LP:MAIN L16 (42)`), Euclidean length. -/
def spatialOscEcc {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceLength (spatialOscEccVector ν μ z i)

/-- Osculating perihelion `a^osc (1 - e^osc)`. -/
def spatialOscPeri {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z i * (1 - spatialOscEcc ν μ z i)

/-- Osculating aphelion `a^osc (1 + e^osc)`. -/
def spatialOscApo {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z i * (1 + spatialOscEcc ν μ z i)

/-- Valid actual-velocity osculating states (`LP:MAIN L16`, nondegenerate ellipses): positive
masses,
`μ > 0`, and for every planet `|q_i| > 0`, `E_i^osc < 0`, `e_i^osc < 1`. -/
abbrev SpatialOscPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 3) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialOscEnergy ν μ z i < 0 ∧
      spatialOscEcc ν μ z i < 1}
```

**Spatial source carriers and source-facing definitions** (namespace `KAM.Planetary.Spatial`; files `SpatialSourceCanonicalPhase.lean`, `SpatialSourceOsculatingPhase.lean`, `SpatialSourceKeplerAxis.lean`, `SpatialSourceKeplerAction.lean`, `SpatialSourceKeplerEccVector.lean`, `SpatialSourceKeplerEcc.lean`, `SpatialSourcePlanetAngularMomentum.lean`, `SpatialSourceAngularMomentum.lean`, `SpatialSourceStrongAMD.lean`, `SpatialSourceKeplerPeri.lean`, `SpatialSourceKeplerApo.lean`, `SpatialSourceOscVelocity.lean`, `SpatialSourceOscParam.lean`, `SpatialSourceOscEnergy.lean`, `SpatialSourceOscAxis.lean`, `SpatialSourceOscEccVector.lean`, `SpatialSourceOscEcc.lean`, `SpatialSourceOscPeri.lean`, `SpatialSourceOscApo.lean`):

```lean
/-- The canonical source carrier (`LP:MAIN §1 (2)`): phase points with positive masses, no planet
at the star and negative Kepler energy of every planet.  This is SP-MODEL's `SpatialElliptic ν`. -/
abbrev SpatialSourceCanonicalPhase (n : ℕ) (ν : Fin n → ℝ) : Type := SpatialElliptic ν

/-- The osculating source carrier (`LP:MAIN L16`): SP-OSC's `SpatialOscPhase n ν μ`. -/
abbrev SpatialSourceOsculatingPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) : Type :=
  SpatialOscPhase n ν μ

/-- `a_i` on the canonical carrier. -/
def spatialSourceKeplerAxis {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : ℝ := spatialKeplerAxis ν z.1 i

/-- `Λ_i = ν_i √a_i` on the canonical carrier. -/
def spatialSourceKeplerAction {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : ℝ := spatialKeplerAction ν z.1 i

/-- The eccentricity vector `𝐞_i` on the canonical carrier. -/
def spatialSourceKeplerEccVector {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : Fin 3 → ℝ := spatialKeplerEccVector ν z.1 i

/-- The eccentricity `e_i = |𝐞_i|` on the canonical carrier. -/
def spatialSourceKeplerEcc {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : ℝ := spaceLength (spatialSourceKeplerEccVector z i)

/-- The individual angular momentum `L_i = q_i × p_i` on the canonical carrier. -/
def spatialSourcePlanetAngularMomentum {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : Fin 3 → ℝ := planetAngularMomentum3 z.1 i

/-- The total angular momentum `L = Σ_i q_i × p_i` on the canonical carrier. -/
def spatialSourceAngularMomentum {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) :
    Fin 3 → ℝ := angularMomentum3 z.1

/-- The strong AMD `C = Σ_i Λ_i − |L|` on the canonical carrier. -/
def spatialSourceStrongAMD {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) : ℝ :=
  (∑ i, spatialSourceKeplerAction z i) - spaceLength (spatialSourceAngularMomentum z)

/-- `a (1 - e)` on the canonical negative-energy carrier. -/
def spatialSourceKeplerPeri {n : ℕ} {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) : ℝ :=
  spatialKeplerPeri ν z.1 i

/-- `a (1 + e)` on the canonical negative-energy carrier. -/
def spatialSourceKeplerApo {n : ℕ} {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) : ℝ :=
  spatialKeplerApo ν z.1 i

/-- `V_i` on the valid osculating carrier. -/
def spatialSourceOscVelocity {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : Fin 3 → ℝ := spatialOscVelocity ν μ z.1 i

/-- `k_i` on the valid osculating carrier. -/
def spatialSourceOscParam {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (_z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscParam ν μ i

/-- `E_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEnergy {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscEnergy ν μ z.1 i

/-- `a_i^osc` on the valid osculating carrier. -/
def spatialSourceOscAxis {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z.1 i

/-- `𝐞_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEccVector {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : Fin 3 → ℝ := spatialOscEccVector ν μ z.1 i

/-- `e_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEcc {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscEcc ν μ z.1 i

/-- `a^osc (1 - e^osc)` on the valid osculating carrier. -/
def spatialSourceOscPeri {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscPeri ν μ z.1 i

/-- `a^osc (1 + e^osc)` on the valid osculating carrier. -/
def spatialSourceOscApo {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : ℝ :=
  spatialOscApo ν μ z.1 i
```

### 4.4 Raw total helpers that occur in anchor texts (review 5, R5.1)

The total formulas stay **internal implementation helpers in the definition closure** and are not certified as
MAIN's objects off their carriers: `strongAMD`, `keplerPeri/Apo`, `oscVelocity/oscParam/oscEnergy/oscAxis/
oscEccVector/oscEcc/oscPeri/oscApo`, `pairThreshold`, `spatialKeplerEnergy`, `spatialKeplerAxis/Action/EccVector`,
`spatialKeplerPeri/Apo`, `spatialHamiltonian` and `spatialOsc*`. In the anchor texts only the following occur
directly, each only as a sign condition inside a guarded predicate:

- planar: `keplerEnergy` (frozen) in the physical premise and in `h₀`, `h`, `hs`; `oscEnergy` and `oscEcc` in the
  osculating carrier predicate (`ho`);
- spatial: `spatialKeplerEnergy` in the physical premise and the canonical carrier predicate (`h₀`, `hs`);
  `spatialOscEnergy` and `spatialOscEcc` in the osculating carrier predicate (`ho`).

These predicates are false whenever `|q_i| = 0` (Lean's `x / 0 = 0` sends the energies to `|p|²/(2ν) ≥ 0`,
resp. `|V|²/2 ≥ 0`) and literal otherwise. `spatialHamiltonian` (and the frozen planar `movingHamiltonian`) is
totalized at collisions and consumed only through `IsSpatialMovingSolutionOn` (resp. `IsMovingSolutionOn`), whose
collision guard and differentiability on the open collision-free domain make the predicate faithful (review 4,
R4.8).

## 5. Characterization theorems (one semantic unit with their definitions)

Each is a separate frozen theorem file (DRAFT_SORRY at freeze, sealed by its provider from the proof that already
exists; the provider imports only the implementation, never another provider).

| Lean name | Characterizes | Frozen path | Provider export | Proof today in |
|---|---|---|---|---|
| `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast` | `orderedPairThreshold`, `pairThreshold` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean` | `KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast` | `KAM.Planetary.StrongAMD.Threshold.Pair` |
| `KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value` | `orderedPairThreshold`, `pairThreshold` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean` | `KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value` | `KAM.Planetary.StrongAMD.Threshold.Pair` |
| `KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast` | `orderedCrossThreshold` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean` | `KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast` | `KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold` |
| `KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast` | `orderedStrongThreshold` | `KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean` | `KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast` | `KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold` |
| `KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg` | `sourceStrongAMD` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean` | `KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD` | `sourceStrongAMD` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean` | `KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceKepler_axis_pos` | `SourceCanonicalPhase` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean` | `KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one` | `SourceCanonicalPhase` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean` | `KAM.Provider.Planetary.StrongAMD.sourceKepler_ecc_le_one` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength` | `sourceKeplerPeri` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean` | `KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo` | `sourceKeplerApo` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean` | `KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceKeplerApo` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceOscAxis_pos` | `sourceOscAxis` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean` | `KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceOscPeri_pos` | `sourceOscPeri` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean` | `KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength` | `sourceOscPeri` | `KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean` | `KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo` | `sourceOscApo` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean` | `KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo` | `KAM.Planetary.StrongAMD.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos` | `spatialSourceKeplerAxis` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerAction_pos` | `spatialSourceKeplerAction` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerAction_sq` | `spatialSourceKeplerAction` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq` | `spatialSourceKeplerEcc`, `spatialSourcePlanetAngularMomentum` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg` | `spatialSourceKeplerEcc` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one` | `spatialSourceKeplerEcc` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length` | `spatialSourcePlanetAngularMomentum` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean` | `KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le` | `spatialSourcePlanetAngularMomentum` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean` | `KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length` | `spatialSourceKeplerPeri` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length` | `spatialSourceKeplerApo` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg` | `spatialSourceStrongAMD` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le` | `spatialSourceStrongAMD` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscParam_pos` | `spatialSourceOscParam` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscEnergy_neg` | `spatialSourceOscEnergy` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one` | `spatialSourceOscEcc` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg` | `spatialSourceOscEcc` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscAxis_pos` | `spatialSourceOscAxis` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscPeri_pos` | `spatialSourceOscPeri` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length` | `spatialSourceOscPeri` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length` | `KAM.Planetary.Spatial.SourceCarrier` |
| `KAM.Planetary.Spatial.spatialSourceOscApo_ge_length` | `spatialSourceOscApo` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean` | `KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length` | `KAM.Planetary.Spatial.SourceCarrier` |

`orderedCrossThreshold_isLeast` and `orderedStrongThreshold_isLeast` are new (package LP-FREEZE7,
`PlanarSafety/SourceThreshold.lean`): they certify that the carrier `⨅`s are the genuine attained minima of MAIN (3)
(for `2 ≤ n` both index types are nonempty; the real `⨅` of an empty family would be `0`). The pair threshold's unit
is `orderedPairThreshold_isLeast` with `orderedPairThreshold_existsUnique_value` (statement review 1, F3). The
literal restrictions without a listed characterization (`sourceOscEnergy`, `sourceOscEccVector`, `sourceOscEcc`,
`sourceOscVelocity`, `sourceOscParam`, `spatialSourceKeplerEccVector`, `spatialSourceAngularMomentum`,
`spatialSourceOscVelocity`, `spatialSourceOscEccVector`) are literal formulas on their carriers
(`CHARACTERIZATION: N/A_LITERAL`); their carriers' own conditions (`E^osc < 0`, `e^osc < 1`) are the carrier
definitions themselves.

### 5.1 Characterization texts (exact)

Namespace `KAM.Planetary.StrongAMD` (each statement is followed in its file by ` :=` and the `by sorry` proof region):

```lean
/-- The ordered pair threshold is the attained minimum of the objective over the feasible set
(carrier-level characterization; `LP:MAIN L4`). -/
theorem orderedPairThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n)
    (hij : i < j) :
    IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j) (orderedPairThreshold I i j hij)

/-- The value of the ordered pair threshold is the unique least value. -/
theorem orderedPairThreshold_existsUnique_value {n : ℕ} {ν : Fin n → ℝ} (I : OrderedActions ν)
    (i j : Fin n) (hij : i < j) :
    ∃! b : ℝ, IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j) b

/-- **`B_cross` is an attained minimum** (`LP:MAIN §1 (3) (47–55)`): on the carrier, for `2 ≤ n`,
`orderedCrossThreshold hn I` is the least element of the set of adjacent pair thresholds
`B_{i,i+1}(I)`. -/
theorem orderedCrossThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast {b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij}
      (orderedCrossThreshold hn I)

/-- **`B` is an attained minimum** (`LP:MAIN §1 (3) (47–55)`): on the carrier, for `2 ≤ n`,
`orderedStrongThreshold hn I = min (B_cross(I), min_i I_i)` is the least element of the set of
adjacent pair thresholds `B_{i,i+1}(I)` together with the actions `I_i`. -/
theorem orderedStrongThreshold_isLeast {n : ℕ} {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast ({b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij} ∪ Set.range I.1)
      (orderedStrongThreshold hn I)

/-- `0 ≤ C` on source canonical phases (`LP:MAIN L3 (130–139)`). -/
theorem sourceStrongAMD_nonneg {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    0 ≤ sourceStrongAMD z

/-- The deficit bound `Σ_i Λ_i D(e_i) ≤ C` on source canonical phases
(`LP:MAIN L3 (130–139)`). -/
theorem sum_action_mul_eccDeficit_le_sourceStrongAMD {n : ℕ} {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) :
    ∑ i, keplerAction ν z.1 i * eccDeficit (planeLength (keplerEccVector ν z.1 i)) ≤
      sourceStrongAMD z

/-- `0 < a_i` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKepler_axis_pos {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    0 < keplerAxis ν z.1 i

/-- `e_i ≤ 1` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKepler_ecc_le_one {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    planeLength (keplerEccVector ν z.1 i) ≤ 1

/-- `a_i (1 - e_i) ≤ |q_i|` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKeplerPeri_le_planeLength {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν)
    (i : Fin n) : sourceKeplerPeri z i ≤ planeLength (bodyVector z.1.1 i)

/-- `|q_i| ≤ a_i (1 + e_i)` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem planeLength_le_sourceKeplerApo {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceKeplerApo z i

/-- `0 < a_i^osc` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem sourceOscAxis_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : 0 < sourceOscAxis z i

/-- `0 < a_i^osc (1 - e_i^osc)` on source osculating phases. -/
theorem sourceOscPeri_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : 0 < sourceOscPeri z i

/-- `a^osc (1 - e^osc) ≤ |q_i|` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem sourceOscPeri_le_planeLength {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscPeri z i ≤ planeLength (bodyVector z.1.1 i)

/-- `|q_i| ≤ a^osc (1 + e^osc)` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem planeLength_le_sourceOscApo {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceOscApo z i
```

Namespace `KAM.Planetary.Spatial` (each statement is followed in its file by ` :=` and the `by sorry` proof region):

```lean
/-- `0 < a_i` (`LP:MAIN L2 (110–128)`, `d = 3`). -/
theorem spatialSourceKeplerAxis_pos {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 < spatialSourceKeplerAxis z i

/-- `0 < Λ_i`. -/
theorem spatialSourceKeplerAction_pos {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 < spatialSourceKeplerAction z i

/-- `Λ_i² = ν_i² a_i` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerAction_sq {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerAction z i ^ 2 = ν i ^ 2 * spatialSourceKeplerAxis z i

/-- `e_i² = 1 − |L_i|²/Λ_i²` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerEcc_sq {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerEcc z i ^ 2 =
      1 - spaceLength (spatialSourcePlanetAngularMomentum z i) ^ 2 /
        spatialSourceKeplerAction z i ^ 2

/-- `0 ≤ e_i`. -/
theorem spatialSourceKeplerEcc_nonneg {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 ≤ spatialSourceKeplerEcc z i

/-- `e_i ≤ 1` (`LP:MAIN L2 (110–128)`; the radial case `e_i = 1` is included). -/
theorem spatialSourceKeplerEcc_le_one {n : ℕ} {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerEcc z i ≤ 1

/-- `|L_i| = Λ_i √(1 − e_i²)` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourcePlanetAngularMomentum_length {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spaceLength (spatialSourcePlanetAngularMomentum z i) =
      spatialSourceKeplerAction z i * Real.sqrt (1 - spatialSourceKeplerEcc z i ^ 2)

/-- `|L_i| ≤ Λ_i`. -/
theorem spatialSourcePlanetAngularMomentum_length_le {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spaceLength (spatialSourcePlanetAngularMomentum z i) ≤ spatialSourceKeplerAction z i

/-- Radial incidence on the canonical carrier: `a_i (1 − e_i) ≤ |q_i|` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerPeri_le_length {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerPeri z i ≤ spaceLength (bodyVector3 z.1.1 i)

/-- Radial incidence on the canonical carrier: `|q_i| ≤ a_i (1 + e_i)` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerApo_ge_length {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceKeplerApo z i

/-- `0 ≤ C` on the canonical carrier (`LP:MAIN L3 (130–139)`). -/
theorem spatialSourceStrongAMD_nonneg {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) : 0 ≤ spatialSourceStrongAMD z

/-- `Σ_i Λ_i (1 − √(1 − e_i²)) ≤ C` on the canonical carrier (`LP:MAIN L3 (130–139)`). -/
theorem spatialSourceAction_mul_eccDeficit_le {n : ℕ} {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) :
    ∑ i, spatialSourceKeplerAction z i * (1 - Real.sqrt (1 - spatialSourceKeplerEcc z i ^ 2)) ≤
      spatialSourceStrongAMD z

/-- On the osculating carrier: `0 < k_i`. -/
theorem spatialSourceOscParam_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscParam z i

/-- On the osculating carrier: `E_i^osc < 0`. -/
theorem spatialSourceOscEnergy_neg {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : spatialSourceOscEnergy z i < 0

/-- On the osculating carrier: `e_i^osc < 1`. -/
theorem spatialSourceOscEcc_lt_one {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : spatialSourceOscEcc z i < 1

/-- On the osculating carrier: `0 ≤ e_i^osc`. -/
theorem spatialSourceOscEcc_nonneg {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 ≤ spatialSourceOscEcc z i

/-- On the osculating carrier: `0 < a_i^osc` (SP-OSC's `spatialOscPhase_ellipse`). -/
theorem spatialSourceOscAxis_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscAxis z i

/-- On the osculating carrier: `0 < a^osc (1 − e^osc)`. -/
theorem spatialSourceOscPeri_pos {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscPeri z i

/-- Radial incidence on the osculating carrier: `a^osc (1 − e^osc) ≤ |q_i|`. -/
theorem spatialSourceOscPeri_le_length {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) :
    spatialSourceOscPeri z i ≤ spaceLength (bodyVector3 z.1.1 i)

/-- Radial incidence on the osculating carrier: `|q_i| ≤ a^osc (1 + e^osc)`. -/
theorem spatialSourceOscApo_ge_length {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) :
    spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceOscApo z i
```

## 6. Manifest entry drafts

[`freeze/draft7/manifest-entries.json`](freeze/draft7/manifest-entries.json) has one entry per file (127),
in the schema of `manifest/frozen-anchors.json`:

- `id` `<group>.v1` and `contract` `{id: <group>, version: "1"}` with `<group> = planetary.d59.<name>`
  (`fourier.d59.modeSize` for the ℓ¹ mode size);
- `kind`, `path`, `export` as in §2, §4, §5;
- `source.revision` = `KAM-inp@701c239b docs/tracks/LP/source/MAIN.md (sha256 …) as amended by
  docs/tracks/LP/source/AMENDMENTS.md (sha256 …); exact text docs/tracks/LP/FREEZE-PROPOSAL.md draft 7`;
  `source.range` = the MAIN item and lines;
- `split_policy` `NOT_SPLIT`, one source group per entry, `ruling_ref` `docs/DECISIONS.md D59` (to be extended by
  the decision that approves the exact text);
- `definition_closure` = the complete transitive closure of frozen definition files imported (existing and new),
  with `sha256: "TBD at freeze"`;
- theorems: `implementation` = the provider module and export, `state: "DRAFT_SORRY"`, `prefix_sha256`,
  `suffix_sha256` `"TBD at freeze"`, empty `draft_allowlist`; definitions: `state: "SEALED"`,
  `full_file_sha256: "TBD at freeze"`;
- `abi_sha256: "TBD at freeze"`; `author_approval: "PENDING (D59 approves rulings only)"`.

## 7. Rebase plan (freeze time)

The fully qualified name of every new frozen definition is its current implementation name, so no LP theorem
statement changes. For each implementation module: delete the listed `def`/`abbrev`s (and nothing else), and add
`public import` of their frozen files.

| Implementation module | Definitions deleted (now frozen, same names) | Frozen files to `public import` |
|---|---|---|
| `KAM.Fourier.Derivative` | `modeSize` | `KAM.Frozen.Fourier.Defs.{ModeSize}` |
| `KAM.Planetary.StrongAMD.Threshold.Defs` | `actionAxis`, `chamber`, `eccDeficit`, `pairFeasible`, `pairObjective`, `pairThreshold`, `AdjIdx`, `AdjIdx.upperIdx`, `OrderedActions`, `orderedPairThreshold`, `orderedCrossThreshold`, `orderedStrongThreshold` | `KAM.Frozen.Planetary.StrongAMD.Defs.{ActionAxis, Chamber, EccDeficit, PairFeasible, PairObjective, PairThreshold, AdjIdx, AdjIdxUpperIdx, OrderedActions, OrderedPairThreshold, OrderedCrossThreshold, OrderedStrongThreshold}` |
| `KAM.Planetary.StrongAMD.Momentum` | `strongAMD` | `KAM.Frozen.Planetary.StrongAMD.Defs.{StrongAMD}` |
| `KAM.Planetary.StrongAMD.Osculating.Basic` | `keplerPeri`, `keplerApo`, `oscVelocity`, `oscParam`, `oscEnergy`, `oscAxis`, `oscEccVector`, `oscEcc`, `oscPeri`, `oscApo` | `KAM.Frozen.Planetary.StrongAMD.Defs.{KeplerPeri, KeplerApo, OscVelocity, OscParam, OscEnergy, OscAxis, OscEccVector, OscEcc, OscPeri, OscApo}` |
| `KAM.Planetary.StrongAMD.SourceCarrier` | `SourceCanonicalPhase`, `SourceOsculatingPhase`, `sourceStrongAMD`, `sourceKeplerPeri`, `sourceKeplerApo`, `sourceOscVelocity`, `sourceOscParam`, `sourceOscEnergy`, `sourceOscAxis`, `sourceOscEccVector`, `sourceOscEcc`, `sourceOscPeri`, `sourceOscApo` | `KAM.Frozen.Planetary.StrongAMD.Defs.{SourceCanonicalPhase, SourceOsculatingPhase, SourceStrongAMD, SourceKeplerPeri, SourceKeplerApo, SourceOscVelocity, SourceOscParam, SourceOscEnergy, SourceOscAxis, SourceOscEccVector, SourceOscEcc, SourceOscPeri, SourceOscApo}` |
| `KAM.Planetary.Spatial.Vector` | `spaceDot`, `spaceSq`, `spaceLength`, `spaceCross`, `bodyVector3` | `KAM.Frozen.Planetary.Spatial.Defs.{SpaceDot, SpaceSq, SpaceLength, SpaceCross, BodyVector3}` |
| `KAM.Planetary.Spatial.Elements` | `planetAngularMomentum3`, `angularMomentum3`, `spatialKeplerEnergy`, `spatialKeplerAxis`, `spatialKeplerAction`, `spatialKeplerEccVector`, `SpatialNegativeEnergy`, `SpatialElliptic` | `KAM.Frozen.Planetary.Spatial.Defs.{PlanetAngularMomentum3, AngularMomentum3, SpatialKeplerEnergy, SpatialKeplerAxis, SpatialKeplerAction, SpatialKeplerEccVector, SpatialNegativeEnergy, SpatialElliptic}` |
| `KAM.Planetary.Spatial.Model` | `spatialHamiltonian`, `SpatialNoCollision`, `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn` | `KAM.Frozen.Planetary.Spatial.Defs.{SpatialHamiltonian, SpatialNoCollision, IsSpatialMovingSolutionOn, SpatialMovingUniqueOn}` |
| `KAM.Planetary.Spatial.Newton` | `spatialBarycentricPositions`, `spatialBarycentricVelocities`, `spatialMasses`, `IsSpatialNewtonSolutionOn` | `KAM.Frozen.Planetary.Spatial.Defs.{SpatialBarycentricPositions, SpatialBarycentricVelocities, SpatialMasses, IsSpatialNewtonSolutionOn}` |
| `KAM.Planetary.Spatial.Osculating.Basic` | `spatialKeplerPeri`, `spatialKeplerApo`, `spatialOscVelocity`, `spatialOscParam`, `spatialOscEnergy`, `spatialOscAxis`, `spatialOscEccVector`, `spatialOscEcc`, `spatialOscPeri`, `spatialOscApo`, `SpatialOscPhase`, `spatialSourceKeplerPeri`, `spatialSourceKeplerApo`, `spatialSourceOscVelocity`, `spatialSourceOscParam`, `spatialSourceOscEnergy`, `spatialSourceOscAxis`, `spatialSourceOscEccVector`, `spatialSourceOscEcc`, `spatialSourceOscPeri`, `spatialSourceOscApo` | `KAM.Frozen.Planetary.Spatial.Defs.{SpatialKeplerPeri, SpatialKeplerApo, SpatialOscVelocity, SpatialOscParam, SpatialOscEnergy, SpatialOscAxis, SpatialOscEccVector, SpatialOscEcc, SpatialOscPeri, SpatialOscApo, SpatialOscPhase, SpatialSourceKeplerPeri, SpatialSourceKeplerApo, SpatialSourceOscVelocity, SpatialSourceOscParam, SpatialSourceOscEnergy, SpatialSourceOscAxis, SpatialSourceOscEccVector, SpatialSourceOscEcc, SpatialSourceOscPeri, SpatialSourceOscApo}` |
| `KAM.Planetary.Spatial.SourceCarrier` | `SpatialSourceCanonicalPhase`, `SpatialSourceOsculatingPhase`, `spatialSourceKeplerAxis`, `spatialSourceKeplerAction`, `spatialSourceKeplerEccVector`, `spatialSourceKeplerEcc`, `spatialSourcePlanetAngularMomentum`, `spatialSourceAngularMomentum`, `spatialSourceStrongAMD` | `KAM.Frozen.Planetary.Spatial.Defs.{SpatialSourceCanonicalPhase, SpatialSourceOsculatingPhase, SpatialSourceKeplerAxis, SpatialSourceKeplerAction, SpatialSourceKeplerEccVector, SpatialSourceKeplerEcc, SpatialSourcePlanetAngularMomentum, SpatialSourceAngularMomentum, SpatialSourceStrongAMD}` |

Specific points (flagged):

1. **`KAM.Fourier.modeSize` lives in the shared `KAM/Fourier/Derivative.lean`** (not an LP file; AGENTS and the
   common brief forbid track provers from editing `KAM/Fourier`). The freeze commit must delete its two-line `def`
   there and add `public import KAM.Frozen.Fourier.Defs.ModeSize`; this needs the orchestrator (a shared-module
   edit). Same name, same type, same body (check (b): `rfl` and alpha-equivalent value), so every consumer in every
   track compiles unchanged.
2. **`orderedCrossThreshold`**: the frozen body inlines `(Nat.lt_succ_self a.1.val)` for `a.lt_upperIdx`; the
   theorem `AdjIdx.lt_upperIdx` stays in `Threshold/Defs.lean`, and `orderedCrossThreshold_eq` stays `rfl`.
3. **Characterization lemmas.** The 32 existing characterization lemmas (`Threshold/Pair.lean`: 2,
   `StrongAMD/SourceCarrier.lean`: 10, `Spatial/SourceCarrier.lean`: 20) and the two new ones
   (`PlanarSafety/SourceThreshold.lean`) have **no consumer outside their own files** (checked by `grep -rlw`).
   At freeze each is deleted from its implementation module and its proof moves verbatim into its provider
   `KAM/Provider/Planetary/{StrongAMD,Spatial}/<Name>.lean` as `KAM.Provider.…<name>`, so the frozen theorem keeps the
   implementation's fully qualified name with no rename anywhere. Two proofs use a sibling characterization and are
   inlined in the provider: `sourceOscPeri_pos` (uses `sourceOscAxis_pos`) and `orderedStrongThreshold_isLeast` (uses
   `orderedCrossThreshold_isLeast`); after sealing, any module may import the sealed frozen theorem instead (D58).
   `PlanarSafety/SourceThreshold.lean` is then empty and is deleted.
4. **Anchor providers** are one-line: `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier := lp0_planar_barrier_source …`
   and so on (table in §2); they import `PlanarSafety/SourceCorollary.lean`, `PlanarSafety/Source.lean`,
   `Spatial/SpatialSafety/Source.lean`, `Spatial/SpatialSafety/SourceCorollary.lean`. No implementation theorem is
   renamed.
5. **Sealing order.** Freeze commit: all 127 files, definitions SEALED, the 39 theorems DRAFT_SORRY with
   stub providers (D20/D25 pattern). Seal commit right after: all providers filled (every proof exists), bodies
   `by exact …`; the semantic-unit rule requires sorry-free characterizations before the units are relied on.
6. **No rename is needed** for any definition. No frozen name clashes with an existing frozen name or a Mathlib short
   name (`main_shortname_check.py`, exit 0, on the new implementation modules; the frozen names are the current
   implementation names).

## Appendix A. History, alternatives not chosen, review notes

**Drafts.** Draft 1 (02:40) gave LP0/LP1 with total helpers; review 1 (RETURN FOR REVISION: F1 full L5, F2 full L16
outputs, F3 threshold carriers, F4 total physical formulas) led to draft 2 (review 2: PASS for the theorem types);
draft 3 added LP1 under OD-11 (b) (review 3: PASS); drafts 4–5 added LP2 (review 4: PASS for fidelity, R4.1 BLOCKING
for (b)); draft 6 applied R4.1 resolution (A) (review 5: PASS WITH NOTES). The draft-6 file is in git history
(`git show 701c239b:docs/tracks/LP/FREEZE-PROPOSAL.md`); its texts §2, §3, §3c (total-helper forms) are superseded
by §3 here.

**Alternatives not chosen (recorded, not proposed).**
- OD-1: the signed `physicalAMD` (would force `L > 0` through the premise).
- OD-2 / OD-11 (a): total threshold formulas and total physical formulas with guarded interpretation.
- Review 4, R4.1 resolution (B): freezing `spatialKeplerAxis/Action/EccVector` as total formulas under the planar
  inherited convention.
- OD-3: dropping `max ν = 1` (the general versions stay ordinary theorems).
- Diophantine condition through the frozen `KAM.IsDiophantine γ τ ω` (`γ / |k|₁^τ ≤ |k·ω|`) instead of
  `γ * modeSize k ^ (-τ) ≤ |k·ω|`: equivalent pointwise (`modeSize k ≥ 0`, `Real.rpow_neg`) and it would avoid
  freezing `KAM.Fourier.modeSize` (rebase point 1); not chosen, because the reviewed text (reviews 1–5) uses
  `modeSize`.

**Review notes and their disposition.**

| Note | Disposition in draft 7 |
|---|---|
| R4.2 anchor names | Applied: §2 names are the anchor surface for all five anchors. |
| R4.3 spatial §4b bullet | Applied (§4), with the closure corrections of §4.2 notes. |
| R4.4 / R5.4 `h₀`/`hs` shapes | Kept: planar `(∀ i, 0 < ν i) ∧ ∀ i, …` with `h₀` after `hch`; spatial `∀ i, 0 < ν i ∧ …` with `h₀` after the physical premise and one `∃ hs`. Logically equivalent; the planar text keeps the frozen raw canonical helpers. |
| R4.5 geometric L16 scope | Unchanged: the anchors export radial incidence `a^osc(1−e^osc) ≤ |q| ≤ a^osc(1+e^osc)` and the quantitative estimates, not geometric tangency; frozen docstrings no longer say "tangency". |
| R4.6 docstring misnomers | `spatialKeplerAxis` fixed in its frozen file; `Spatial/Model.lean` module docstring ("no totalization") is an implementation docstring, not frozen (to be fixed by its owner). |
| R4.7 `SpatialElliptic` is a `def` | Kept (§4.2 notes). |
| R4.8 `spatialHamiltonian` totalized | Recorded in its frozen module docstring and §4.4. |
| R4.9 no spatial LP0 | Recorded: no spatial barrier anchor is proposed; T19 does not need one. |
| R5.1 §4b wording | Applied (§4.4). |
| R5.2 SourceCarrier docstring | Implementation docstring, not frozen; optional. |
| R5.3 stale prose | Removed by this rewrite. |
| R5.5 `h₀` adjacency | Kept. |
| R5.6, R5.7 | Carry-overs handled above; handoff details not applicable. |
