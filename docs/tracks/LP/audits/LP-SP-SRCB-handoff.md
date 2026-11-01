# Handoff LP-SP-SRCB

## Files
- New: `KAM/Planetary/Spatial/SpatialSafety/Source.lean` (~243 lines).
- Regenerated (generator output only, `scripts/gen_root_imports.py`): `KAM/Root/Planetary.lean`. Without it `lp_lint.sh` fails ("KAM.lean is out of date").
- No other file edited. The facade import `SpatialSafety.lean` is left for landing.

## Items proved (LP:MAIN T19 (599-603), L16 (508-529), d = 3)
- `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_general`: LP2 §3c without `hνmax`/`hνle`.
- `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source`: with `hνmax`, `hνle` (unused).

Approach (same as planar `lp1_planar_strongAMD_safety_source{,_general}`): both are proved from `lp2_spatial_strongAMD_safety` / `…_normalized`.
- Typing binder `h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0`. It is `SpatialNegativeEnergy ν z₀` unfolded, so it is the membership of `SpatialSourceCanonicalPhase n ν`.
- The initial AMD hypothesis is `spatialSourceStrongAMD ⟨z₀, h₀⟩ ≤ orderedStrongThreshold … - δ`.
- In the conclusion, the AMD margin and drift clauses are `∃ hs, … spatialSourceStrongAMD ⟨z t, hs⟩ …`.
- The osculating block is `∃ hs ho, …` with `spatialSourceOsc{Energy,Axis,Ecc,EccVector,Peri,Apo}` on `SpatialSourceOsculatingPhase n ν μ` and `spatialSourceKeplerPeri/Apo` on `SpatialSourceCanonicalPhase n ν`.
- The `ho` membership is `(∀ i, 0 < ν i) ∧ 0 < μ ∧ ∀ i, 0 < spaceLength … ∧ spatialOscEnergy … < 0 ∧ spatialOscEcc … < 1`.
- The remaining conclusion clauses keep the internal `spatialKepler*` names, as in the planar §3b.
- The guards come from the conclusions of the base theorem, so no new analysis.

## Not done
Nothing outstanding.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-spsrcb KAM.Planetary.Spatial.SpatialSafety.Source`: `✔ [9360/9360] Built KAM.Planetary.Spatial.SpatialSafety.Source`, "Build completed successfully". No warnings in my file.
- `lp_lint.sh`: exit 0, after regenerating the root. Lines over 100 characters were fixed first.
- `main_shortname_check.py … KAM.Planetary.Spatial.SpatialSafety.Source`: "short-name check OK", exit 0.
- `#print axioms` (both theorems, run via `lp_lean.sh` on `.drafts/ax_srcb.lean`): `[propext, Classical.choice, Quot.sound]`.

## #check output for FREEZE-PROPOSAL §3d (`pp.proofs.withType false`)
```
@lp2_spatial_strongAMD_safety_source : ∀ {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ),
  (∀ (i : Fin n), 0 < ν i) →
    (∃ i, ν i = 1) →
      (∀ (i : Fin n), ν i ≤ 1) →
        ∀ (A : Set (Fin n → ℝ)),
          IsCompact A →
            (∀ a ∈ A, (∀ (i : Fin n), 0 < a i) ∧ ∀ (i j : Fin n), i < j → a i < a j) →
              ∀ (δ γ τ : ℝ),
                0 < δ →
                  0 < γ →
                    ↑n - 1 < τ →
                      ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem,
                        0 < μ₀ ∧
                          0 < c ∧
                            0 < T₀ ∧
                              0 < AΛ ∧
                                0 < Aa ∧
                                  0 < dStar ∧
                                    0 < dPair ∧
                                      0 < Aosc ∧
                                        0 < Aelem ∧
                                          Aosc * μ₀ ≤ dStar / 2 ∧
                                            2 * (Aosc * μ₀) ≤ dPair / 2 ∧
                                              ∀ (μ : ℝ),
                                                0 < μ →
                                                  μ ≤ μ₀ →
                                                    ∀ (z₀ : KAM.Planetary.Phase (n * 3)),
                                                      (∀ (i : Fin n),
                                                          0 < spaceLength (bodyVector3 z₀.1 i) ∧
                                                            spatialKeplerEnergy ν z₀ i < 0) →
                                                        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
                                                          (∀ (k : Fin n → ℤ),
                                                              k ≠ 0 →
                                                                γ * KAM.Fourier.modeSize k ^ (-τ) ≤
                                                                  |∑ i,
                                                                      ↑(k i) *
                                                                        (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
                                                            ∀
                                                              (hch :
                                                                (fun i => spatialKeplerAction ν z₀ i) ∈
                                                                  KAM.Planetary.StrongAMD.chamber ν)
                                                              (h₀ :
                                                                ∀ (i : Fin n),
                                                                  0 < ν i ∧
                                                                    0 < spaceLength (bodyVector3 z₀.1 i) ∧
                                                                      spatialKeplerEnergy ν z₀ i < 0),
                                                              spatialSourceStrongAMD ⟨z₀, h₀⟩ ≤
                                                                  KAM.Planetary.StrongAMD.orderedStrongThreshold hn
                                                                      ⟨fun i => spatialKeplerAction ν z₀ i, hch⟩ -
                                                                    δ →
                                                                have T :=
                                                                  T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))));
                                                                ∃ z,
                                                                  z 0 = z₀ ∧
                                                                    IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
                                                                      SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
                                                                        (IsSpatialNewtonSolutionOn (spatialMasses ν μ)
                                                                            (Set.Icc (-T) T) (fun t => ⋯) fun t => ⋯) ∧
                                                                          ∀ t ∈ Set.Icc (-T) T, ⋯
```
The source text is the file itself (`Source.lean`, theorem statements).

## AUDIT FOCUS
- The carrier membership binders `h₀`, `hs`, `ho`: are they exactly the carriers of SourceCarrier.lean and Osculating/Basic.lean? `h₀` and `hs` are `SpatialNegativeEnergy` unfolded.
- Quantifier placement: `h₀` after `hch`, `hs` and `ho` existential per time `t`.
- `∃ hs` sits inside `∃ hcht` for the margin clause, and is repeated for the drift clause and the osculating block (as planar).
- Whether the clauses left with internal `spatialKepler*` names (axis, eccentricity vector, action) should also go through the source carrier. The planar template keeps them.

## Errata, deviations, design signals
- No source errata.
- Deviation: the regenerated `KAM/Root/Planetary.lean`.
- No elaboration problems, no heartbeat options, and the file is far below the 1500-line cap.
