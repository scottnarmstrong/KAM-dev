# LP3-SRC handoff

Package LP3-SRC (LP3-1 and LP3-2 restated through the source carriers; OD-11 (b), D59), track LP, non-frozen.

## Files
New: `KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean` (205 lines), `KAM/Planetary/Spatial/Nek/SpatialSafety/Source.lean` (238 lines),
`docs/tracks/LP/freeze/odb-LP3-PlanarSource.lean.txt`, `odb-LP3-SpatialSource.lean.txt` (copies of the two modules).
Changed: generated `KAM/Root/Planetary.lean` only (via `scripts/gen_root_imports.py`: two new imports).
Both module docstrings carry "The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md."

## Declarations (all proved; none stubbed)
- `KAM.Planetary.StrongAMD.lp3_planar_strongAMD_safety_source_general` / `lp3_planar_strongAMD_safety_source` (the latter adds `hνmax hνle`), template §3b.
- `KAM.Planetary.Spatial.lp3_spatial_strongAMD_safety_source_general` / `lp3_spatial_strongAMD_safety_source` (the latter adds `hνmax hνle`), template §3d.
Full statements: see the files (they are the elaborated texts; `odb-*.txt` are identical copies).

## Approach
Each theorem is the (b) template theorem with exactly the three LP3 changes, proved as the templates are proved:
obtain the constants from `lp3_planar_strongAMD_safety` / `lp3_spatial_strongAMD_safety{,_normalized}`, then repackage the
per-time conclusion with the typing binders `hs`, `ho` built from its guards. The only proof edits are dropping `γ τ hγ hτ`
and the Diophantine hypothesis `hdio`. No template clause failed to transport. No premise added.

## Token diff against the templates (`_general` forms; the non-general forms differ from these only by `hνmax hνle`, as in the templates)
```
1c1
< theorem lp1_planar_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
---
> theorem lp3_planar_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
5c5
<     (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
---
>     (δ : ℝ) (hδ : 0 < δ) :
13,15d12
<         (∀ k : Fin n → ℤ, k ≠ 0 →
<           γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
<             |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
21c18
<         let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
---
>         let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
35,36c32,35
<             ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
<             ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
---
>             ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
>               AΛ * μ ^ planetaryDriftExponent n ∧
>             ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
>               Aa * μ ^ planetaryDriftExponent n ∧
41c40
<                 n * AΛ * Real.sqrt μ) ∧
---
>                 n * AΛ * μ ^ planetaryDriftExponent n) ∧
---
1c1
< theorem lp2_spatial_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
---
> theorem lp3_spatial_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
5c5
<     (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
---
>     (δ : ℝ) (hδ : 0 < δ) :
15,18d14
<         (∀ k : Fin n → ℤ, k ≠ 0 →
<           γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
<             |∑ i, (k i : ℝ) * (ν i ^ 3 /
<               spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3)|) →
23c19
<         let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
---
>         let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
39c35
<               AΛ * Real.sqrt μ ∧
---
>               AΛ * μ ^ planetaryDriftExponent n ∧
42c38
<               Aa * Real.sqrt μ ∧
---
>               Aa * μ ^ planetaryDriftExponent n ∧
45c41
<               n * AΛ * Real.sqrt μ ∧
---
>               n * AΛ * μ ^ planetaryDriftExponent n ∧
```
Only the three LP3 changes (plus theorem names, and line re-wrapping of the two planar drift lines).

## Checks
- `lp_build.sh` of `KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source` and `KAM.Planetary.Spatial.Nek.SpatialSafety.Source`: "Build completed successfully", no warnings in the new files.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- `main_shortname_check.py`: exit 0 ("short-name check OK").
- `#print axioms` of all four theorems (via `lp_lean.sh`): `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- Token diff above: confirm nothing but the three changes; in particular the `μ ^ planetaryDriftExponent n` occurs in exactly the action, axis and AMD lines, and `planetaryTimeExponent n` in `T`.
- Spatial premise order is the template's (`h₀` right after the physical premise, before `∈ A`), unchanged from `lp2_..._source`; the LP3 theorem has no `h₀`, so the guard is a typing binder only.
- The planar orbit-element lines keep raw `keplerAxis/keplerAction/keplerEccVector` (§3b); spatial goes through `spatialSource*` throughout (§3d).
- `_general` drops `hνmax hνle`; the non-general forms keep them unused (named without underscore in the spatial form, as in the template).

## Errata / deviations / design signals
None. No elaboration issues; files well under the cap.
