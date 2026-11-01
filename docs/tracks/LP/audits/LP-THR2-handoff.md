# LP-THR2 handoff (track LP, non-frozen)

Files: KAM/Planetary/StrongAMD/Threshold/{Defs,Pair,Strong}.lean (no others; grep showed only THR files use the changed definitions; Geometry and Modulus rebuilt fine).

Changes (F3):
- `orderedCrossThreshold {ν} (_hn : 2 ≤ n) (I : OrderedActions ν) : ℝ := ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx`
- `orderedStrongThreshold {ν} (hn : 2 ≤ n) (I) : ℝ := min (orderedCrossThreshold hn I) (⨅ i, I.1 i)`
- `orderedCrossThreshold_eq (hn) (I) : orderedCrossThreshold hn I = crossThreshold ν I.1 := rfl`; `orderedStrongThreshold_eq` still `rfl`.
- `orderedStrongThreshold_eq_min_first` updated to `orderedCrossThreshold hn I`; `_pos`, `continuous_` unchanged and compile.
- New in Pair.lean: `orderedPairThreshold_isLeast`, `orderedPairThreshold_existsUnique_value` (exact review text).
Not done: optional finite-minimum characterizations of ordered cross/strong (the total versions already exist in Strong.lean).

Checks: lp_build.sh on Threshold.{Defs,Pair,Continuity,Strong}, Threshold, Geometry, Modulus: all "Build completed successfully". lp_lint.sh exit 0 (check_lean_modules PASS, frozen guard OK, ABI hashes OK). main_shortname_check.py: "short-name check OK" (exit 0; it printed two harmless "cannot change to ...Continuity.lean: Not a directory" git messages from my file-list args).
Axioms (all new/changed theorems): propext, Classical.choice, Quot.sound.

AUDIT FOCUS: `_hn` is unused typing data in orderedCrossThreshold; n=1 case now excluded at the carrier. Changed lines ≈ 30.
Errata: none. Deviations: none. Design signals: none.
