# Handoff P-CLOSE-LEAN

## Files
- `KAM/Planetary/AMD/Geometry.lean` (+ `geometry_radial`, line 176; file 260 lines)
- `KAM/Planetary/SecularBox/Covariance.lean` (+ `sb_cov_full`, line 125; file 149 lines)
No existing statement changed; no frozen/provider/KAM.lean/README touched.

## Approach
`geometry_radial` calls `geometry` and projects the two radial inequalities from `elements` (clauses
hlow/hup), the box bounds from geometry's own conclusion. `sb_cov_full` reuses `sb_cov` and the
existing private root/ecc/orbitalUnit lemmas; rho = Gamma/Lambda uses Lambda fixed (`fast w.2`);
x-shift is `planeDot_rot` after `sbCov_orbitalUnit`. No elliptic hypothesis needed (identities algebraic).

## Node -> declaration
| node | declaration | SOURCE_CONCLUSION part |
|---|---|---|
| bpP:p14:geometry, stepP:p14:geo-b | `KAM.Planetary.geometry_radial` (Geometry.lean:176) | `a_i(1-e_i) <= |q_i| <= a_i(1+e_i)` and `d <= |q_i| <= R` (first conjunct), plus (a),(c),(d),K_1 conjunction of `geometry` (second conjunct) |
| bpP:p14:sb-cov, stepP:p14:sb-cv-1, stepP:p14:sb-cv-2 | `KAM.Planetary.sb_cov_full` (Covariance.lean:125) | Gamma, k, rho=Gamma/Lambda, a unchanged; v'=R_theta v (first conjunct); x(F)=x(F-theta), J, q, p covariance (second conjunct) |

## Checks
- gate build `KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance`: Build completed successfully (9111 jobs), no warnings from these files.
- `scripts/lint_sources.sh`: check_lean_modules PASS; FROZEN-ANCHOR GUARD OK; ABI HASHES OK (144).
- main_shortname_check: OK (no reused public short name).
- No line over 100 columns.
- `#print axioms` geometry_radial, sb_cov_full: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata
None. geo-b's hypothesis "item (a)" is covered since the second conjunct of `geometry_radial` is `geometry`'s conclusion under the same hypotheses. `sb_cov_full` is stated for all w (stronger than "w elliptic").

## Round 2
Two new theorems; no existing statement changed; no frozen/provider/KAM.lean/README touched.

| node | declaration | file:line | SOURCE_CONCLUSION part |
|---|---|---|---|
| bpP:p14:geometry | `KAM.Planetary.geometry_complete` | AMD/Geometry.lean:260 | all of `geometry_radial`, plus `IsCompact (amdCompact B)`, `amdCompact B ⊆ collisionFreeDomain n`, and for i≠j `d ≤ |q_i-q_j| ≤ |q_i|+|q_j| ≤ 2R` |
| stepP:p14:sb-cv-1 | `KAM.Planetary.sb_cov_slow_data` | SecularBox/Covariance.lean:148 | Γ, k, source ρ=√((1-Γ/(2Λ))/Λ), a invariant; v' = R_θ v |

Approach: geometry_complete = `geometry_radial` + `amd_compact` + triangle inequality
(`planeLength_add_le`, `planeLength_neg`) + radius bounds; sb_cov_slow_data reuses private
sbCov_gamma/root/ecc, and ρ invariance by rewriting Γ and fast-action invariance.

Checks: gate build of both modules OK (9111 jobs, only inherited Energy.lean warnings);
`scripts/lint_sources.sh` PASS (modules, frozen guard, ABI 144); main_shortname_check exit code
OK (no reused public short name); no line >100 cols; `#print axioms` both: [propext, Classical.choice,
Quot.sound]. Uncertainties/errata/deviations: none.
