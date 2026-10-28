# Handoff T19 (P11C, `PlanarTorsion/Asymptotics`)

## Files (new)
- `KAM/Planetary/PlanarTorsion/Asymptotics.lean` (facade + signed theorems `asymptotics`,
  `asymptotics_uniform_ratio`, `asymptotics_general_axes`, statements verbatim, only line-wrapped)
- `Asymptotics/Homogeneity.lean` (`p11cAs_Q_smul`, `p11cAs_coeffs_smul`, `p11cAs_beta_smul`, projector invariance)
- `Asymptotics/Normalize.lean` (`p11cAs_unit r` = G=m0=1, masses (r,1); `p11cAs_beta_ratio`: beta p ![a,1] = (m0)⁻¹ • beta (unit r) ![a,1])
- `Asymptotics/Relative.lean` (`p11c_relativeError` verbatim def, `p11cAs_rel`, `p11cAs_rel_explicit`)
- `Asymptotics/Limits.lean` (`p11cAs_det`: det = -117/(16 m0²) a³ + O(a⁵), node as-det)
Merged inp-p11c-t18 (T18b) before the final build. KAM.lean not touched (lint reports it out of date: orchestrator regenerates).

## Approach
Entries: as_ent (absolute form) -> relative O(α²) via `p11cAs_rel`. Determinant: (a-A0)d + A0(d-D0) - (b-B0)(b+B0), leading k0k2-k1² = -117/16/m0². Homogeneity: Q scales by (s√s)⁻¹, projector invariant, coeffs by s⁻², beta_def linear in coeffs. Uniformity: exact reduction to normalised data `p11cAs_unit ratio` (beta scales by 1/m0), constants from the single normalised IsBigO; general_axes from uniform det clause + homogeneity (a = a1 • ![α,1]). Uses only `as_ent` of T18 (leading components via obtain), so T18b conjuncts do not matter.

## Checks
- `inp_lake_build.sh ... KAM.Planetary.PlanarTorsion.Asymptotics`: Build completed successfully, no sorry/error.
- `scripts/lint_sources.sh`: all PASS except "KAM.lean is out of date" (generated; not edited by me).
- `#print axioms` of asymptotics, asymptotics_uniform_ratio, asymptotics_general_axes: [propext, Classical.choice, Quot.sound].
- No heartbeat options; all files < 200 lines; lines ≤ 100.

## Notes
- New public helper names all prefixed `p11cAs_`; `p11c_relativeError` was not in KAM (signature def, defined in Relative.lean).
- asymptotics_general_axes has no alpha0 ≤ 1 clause; not needed (α<1 on axes).
- Uncertainties: none known. Suspected errata: none. Deviations: none (statements only re-wrapped across lines).
