# P7-7 prover handoff (branch inp-p77, c526f74; contains inp-p75 (P7-5, delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Planetary/Poincare/D25.lean` (~330 lines). No other file touched (KAM.lean not regenerated; lint reports it out of date, as expected).

## Nodes / declarations (signatures copied verbatim from KeplerSignaturesP.lean, section D25)
- `bpP:p7:d25` (a): `secularGamma_eq`, `secularRoot_eq`, `secularEccVector_eq`, `secularAxis_eq`
- (c): `ellipsePhase_eq_poincareProd`, `ellipsePhase_eq_poincareProd_self`
- (d)/(e): `keplerFunctions_poincareProd`, `exists_poincareProd_of_progradeElliptic`
- `bpP:p7:average`: `average_via_eccentric_longitude`, `poincareProd_means`
- Helpers (non-signature, all proved): `planetBlock_assemble`, `poincare_block_eq_ellipse`, `integral_via_keplerPhi`, `orbitalUnit_add_two_pi`, `ellipsePosition_add_two_pi`, `ellipseMomentum_add_two_pi`, `longitudeJacobian_add_two_pi`, `ellipsePhase_update_add_two_pi`, `continuous_assemble_update`.

## Approach
- (a): unfolding frozen defs. (c): the general block lemma `poincare_block_eq_ellipse` (chart on a block with the same coordinates as `w` except the angle, with `poincareF P = F`, equals `(ellipsePosition, ellipseMomentum)`); `poincareF` of the assembled block is `F_j` by `keplerLong_unique`. The `_self` version applies the block lemma to `planetBlock w j` directly.
- (d): `poincare_elements` (kappa = 1) per block via `poincareProd_block`, `regionProd_one_iff`, `poincareProd_mem_regionProd`. (e): `poincareProd_image` + `regionProd_one_iff`.
- average: `integral_via_keplerPhi` (`intervalIntegral.integral_comp_mul_deriv'` with f = `keplerPhi v`, f' = `keplerJac v`, limits `F(0)`, `F(0)+2pi`, then `Function.Periodic.intervalIntegral_add_eq`). Continuity of the integrand uses `analyticOnNhd_poincareProd`; periodicity of the RHS integrand is direct from `orbitalUnit (F + 2pi) = orbitalUnit F`.
- means: reduces to the single-planet `poincare_means` (Symplectic.lean) blockwise plus `poincare_facts` (`planeSq v = 1 - K^2`).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p77 KAM.Planetary.Poincare.D25`: "Build completed successfully (9117 jobs)"; no sorry; only unused-variable warnings (`hm`, `hw`) from the frozen signatures `secularAxis_eq`-style/`ellipsePhase_eq_poincareProd_self` (kept verbatim).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; informational: KAM.lean out of date (orchestrator regenerates), 8 lines > 100 chars in D25.lean (verbatim signature lines).
- `#print axioms` of all 10 signature theorems: `[propext, Classical.choice, Quot.sound]`.
- No `set_option`, no heartbeat issues (file elaborates in ~9 s).

## Uncertainties / errata / deviations
- None found; no statement needed an extra hypothesis. Unused `hm`/`hw` in `ellipsePhase_eq_poincareProd_self` and (in the dictionary) `secularAxis`-adjacent lemmas are just unused premises of the frozen signature.
- The `n` in `poincareProd_means` is supplied by a section `variable {n : ℕ}` (as in the signature file).
- No design signals.

AUDIT FOCUS (design docs/tracks/P/design/KEPLER-LEAN-DESIGN.md §7 row P7-7, §7.1, decision D25; blueprint-P d25, average): (1) statements = design and blueprint (the D25 identities and the averages over the product Poincaré chart, with the eccentric-longitude representation); (2) proofs sound; (3) hygiene. Audit ONLY the P7-7 module(s) (git diff inp-p75...HEAD restricted to KAM/Planetary/Poincare/).
