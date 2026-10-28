# P23-18 prover handoff (branch inp-p2318, 0e8f853; contains inp-p2317 (audited); offloaded package run by the main orchestrator; prover on claude-10)


## Files (10, all < 300 lines; LimitMap.lean is the facade)
- `LimitMapScale`: `limitmap_data` (verbatim from P23Signatures), rescalings `unsc`/`sc` (max norm on `Fin (n+n)`), norm/triangle lemmas.
- `LimitMapPsi`: `PsiSteps` (Prop bundle = proved outputs of `iterative` about `Ψ_{j+1}`, `Φ_j`, `D_j`), `iterative_steps` (applicability: ActionSteps + PsiSteps projected from ONE `iterative` output, same witnesses), `psiR`, `phaseTube`, `psi_step` (pl-dom, pl-disp, real).
- `LimitMapLip`: `unsc_mem`, `scaled_bound`, `psi_lip_step` (pl-lip: `lip_sup` with N=2n, ε_j=min{ρ_{j+1}/2ρ̂₀, s_{j+1}/s₀}, constant 192 n c^j Ê_j).
- `LimitMapPack`: `psi_lip_of_steps` (local `psi_lip`: maps-to, scaled displacement (3/4)Ê_j/12^j, Lipschitz ς_j, Σς ≤ 384nÊ₀ < 1/20).
- `LimitMapPhi`/`LimitMapDisp`/`LimitMapLimit`: composition rule `phi_lip` (∏(1+ς)−1), complex telescoping `phi_disp_complex`, `lp_le` (≤768nÊ₀<1/10), Cauchy/limit `phi_limit`, `phi_disp_real`.
- `LimitMapReal`: `PsiSteps.limit_phi_real_of_steps` (uniform limit on ℝⁿ×D_*, 768nÊ₀ Lipschitz, 9/10–11/10, InjOn, lattice identity, 3 block sup bounds 3/2·…).
- `LimitMapStrip`: `StripLimit`, `strip_comp`, `limit_phi_strip_of_steps` (complex θ-extension per coordinate via `fourier_compact`, strip |Im θ|<s̄/2π, bounds 3/2·…, derivative convergence).
- `LimitMap`: facade + `limit_map_of_iterative` (joint check: iterative_steps → limit_actions_of_steps → limit_phi_real → strip on the same witnesses, D_* = ǐ(D₀)).

## Private-interface inventory (release gate)
| local obligation | helper | application |
|---|---|---|
| psi_lip pl-dom/pl-disp | `PsiSteps.psi_step`, `psi_disp`, `psi_lip_of_steps` (1,2) | needs `PsiSteps` fields psi_diff/real/bd/tube/rho_* from iterative |
| pl-lip | `psi_lip_step` → `psi_lip_of_steps` (3) | lip_sup (P23-07) |
| pl-sum | `psi_lip_of_steps` (4–6) via `sums` | |
| lp-tele | `phi_disp_complex`, `phi_disp_real` | psi_bd + psi_maps |
| lp-cauchy | `phi_lip`, `lp_le`, `phi_step_diff`, `phi_limit` | |
| lp-per | `limit_phi_real_of_steps` (lattice, InjOn) | phi_per |
| lp-an | `limit_phi_strip_of_steps` | fourier_compact (P23-09) |
Hypotheses of all helpers: only `PsiSteps` (every field a projection of `iterative`, discharged by `iterative_steps`) and `hD : D_* ⊆ realTube (Ds j) (ρ_j/2) ∀ j` (the proved output (ii) of `limit_actions_of_steps`, instantiated in `limit_map_of_iterative`), `hU` (output of limit_phi_real). No conclusion-shaped hypotheses. Witness variables: `Ds hs fs Ψ Φ is` of `iterative`.

## Checks
- Gate build `KAM.Planetary.TwoScale.LimitMap`: success, no errors, no sorry. `scripts/lint_sources.sh`: PASS except "KAM.lean is out of date" (generated; not edited).
- `#print axioms` for psi_lip_of_steps, limit_phi_real_of_steps, limit_phi_strip_of_steps, iterative_steps, limit_map_of_iterative: [propext, Classical.choice, Quot.sound].
- No heartbeat overrides, no design signals. No file >300 lines.

## Notes / deviations / uncertainties
- No signatures existed for psi_lip/limit_phi; statements are mine, from blueprint P3b L45–95 and the design's bullets. `limitmap_data` copied verbatim from the signature file (was not yet in KAM).
- Strip result is coordinatewise (as `fourier_compact` is scalar); angle bound is `(3/2)Ê₀s₀/(2π)` per coordinate, first/last action blocks per coordinate with `(M̂/M)` / 1. Derivative convergence is for the finite-stage coordinate functions `stripSeq` of `Φ_j(θ,I)−(θ,I)`.
- Lipschitz/Cauchy bounds use `Ê_j<1/160` (proved) wherever blueprint uses weaker constants; psi_disp bound uses `ρ̂_j ≤ ρ̂₀/16^j ≤ ρ̂₀/12^j`.
- The "scaled displacement" uses (3/4)Ê_j 12^{-j} (equal to the blueprint's with k=j+1).
- Suspected errata: none found.
- Not done here: P23-19/20/21 consume these (invariance's common inner domain not covered).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md: row P23-18, the psi_lip / limit_phi bullets, finding N2 and the 'Private-interface release gate'; blueprint P3b L45-L95; P23-17 audit docs/tracks/P/audits/P23-17-audit-1.md for the parallel ActionSteps ruling; signature file .drafts/design/P23Signatures.lean for limitmap_data). P23-18 is a PRIVATE conditional package except limitmap_data (verbatim). Refute-first: (1) PsiSteps is a Prop bundle: verify EVERY field is exactly a proved output of iterative on the same witnesses, discharged in full by iterative_steps (projected from ONE iterative output together with ActionSteps), with no field that smuggles a limit_phi/psi_lip conclusion or a hard step; (2) psi_lip_of_steps, phi_lip, phi_disp_complex, phi_limit, phi_disp_real, limit_phi_real_of_steps and limit_phi_strip_of_steps prove every obligation of the design bullets (scaled composition, 768n bound, common strip, InjOn, lattice identity, block sup bounds, derivative convergence); check the constants 192n c^j Ehat_j, 384n Ehat_0 < 1/20, 768n Ehat_0 < 1/10 are proved, not assumed; (3) limit_map_of_iterative really chains everything on the SAME witnesses with D_* = icheck(D_0); (4) the inventory maps each local obligation to a helper; the prover notes invariance's common inner domain is NOT covered (P23-20): confirm nothing claims it; (5) proofs sound, no sorry/axioms; (6) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/TwoScale/LimitMap*.lean (the branch diff also shows many files from a newer inp base; ignore them).
