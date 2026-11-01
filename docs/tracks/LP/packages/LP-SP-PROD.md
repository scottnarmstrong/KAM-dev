# Package LP-SP-PROD: the n-body spatial product chart (MAIN Lemma 17 for n bodies, (45) summed, (47) identity)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spprod` = `inp-lp` + LP-SP-ROT + LP-SP-CHART +
LP-SP-MODEL + LP-SP-GEO (handoffs in `docs/tracks/LP/audits/`).

## Template

The planar product chart `KAM/Planetary/Poincare/Product.lean` (`planetBlock`, `poincareProd`, `poincareProdDom`,
`regionProd`, `poincareProd_symplectic`, `poincareProd_image`, `movingHamiltonian_poincareProd`,
`analyticOnNhd_poincareProd`) and track P's `Exponential/Dictionary.lean` (`sec_domain_chart_facts`, `chartAMD`).

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 17 (533–578; the last sentence of the statement: the fixed-plane deficit
`C_{e₃} = Σ I_i − L·e₃ = ½ Σ (x_i² + y_i² + u_i² + v_i²)`), Lemma 18 (580–597: the alignment of `e₃` with `L`, and
`C_{e₃} = C` along a solution), with `source/AMENDMENTS.md` N12 (the spatial chart has `n` fast and `2n` slow pairs).

## Owned files

`KAM/Planetary/Spatial/Product.lean` (and parts). Do not edit other files.

## Statements

1. **Layout.** A chart phase `Phase (n + (n + n) + ...)`-style layout with `n` fast pairs `(λ_i, I_i)` and `2n` slow
   pairs (`(ξ_i, η_i)` and `(v_i, u_i)` in LP-SP-CHART's slot convention). Choose a clean layout, document it, and
   provide block maps. Prefer `Phase (n + 2 * n)` or `Phase (n + (n + n))` so that `Nekhoroshev.PartialBlock n (2*n)`
   slots match (`fastAction`, `slowPair` in `KAM/Nekhoroshev/Partial/Setting.lean`).
2. **Product chart.** `spatialPoincareProd ν w : Phase (n * 3)`, applying LP-SP-CHART's `spatialPoincare (ν i)`
   to each body block, and `spatialPoincareProdDom` (each block in (44)). Prove:
   - analyticity on the domain;
   - fast-shift periodicity;
   - symplecticity (block sum of LP-SP-CHART item 5, in the repository's symplectic-form convention);
   - the image is the set of states with negative energies and positive `e₃`-projections `(q_i ⨯₃ p_i) · e₃ > 0`;
   - injectivity mod the fast lattice, and local analytic diffeomorphism.
3. **(45) summed / fixed-plane deficit.** On the domain:
   - `spatialKeplerAction ν (Ψ w) i = I_i`;
   - `angularMomentum3 (Ψ w) · e₃ = Σ_i (I_i − Γ_i − Z_i)`;
   - hence `Σ_i I_i − L · e₃ = Σ_i (Γ_i + Z_i)`, i.e. `spatialFixedPlaneDeficit = chartAMD`-style, half the
     squared slow norm.
   - When `L = |L| e₃` (aligned), `spatialStrongAMD ν (Ψ w) = Σ_i (Γ_i + Z_i)` (MAIN (47) and L18 line 595).
4. **Exact split.** `spatialHamiltonian ν μ (Ψ w) = −Σ ν_i³/(2 I_i²) + μ · fSpatial (Ψ w)`, with the literal
   perturbation `fSpatial` (MAIN (1): recoil plus pair potentials), and `fSpatial ∘ Ψ` analytic on the
   collision-free part of the domain.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 2–4.

Expected size 800–1,800 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-PROD-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-PROD.md`,
then `touch .drafts/READY-LP-SP-PROD`.
