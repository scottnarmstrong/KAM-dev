# LP-W4C: combined audit handoff for LP-SP-CHART + LP-SP-PROD (track LP, wave 4: the spatial chart, MAIN Lemma 17)

Branch `inp-lp-w4c` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-spprod` (SP-CHART 3bc913d7 and SP-PROD e2a64cdc, on
the landed SP-ROT/SP-MODEL) + `inp-lp` (through W4B). The package diff is `git diff inp-lp...HEAD -- KAM`: the
`Spatial/Chart` facade and its parts (Defs, Elements, Analytic, RotAlgebra, LineDeriv, Symplectic, Inverse, Image,
Diffeo) and the `Spatial/Product` facade and its parts (Defs, Chart, Deficit, Split), plus the regenerated root,
about 2,370 lines. Nothing in track LP is frozen. This is the largest single mathematical package of the track
(MAIN L17, including **symplecticity**).

Prover handoffs: `docs/tracks/LP/audits/LP-SP-CHART-handoff.md`, `LP-SP-PROD-handoff.md`. Briefs:
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-SP-CHART.md`, `LP-SP-PROD.md`.

Source: `docs/tracks/LP/source/MAIN.md` Lemma 17 (533–578: (44), (45), (46), symplectic computation 562–569, inverse
571–576), Lemma 18 (580–597: fixed-plane deficit, alignment), with `source/AMENDMENTS.md` (N1 typo, N12). The
planar chart `KAM/Planetary/Poincare/*` and the landed SP-ROT (`Spatial/Rotation46.lean`) are reused.

## Orchestrator checks (kam-lp)
- `lp_build.sh` of all spatial modules in import order: built. `lp_lint.sh`: exit 0. Short-name check: OK.
  Every module docstring carries the SPEC §4 sentence.

## REPORT FORMAT
Two sections (LP-SP-CHART, then LP-SP-PROD), each with a verdict, then a combined verdict.

## AUDIT FOCUS
LP-SP-CHART:
- (46) and the domain (44) literally; the slot convention `w.1 = (λ, ξ, v)`, `w.2 = (I, η, u)` under which the
  pullback form is `dI∧dλ + dη∧dξ + du∧dv` (repository sign convention; MAIN's `(x, y) = (ξ, −η)`).
- **Symplecticity** (`spatialPoincare_symplectic`): the direct derivative computation `dR = R[ω]ₓ`,
  `symplectic_form_alg`, `rot3_form_identity`. Verify it is the actual Jacobian identity on the whole domain (44),
  with no density argument needed.
- (45): energy `−ν³/(2I²)`, `|q×p| = G`, `(q×p)·e₃ = I − Γ − Z`, eccentricity vector `R·planar`.
- Image and inverse: onto the negative-energy states with `(q×p)·e₃ > 0`; injectivity mod `2π`; local analytic
  diffeomorphism (the global inverse uses `Complex.arg`; a stated deviation, same as the planar chart).
LP-SP-PROD:
- The `n`-body layout `Phase (n + (n + n))`; the product chart's symplecticity, image and lattice periodicity.
- The fixed-plane deficit identity `Σ I_i − L·e₃ = Σ(Γ_i + Z_i)` and `spatialStrongAMD ≤ spatialFixedPlaneDeficit`
  (all `z`); the aligned equality.
- The exact split `H_μ ∘ Ψ = −Σν³/(2I²) + μ fSpatial ∘ Ψ` with `fSpatial` literal MAIN (1).
