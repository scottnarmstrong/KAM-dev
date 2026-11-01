# Package LP-SP-ROT: the rotation algebra of the spatial chart (MAIN Lemma 17, formula (46) and its inverse)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp`. This is pure matrix algebra. It does NOT depend on LP-SP-MODEL, which runs in parallel and
uses the same Mathlib API.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 17, lines 533–578, in particular (46) (lines 548–556), the identity
`R e₃ = (−c v/√G, −c u/√G, 1 − Z/G)` (lines 557–560), and the inverse (lines 571–576). Read with
`source/AMENDMENTS.md`.

## API (binding, for compatibility with LP-SP-MODEL)

Vectors `Fin 3 → ℝ`, Mathlib `crossProduct` (`⨯₃`, `Mathlib/LinearAlgebra/CrossProduct.lean`), `dotProduct`,
matrices `Matrix (Fin 3) (Fin 3) ℝ` with `Matrix.mulVec`, `Matrix.transpose`, `Matrix.det`. Write `e₃ = ![0,0,1]`.
Never `EuclideanSpace`.

## Owned files

`KAM/Planetary/Spatial/Rotation46.lean` (and parts `KAM/Planetary/Spatial/Rotation46/*.lean` if needed). Nothing
else; never touch LP-SP-MODEL's files.

## Definitions (literal (46))

- `skewMatrix t`, the matrix of `w ↦ t ⨯₃ w`.
- `incTilt u v G : Fin 3 → ℝ := (1/(2√G)) • ![u, −v, 0]` (`t` in (46)).
- `incCos u v G := √(1 − |t|²)` (`c`).
- `incRotation u v G := (1 − 2|t|²) • 1 + 2 • vecMulVec t t + 2c • skewMatrix t` (`R`).

## Theorems

Carrier: `0 < G` and `Z := (u² + v²)/2 < G` (MAIN (44) gives `Γ + Z < I`, i.e. `Z < G`). Then
`|t|² = Z/(2G) < 1/2`.

1. `skewMatrix t * skewMatrix t = vecMulVec t t − |t|² • 1`.
2. `incRotationᵀ * incRotation = 1` and `det incRotation = 1` (a rotation).
3. `incRotation.mulVec e₃ = ![−c v/√G, −c u/√G, 1 − Z/G]` (MAIN line 559).
4. For planar vectors `Q`, `P` embedded as `![Q 0, Q 1, 0]`:
   - `(R Q) ⨯₃ (R P) = R (Q ⨯₃ P)` (rotations preserve the cross product);
   - if `Q ⨯₃ P = G e₃`, then `(R Q) ⨯₃ (R P) = G • R e₃`; hence the projection on `e₃` is `G − Z` (MAIN (45):
     `H = I − Γ − Z`, with `G = I − Γ`).
5. **Inverse (MAIN lines 571–576).** With `ŵ = R e₃`, `ŵ₃ > 0` on the carrier, `c = √((1 + ŵ₃)/2)`, and
   `u = −√G ŵ₂/c`, `v = −√G ŵ₁/c`, both recovered exactly. So `(u, v)` is determined by `R e₃` and `G` (injectivity
   of `(u, v) ↦ R e₃` on the carrier).
6. **Analyticity.** The entries of `incRotation` are real analytic in `(u, v, G)` on the open carrier
   `{0 < G, (u² + v²)/2 < G}` (`AnalyticOnNhd`).

Out of scope: the full spatial chart (composition with the planar chart, symplecticity, the image/inverse of the
whole chart). That is the next package.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–6.

Stop when done or blocked; report, and never add a hypothesis silently. Expected size 400–1,000 lines. Prefer
`Matrix.ext` with `fin_cases` and focused `ring_nf`/`field_simp` lemmas over a large `nlinarith`.

## Handoff

`docs/tracks/LP/audits/LP-SP-ROT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-ROT.md`,
then `touch .drafts/READY-LP-SP-ROT`.
