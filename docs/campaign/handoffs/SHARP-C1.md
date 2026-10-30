# SHARP-C1 handoff: corner bounds (checker side)

## Files (new, `KAM/CertificateSharp/Corner/`, `Tests/Corner.lean`; nothing under `KAM/Certificate/` touched)
- `Vertex.lean`: the vertex inequality for `exp(-Σ a_i y_i)` (product weights `Λ_σ`, convexity of exp),
  `vertex_sum_conv`, `vertex_sum_le`.
- `SupBound.lean`: `signLists`, `dotList`, the lower weight `wloOf` (Taylor lower bound of `e^{2πρ}` computed
  from the weight: **no new certificate data**), `expUb`, `cornerSumUp`, `cornerUp`, `cornerLeq`,
  `norm_le_conv` (convex-combination form), `norm_le_of_cornerLeq` (single model), and the joint row-sum
  version `rowCornerUp/rowCornerLeq`, `sum_norm_le_of_rowCornerLeq`.
- `Checks.lean`: `checkInvarianceCorner` and `checkEmbeddingCorner` with
  `checkInvarianceCorner_sound_of` / `checkEmbeddingCorner_sound`. Same contracts as the landed
  `checkInvariance_sound_of` (field `hE`) and `checkEmbedding_sound` (fields `hball`, `hDK`); the
  landed model construction is reused unchanged, only the final comparison is replaced.
- `Certifier.lean`: `checkTorusCertificateCorner E` (static, ham, **corner** embedding, **corner**
  invariance, energy, gram, torsion, `E.test`), `checkTorusCertificateCorner_sound` (every engine),
  `checkTorusCertificateCornerSharp` and its unconditional soundness (engine `sharpEngine`),
  `checkTorusCertificateCorner_of_old`.
- `Tests/Corner.lean`: non-flat test model and the toys.

## Design decisions
- Vertices: all `2^n` sign vectors (no `2^{n-1}` conjugation saving; negligible for `n = 2, 3`).
- `e^{2πρ j}` for `j < 0` is bounded through `wlo⁻|j|` with `wlo` the order-`expOrder` Taylor sum of
  `e^{2π_lo ρ}`; the weight data of the certificate is unchanged.
- Rows of `DK` use the **joint** vertex (`rowCornerLeq`: `Σ_j cornerUp σ m_j ≤ b` for every `σ`), not a
  sum of per-entry maxima (CertArith has no `max`; the joint form is also the stronger statement).
- **Not done:** corner variants of `checkGram` (σB, ≈ 8 %) and `checkTorsion` (inverse exact, nothing
  to gain), the cosh primitive (C3). `checkGram`/`checkTorsion`/`checkEnergy` are the landed ones, as
  the design table allows (`checkTorsion_sound_of`, `checkEnergy_sound_of` take the embedding
  contract, which the corner embedding check supplies).

## Measured comparison (landed vs corner)
- Toys T2, T3, T2d (flat: `U ≡ 0`, constant `A`): identical bounds for every invariance row and every
  `DK` row (log10 `−42.7949` / `−64.3010` / `−63.8997` equal; `DK` rows 1 and 0), as study §1.3
  predicts. Both corner checks and the whole `checkTorusCertificateCornerSharp` pass by `decide
  +kernel` on T2 and T3 (`toyCert2_corner_passes`, `toyCert3_corner_passes`).
- Non-flat model `e_{(1,1)}+e_{(1,-1)}`, `ρ = 1/100`, `w = 1.065`: landed `2.268`, corner `2.134`
  (kernel-checked: the landed check fails at `b = 2.2`, the corner check passes, and the corner check
  fails at `b = 2.13`, so it is a genuine bound). Anisotropic `(30, ±10)`: landed `24.83`, corner
  `15.94` (0.19 orders), by `#eval` (the design's 2^{n-1} limit is approached for strongly
  anisotropic supports). The R1 gains (+0.75–0.82 orders under v1) are the study's, from
  `optimize.py`; I did not run lunar data.

## Checks
- `nice -n 5 lake build KAM.CertificateSharp.Corner.{Vertex,SupBound,Checks,Certifier}
  KAM.CertificateSharp.Tests.Corner`: success, no heartbeat options.
- `lint_sources.sh`: no complaint on `KAM/CertificateSharp`; only the known ABI-scratch failure.
- `#print axioms` of `exp_le_vertex`, `vertex_sum_conv`, `norm_le_of_cornerLeq`,
  `sum_norm_le_of_rowCornerLeq`, `checkInvarianceCorner_sound_of`, `checkEmbeddingCorner_sound`,
  `checkTorusCertificateCorner_sound`, `checkTorusCertificateCornerSharp_sound`,
  `corner_model_bound`, `toyCert{2,3}_corner_passes`: `[propext, Classical.choice, Quot.sound]`.
- `KAM.lean` regenerated.

## Uncertainties
- `checkEmbeddingCorner_sound` and `checkInvarianceCorner_sound_of` are near-copies of the landed
  proofs (as the design predicted); if the SO track changes the landed proofs they must be re-synced.
- Python optimizer unchanged.
