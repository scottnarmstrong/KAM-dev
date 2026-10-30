# Side campaign `apost-sharp`: a sharper explicit a-posteriori theorem (lemma.farm, 2026-10-30)

Requested by Scott on 2026-10-30 ("make these improvements in a separate branch and then merge to main once they are
finished, without messing up the SO work"), after an analysis of the a-posteriori layer. Run on lemma.farm by a
separate orchestrator; it lands into `main` only when finished and audited.

## Why
The SO certificate checker goes through `KAM.Iso.Apost.g1_explicit`, whose threshold for the lunar package R1 is
about 10⁻⁷⁵ (`docs/tracks/SO/studies/CONSTANTS-STUDY.md`). The three dominant losses are the Cauchy bound on the
torsion (|T| ≤ C_T/δ, so a = 2κ + 2), the small-divisor exponent κ = τ + n, and the single size 𝔪 in every constant;
the 4δ-per-step schedule adds a little. A sharper theorem shrinks certificates (digits, Fourier support, kernel
memory) and is needed for any client with n ≥ 3.

## Scope and status
| Package | Content | Status |
|---|---|---|
| SHARP-PARSEVAL | `KAM.cohomological_parseval`, `KAM.cohomological_operator_parseval`: exponent τ + n/2, constant `cohConstP` (`KAM/Strip/CohomologicalParseval*.lean`) | integrated |
| SHARP-BOX | `KAM.Sharp.g1_box`, `KAM.Iso.Sharp.g1_box`: one certificate covers a parameter box (corollaries of the sealed explicit theorems) | integrated |
| SHARP-RUSSMANN-COH | `KAM.cohomological_russmann`, `KAM.cohomological_operator_russmann`: Rüssmann's exponent τ, constant `cohConstR` (`KAM/Strip/CohomologicalRussmann*.lean`) | integrated |
| SHARP-DESIGN | blueprint `p2s-sharp` (fixed frequency) and `p2s-iso-sharp`: HL19 torsion route (no 1/δ), torsion perturbation O(d/δ), 3δ schedule, separate norms, generic small-divisor data, one Newton engine for both theorems; exact signatures; threshold mirror script | in progress |
| SHARP-ENGINE, SHARP-K, SHARP-ISO | Lean proofs of `KAM.Sharp.g1_sharp` and `KAM.Iso.Sharp.g1_sharp` | after design audit |
| SHARP-CERT | a second certificate checker beside the existing one, sound through `KAM.Iso.Sharp.g1_sharp` (new files only) | last |

## Rules that protect the SO track
- Additive only: new modules under `KAM/Sharp/**`, `KAM/Iso/Sharp/**`, `KAM/Strip/*Parseval*`, `KAM/Strip/*Russmann*`.
  No existing declaration, file or frozen statement changes; `KAM.lean` only gains imports (regenerated).
- Nothing under `KAM/Certificate/**`, `KAM/SpinOrbit/**`, `scripts/spin_orbit/**`, `certificates/**`,
  `docs/tracks/SO/**`, the HQ files or `README.md` is edited. The new checker lives in new files beside the old one.
- Deferred until the lunar certificates are done: re-deriving the sealed `g1_explicit` theorems from the new engine and
  deleting the duplicated iteration code (this would rebuild modules upstream of the certificate checker).
