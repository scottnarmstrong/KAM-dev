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
| SHARP-DESIGN (+ DOCFIX) | blueprint `p2s-sharp` (fixed frequency) and `p2s-iso-sharp`: HL19 torsion route (no 1/δ), torsion perturbation O(d/δ), 3δ schedule, separate norms, generic small-divisor data, one Newton engine for both theorems; exact signatures; threshold mirror script. Two independent audits (fixed: request changes to the written proof only; iso: pass with minor corrections), all corrections applied | integrated |
| SHARP-A1 … A7 | the engine (`KAM/Sharp/Engine`), constants, torsion identity and bound, step, `KAM.Sharp.g1_sharp` (fixed frequency) and `KAM.Iso.Sharp.g1_sharp` (isoenergetic), with Parseval and crude instances. Each final theorem has the binders of the sealed explicit theorem and implies the frozen G1 / I-G1 | integrated |
| SHARP-A8 | `KAM/CertificateSharp/`: an engine-agnostic certifier (`checkTorusCertificateWith`), the old engine as a regression (`rfl`), rational mirrors of the sharp constants, `checkTorusCertificateSharp` and its unconditional soundness `checkTorusCertificateSharp_sound`. Toy margins (threshold/error): T2 10^4.3 → 10^19.4, T3 10^4.3 → 10^27.9 | integrated |

## Rules that protect the SO track
- Additive only: new modules under `KAM/Sharp/**`, `KAM/Iso/Sharp/**`, `KAM/Strip/*Parseval*`, `KAM/Strip/*Russmann*`.
  No existing declaration, file or frozen statement changes; `KAM.lean` only gains imports (regenerated).
- Nothing under `KAM/Certificate/**`, `KAM/SpinOrbit/**`, `scripts/spin_orbit/**`, `certificates/**`,
  `docs/tracks/SO/**`, the HQ files or `README.md` is edited. The new checker lives in new files beside the old one.
- Deferred until the lunar certificates are done: re-deriving the sealed `g1_explicit` theorems from the new engine and
  deleting the duplicated iteration code (this would rebuild modules upstream of the certificate checker).

## Result (v1)

Design threshold for the lunar package R1 (isoenergetic, Rüssmann data): about 10⁻²⁵, against 10⁻⁷⁵ for the sealed
`g1_explicit` (`scripts/apost_sharp/thresholds.py`, design §6). The owner decided (2026-10-30) that the lunar
certificate will switch to the sharp certifier. Work continuing on later branches: v2 (uniform dominance over the
published explicit theorems), the checker-side sharpness study, the applications study.
