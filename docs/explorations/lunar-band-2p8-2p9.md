# Lunar spin–orbit band: aim for 2.8–2.9 %

30 October 2026. A proposal for the SO track, written on the side branch `apost-sharp`. Nothing here changes the
current SO plan: the 3.3 % certificate stays the first milestone.

## Summary

- **Proposal.** Once the sharp a-posteriori theorem lands, re-target the lunar barriers from ν± = 1 ± 1/(40+g) to
  about 1 ± 1/(50+g) or 1 ± 1/(60+g), with g = (√5−1)/2. That shrinks the band from |p − 1| ≤ 3.3 % to roughly
  **2.9 % or 2.8 %**.
- **Floor.** No rotational barrier can do better than the separatrix of the synchronous resonance, at
  |p − 1| ≈ 2.62 % in this model. The gain available with the present geometry is about 0.4–0.6 points, not an order
  of magnitude.
- **Why it becomes affordable.** The sharp theorem moves the required invariance error from about 10⁻⁷⁵ to about
  10⁻²⁵ for the current package R1 (`docs/campaign/design/APOST-SHARP-LEAN-DESIGN.md` §6). The saving can be spent on
  tori closer to the resonance.
- **Literature.** A certified 2.8–2.9 % band would be tighter than the classical rotational benchmark this project
  reproduces (Celletti's ≈ 3 % interval with the same barrier frequencies). As far as we know, it would be the first
  formally verified band of this kind. It does not supersede the published *librational* trapping tori: those prove
  a different, stronger confinement for near-synchronous initial data.

## Where 3.3 % comes from, and the floor

The model is the seven-term spin–orbit equation of `docs/explorations/lunar-spin-orbit-certificate-proposal.md` §2:
ε = 69/200000, e = 0.0549, synchronous coefficient A₂ = 1/2 − 5e²/4 + 13e⁴/32 ≈ 0.4962. Near p = 1 the dominant term
gives the pendulum ψ̈ = −4πεA₂ sin(4πψ), with ψ = q − φ and ψ̇ = p − 1.

- **Separatrix.** Its maximal speed is |p − 1| = 2√(εA₂) ≈ **0.02617**. A rotational invariant torus enclosing the
  synchronous resonance lies outside the separatrix, so its maximum of |p − 1| exceeds this value.
- **Other terms.** They are small near p = 1:
  - the forced oscillations from the m = 1 and m = 3 terms have amplitude about 2εAₘ ≲ 10⁻⁴;
  - the chaotic layer at the separatrix is exponentially thin, since the forcing frequency (1) is about 38 times the
    libration frequency.

  Rotational tori should therefore exist very close to the floor; certifying them is the difficulty.

Pendulum estimate of the band for each choice of barrier frequencies (exact rotation number of the pendulum orbit,
maximum of |ψ̇| on it):

| Barriers ν± | ν± − 1 | max \|p − 1\| on the barrier | Energy above separatrix |
|---|---:|---:|---:|
| 1 ± 1/(40+g) (current) | ±0.02462 | 3.19 % | 98 % |
| 1 ± 1/(50+g) | ±0.01976 | 2.89 % | 44 % |
| 1 ± 1/(60+g) | ±0.01650 | 2.75 % | 20 % |
| 1 ± 1/(80+g) | ±0.01240 | 2.64 % | 4 % |
| 1 ± 1/(100+g) | ±0.00994 | 2.62 % | 0.8 % |

The current target of 3.3 % is the 3.19 % of the first row plus the certified-graph margins. The same margins on the
second and third rows give about 2.9–3.0 % and 2.8–2.85 %.

## Cost of moving closer to the separatrix

1. **Diophantine constant.**
   - With τ = 1 the binding mode is k = (1, −1), so γ ≈ 2/(N+g).
   - From N = 40 to N = 50 the threshold factor γ⁴ costs 0.4 orders of magnitude; to N = 60 it costs 0.7. This is
     small against the ≈ 50 orders the sharp theorem gains.
2. **Analyticity and Fourier support.**
   - Closer to the separatrix the torus is less uniform, so its Fourier coefficients decay more slowly and the
     admissible strip is narrower. This is the real cost driver, because the kernel replay cost scales with the
     product support (decision D34).
   - It must be measured, not guessed.
3. **Torsion and Gram constants.** They change little between N = 40 and N = 60; the design's sensitivity table
   (§6.5) shows the threshold is not sensitive to them at this scale.

## Proposed experiment, cheap and numerical

Use the existing generator (`scripts/spin_orbit/`, rotated frame of SO-GEN2) for N ∈ {50, 55, 60}:

- compute the approximate tori and their analyticity widths;
- size the truncation to the sharp threshold (`scripts/apost_sharp/thresholds.py`, Rüssmann instance, with the actual
  majorants of each torus);
- report digits, the Fourier support of v and E, the product pairs, the max |p − 1| of the certified graphs, and the
  barrier separation.

Pick the smallest band whose certificate fits the kernel budget the SO track measured after D34. **Primary target
2.9 % (N ≈ 50); stretch target 2.8 % (N ≈ 55–60).**

## Comparison with published results

- **Celletti (1990), synchronous resonance, Part I** (ZAMP 41).
  - A computer-assisted KAM proof of invariant tori trapping the synchronous resonance from above and below, at the
    true eccentricity and oblateness of the Moon (and of Rhea, Enceladus, Dione), in a truncated model.
  - Its benchmark, reproduced by this project, uses the frequencies 1 ± 1/(40+g) and the spin interval
    [0.97, 1.03] (Celletti, *Stability and Chaos in Celestial Mechanics*, §7.3.1, as cited in the SO proposal).
  - The table above suggests these tori actually reach |p − 1| ≈ 3.2 %. That is why the Lean target became 3.3 %.
    Check the book's convention before quoting either number publicly.
- **Celletti (1994)**, librational invariant tori in the spin–orbit problem (ZAMP), and the companion paper on
  librational trapping tori (Celestial Mechanics).
  - Birkhoff normalization around the synchronous periodic orbit followed by KAM, applied to the Moon–Earth and
    Rhea–Saturn systems.
  - These tori bound the *resonance angle* for near-synchronous initial data. That is stronger than a spin-rate band
    and much tighter in |p − 1|. They are a different theorem, not a competitor of the rotational band.
- **Calleja–Celletti–Gimeno–de la Llave (2021–23).** Dissipative spin–orbit; a-posteriori constructions near
  breakdown, numerically validated rather than fully rigorous by their own description.

**Assessment.**
- A certified 2.8–2.9 % rotational band would be tighter than the classical rotational benchmark (≈ 3 %, realized
  here as 3.3 %).
- As far as we found, no published rigorous rotational band for the Moon is tighter. This was not an exhaustive
  search: the 1990 and 1994 papers must be read before any claim is made.
- It would be the first such band that is kernel-checked with exact arithmetic: the 1990s proofs used floating-point
  interval arithmetic outside a proof assistant.
- The genuinely stronger target is the librational one below.

## Beyond the floor: librational barriers

To go well below 2.6 %, use 2-tori inside the resonance, around the stable synchronous periodic orbit, as in
Celletti (1994). For initial data near that orbit the band could be a fraction of a percent, and the theorem would
say the Moon stays locked in synchronous rotation forever (the spin–orbit angle stays bounded). It needs:

- tori that are not graphs over (q, φ): either a certified symplectic change of variables around the periodic orbit
  (a Birkhoff-type normal form, then the existing primary-torus theorem), or a version of G1 for general embedded tori;
- the same two-barrier confinement argument in the three-dimensional energy level.

This is a separate project (SO proposal §13.4); scope it after the 2.8–2.9 % band.

## Caveats

- Every number in the table comes from the pendulum approximation of the dominant term. The SO generator, on the full
  seven-term model, decides.
- The thresholds of the sharp theorem are design projections until the Lean packages of `apost-sharp` are proved.

## Sources

- Celletti, *Analysis of resonances in the spin-orbit problem in Celestial Mechanics: the synchronous resonance
  (Part I)*, ZAMP 41 (1990). <https://link.springer.com/content/pdf/10.1007/BF00945107.pdf>
- Celletti, *Construction of librational invariant tori in the spin-orbit problem*, ZAMP (1994).
  <https://link.springer.com/article/10.1007/BF00942847>
- Celletti, *Stability of the synchronous spin-orbit resonance by construction of librational trapping tori*,
  Celestial Mechanics. <https://link.springer.com/article/10.1007/BF00692482>
- Calleja, Celletti, Gimeno, de la Llave, *KAM quasi-periodic tori for the dissipative spin-orbit problem*,
  arXiv:2107.02853. <https://arxiv.org/pdf/2107.02853>
- Celletti, *Perturbation theory in celestial mechanics* (survey). <https://web.ma.utexas.edu/mp_arc/c/07/07-303.pdf>
