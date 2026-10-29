# SO-FREQ prover handoff (branch inp-sofreq, 6c395ff8; track SO package run by the main orchestrator)


## Files (new)
- `KAM/Certificate/Freq.lean`: `FreqBox`, `FreqEncloses`, `algFreq`, `checkAlgBox`, `algFreq_encloses`
  (signed verbatim; helpers `algTermLo/Hi`, `algRowLo/Hi`, private `algTerm_bounds`).
- `KAM/SpinOrbit/Freq.lean`: `lunarFreqMinus_eq`, `lunarFreqPlus_eq` (signed verbatim), built on
  `lunarNuMinus_eq`/`lunarNuPlus_eq` of the landed QuadraticDiophantine.

## Approach
Rational interval evaluation per coordinate: each term `a x^j` bounded using `0 ≤ lo ≤ x ≤ hi` and
the sign of `a`; sums bounded termwise. `checkAlgBox` also checks `box.length = n` and `0 ≤ lo`
(the signature has no `0 ≤ lo` hypothesis, so the Bool checks it). Lunar equalities: `algFreq` on
`[[a,b],[c]]` unfolds to `![a + b x, c]`, then `ring` with `lunarNuMinus_eq`.
The `IsDiophantine` theorems stay in QuadraticDiophantine (`lunarNu*_half_isDiophantine`).

## Checks
- gate build `KAM.Certificate.Freq KAM.SpinOrbit.Freq`: "Build completed successfully (2197 jobs)", no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
  It prints "KAM.lean is out of date" (new modules; KAM.lean is generated, not edited by me).
- No line > 100 columns. Kernel `decide` sanity of `checkAlgBox` on the lunar `ν₋` row with a box succeeded.
- `#print axioms` of `algFreq_encloses`, `lunarFreqMinus_eq`, `lunarFreqPlus_eq`:
  `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- None for the signed statements. `FreqBox`/`FreqEncloses`/`algFreq` are `noncomputable`/`abbrev` as in the draft;
  `checkAlgBox` body is mine (draft was `sorry`). Names `algTerm*`/`algRow*` are new short names (grep-clean).
- Downstream: `lunarLowerCert_freq` needs the box from a certificate (later package).

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 3); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Design section G 'Exact frequencies' and section I 'Lunar frequencies' (finding F1 of design audit 1: the frequency is an exact real, and a rational box encloses it). The branch was cut from inp-soaif, which has since landed on inp; audit only the two Freq modules. Check that the lunar frequency is EXACTLY (nu, 1) with nu = 1 - 1/(40+g) resp. 1 + 1/(40+g), g the golden ratio, matching the landed KAM/Certificate/QuadraticDiophantine.lean, and that checkAlgBox (prover's own body; the draft had sorry) soundly proves the enclosure.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Freq.lean and KAM/SpinOrbit/Freq.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
