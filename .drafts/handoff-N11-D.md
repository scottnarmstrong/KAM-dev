# Handoff N11-D (Hypotheses / real systems and continuation)

Branch inp-n11d. Hard rules respected: no maxHeartbeats, files 443 + 110 lines, no sorry/axiom,
no EuclideanSpace, lines <= 100 columns.

## Files (new)
- `KAM/Nekhoroshev/Partial/RealSystem.lean` (443 lines)
- `KAM/Nekhoroshev/Partial/Continuation.lean` (110 lines)
(KAM.lean not edited; lint reports it out of date, which is expected.)

## Declarations (signatures copied verbatim from N11Signatures.lean; only line-wrap in real_system)
- `KAM.Nekhoroshev.real_system` (graph `bpN:p11:real-system` (a),(b) = rs-a, rs-b, incl. field
  periodicity `realWfield` integer-angle invariance, design audit F2)
- `KAM.Nekhoroshev.real_system_bounds` (rs-cd (c))
- `KAM.Nekhoroshev.real_system_resonant` (rs-cd (d); both Re and Im spans, audit F3)
- `KAM.Nekhoroshev.continuation` (`bpN:p11:continuation`; ct-data = private
  `uniform_data_periodic`, ct-concl = the theorem body via `KAM.ODE.gen_continuation`)

## Approach
- Regrouping/derivative transport on `EC n k` is done locally: private `extCxCLM` (real points as a
  CLM), `fderiv_ext_real` (unequal-carrier analogue of `KAM.hamiltonian_real_fderiv`, no equality
  premise), component identities via `ext_cases` (Coordinates), symplectic cancellation
  `clm_realWfield_zero` through `Fin.sum_univ_add`.
- Energy: orbit for radius r <= R; fields built from `realHamiltonianExt b r H` and `... R H`
  agree on `realDom r` because fderivs agree on an open set.
- Bounds/resonant: Part 7 fixed-base Fourier argument generalised to base dimension n+(k+k)
  (private copies of the Part-7 helpers, distinct names).
- Continuation: `gen_uniform_periodic` proof redone with independent transverse dimension N.
- All helpers are `private`, so no public short names were added.

## Checks
- Gate build `KAM.Nekhoroshev.Partial.RealSystem KAM.Nekhoroshev.Partial.Continuation`:
  "Build completed successfully"; only warning in my files: unused binder `hR` of `real_system`
  (kept: signature verbatim).
- `#print axioms` of real_system, real_system_bounds, real_system_resonant, continuation:
  [propext, Classical.choice, Quot.sound] each.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK;
  only complaints were the 103-column line (fixed afterwards) and the generated KAM.lean being stale.
  Final rerun after the fix: no long-line complaint; check_lean_modules PASS, guards OK.

## Uncertainties / errata / deviations
- None. No statement was false or under-hypothesised. `hR` of `real_system` is unused (the
  statement is true without it). Pre-existing linter noise in Coordinates.lean (N11-A) is not mine.
- Design signals: none (all proofs elaborate at default heartbeats, <= 20 s per file).
