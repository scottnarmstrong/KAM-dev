# N11-D prover handoff (branch inp-n11d, ca5b8ed5; offloaded package run by the main orchestrator)


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

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-D (real_system incl. field periodicity; Fourier gradient real/imaginary spans; continuation) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Audit ONLY KAM/Nekhoroshev/Partial/{RealSystem,Continuation}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
