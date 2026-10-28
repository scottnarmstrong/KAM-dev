# N11-E3 prover handoff (branch inp-n11e3, 6110c022; contains N11-A and N11-B (both passed); offloaded package run by the main orchestrator)


## Files (new)
- `KAM/Nekhoroshev/Partial/Domain.lean` (≈435 lines)
- `KAM/Nekhoroshev/Partial/Hessian.lean` (≈360 lines; imports Domain because `hessian*` mention `signedH`)

## Declarations (verbatim from N11Signatures.lean; checked by an `example`-style file restating each signed
theorem and closing it with the proved one — elaborated with no error; defs compared textually)
- Domain: `block_setting`, `signedH`, `signedF`, `slowScale`, `blockPert`, `physicalDomain`, `domain`
  (steps dm-pts, dm-norm), `domain_field` (dm-field). Only reformatting: two long lines of `domain_field`'s
  statement wrapped (lint 100 cols).
- Hessian: `FastConvex.toRealFastConvex`, `hessian_at_sign`, `hessian` (hs-op, real-hessian bridge).
- Already in N11-A/B (not redone): FastConvex/RealFastConvex, PartialData, DefiniteSign.
- Extra public helpers (unique short names, grep-checked): `polyNbhd_realBall_subset` (Domain; real ball
  of radius ≤ ρ around Ic ∈ G lies in actionNbhd G' ρ), `realPart_hessian_apply` (Hessian; real Hessian of
  `realPart h` at a real point = Re of the complex Hessian on real vectors, h holomorphic on an open set).

## Approach
- `domain`: complex points → `partialComplexDomain` via `blockLift_mem` (private; uses lam·R = d/4, innerCore,
  collar, r0 ≤ ρ/2); holomorphy by composing the frozen `P` with the affine map `blockLift ∘ slowScale`;
  periodicity via `blockLift_shift` and the frozen shift invariance; reality via `thetaInv`/`complexifyPhase`;
  weighted bound by `KAM.Weighted.wbound_of_sup_bound` (s+s = ρ/2π) giving `coth(πs)^n · μ/2π = eps μ`.
- `domain_field`: the frozen `degenerateHamiltonian` is unguarded, so `σ · converted H = Re(liftFast + signedF ∘ extCx)`
  holds pointwise everywhere (`blockLift_extCx`); then `realWfield` commutes with σ = ±1.
- `toRealFastConvex`: Re ≤ norm after `realPart_hessian_apply`; Euclid norm of reals = of their inclusion.
- `hessian_at_sign`: m ≤ Mc from one unit vector at a point of G; FastConvex fields via
  realPart(signedH) = σ/(2π)·realPart h, `fderiv_const_smul_field`, and a Euclid column bound from the
  operator-norm bound (`hessHelper_hess_bound`, test vector conj of the column). `hessian` extracts σ from the
  frozen `HasDefiniteFastPart` witness and adds the frequency bound.

## Checks
- `inp_lake_build.sh … KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian`: Build completed
  successfully (only unused-variable warnings, below).
- `scripts/lint_sources.sh`: only output other than PASS lines is "KAM.lean is out of date" (generated; not edited
  per rules); check_lean_modules PASS; FROZEN-ANCHOR GUARD OK; ABI HASHES OK.
- `#print axioms` of `hessian`, `hessian_at_sign`, `FastConvex.toRealFastConvex`, `domain`, `domain_field`,
  `realPart_hessian_apply`: all `[propext, Classical.choice, Quot.sound]`.
- No sorry/axiom/maxHeartbeats; no file over 1500 lines; no design signals.

## Uncertainties / notes
- `domain_field` holds without its hypotheses (hμ, hσ, hIc, hR, hRR, hd, hP unused → linter warnings): the statement
  is signed, so kept verbatim; the equality is in fact global because `degenerateHamiltonian` has no guard.
- Hessian imports Domain (design table lists them as independent leaves; the signed `signedH` lives in Domain).
- `ext_class` in `domain` is proved from InClass at 2s (monotone to s), as the weighted bound needs width s+s.

## Suspected errata / deviations
None found in the sources for these nodes. Deviation: only the import direction above.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-E3 (physicalDomain/block_setting/blockPert, complex domain, field equality, selected sign, FastConvex/RealFastConvex and toRealFastConvex) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node mapped to Domain/Hessian is established (in the proof or as an export); an UNSIGNED export named after a graph node states that node's literal conclusion; signed declarations follow the signature file; definitions mean the source objects on their whole carriers (frozen perturbation/definiteness consumed as defined); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Nekhoroshev/Partial/{Domain,Hessian}.lean.
