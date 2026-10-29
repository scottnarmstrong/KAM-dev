# N11-M1 and N11-M2: independent audit 1

Lane N (Zohar's team), 2026-10-28. This is an independent, refute-first, read-only audit. Nothing was compiled
during the audit; the gate build is recorded separately: commit `e6c962b6` on `zohar/n11`, 0 errors.
- **Scope:** `KAM/Nekhoroshev/Partial/Nonresonant.lean` (N11-M1, `nonresonant`) and
  `KAM/Nekhoroshev/Partial/Resonant.lean` (N11-M2, `resonant`). Both were compiled against the signed
  statement of `nf` (N11-K2), which was then a stub.
- **Read against:** the signature file, the design rows and decisions, blueprint p11c L43–121, and every
  upstream lemma the two files consume.

## Verdicts

- **N11-M1 `nonresonant`: PASS WITH NOTES.**
- **N11-M2 `resonant`: PASS WITH NOTES.**

Neither file has a soundness or fidelity defect. Both depend on `nf` only through its signed statement, and
must be re-gated once K2 lands.

## (a) Signed declarations

Each statement was compared with the signature file after whitespace normalization.

| Declaration | File:lines | Result |
|---|---|---|
| `nonresonant` | Nonresonant.lean:342–353 | IDENTICAL |
| `resonant` | Resonant.lean:334–347 | IDENTICAL |
| `nf` (consumed) | NormalForm.lean | IDENTICAL |

## (b) Node coverage

| Node | Declaration or step | Result |
|---|---|---|
| `bpN:p11:nonresonant` | signed `nonresonant` | PASS |
| `stepN:p11:nr-nf` | `nf` with Λ = {0}; `ExtConjHyp` from the `nf` clauses | PASS |
| `stepN:p11:nr-t12` | (T1) `nnr_fast_re_le`/`nnr_slow_re_le`; (T2) `preimage` with ρ = r/2, σ = s/3 | PASS |
| `stepN:p11:nr-t3` | proved: `real_system_resonant` with resSpan {0} = ⊥, `real_system_bounds`, mean value bound | PASS |
| `stepN:p11:nr-concl` | `transfer_conditional`, final bound 31 r/64 ≤ r/2 | PASS |
| `bpN:p11:resonant` | signed `resonant` | PASS |
| `stepN:p11:rs-red` | `nrs_key`, `nrs_nf_small`: the smallness for `nf` is derived from ε ≤ m r²/2¹⁴ | PASS |
| `stepN:p11:rs-nf` | `nf`, `FastConvex.toRealFastConvex` (Revision 2 F1), g ≤ 5ε/4, η ≤ ε/e, slow loss | PASS |
| `stepN:p11:rs-t12` | (T1) in `euclid`; (T2) `preimage` | PASS |
| `stepN:p11:rs-t3` | `nrs_t3` = `energy_free` with r̃ = r/2, s̃ = s/6, δ = m r/32, ζ = η | PASS |
| `stepN:p11:rs-concl` | `transfer_conditional` with `Nrm = euclid`, final bound 129 r/1024 ≤ r/2 | PASS |

## (c) Soundness

- Premise T3 is proved in both files before `transfer_conditional` is applied (decision 5); neither file
  assumes it.
- Neither signed theorem gains a premise.
- The margins were checked by hand against each lemma's statement:
  - **`preimage`:** κ ≤ 1/4.
  - **`transfer_conditional`:** d + a < r/2 and dx < r/2.
  - **`energy_free`:** ε ≤ m(r/2)²/2¹², δ = m(r/2)/16, d < δ/(4M), and the time bound.
  - **M1 drift:** 6 r/(5e) ≤ 15 r/32, using `Real.exp_one_gt_d9`.
- The files use only the following clauses of `nf`, so the real `nf` cannot break them:
  - holomorphy, maps-to, canonicity and reality;
  - the classes of `g` and f_*, and the support of `g`;
  - the identity;
  - the two weighted bounds;
  - the three displacement bounds.

## (d) Hygiene

- No `sorry`, `axiom`, `admit`, heartbeat options or `EuclideanSpace`.
- Lines are at most 100 characters.
- Every helper is `private` (prefixes `nnr_` and `nrs_`), so no public helper names are reused.

## Findings

- **M-1 (low, verification), Nonresonant.lean:233.** `ContinuousLinearMap.add_apply` was replaced by bare
  `add_apply` to clear a deprecation warning. Resolved: the edited file is the one gate-built in `e6c962b6`.
- **M-2 (info, landing).**
  - Re-gate both files, and `#print axioms`, against the real `NormalForm.lean`.
  - Any new public `KAM.Nekhoroshev` name in K1/K2 must not shadow a name these files reach through
    `open KAM.Weighted KAM.NormalForm`. The K1/K2 short-name check covers this.
- **M-3 (info, docstring), Resonant.lean:287.** The docstring now says "240 M T η ≤ s m r", which matches
  the hypothesis. Fixed.
- **M-4 (info, duplication).** `nnr_ext_class_add` copies the public `ext_class_add` of
  EnergyIdentity.lean. The reuse is optional and not done.
- **M-5 (info, proof route), recorded deviations; no statement changes.**
  - nr-t3 uses a direct mean-value bound over the whole interval instead of the blueprint's exit-ball
    contradiction (p11c L72). This is valid because the velocity bound holds on all of the real domain
    at radius r_B/2.
  - (T1) uses |Re a − x| ≤ |a − x|.
- **M-6 (info, imports and size).**
  - Both files import F1's `CompositionCoeff` for `wbound_add_ext`. This creates no import cycle.
  - M1 is 474 lines against an estimate of 350.
