# SO-R1B independent audit 1

Verdict: **PASS WITH NOTES** for the SO-R1B delta and all five signed declarations. No Lean correctness defect found. Notes concern stale design prose and the permitted generated-root lint exception. There is **no frozen anchor/provider in this package**: seal readiness is inapplicable. This is parameter infrastructure and kernel pre-checks, not a completed lunar certificate or confinement theorem.

## Scope and authority

Worktree `/root/code/KAM-inp-sor1b`, HEAD `f78613d89a9c4a4ccdb15896e5254a4747bcbea7`, compared with `inp` at `b54c8c61ac30dc01421424799cb95e6dadb58cbc` using the full `git diff inp...HEAD`. Also compared the stated audited predecessor `c2a05fa3...HEAD`: the same two-file delta. Changes: `KAM/SpinOrbit/LunarParams.lean` (14 additions, 12 removals), plus `docs/tracks/SO/audits/SO-R1B-handoff.md` (51 additions). No inherited implementation changes were omitted.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, SO-R1B handoff and producer brief, signed `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean` §I.4, SO design §6 and Appendix I.4, and the SO-DATA-1 report/handoff in `/root/code/KAM-inp-sodata1`. The producer brief explicitly authorizes the updated body under overnight ruling D29; it controls over older descriptive numbers. This SO package has no SO `statement.md` or SO frozen anchor/blueprint theorem; the signed interface and checker definitions supply its contract. Reviewed `CertParams`, `checkStatic`, `checkSmallness`, `hamBoundsOk`, the jet/ball path and the relevant imported frozen definitions.

Only `lunarR1.M` changes among parameter fields: `1987/1000 → 203/100`. All three σ fields remain `1987/1000`; `err`/`disp` remain arguments. The three helper smallness statements are intentionally restated, so the phrase “only change to declarations” must be understood as “only parameter-field change.”

## Declaration review

Names below have prefix `KAM.SpinOrbit`; line numbers refer to `KAM/SpinOrbit/LunarParams.lean`.

| Node / line | Declaration | Verdict | Reason |
|---|---|---|---|
| Signed I.4 / 27 | `lunarR1TimeScale` | PASS | Exact signed body `237/125`. |
| Signed I.4 / 29 | `lunarR1Scalar` | PASS | Exact signed body `1 + 1/10^6`. |
| Signed I.4 / 32 | `lunarR1Kappa` | PASS | Exact signed quotient `c/s`. |
| Signed I.4 / 35 | `lunarR1` | PASS | Exact updated signed body, including the M comment; unchanged σ and other fields. |
| Signed I.4 / 54 | `lunarR1Kappa_div` | PASS | Exact signed type, kernel proof of `κ/42 = 316000/7000007`. |
| Static helper / 61 | `lunarR1StaticCore` | PASS | Faithful dimension-two parameter sub-conjunction of `checkStatic`. |
| Static helper / 67 | `lunarR1_staticCore_zero` | PASS | Kernel decision with zero budgets. |
| Static helper / 71 | `lunarR1_staticCore` | PASS | Holds for all rational budgets, stronger than the nonnegative-budget prose. |
| Static helper / 75 | `lunarR1_err_nonneg` | PASS | Exactly the omitted nonnegative-error conjunct, from `0 ≤ err`. |
| Static helper / 80 | `lunarR1_staticCore_gen2` | PASS | Positive conservative budgets `4.1e-78` and `7.9e-78`, above the measured budgets. |
| C₁ helper / 89 | `lunarR1_smallness_C1` | PASS | Checker's exact strict inequality at `9/10^76`. |
| C₁ helper / 96 | `lunarR1_smallness_C1_fails` | PASS | Same strict inequality false at `1/10^75`. |
| C₂ helper / 104 | `lunarR1_smallness_C2` | PASS | Checker's displacement inequality at error `9/10^76`, displacement `1/10^39`. |
| Box helper / 112 | `lunarR1Box` | PASS | Rational center/radius enclosure; no change in this delta. |
| Ray helper / 118 | `lunarR1_rayMargins` | PASS | Both lower/upper boxes and both margins decided directly; independent of M. |
| Norm helper / 128 | `lunarR1Box_normLo` | PASS | Explicit coordinate bound is the natural max-reduction premise of a distinct conditional helper. |

The four signed definition blocks compare byte-for-byte equal to the current signature file. A fresh namespace copy of those definitions and the signed theorem elaborated at default settings. `rfl` checks compared each definition, including the parameter record for arbitrary budgets; `type_of%` checked the theorem type. A fresh theorem with the signed conclusion and body `by exact KAM.SpinOrbit.lunarR1Kappa_div` also elaborated. There are no explicit binders to supply. Generic frozen-provider type/seal probes are otherwise inapplicable.

## Definition classification and hypotheses

All six definitions are intended on their whole carriers:

- `lunarR1TimeScale`, `lunarR1Scalar`, `lunarR1Kappa`: exact rational constants with nonzero denominators.
- `lunarR1 err disp`: pure rational data; preserves arbitrary input budgets, including negative ones, without fallback. Checker predicates establish admissibility separately.
- `lunarR1StaticCore`: Bool predicate containing the fifteen nontrivial retained parameter conjuncts of dimension-two `checkStatic`. Shape, weights, π enclosure, frequency margins and nonnegative error are outside its stated scope. It does not claim a full static or certificate check.
- `lunarR1Box a b`: two explicit rational center/radius pairs. Radius `κ|b|/(3118·10^6)` is nonnegative; no indexing fallback is used here.

No new abbrev/structure, hidden proof field, conclusion-shaped analytic premise, weakened checker norm or imported provider occurs. The full KAM import closure has 99 files, no provider import and no DRAFT_SORRY anchor; all 19 encountered frozen definitions are manifest-SEALED. The conditional norm helper does not replace the independently decided concrete ray checks.

## Independent numerical verification

The probe evaluated the actual `isoC1Q`/`isoC2Q` expressions with the same argument order as `checkSmallness` (`KAM/Certificate/Defs.lean:285`). With `p = lunarR1 0 0`, put

`T = p.γ^4 * p.rho^(4*p.tau) / isoC1Q 2 p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT p.μ p.nuRay p.γbar`.

Exact output:

```text
T = 5415673711196611889500450363905948435681950325656135570526123046875 /
5541893568355888510943158276183704823811240097690100147758596141563896907077199650084272944402787269610404669483257062655014116150061547126784
k = 45925799347544020570983273203846743840910961055557416637225569878016 /
268717291620682321124048534765625
```

Here `k = isoC2Q / (γ²ρ²)`. Both outputs exactly match the handoff. An additional kernel-decided example proves the strict bracket `9/10^76 < T ∧ T < 1/10^75`; another proves `0 < k`. Thus the pre-checks are non-vacuous. `T = 9.7722441696102037932e-76`, `log10 T = -75.010005690267…`; `k = 1.7090749564554355185e35`, `log10 k = 35.232761110387…`.

Python `fractions.Fraction` arithmetic on those exact outputs, followed by 45-digit Decimal conversion, gives:

| Error budget | Exact headroom expression | Headroom | Required displacement `k*err` |
|---|---|---|---|
| `403/10^80` | `T*10^80/403` | `242.48744837742441174285…` | `6.8875720745154051396e-43` |
| `784/10^80` | `T*10^80/784` | `124.64597155115055858721…` | `1.3399147658610614465e-42` |

The handoff's ×242.5 and ×124.6 are correct rounded values. At `9e-76`, `k*err ≈ 1.53816746e-40 < 1e-39`.

### Hamiltonian-bound spot-check

`hamBoundsOk` (`KAM/Certificate/Defs.lean:151-161`) uses the full Hessian double sum as its last conjunct; both off-diagonal angle entries count. From the landed expression (`KAM/SpinOrbit/Rotated.lean:86-91,124`) the corresponding closed-form majorant is

`c * (1 + Σ_{m=1}^7 ε|A_m|(2π)^2 (2+|2-m|)^2 exp(2πρ_H(2+|2-m|)))`.

Independent Python calculation using the exact coefficient polynomials from `KAM/SpinOrbit/Model.lean:65-74`, `c=237/125`, `ρ_H=257/10000`, gives `2.0205300738032`. Thus `2.03` exceeds it by approximately `0.0094699262`.

A separate Lean scratch probe directly evaluated `(soRotHamExprScaled (237/125)).jet.prog.balls`, then the actual `sumRangeQ`/`slotMagQ` double sum in the binding conjunct. Inputs: `weightH = ⟨257/10000,1175246440729/10^12⟩`, `expOrder=1`; lower centers `[48769/50000,24983/50000]`, radii `[191/12500,127/20000]`; upper first center/radius replaced by `51231/50000`, `1529/100000`. The slot-ball computation succeeds on both domains and returns the identical exact sum:

```text
3232848162025963525876220946361919404051524016135220576405503695711671087347718658492665124096754817015620886677843450755477477 /
1600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
```

This is `2.0205301012662273…`. Exact Fraction comparisons show it is below `203/100` and above `1987/1000`. The slight excess over the closed form is consistent with outward ball/π enclosure arithmetic. This is a computational spot-check using an auditor-selected rational weight, not a kernel proof of weight validity or the completed certificates' `checkHamBounds`; no such certificate closure is inferred. It independently confirms the reported value and the reason for raising M.

## Fresh checks and outputs

All Lean/Lake invocations were serialized and inherited `LEAN_NUM_THREADS=1`; each ran at `nice -n 5`. No resource override, cache update, full-library rebuild or generated-file edit was used.

1. Targeted compile gate:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sor1b KAM.SpinOrbit.LunarParams
```

Exit 0. Output: `[inp-gate] slot 1 acquired 23:22:17 for KAM.SpinOrbit.LunarParams`; `Build completed successfully (3250 jobs).` Replayed upstream warnings only: PiHigh:218 unused `Nat.succ_eq_add_one`; Expr/Basic:85 unused `hS`. No package errors or default-heartbeat failures.

2. Signed definitions/type/theorem-body, numerical probes and every public theorem's axioms:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOR1BAudit.lean
```

Exit 0. Exact axiom output:

```text
'KAM.SpinOrbit.lunarR1Kappa_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_err_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore_gen2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C1_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_rayMargins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1Box_normLo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.LunarParams
```

Exit 0; exact output: `replaying KAM.SpinOrbit.LunarParams`. This is the sole changed Lean module; there are no separate provider/lemma modules in the delta.

4. Landed Hamiltonian/ball spot-check:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/HamSpot.lean
```

Exit 0; exact rational outputs given above, identical for both domains.

5. Source lint:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the brief-permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1382 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All substantive source, module, frozen-anchor and ABI checks pass. The generated root was not regenerated.

6. Short names:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sor1b KAM.SpinOrbit.LunarParams
```

Exit 0: `short-name check OK (no reused public short name)`.

7. Source/protected-path checks: `LunarParams.lean` has 136 lines and zero lines over 100 columns. Module header, public import, docstring, exposed public section present. No forbidden token/resource override/native decision in the changed file. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty; `git diff --check` exits 0. No state-changing git command was run.

## Documentation defects, errata and limitations

1. **Updated signature prose is stale.** `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean:348-350` still says “𝔪 = M = σK = σB = σT = 1987/1000” and “threshold 10^{-74.669}”, but its authoritative updated body at :366 says `M := 203 / 100`. The correct new threshold is `10^-75.01000569`. This is design-document inconsistency, not a proof defect. The production module correctly separates M from the σ fields.
2. **Tracked design copy is superseded.** `docs/tracks/SO/design/SO-LEAN-DESIGN.md:500-506` still uses “M = σK = σB = σT = 1987/1000” and the old threshold; Appendix I.4 at :2432 still has `M := 1987 / 1000`. The producer brief explicitly selects the updated external signed body. Synchronize the descriptive design and embedded signature before treating the tracked design as a current specification. Older O5 summary :121 also retains Revision-5 values `39/20`, `7/4`; these are historical rather than current R1B parameters.
3. **Prior majorant mismatch confirmed within the requested scope.** The SO-DATA-1 finding that the SO-GEN2 estimate fails to pay the landed Hessian double sum is supported by both independent spot-checks. Raising M repairs this parameter shortfall; it does not validate all generated data or any unrun checker stage. No suspected defect in a pinned external mathematical source was found.

No implementation deviation introduced by the auditor. Only this report was added to repository files. Audit probes and their local logs were removed from `.lake/abi-scratch/` after their results were recorded. Generated root left unchanged as directed. Remaining scope limitation: full lunar certificate checks, barriers, confinement and any frozen-anchor seal are outside SO-R1B.
